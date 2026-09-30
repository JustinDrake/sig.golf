import SigGolfCandidate.Verify.FoldRuns

/-! # Chains (JALR dispatch tables, row-specific pair dispatch): expected symbolic results

The 42 chains of a layer form the units `(0,1) .. (18,19), 20, (21,22) .. (39,40), 41`. A pair
`(A, B)` has one 64-entry table for `A`, indexed by `dA + 8 dB`; the code of the pair is
duplicated per digit `dB` of `B` ("copy" `k = dB`): copy `k` holds `A`'s seven steps, then `B`'s
head (without `jalr`, it stores `B`'s start value itself) and `B`'s steps `k + 1 .. 7`, then the
next unit's dispatch and head. A single chain (20, 41) has an 8-entry table and one copy.
-/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def tget (tab : List (List Nat)) (lay i : Nat) : Nat := (tab.getD lay []).getD i 0
def tget3 (tab : List (List (List Nat))) (lay i k : Nat) : Nat := ((tab.getD lay []).getD i []).getD k 0

/-- Step-1 pc of code copy `k` of chain `i` (virtual for the pair-second chain: its step `mu > k`
is at `s1K + 2 (mu - 1)`). -/
def s1K (lay i k : Nat) : Nat := tget3 s1KTab lay i k
/-- The end of copy `k` of chain `i`: the next chain's head (for a pair-first chain, the code of the
pair-second chain at the same copy). -/
def nextK (lay i k : Nat) : Nat := s1K lay i k + 15
/-- The end of the single (one-copy) chain `i`, used for chain 41 (the leaf code follows). -/
def nextPc' (lay i : Nat) : Nat := nextK lay i 0
def tabAddr (lay i : Nat) : Nat := tget tabTab lay i
def bVal (lay i : Nat) : Nat := tget bTab lay i
def hasLui (lay i : Nat) : Bool := (luiTab.getD lay []).getD i false

/-- B at the checkpoint of chain `i`. -/
def bIn (lay i : Nat) : Nat := if i = 0 then bVal lay 0 else bVal lay (i - 1)

/-- Chain kinds: pair-first chains (with a dispatch prep), pair-second, singles. -/
def isSingle (i : Nat) : Bool := i = 20 || i = 41
def isFirst (i : Nat) : Bool := !isSingle i && (i % 21) % 2 = 0
/-- Pair-second chains: no table and no `jalr` (the pair's table dispatches on both digits). -/
def isSec (i : Nat) : Bool := !isSingle i && !isFirst i
/-- The chain's segment starts with a dispatch prep (not for chain 0: prep in the layer code). -/
def hasPrep (i : Nat) : Bool := i ≠ 0 && (isFirst i || isSingle i)
/-- The number of code copies of chain `i`. -/
def nCp (i : Nat) : Nat := if isSingle i then 1 else 8

def hWord (lay : Nat) : Nat := 0x101 + 65536 * lay

/-- Known registers in the chain blocks (`a2` is set by each head and by step 7). -/
def chK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x27, BitVec.ofNat 64 (hWord lay)), (.x10, 0xC0), (.x11, 64)]

/-- ... and the answer slot `a2 = CB + 48` inside a chain. -/
def chKa (lay : Nat) : List (Reg × Word) := chK lay ++ [(.x12, 0xF0)]

def headK (lay i : Nat) : List (Reg × Word) := chK lay ++ [(.x15, BitVec.ofNat 64 (bIn lay i))]

def dReg (i : Nat) : Reg := if i < 21 then .x16 else .x17

/-- The dispatch register value computed by the prep of chain `i` (`r = i mod 21`). -/
def maskE (i : Nat) : E :=
  if isSingle i then mkBin .sll (mkBin .srl (.reg (dReg i)) (cw 60)) (cw 4)
  else if i % 21 = 0 then mkBin .and (mkBin .sll (.reg (dReg i)) (cw 4)) (cw 0x3F0)
  else mkBin .and (mkBin .srl (.reg (dReg i)) (cw (3 * (i % 21) - 4))) (cw 0x3F0)

def rE (lay i : Nat) : E := mkBin .add (maskE i) (cw (bVal lay i))

def chainAddr (lay i : Nat) : Nat := 0x800 + layBody lay + 16 * i

/-- A byte store `sb v, off(CB)` into the chain tweak word at CB. -/
def stB (off : Nat) (v : E) : E := .bin (.st .b off) (ldE 0xC0) v

/-- Chains `i < 7` store their index byte from a register that already holds `i` in the layers
(`zero, t1, t2, s0, s1, a3, s10`, see `baseK`/`gkL`), so their head has no `addi TP, i`. -/
def tagReg (i : Nat) : Bool := decide (i < 7)

/-- The `TP` update of a head: none when the index byte comes from a constant register. -/
def setTag (i : Nat) (rf : RegFile) : RegFile := if tagReg i then rf else rf.set .x4 (cw i)

/-- Head of chain `i`: (lui) (prep) `ld; ld; addi TP, i; sb TP, CB+5; addi a2, CB+48; jalr`,
stopping at the symbolic target; for `i < 7` the byte store is `sb R_i, CB+5` and `addi TP, i` is
absent (the stored byte is the same constant). -/
def headExp (lay i : Nat) : PRes :=
  let wa := chainAddr lay i
  let rf0 := RegFile.withKnown (headK lay i)
  let rf1 := if hasPrep i && hasLui lay i then rf0.set .x15 (cw (bVal lay i)) else rf0
  let rf2 := if hasPrep i then rf1.set .x14 (rE lay i) else rf1
  let rcur : E := if hasPrep i then rE lay i else .reg .x14
  let n := (if tagReg i then 5 else 6) + (if hasPrep i then 3 else 0) +
    (if hasPrep i && hasLui lay i then 1 else 0)
  ⟨⟨(setTag i ((rf2.set .x1 (ldE wa)).set .x2 (ldE (wa + 8)))).set .x12 (cw 0xF0),
    [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 5 (cw i))], []⟩, 0, false, n, n, [],
    some (mkBin .and (mkAdd rcur (.c (BitVec.ofNat 64 (tabAddr lay i) - BitVec.ofNat 64 (bVal lay i))))
      (.c (~~~1#64)))⟩

/-- Where the head of the pair-second chain `i` at copy `k` stops: at step `k + 1` (k < 7), else at
the next head. -/
def bStop (lay i k : Nat) : Nat := if k < 7 then s1K lay i k + 2 * k else nextK lay i k

/-- Where the pair-second chain `i` at copy `k` stores its start value: CB+48 (k < 7) or its
leaf slot (k = 7). -/
def bDst (i k : Nat) : Nat := if k < 7 then 0xF0 else 0x360 + 16 * i

/-- The length (= cycles) of the head of the pair-second chain `i` at copy `k`. -/
def bN (i k : Nat) : Nat := (if tagReg i then 4 else 5) + (if k < 7 then 2 else 3)

/-- Head of the pair-second chain `i` at copy `k` (its digit): the head without `jalr`
(`ld; ld; (addi TP, i); sb; addi a2, CB+48`), then `sd; sd` of the start value to `bDst i k`, and
for k = 7 a `nop`. The registers are those of `headExp` (the chain has no dispatch prep). -/
def bExp (lay i k : Nat) : PRes :=
  ⟨⟨(headExp lay i).st.regs,
    [(⟨none, BitVec.ofNat 64 (bDst i k + 8)⟩, ldE (chainAddr lay i + 8)),
     (⟨none, BitVec.ofNat 64 (bDst i k)⟩, ldE (chainAddr lay i)),
     (⟨none, BitVec.ofNat 64 0xC0⟩, stB 5 (cw i))], []⟩, pcOf (bStop lay i k), false, bN i k, bN i k, [], none⟩

/-- Step `mu ∈ 1..7` of copy `k`, from its label to its ecall: `sb MU_{mu-1}, 4(a0)` (byte 4 of the
chain tweak = `mu - 1`); step 7 also redirects `a2` to the leaf slot. -/
def stepExp (lay i k mu : Nat) : PRes :=
  let st := s1K lay i k + 2 * (mu - 1)
  if mu = 7 then
    ⟨⟨(RegFile.withKnown (chKa lay)).set .x12 (cw (0x360 + 16 * i)),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 4 (cw (mu - 1)))], []⟩, pcOf (st + 2), true, 2, 2, [], none⟩
  else
    ⟨⟨RegFile.withKnown (chKa lay),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 4 (cw (mu - 1)))], []⟩, pcOf (st + 1), true, 1, 1, [], none⟩

def ckeep : List Reg := [.x14, .x15, .x16, .x17, .x23, .x30, .x31]

def okC (o : Option PRes) (e : PRes) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  optBeq o e && resOK gkL e && knownB post e && keepB keep e

def entryIdx (lay i e : Nat) : Nat := (tabAddr lay i - 0x1000) / 4 + 4 * e

def nEnt (i : Nat) : Nat := if isSingle i then 8 else 64

def entDigit (i e : Nat) : Nat := if isSingle i then e else if isFirst i then e % 8 else e / 8

/-- The code copy that entry `e` of chain `i`'s table jumps into. -/
def entCp (i e : Nat) : Nat := if isSingle i then 0 else e / 8

def resBeq (a b : Result) : Bool :=
  SymState.beq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles

theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [SymState.beq_eq h1, E.beq_eq h2, h3, h4, h5]

/-- Table entry of chain `i` for its digit `d` into copy `k`, as a straight-line run ending at the `jal`. -/
def entryRes (lay i k d : Nat) : Result :=
  let dst := if d < 7 then 0xF0 else 0x360 + 16 * i
  let tgt := if d < 7 then s1K lay i k + 2 * d else nextK lay i k
  let n := if d < 7 then 3 else 4
  ⟨⟨RegFile.init,
    [(⟨none, BitVec.ofNat 64 (dst + 8)⟩, .reg .x2), (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)], []⟩,
    .c (pcOf tgt), .jump, n, n⟩

/-- Check the entries `e, e+1, ...` of a table whose code (from entry `e`) is `ws`. -/
def entChk (lay i : Nat) : List (BitVec 32) → Nat → Nat → Bool
  | _, _, 0 => true
  | ws, e, n + 1 =>
    (match symRun cfg0 ws (pcOf (entryIdx lay i e)) 4 with
     | some r => resBeq r (entryRes lay i (entCp i e) (entDigit i e))
     | none => false) && entChk lay i (ws.drop 4) (e + 1) n

def entriesCheck (lay i : Nat) : Bool :=
  isSec i || entChk lay i (codeFrom (entryIdx lay i 0)) 0 (nEnt i)

/-- The steps of every copy (for the pair-second chain, copy `k` has the steps `k + 1 .. 7`). -/
def stepsCheck (lay i : Nat) : Bool :=
  (List.range (nCp i)).all fun k => (List.range 7).all fun m =>
    (isSec i && decide (m < k)) ||
    okC (runAt (chKa lay) [] (s1K lay i k + 2 * m) []) (stepExp lay i k (m + 1))
      (chK lay ++ [(.x12, BitVec.ofNat 64 (if m = 6 then 0x360 + 16 * i else 0xF0))]) ckeep

def headKeep (i : Nat) : List Reg :=
  [.x16, .x17, .x23, .x30, .x31] ++ (if hasPrep i then [] else [.x14])

/-- The head of chain `i` at the end of copy `k` of chain `i - 1`. -/
def headOk (lay i k : Nat) : Bool :=
  if isSec i then
    okC (runAt (headK lay i) [bStop lay i k] (nextK lay (i - 1) k) []) (bExp lay i k)
      (chKa lay ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i)
  else
    okC (runAt (headK lay i) [] (nextK lay (i - 1) k) [.jmp]) (headExp lay i)
      (chKa lay ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i)

def headCheck (lay i : Nat) : Bool :=
  i == 0 || (List.range (nCp (i - 1))).all fun k => headOk lay i k

def chainCheck (lay i : Nat) : Bool := headCheck lay i && stepsCheck lay i && entriesCheck lay i

end SigGolfCandidate.Verify
