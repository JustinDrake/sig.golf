import SigGolfCandidate.Verify.FoldRuns

/-! # W1a chains (in place, triple dispatch, layer-shared code): expected symbolic results

Chain `i` of layer `lay` is hashed in its witness block `blk(lay, i) = WIT + blockOff lay i`
(`[tweak slot 16 | pad 32 | value 16]`). The 42 chains form the 14 triples `(3t, 3t+1, 3t+2)`;
one interleaved table (`ttab`, 512 rows `k = dA + 8 dB + 64 dC` of 16 slots of 8 words) holds in
slot `t` of row `k` chain `A = 3t`'s head (digit `< 7`) or its digit-7 copy and a jump into the
code shared by all layers for `(t, dB, dC)`: `A`'s rungs `1 .. 7` (entered at `dA + 1`), then `B`,
then `C` (head and rungs `d + 1 .. 7`, or the digit-7 copy), then the extraction of triple
`t + 1` and its `jalr`, or for `t = 13` the return `jalr zero, ra`.

The code is layer independent: it addresses the blocks relative to `s6 = x22` (the layer base
`blk(lay, 0) + 1344`), initializes the first tweak from `x27`, then bumps the running tweak
word 0 in `s9 = x25` by `t3 = 2^40`, and stores
tweak word 1 from `t6 = x31`. Its runs are therefore checked once, with `x22`, `x25`, `x31`,
`a0 = x10`, `a2 = x12` symbolic; the memory writes and obligations have the base `x22` or `x10`.

* head: `addi a0, s6, off; addi a2, a0, 48; add s9, s9, t3; sd s9, 0(a0); sd t6, 8(a0)`;
  chain 0 uses `mv s9, s11` instead of the add, including on the digit-7 copy path;
* rung `mu`: `sb MU_{mu-1}, 4(a0); [li a2, slot_i (mu = 7)]; ecall`;
* digit 7: `ld gp, off+48(s6); ld a4, off+56(s6); sd gp, slot_i; sd a4, slot_i+8; add s9, s9, t3`.
-/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- Known registers in the chain code (layer independent). -/
def chK0 : List (Reg × Word) := gkL ++ [(.x11, 64)]

/-- The offset of chain block `i` from the layer base `s6 = blk(lay, 0) + 1344`. -/
def offW (i : Nat) : Word := BitVec.ofNat 64 (64 * i) - BitVec.ofNat 64 1344

/-- The leaf-pk slot of chain `i` (`LB + 32 + 16 i`). -/
def slotA (i : Nat) : Nat := 0x360 + 16 * i

/-- The address `s6 + off_i + k` as the executor normalizes it. -/
def bk (i k : Nat) : Addr := norm (addC (.reg .x22) (offW i + BitVec.ofNat 64 k))

/-- The doubleword load at `s6 + off_i + k`. -/
def ldK (i k : Nat) : E := .ld (bk i k).toE

/-- The step byte `mu - 1` as a register value. -/
def posE (d : Nat) : E := .c (BitVec.ofNat 64 d)

/-- The running tweak word 0 after the bump. -/
def s9E (i : Nat) : E := if i = 0 then addC (.reg .x27) (-256#64) else addC (.reg .x25) K40

/-! ## Code tables -/

def triBase (t dB dC : Nat) : Nat := triBaseTab.getD (64 * t + 8 * dB + dC) 0
/-- The length of the code of a triple's second or third chain at digit `d`. -/
def partLen (d : Nat) : Nat := if d = 7 then 4 else 5 + 2 * (7 - d)
def pcB (t dB dC : Nat) : Nat := triBase t dB dC + 15
def pcC (t dB dC : Nat) : Nat := pcB t dB dC + partLen dB
def pcX (t dB dC : Nat) : Nat := pcC t dB dC + partLen dC
/-- Slot `t` of row `k` of the triple table. -/
def entW (t k : Nat) : Nat := ttabIdx + 128 * k + 8 * t

/-- The ecall pc of a rung starting at word `p` (step `mu`). -/
def rungEnd (p mu : Nat) : Nat := p + (if mu = 7 then 2 else 1)

/-! ## Expected results -/

/-- Rung `mu` of chain `i` (from its `sb`, `a0` symbolic), stopping at its `ecall`. -/
def rungExp (i mu p : Nat) : PRes :=
  let rf := RegFile.withKnown chK0
  ⟨⟨if mu = 7 then rf.set .x12 (cw (slotA i)) else rf,
    [(⟨some (.reg .x10), 0⟩, .bin (.st .b 4) (.ld (.reg .x10)) (posE (mu - 1)))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 4⟩ 1]⟩,
    pcOf (rungEnd p mu), true, (if mu = 7 then 2 else 1), (if mu = 7 then 2 else 1), [], none⟩

/-- The head of chain `i` at digit `d < 7` and its first rung (`mu = d + 1`, at word `p`), stopping at
the rung's `ecall`; `j` = the table entry's jump in between (chain `A`). -/
def headExp (i d p : Nat) (j : Bool) : PRes :=
  let a0 : E := addC (.reg .x22) (offW i)
  let rf := (RegFile.withKnown chK0).set .x10 a0
  let n := 4 + (if j then 1 else 0) + (if d = 6 then 2 else 1)
  ⟨⟨rf.set .x12 (if d = 6 then cw (slotA i) else addC a0 48),
    [(bk i 0, .bin (.st .b 4) a0 (posE d)), (bk i 8, .reg .x31)],
    [.align8 (.reg .x22), .valid (bk i 4) 1, .valid (bk i 8) 8, .valid (bk i 0) 8]⟩,
    pcOf (rungEnd p (d + 1)), true, n, n, [], none⟩

/-- The digit-7 copy of chain `i` into its leaf-pk slot, stopping at `q` (the next chain's code);
`j` = the table entry's jump. -/
def copyExp (i q : Nat) (j : Bool) : PRes :=
  let n := 4 + (if j then 1 else 0)
  ⟨⟨((RegFile.withKnown chK0).set .x3 (ldK i 48)).set .x14 (ldK i 56),
    [(⟨none, BitVec.ofNat 64 (slotA i + 8)⟩, ldK i 56), (⟨none, BitVec.ofNat 64 (slotA i)⟩, ldK i 48)],
    [.valid (bk i 56) 8, .valid (bk i 48) 8]⟩,
    pcOf q, false, n, n, [], none⟩

/-- The table index of triple `t` (`a4` before the `jalr`). -/
def triX (t : Nat) : E :=
  let w : Reg := if t < 7 then .x16 else .x17
  let sh := 9 * (t % 7)
  let e0 : E := if sh < 9 then mkBin .sll (.reg w) (cw (9 - sh))
    else if 9 < sh then mkBin .srl (.reg w) (cw (sh - 9)) else addC (.reg w) 0
  mkAdd (mkBin .and e0 (.c TMASK)) (.c TTA5)

/-- The dispatch target of triple `t` (`jalr 32 t - 2048(a4)`). -/
def triTgt (t : Nat) : E :=
  mkBin .and (mkAdd (triX t) (.c (BitVec.ofNat 64 (32 * t) - BitVec.ofNat 64 2048))) (.c (~~~1#64))

/-- Dispatch omits the register copy when the digit shift is zero. -/
def xSteps (t : Nat) : Nat := if t % 7 = 0 then 3 else 4

/-- After chain `C` of triple `t`: the extraction and dispatch of triple `t + 1`, or the return. -/
def xExp (t : Nat) : PRes :=
  if t + 1 < 14 then
    ⟨⟨(RegFile.withKnown chK0).set .x14 (triX (t + 1)), [], []⟩, 0, false, xSteps t, xSteps t, [], some (triTgt (t + 1))⟩
  else
    ⟨⟨RegFile.withKnown chK0, [], []⟩, 0, false, 1, 1, [], some (mkBin .and (.reg .x1) (.c (~~~1#64)))⟩

/-! ## Checks -/

def rungCheck (i mu p : Nat) : Bool := optBeq (runAt chK0 [] p []) (rungExp i mu p)

/-- The code of chain `i` (a triple's `B` or `C`) at digit `d`, from word `p` to `q`. -/
def partCheck (i d p q : Nat) : Bool :=
  if d = 7 then optBeq (runAt chK0 [q] p []) (copyExp i q false)
  else optBeq (runAt chK0 [] p []) (headExp i d (p + 4) false) &&
    (List.range' (d + 2) (6 - d)).all fun mu => rungCheck i mu (p + 4 + 2 * (mu - d - 1))

/-- Table slot `t` of row `k`. -/
def entCheck (t k : Nat) : Bool :=
  let dA := k % 8
  let dB := k / 8 % 8
  let dC := k / 64
  if dA = 7 then optBeq (runAt chK0 [pcB t dB dC] (entW t k) []) (copyExp (3 * t) (pcB t dB dC) true)
  else optBeq (runAt chK0 [] (entW t k) []) (headExp (3 * t) dA (triBase t dB dC + 2 * dA) true)

/-- The shared code of `(t, dB, dC)`: `A`'s rungs `2 .. 7`, `B`, `C`, the extraction or return. -/
def blkCheck (t dB dC : Nat) : Bool :=
  ((List.range' 2 6).all fun mu => rungCheck (3 * t) mu (triBase t dB dC + 2 * (mu - 1))) &&
  partCheck (3 * t + 1) dB (pcB t dB dC) (pcC t dB dC) &&
  partCheck (3 * t + 2) dC (pcC t dB dC) (pcX t dB dC) &&
  optBeq (runAt chK0 [] (pcX t dB dC) [.jmp]) (xExp t)

/-- Everything of triple `t`: its 512 table slots and its 64 code blocks. -/
def triCheck (t : Nat) (lo n : Nat) : Bool :=
  ((List.range' lo n).all fun k => entCheck t k) &&
  ((List.range' (lo / 8) (n / 8)).all fun q => blkCheck t (q / 8) (q % 8))

end SigGolfCandidate.Verify
