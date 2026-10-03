import SigGolfCandidate.T3M.Verify.DigestGate

/-!
# The FTS stream machine: invariants at the block boundaries (T3M)

Ghost context `FCtx` (public key, witness, digest answer `a`): `idx = a mod 2^31`, the selections, the global leaf
`g s = selLeaf sel_c j` of leaf slot `s = 3 c + j`.

* `WitF w ptr m` : the witness words of the header `[0, 64)`, of the leaf blocks outside their `T` slots, and of the
  stream (and the zero memory after the witness) from the header pointer `ptr` on are original — **an overflowing
  stream reads only original witness bytes** (the verifier writes only behind the pointer and inside the segment
  being hashed);
* `FB F c m` : the constant registers (`gkF`, coordinate words `packedCK c F.idx`, `s6 = idx`), `Glob`, the 21 sorted heap
  indices at `ETAB`, the stack sentinel, the zero pads of the merge frames;
* `StackOK stk m` : stack element `i` (from the bottom) in merge frame `i + 1` (`pnode` at `+0`, `Q` at `-16`);
* `PendOK` : the pending block (leaf block with its header, or the popped merge frame `[pnode | T | 0 | node]`);
* boundaries `LeafIn` (leaf code), `DispIn` (dispatch), `RungIn` (fold `i` of a segment), `TailIn` (after the
  segment's last hash), `CoordIn` (`coord_end`);
* budgets: `segRem`, `tailsRem`, `leafRem`, `coordRem`, the accepting bound `Afts` and the all-oracle bound `Cfts`.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

structure FCtx where
  pk : Digest
  w : WBytes
  a : HashOutput

namespace FCtx
def idx (F : FCtx) : Nat := F.a.toNat % 2 ^ 31
def sel (F : FCtx) (c : Nat) : Selection := selC F.a c
/-- The global leaf `256 bucket + x_j` of leaf slot `s = 3 c + j` (sorted). -/
def g (F : FCtx) (s : Nat) : Nat := T3M.selLeaf (F.sel (s / 3)) (s % 3)
theorem idx_lt (F : FCtx) : F.idx < 2 ^ 31 := Nat.mod_lt _ (by decide)
end FCtx

/-! ## Witness frontier -/

/-- A leaf-region word outside the 21 header slots (`T` at `+16, +24` of each leaf block). -/
def leafNT (o : Nat) : Prop := 64 ≤ o ∧ o < 1088 ∧ (o - 64) % 48 ≠ 16 ∧ (o - 64) % 48 ≠ 24

/-- At a dispatch with header pointer `ptr`. -/
def WitF (w : WBytes) (ptr : Nat) (m : MachineState) : Prop :=
  Orig w (fun o => o < 64 ∨ leafNT o ∨ ptr ≤ o) m

/-! ## The common part -/

/-- `w0` of the node / leaf headers of coordinate `c` (`hdr0 10 c idx 0`, `hdr0 9 c idx 0`). -/
def nodeW0 (c : Nat) : Nat := 0xa01 + 65536 * c
def leafW0 (c : Nat) : Nat := 0x901 + 65536 * c

structure FB (F : FCtx) (c : Nat) (m : MachineState) : Prop where
  glob : Glob gkF F.w F.pk m
  ck : KnownOK (packedCK c F.idx) m
  idx : m.getReg .x22 = BitVec.ofNat 64 F.idx
  etab : ∀ s, s < 21 → m.getMem (BitVec.ofNat 64 (ETAB + 8 * s)) = BitVec.ofNat 64 (TAB + 8 * F.g s)
  sent : m.getMem (BitVec.ofNat 64 SENTINEL) = -1#64
  fpad : ∀ d, 1 ≤ d → d ≤ 2 → m.getMem (BitVec.ofNat 64 (frameA d + 32)) = 0 ∧
    m.getMem (BitVec.ofNat 64 (frameA d + 40)) = 0
  hc : c < 7

/-- Stack element `i` (from the bottom, Core's `segLoop` stack has its top first) in merge frame `i + 1`. -/
def StackOK (stk : List (Digest × Nat)) (m : MachineState) : Prop :=
  ∀ i, i < stk.length → DigAt m (frameA (i + 1)) (stk.reverse.getD i (0, 0)).1 ∧
    m.getMem (BitVec.ofNat 64 (frameA (i + 1) - 16)) = FtsRev.rv (stk.reverse.getD i (0, 0)).2 ∧
    (stk.reverse.getD i (0, 0)).2 < 4096

/-- The roots of the finished coordinates in the forest frame. -/
def RootsOK (roots : List Digest) (m : MachineState) : Prop :=
  ∀ k, k < roots.length → DigAt m (forestSlot k) (roots.getD k 0)

/-- The pending block of the next segment (at `x10`), with its header written. -/
def PendOK (F : FCtx) (c d : Nat) (node : Digest) (m : MachineState) : Pending → Prop
  | .leaf s g => s / 3 = c ∧ s < 21 ∧ g = F.g s ∧ m.getReg .x10 = BitVec.ofNat 64 (WIT + 64 + 48 * s) ∧
      m.getMem (BitVec.ofNat 64 (leafT s)) = BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx) ∧
      m.getMem (BitVec.ofNat 64 (leafT s + 8)) = FtsRev.rv (2048 + g)
  | .merge heap left => d + 1 ≤ 2 ∧ heap < 2048 ∧ m.getReg .x10 = BitVec.ofNat 64 (frameA (d + 1)) ∧
      DigAt m (frameA (d + 1)) left ∧
      m.getMem (BitVec.ofNat 64 (frameA (d + 1) + 16)) = BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) ∧
      m.getMem (BitVec.ofNat 64 (frameA (d + 1) + 24)) = FtsRev.rv heap ∧
      DigAt m (frameA (d + 1) + 48) node

def isLeafP : Pending → Bool
  | .leaf _ _ => true
  | .merge _ _ => false

/-! ## Bounds -/

/-- Segments done before a dispatch of leaf `j` with stack depth `d` in coordinate `c` (every finished
coordinate had exactly five). -/
def segsDone (c j d : Nat) : Nat := 5 * c + 2 * j - d

structure SegBnd (c j d ptr folds : Nat) : Prop where
  hc : c < 7
  hj : j < 3
  hd : d ≤ j ∧ d ≤ 2
  hptr : ptr = 1088 + 8 * segsDone c j d + 80 * folds
  hf : folds ≤ 11 * segsDone c j d

/-! ## Boundaries -/

/-- The link of the leaf loop of leaf `j` of coordinate `c`. -/
def lnk (c j : Nat) : Nat := 0x1000 + 4 * leafRet (3 * c + j)

/-- At the code of leaf `j` of coordinate `c` (the previous leaves' results on the stack). -/
structure LeafIn (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (ptr folds : Nat)
    (m : MachineState) : Prop where
  fb : FB F c m
  pc : m.pc = pcOf (leafPc (3 * c + j))
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)
  a5 : m.getReg .x15 = BitVec.ofNat 64 (frameA stk.length)
  s4 : j = 1 → m.getReg .x20 = BitVec.ofNat 64 tbN
  s9 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)
  stack : StackOK stk m
  rts : RootsOK roots m
  hroots : roots.length = c
  wit : WitF F.w ptr m
  bnd : SegBnd c j stk.length ptr folds

/-- At a dispatch (`lbu gp, 880(a4)`) of a segment of leaf `j`: Core's `segLoop` arguments. -/
structure DispIn (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (pend : Pending)
    (E ptr folds : Nat) (node : Digest) (m : MachineState) : Prop where
  fb : FB F c m
  pc : (isLeafP pend = true ∧ m.pc = pcOf (leafDisp (3 * c + j))) ∨
    (isLeafP pend = false ∧ ∃ k, k < 141 ∧ m.pc = pcOf (mDispPc k) ∧ m.getReg .x17 = BitVec.ofNat 64 (lnk c j))
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)
  a5 : m.getReg .x15 = BitVec.ofNat 64 (frameA stk.length)
  s4 : m.getReg .x20 = BitVec.ofNat 64 (tabPc (tselJ j))
  s7 : m.getReg .x23 = FtsRev.rv E
  s9 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)
  stack : StackOK stk m
  pnd : PendOK F c stk.length node m pend
  rts : RootsOK roots m
  hroots : roots.length = c
  wit : WitF F.w ptr m
  bnd : SegBnd c j stk.length ptr folds
  hE : E < 4096
  hleaf : isLeafP pend = true → stk.length + 2 * j ≤ 2 * j + j

/-- The fold block `i` of the segment at `ptr`, its words as witness offsets. -/
def fblk (ptr i : Nat) : Nat := ptr + 8 + 80 * i

/-- At fold `i` of a segment (header at `ptr`, `a` folds, variant `X`): the current node in the block's current slot
(side `t = E % 2`: `R` if `t = 1`), the sibling and pad original. -/
structure RungIn (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (X a i E ptr folds : Nat)
    (node : Digest) (m : MachineState) : Prop where
  fb : FB F c m
  pc : m.pc = pcOf (foldPc (tselJ j) X a ((segSides (wbyte F.w ptr).toNat)) (E % 2) i)
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880 + 8 + 80 * a)
  a5 : m.getReg .x15 = BitVec.ofNat 64 (frameA stk.length)
  s4 : m.getReg .x20 = BitVec.ofNat 64 (tabPc (tselJ j))
  s7 : m.getReg .x23 = FtsRev.rv E
  s8 : m.getReg .x17 = BitVec.ofNat 64 (lnk c j)
  s9 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)
  stack : StackOK stk m
  rts : RootsOK roots m
  hroots : roots.length = c
  nd : DigAt m (WIT + fblk ptr i + 48 * (E % 2)) node
  wit : Orig F.w (fun o => o < 64 ∨ leafNT o ∨ fblk ptr i + 80 ≤ o ∨ o = fblk ptr i + 32 ∨ o = fblk ptr i + 40 ∨
    (E % 2 = 1 ∧ (o = fblk ptr i ∨ o = fblk ptr i + 8)) ∨ (E % 2 = 0 ∧ (o = fblk ptr i + 48 ∨ o = fblk ptr i + 56))) m
  bnd : SegBnd c j stk.length ptr folds
  hX : X = segX (tselJ j) (wbyte F.w ptr).toNat ∧ a = segA (wbyte F.w ptr).toNat
  hi : i < a ∧ a ≤ 11
  hE : E < 4096
  sides : ∀ k, i+k < min a 3 → E/2^k%2 = (segSides (wbyte F.w ptr).toNat)/2^(i+k)%2

/-- The destination of the last hash of variant `X` at stack depth `d`. -/
def destA (c X d : Nat) : Nat := if X = 0 then frameA d + 48 else if X = 1 then frameA (d + 1) else forestSlot c

/-- After the last hash of a segment of variant `X` (tail copy `k`), `ptr` = the next header, `folds` updated. -/
structure TailIn (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (X E ptr folds : Nat)
    (node : Digest) (m : MachineState) : Prop where
  fb : FB F c m
  pc : ∃ k, k < 141 ∧ m.pc = pcOf (tailPc X k)
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)
  a5 : m.getReg .x15 = BitVec.ofNat 64 (frameA stk.length)
  s4 : m.getReg .x20 = BitVec.ofNat 64 (tabPc (tselJ j))
  s7 : m.getReg .x23 = FtsRev.rv E
  s8 : m.getReg .x17 = BitVec.ofNat 64 (lnk c j)
  s9 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)
  stack : StackOK stk m
  rts : RootsOK roots m
  hroots : roots.length = c
  nd : DigAt m (destA c X stk.length) node
  wit : WitF F.w ptr m
  bnd : c < 7 ∧ j < 3 ∧ stk.length ≤ j ∧ stk.length ≤ 2 ∧
    ∃ folds0 a, SegBnd c j stk.length (ptr - 8 - 80 * a) folds0 ∧ a ≤ 11 ∧ folds = folds0 + a
  hX : X < 3 ∧ (X = 1 → j < 2) ∧ (X = 2 → j = 2)
  hE : E < 4096

/-- At `coord_end_c`: the root of coordinate `c` in its forest slot. -/
structure CoordIn (F : FCtx) (c : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (E ptr folds : Nat)
    (node : Digest) (m : MachineState) : Prop where
  fb : FB F c m
  pc : m.pc = pcOf (coordEndPc c)
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)
  a5 : m.getReg .x15 = BitVec.ofNat 64 (frameA stk.length)
  s7 : m.getReg .x23 = FtsRev.rv E
  s9 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)
  stack : StackOK stk m
  rts : RootsOK roots m
  hroots : roots.length = c
  nd : DigAt m (forestSlot c) node
  wit : WitF F.w ptr m
  bnd : stk.length ≤ 2 ∧ ∃ folds0 a, SegBnd c 2 stk.length (ptr - 8 - 80 * a) folds0 ∧ a ≤ 11 ∧ folds = folds0 + a
  hE : E < 4096

/-! ## Budgets -/

def segRem (c j d : Nat) : Nat := 5 - 2 * j + d + 5 * (6 - c)
def tailsRem (c j d : Nat) : Nat := 4 * ((2 - j) + 2 * (6 - c)) + 7 * (d + 2 - j + 2 * (6 - c)) + (1 + (6 - c))
def leafRem (c j : Nat) : Nat := (if j = 0 then 13 else if j = 1 then 7 else 0) + 20 * (6 - c)
def coordRem (c : Nat) : Nat := 7 * (6 - c) + 4

/-- Accepting runs from a dispatch: 15 per segment, 16 per fold (at most 124 in total), tails, leaf codes,
coordinate ends, the forest (24). -/
def Afts (c j d folds A' : Nat) : Nat :=
  15 * segRem c j d + 15 * (119 - folds) + tailsRem c j d + leafRem c j + coordRem c + 24 + A'
/-- Every run from a dispatch: at most 191 per segment. -/
def Cfts (c j d C' : Nat) : Nat := 191 * segRem c j d + tailsRem c j d + leafRem c j + coordRem c + 24 + C'

end SigGolfCandidate.T3M.Verify
