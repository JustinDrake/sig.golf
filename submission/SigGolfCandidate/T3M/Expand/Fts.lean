import SigGolfCandidate.T3M.Expand.Tail
import SigGolfCandidate.T3M.Search.DigestSearch
import SigGolfCandidate.T3M.Witness.Encode

/-!
# `expand`: the FTS phase interface (stream E)

`ftsFold` is the first statement of Core's `recoverFts` (the seven coordinates: `recoverChild` of the bucket subtree,
the three outer folds); `recoverFts_eq` splits `recoverFts` into it, the canonical-tail check and the forest pk.

`FtsSpec sk` is the machine statement of the FTS phase (`fts_coord` .. `fts_done`, words 65 .. 215, with
`recover_child` 824 .. 996): from `FtsPre` (after `ds_done`) the machine refines `ftsFold` within `ftsCost` cycles
and ends in `FtsPost` (the roots in the forest block, the secrets and the honest stream `streamBytes` in the witness).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Signature Selection recoverChild recoverFts nodeHash forestPk)
open SigGolfCandidate.T3M.Search (NODE NOUT ENC SelRows FailedAt)

set_option autoImplicit false

/-- One coordinate of Core's FTS fold (the body of `recoverFts`'s first `foldlM`). -/
def ftsStep (sig : Signature) (index : Nat) (chosen : List Selection) (state : Option (List Digest × Nat))
    (coord : Nat) : T3.M (Option (List Digest × Nat)) := do
  let some (roots,used) := state | pure none
  let sel := chosen.getD coord ⟨0,[]⟩
  let selected := sel.leaves.map (fun s => sel.bucket*128+s)
  let values := (List.range 3).map (fun j => sig.secrets ⟨(coord*3+j)%21,Nat.mod_lt _ (by decide)⟩)
  let some (value,next) ← recoverChild index coord selected values sig.proof 7 sel.bucket used | pure none
  let result ← (List.range 4).foldlM
    (fun (state : Option (Digest × Nat)) j => do
      let some (value,used) := state | pure none
      if h : used < 117 then
        let other := sig.proof ⟨used,h⟩
        let pair := if sel.bucket/2^j%2=0 then (value,other) else (other,value)
        let parent ← nodeHash 10 coord index (2^(4-j-1)+sel.bucket/2^(j+1)) pair.1 pair.2
        pure (some (parent,used+1))
      else pure none) (some (value,next))
  let some (root,next) := result | pure none
  pure (some (roots ++ [root],next))

/-- Core's FTS fold over the seven coordinates. -/
def ftsFold (sig : Signature) (index : Nat) (chosen : List Selection) : T3.M (Option (List Digest × Nat)) :=
  (List.range 7).foldlM (ftsStep sig index chosen) (some ([], 0))

/-- The canonical-tail check of `recoverFts` (proof slots `used .. 123` zero). -/
def tailZero (sig : Signature) (used : Nat) : Bool :=
  (List.range (117 - used)).all fun j => decide (sig.proof ⟨(used + j) % 117, Nat.mod_lt _ (by decide)⟩ = 0)

theorem recoverFts_eq (sig : Signature) (index : Nat) (chosen : List Selection) :
    recoverFts sig index chosen = ftsFold sig index chosen >>= fun state => match state with
      | some (roots, used) => if !tailZero sig used then pure none else
          forestPk index roots >>= fun r => pure (some r)
      | none => pure none := by
  unfold recoverFts ftsFold
  congr 1
  funext state
  rcases state with _ | ⟨roots, used⟩ <;> rfl

/-! ## The machine statement of the FTS phase -/

/-- Entry of the FTS phase (`fts_coord`, word 65, after `ds_done`). -/
structure FtsPre (sig : Signature) (N : HashOutput) (s : MachineState) : Prop where
  pc : s.pc = pcOf 65
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  x18 : s.getReg .x18 = BitVec.ofNat 64 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 0xC40
  x2 : s.getReg .x2 = BitVec.ofNat 64 0x22000
  adm : T3.admissible (T3.selections N) = true
  rows : SelRows s N
  secrets : ∀ k (h : k < 21), DigAt s (0x7010 + 16 * k) (sig.secrets ⟨k, h⟩)
  proof : ∀ k (h : k < 117), DigAt s (0x7160 + 16 * k) (sig.proof ⟨k, h⟩)
  f0 : s.getMem (BitVec.ofNat 64 FLEAF) = 0
  f8 : s.getMem (BitVec.ofNat 64 (FLEAF + 8)) = 0
  f48 : s.getMem (BitVec.ofNat 64 (FLEAF + 48)) = 0
  f56 : s.getMem (BitVec.ofNat 64 (FLEAF + 56)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  wz : ∀ A, 0x840 ≤ A → A < 0x3418 → s.getMem (BitVec.ofNat 64 A) = 0

/-- The registers the FTS phase changes. -/
def ftsRegs : List Reg :=
  [.x1, .x2, .x6, .x7, .x8, .x10, .x11, .x12, .x13, .x14, .x18, .x19, .x20, .x22, .x23, .x24, .x28, .x29, .x30]

/-- The doublewords the FTS phase changes: the stack, the node block (not its zero words), `NOUT`, the FTS leaf
block, the forest roots, the witness secrets and stream. -/
def FtsW (A : Nat) : Prop :=
  (0x22000 - 512 ≤ A ∧ A < 0x22000) ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
    A = NODE + 56 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ (FLEAF ≤ A ∧ A < FLEAF + 64) ∨
    (FOREST ≤ A ∧ A < FOREST + 128 ∧ A ≠ FOREST + 16 ∧ A ≠ FOREST + 24) ∨ (0x840 ≤ A ∧ A < 0x3418)

/-- Exit of the FTS phase: `fail`, or `fts_done` (word 215) with the roots in the forest block, `s2 = used`, the
secrets and the honest stream in the witness. -/
def FtsPost (s : MachineState) (sig : Signature) (N : HashOutput) :
    Option (List Digest × Nat) → MachineState → Prop
  | none, t => FailedAt 354 t
  | some (roots, used), t => t.pc = pcOf 215 ∧ t.getReg .x5 = 0 ∧
      t.getReg .x9 = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧ t.getReg .x18 = BitVec.ofNat 64 used ∧ used ≤ 117 ∧
      roots.length = 7 ∧ (∀ c < 7, DigAt t (FOREST + slotOff c) (roots.getD c 0)) ∧
      t.readWords (BitVec.ofNat 64 0x840) 128 = wordsOf (leafBytes sig) ∧
      t.readWords (BitVec.ofNat 64 0xC40) 1275 = wordsOf (streamBytes (T3.selections N) sig.proof) ∧
      RegsExcept s t ftsRegs ∧ Frame s t FtsW

/-- An all-oracle cycle bound of the FTS phase. -/
def ftsCost : Nat := 100000

/-- **The FTS phase** (to be discharged by the FTS refinement; consumed by `expand_tbsim`). -/
def FtsSpec (sk : BitVec 256) : Prop :=
  ∀ (sig : Signature) (N : HashOutput) (s : MachineState), FtsPre sig N s →
    TBSim image sk s ftsCost (ftsFold sig (N.toNat % 2 ^ 31) (T3.selections N)) (FtsPost s sig N)

/-! ## `expandN` unfolded -/

theorem expandN_eq (m : T3.Message) (pk : Digest) (sig : Signature) : expandN m pk sig =
    T3.digestSearch sig.rho m 0 T3.attemptLimit >>= fun r => match r with
    | none => pure none
    | some (counter, output) =>
      ftsFold sig (output.toNat % 2 ^ 31) (T3.selections output) >>= fun st => match st with
      | none => pure none
      | some (roots, used) =>
        if !tailZero sig used then pure none else
        forestPk (output.toNat % 2 ^ 31) roots >>= fun root =>
        T3.expandLayers sig (output.toNat % 2 ^ 31) 4 root >>= fun r' => match r' with
        | none => pure none
        | some (root', counters) => if root' ≠ pk then pure none else
            pure (some (output, ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)) := by
  unfold expandN
  congr 1
  funext r
  rcases r with _ | ⟨counter, output⟩
  · rfl
  · simp only []
    rw [recoverFts_eq, bind_assoc]
    congr 1
    funext st
    rcases st with _ | ⟨roots, used⟩
    · rfl
    · simp only []
      by_cases h : (!tailZero sig used) = true
      · simp only [h, ↓reduceIte, pure_bind]
      · simp only [h, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
        congr 1; funext root
        congr 1; funext r'
        rcases r' with _ | ⟨root', counters⟩ <;> rfl

end SigGolfCandidate.T3M.Expand
