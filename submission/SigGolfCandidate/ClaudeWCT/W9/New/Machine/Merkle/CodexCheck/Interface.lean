import SigGolfCandidate.W9Machine.WctMerkle
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildBridge

namespace ClaudeWCT.W9.Machine.Merkle.CodexCheck
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
open ClaudeWCT.W9.Machine.Merkle
def childBudget : W9Machine.Budget := ⟨45, 102, 102⟩
theorem goodQ_eq (im : Image) : W9Machine.GoodQFor im = GoodQIm im := rfl
theorem refines_eq {α : Type} (L : W9Machine.Layout) (pre : MachineState → Prop)
    (post : α → MachineState → Prop) (p : M α) :
    W9Machine.RefinesPiece L childBudget pre post p = RefinesIm L.image 45 102 102 pre post p := rfl
theorem recoverPath_split (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (a : HashOutput) (k : Fin 9)
    (root : Digest) :
    W9Machine.recoverPath sig index a k root =
      (sixLevels k.val index (ClaudeWCT.WCT9.child a k).val (finPath (sig.openings k).path) root >>= fun value =>
        let other := (sig.openings k).path 6
        let pair := if (ClaudeWCT.WCT9.child a k).val / 2 ^ 6 % 2 = 0 then (value, other) else (other, value)
        SigGolfCandidate.T3.nodeHash 11 k.val index 1 pair.1 pair.2) :=
  pathSplit k index (ClaudeWCT.WCT9.child a k).val (sig.openings k).path root (ClaudeWCT.WCT9.child a k).isLt
theorem child_refinesPiece (L : W9Machine.Layout) (hcode : ChildRegionAt L.image) (j : Nat) (hj : j < 128)
    (B k index : Nat) (leaf pads sibs : Nat → Digest) (P : MachineState → Prop) (hidx : index < 2 ^ 32)
    (hP : ∀ u, P u → ChildPre j B k index leaf pads sibs u) :
    W9Machine.RefinesPiece L childBudget P (fun v t => ∃ u, P u ∧ ChildPost j B k index u v t)
      (childProg k index j leaf pads sibs) :=
  (allChildren L.image hcode j hj).2.1 B k index leaf pads sibs P hidx hP
theorem child_refinesPiece_canon (L : W9Machine.Layout) (hcode : ChildRegionAt L.image) (j : Nat)
    (hj : j < 128) (B k index : Nat) (ends : List Digest) (path : Nat → Digest) (P : MachineState → Prop)
    (hends : ends.length = 7) (hidx : index < 2 ^ 32)
    (hP : ∀ u, P u → ChildPre j B k index (leafFields k index j ends) (fun _ => 0) path u) :
    W9Machine.RefinesPiece L childBudget P (fun v t => ∃ u, P u ∧ ChildPost j B k index u v t)
      (ClaudeWCT.WCT9.leafHash index k j ends >>= sixLevels k index j path) :=
  (allChildren L.image hcode j hj).2.2 B k index ends path P hends hidx hP
end ClaudeWCT.W9.Machine.Merkle.CodexCheck
