import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildBridge

namespace ClaudeWCT.W9.Machine.Merkle.CodexCheck
open SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Merkle
set_option maxRecDepth 200000
theorem children_linked :
    (List.range 128).all (fun j => W9Machine.sliceChecked (childBase j) (childWords j)) = true := by
  decide +kernel
theorem frozen_childCodeAt (j : Nat) (hj : j < 128) : ChildCodeAt W9Machine.Frozen.image j :=
  childCodeAt_of_codeAt hj
    (W9Machine.slice_at _ _ (List.all_eq_true.mp children_linked j (List.mem_range.mpr hj)))
theorem frozen_children (j : Nat) (hj : j < 128) :
    ChildGood W9Machine.Frozen.image j ∧ ChildRefines W9Machine.Frozen.image j ∧
      ChildRefinesCanon W9Machine.Frozen.image j :=
  ⟨child_good _ j hj (frozen_childCodeAt j hj), child_refines _ j hj (frozen_childCodeAt j hj),
    child_refines_canon _ j hj (frozen_childCodeAt j hj)⟩
#print axioms frozen_children
end ClaudeWCT.W9.Machine.Merkle.CodexCheck
