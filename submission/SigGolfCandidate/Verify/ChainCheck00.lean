import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.FoldCheckB
set_option Elab.async false

/-! Kernel check of triple 0 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_0_0 : triCheck 0 0 256 = true := by decide +kernel
theorem triCheck_0_1 : triCheck 0 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
