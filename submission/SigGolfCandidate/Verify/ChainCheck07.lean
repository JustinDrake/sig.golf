import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheck06
set_option Elab.async false

/-! Kernel check of triple 7 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_7_0 : triCheck 7 0 256 = true := by decide +kernel
theorem triCheck_7_1 : triCheck 7 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
