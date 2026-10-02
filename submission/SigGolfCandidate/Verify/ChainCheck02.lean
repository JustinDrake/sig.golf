import SigGolfCandidate.Verify.ChainCheck01
set_option Elab.async false

/-! Kernel check of triple 2 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_2_0 : triCheck 2 0 256 = true := by decide +kernel
theorem triCheck_2_1 : triCheck 2 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
