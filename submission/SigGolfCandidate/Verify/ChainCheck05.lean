import SigGolfCandidate.Verify.ChainCheck04
set_option Elab.async false

/-! Kernel check of triple 5 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_5_0 : triCheck 5 0 256 = true := by decide +kernel
theorem triCheck_5_1 : triCheck 5 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
