import SigGolfCandidate.Verify.ChainCheck05
set_option Elab.async false

/-! Kernel check of triple 6 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_6_0 : triCheck 6 0 256 = true := by decide +kernel
theorem triCheck_6_1 : triCheck 6 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
