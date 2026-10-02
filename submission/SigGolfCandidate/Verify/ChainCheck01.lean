import SigGolfCandidate.Verify.ChainCheck00
set_option Elab.async false

/-! Kernel check of triple 1 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_1_0 : triCheck 1 0 256 = true := by decide +kernel
theorem triCheck_1_1 : triCheck 1 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
