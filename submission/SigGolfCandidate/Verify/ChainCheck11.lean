import SigGolfCandidate.Verify.ChainCheck10
set_option Elab.async false

/-! Kernel check of triple 11 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_11_0 : triCheck 11 0 256 = true := by decide +kernel
theorem triCheck_11_1 : triCheck 11 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
