import SigGolfCandidate.Verify.ChainCheck03
set_option Elab.async false

/-! Kernel check of triple 4 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_4_0 : triCheck 4 0 256 = true := by decide +kernel
theorem triCheck_4_1 : triCheck 4 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
