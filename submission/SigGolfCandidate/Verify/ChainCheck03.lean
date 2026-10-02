import SigGolfCandidate.Verify.ChainCheck02
set_option Elab.async false

/-! Kernel check of triple 3 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_3_0 : triCheck 3 0 256 = true := by decide +kernel
theorem triCheck_3_1 : triCheck 3 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
