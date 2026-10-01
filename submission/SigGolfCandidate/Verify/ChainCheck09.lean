import SigGolfCandidate.Verify.ChainCheck08
set_option Elab.async false

/-! Kernel check of triple 9 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_9_0 : triCheck 9 0 256 = true := by decide +kernel
theorem triCheck_9_1 : triCheck 9 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
