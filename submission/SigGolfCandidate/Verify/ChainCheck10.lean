import SigGolfCandidate.Verify.ChainCheck09
set_option Elab.async false

/-! Kernel check of triple 10 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_10_0 : triCheck 10 0 256 = true := by decide +kernel
theorem triCheck_10_1 : triCheck 10 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
