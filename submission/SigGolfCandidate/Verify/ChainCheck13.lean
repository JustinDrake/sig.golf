import SigGolfCandidate.Verify.ChainCheck12

/-! Kernel check of triple 13 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_13_0 : triCheck 13 0 256 = true := by decide +kernel
theorem triCheck_13_1 : triCheck 13 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
