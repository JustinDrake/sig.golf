import SigGolfCandidate.Verify.ChainCheck11

/-! Kernel check of triple 12 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_12_0 : triCheck 12 0 256 = true := by decide +kernel
theorem triCheck_12_1 : triCheck 12 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
