import SigGolfCandidate.Verify.ChainCheck07

/-! Kernel check of triple 8 of the layer-shared chain code: its table slots and code blocks, in
two halves (the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem triCheck_8_0 : triCheck 8 0 256 = true := by decide +kernel
theorem triCheck_8_1 : triCheck 8 256 256 = true := by decide +kernel

end SigGolfCandidate.Verify
