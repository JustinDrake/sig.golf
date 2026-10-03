import SigGolfCandidate.T3M.Verify.ChainCheckT3

/-! Kernel check of the lower chain code, triples 8 and 9: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem triCheck_8_0 : triCheck 8 0 256 = true := by decide +kernel
theorem triCheck_8_1 : triCheck 8 256 256 = true := by decide +kernel
theorem triCheck_9_0 : triCheck 9 0 256 = true := by decide +kernel
theorem triCheck_9_1 : triCheck 9 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M
