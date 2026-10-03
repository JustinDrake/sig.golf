import SigGolfCandidate.T3M.Verify.ChainCheckT4

/-! Kernel check of the lower chain code, triples 10 and 11: their `ttab` slots and shared blocks, in
halves (the import chain serializes the check files to bound parallel build memory). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem triCheck_10_0 : triCheck 10 0 256 = true := by decide +kernel
theorem triCheck_10_1 : triCheck 10 256 256 = true := by decide +kernel
theorem triCheck_11_0 : triCheck 11 0 256 = true := by decide +kernel
theorem triCheck_11_1 : triCheck 11 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M
