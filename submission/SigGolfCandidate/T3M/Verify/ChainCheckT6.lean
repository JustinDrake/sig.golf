import SigGolfCandidate.T3M.Verify.ChainCheckT5

/-! Kernel check of the lower chain code, triples 12 and 13: their `ttab` slots and shared blocks, in
halves (two import chains limit concurrent heavy checks to respect hosted memory). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem triCheck_12_0 : triCheck 12 0 256 = true := by decide +kernel
theorem triCheck_12_1 : triCheck 12 256 256 = true := by decide +kernel
theorem triCheck_13_0 : triCheck 13 0 256 = true := by decide +kernel
theorem triCheck_13_1 : triCheck 13 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M
