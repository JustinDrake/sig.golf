import SigGolfCandidate.T3M.Verify.ChainCheckT1

/-! Kernel check of the lower chain code, triples 4 and 5: their `ttab` slots and shared blocks, in
halves (two import chains limit concurrent heavy checks to respect hosted memory). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem triCheck_4_0 : triCheck 4 0 256 = true := by decide +kernel
theorem triCheck_4_1 : triCheck 4 256 256 = true := by decide +kernel
theorem triCheck_5_0 : triCheck 5 0 256 = true := by decide +kernel
theorem triCheck_5_1 : triCheck 5 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M
