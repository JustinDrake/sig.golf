import SigGolfCandidate.T3M.Verify.ChainCheckT0

/-! Kernel check of the lower chain code, triples 2 and 3: their `ttab` slots and shared blocks, in
halves (two import chains limit concurrent heavy checks to respect hosted memory). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem triCheck_2_0 : triCheck 2 0 256 = true := by decide +kernel
theorem triCheck_2_1 : triCheck 2 256 256 = true := by decide +kernel
theorem triCheck_3_0 : triCheck 3 0 256 = true := by decide +kernel
theorem triCheck_3_1 : triCheck 3 256 256 = true := by decide +kernel

end SigGolfCandidate.T3M
