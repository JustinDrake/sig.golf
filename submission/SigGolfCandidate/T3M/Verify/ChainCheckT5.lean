import SigGolfCandidate.T3M.Verify.ChainCheckT4

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem triCheck_10_0 : triCheck 10 0 256 = true := by decide +kernel
theorem triCheck_10_1 : triCheck 10 256 256 = true := by decide +kernel
theorem triCheck_11_0 : triCheck 11 0 256 = true := by decide +kernel
theorem triCheck_11_1 : triCheck 11 256 256 = true := by decide +kernel
end SigGolfCandidate.T3M
