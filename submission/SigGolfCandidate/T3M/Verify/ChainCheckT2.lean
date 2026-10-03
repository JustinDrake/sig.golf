import SigGolfCandidate.T3M.Verify.ChainCheckT1

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem triCheck_4_0 : triCheck 4 0 256 = true := by decide +kernel
theorem triCheck_4_1 : triCheck 4 256 256 = true := by decide +kernel
theorem triCheck_5_0 : triCheck 5 0 256 = true := by decide +kernel
theorem triCheck_5_1 : triCheck 5 256 256 = true := by decide +kernel
end SigGolfCandidate.T3M
