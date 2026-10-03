import SigGolfCandidate.T3M.Verify.ChainCheckT2

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem triCheck_6_0 : triCheck 6 0 256 = true := by decide +kernel
theorem triCheck_6_1 : triCheck 6 256 256 = true := by decide +kernel
theorem triCheck_7_0 : triCheck 7 0 256 = true := by decide +kernel
theorem triCheck_7_1 : triCheck 7 256 256 = true := by decide +kernel
end SigGolfCandidate.T3M
