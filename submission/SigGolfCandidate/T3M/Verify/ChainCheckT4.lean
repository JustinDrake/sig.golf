import SigGolfCandidate.T3M.Verify.ChainCheckT3

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem triCheck_8_0 : triCheck 8 0 256 = true := by decide +kernel
theorem triCheck_8_1 : triCheck 8 256 256 = true := by decide +kernel
theorem triCheck_9_0 : triCheck 9 0 256 = true := by decide +kernel
theorem triCheck_9_1 : triCheck 9 256 256 = true := by decide +kernel
end SigGolfCandidate.T3M
