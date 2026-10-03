import SigGolfCandidate.T3M.Verify.ChainRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem triCheck_0_0 : triCheck 0 0 256 = true := by decide +kernel
theorem triCheck_0_1 : triCheck 0 256 256 = true := by decide +kernel
theorem triCheck_1_0 : triCheck 1 0 256 = true := by decide +kernel
theorem triCheck_1_1 : triCheck 1 256 256 = true := by decide +kernel
end SigGolfCandidate.T3M
