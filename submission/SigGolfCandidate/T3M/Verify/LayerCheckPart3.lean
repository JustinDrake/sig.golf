import SigGolfCandidate.T3M.Verify.LayerRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
end SigGolfCandidate.T3M
