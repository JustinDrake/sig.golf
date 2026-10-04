import SigGolfCandidate.T3M.Verify.LayerRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem ld3Check_ok : ld3Check = true := by decide +kernel
end SigGolfCandidate.T3M
