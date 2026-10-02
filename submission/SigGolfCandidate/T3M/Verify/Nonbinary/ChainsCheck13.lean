import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout

namespace SigGolfCandidate.T3M.Nonbinary
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

theorem tripleCheck_13 : tripleCheck 13=true := by decide +kernel

end SigGolfCandidate.T3M.Nonbinary
