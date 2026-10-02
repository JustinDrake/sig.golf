import SigGolfCandidate.T3.Secc.CaseCForecast
import SigGolfCandidate.T3.Gate6.ThetaExcess

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)

/-- The wider mean allowance pays the same excess charge at threshold63 / 64. -/
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37 / 64) :
    (13 / 8) * (value - 63 / 64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  BPORS.History.theta_excess_le_square value mean hvalue hmean

/-- Excess of the complete uniform proposal word, with the actual5744 gate. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      11400 / 100000000 := by
  simpa only [theta] using BPORS.History.excess_three_quarters

end SigGolfCandidate.T3.Security.CaseC
