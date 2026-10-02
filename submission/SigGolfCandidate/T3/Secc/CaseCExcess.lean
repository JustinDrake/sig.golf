import SigGolfCandidate.T3.Secc.CaseCForecast
import SigGolfCandidate.T3.Gate6.ThetaExcess

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)

/-- The wider mean allowance pays the same excess charge at threshold7 / 8. -/
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 3 / 8) :
    2 * (value - 7 / 8) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  BPORS.History.theta_excess_le_square value mean hvalue hmean

/-- Excess of the complete uniform proposal word, with the actual5744 gate. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      2300 / 100000000 := by
  simpa only [theta] using BPORS.History.excess_three_quarters

end SigGolfCandidate.T3.Security.CaseC
