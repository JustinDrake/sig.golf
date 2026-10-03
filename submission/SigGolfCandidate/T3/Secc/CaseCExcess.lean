import SigGolfCandidate.T3.Secc.CaseCForecast
import SigGolfCandidate.T3.Gate6.ThetaExcess

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)

/-- The wider mean allowance pays the certified excess charge at threshold 1023/1024. -/
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 4995/8192) :
    (3189/2048) * (value - 1023/1024) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  BPORS.History.theta_excess_le_square value mean hvalue hmean

/-- Excess of the complete uniform proposal word, with the actual 135/1024 gate. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      13145 / 100000000 := by
  simpa only [theta] using BPORS.History.excess_three_quarters

end SigGolfCandidate.T3.Security.CaseC
