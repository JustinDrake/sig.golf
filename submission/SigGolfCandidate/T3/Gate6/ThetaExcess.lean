import SigGolfCandidate.T3.Gate6.BPORSPrefix

namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 4995/8192) :
    (3189/2048)*(value-1023/1024)+2*mean*value ≤ value^2+mean^2 :=
  SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean

/-- Threshold 1023/1024 leaves 1/1024 to cover cached digest reuse. Historical API name retained. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W-1023/1024) ≤
      13145/100000000 :=
  fullPrice_excess_of_pointwise (1023/1024) theta_excess_le_square

end SigGolfCandidate.T3.BPORS.History
#print axioms SigGolfCandidate.T3.BPORS.History.theta_excess_le_square
#print axioms SigGolfCandidate.T3.BPORS.History.excess_three_quarters
