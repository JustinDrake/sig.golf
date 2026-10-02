import SigGolfCandidate.T3.Gate6.SourceBridge
import SigGolfCandidate.T3.Gate6.BankMoments
namespace SigGolfResearch.Gate6.Source
open SigGolfCandidate.T3 OracleComp ENNReal OracleComp.EvalDist Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 1000000

/-- Full payoff factorization for the actual source predicate. This is the
replacement for T3.DigestSampling.accepted_samplingData with the gate enforced. -/
theorem actual_accepted_mark_weight (payoff : MarkedLabel → ENNReal) :
    expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      (fun output => if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        Moments.finiteAverage payoff*acceptance := by
  have hs (output : BitVec 256) :
      (if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        ∑ mark : MarkedLabel,
          (if digestAdmissible output=true ∧ (digestRecord output).1=mark then 1 else 0)*payoff mark := by
    by_cases ha : digestAdmissible output=true
    · simp [ha,eq_comm]
    · simp [ha]
  simp only [expectedValue_def]
  simp_rw [hs,Finset.mul_sum,←mul_assoc,mul_ite,mul_one,mul_zero]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,actual_mark_joint_exact]
  simp only [Moments.finiteAverage,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat,
    div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mark _
  ring

end SigGolfResearch.Gate6.Source
