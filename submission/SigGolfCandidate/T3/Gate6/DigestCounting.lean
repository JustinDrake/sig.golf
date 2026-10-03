import SigGolfCandidate.T3.Gate6.BPORSPrefix
import SigGolfCandidate.T3.Gate6.Budget

namespace SigGolfCandidate.T3.DigestCounting
open SigGolfResearch.Gate6 OracleComp ENNReal Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def p0 : Rat := SigGolfResearch.Gate6.Budget.p0
theorem packed_card {α : Type} [DecidableEq α] {y n : Nat} (hy : 3≤y) (hn : 0<n)
    (P : Finset α) (g : α → Nat) (hP : P.card<y-1) :
    ((∑ a ∈ P,y^g a)%y^n)%(y-1)=(P.filter (g · < n)).card := by
  rw [SigGolfResearch.Gate6.mod_pow_sum_generic hn P g (by omega),
    SigGolfResearch.Gate6.sum_pow_mod_pred_generic hy,
    Nat.mod_eq_of_lt ((card_filter_le _ _).trans_lt hP)]
theorem acceptanceProbability_eq_p0 :
    DigestSampling.acceptanceProbability=ENNReal.ofReal (p0 : Real) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (by unfold DigestSampling.acceptanceProbability acceptance;finiteness)
    (by finiteness)).mp
  norm_num [DigestSampling.acceptanceProbability,acceptance,p0,
    SigGolfResearch.Gate6.Budget.p0,ENNReal.toReal_div]
theorem digest_probability_eq_p0 :
    Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (p0 : Real) := by
  have he (answer : HashOutput) : (Sampling.digestDecode answer).isSome=digestAdmissible answer := by
    cases ha : digestAdmissible answer <;> simp only [Sampling.digestDecode,ha,
      Bool.false_eq_true,if_false,if_true,Option.isSome_none,Option.isSome_some]
  simp_rw [he]
  rw [SigGolfResearch.Gate6.Source.actual_acceptance_exact]
  exact acceptanceProbability_eq_p0
end SigGolfCandidate.T3.DigestCounting
namespace SigGolfCandidate.T3.Acceptance
open ENNReal DigestSampling
theorem acceptanceProbability_le_one_sixteenth : acceptanceProbability≤(1/16 : ENNReal) := by
  apply (ENNReal.toReal_le_toReal
    (by unfold acceptanceProbability SigGolfResearch.Gate6.acceptance;finiteness)
    (by finiteness)).mp
  norm_num [acceptanceProbability,SigGolfResearch.Gate6.acceptance,ENNReal.toReal_div]
end SigGolfCandidate.T3.Acceptance
