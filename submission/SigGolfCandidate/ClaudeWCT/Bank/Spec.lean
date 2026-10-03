import SigGolfCandidate.T3.Secc.CaseCForecast

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure FtsBankSpec (P : Type) [Fintype P] [SampleableType P] where
  admissible : HashOutput → Bool
  exists_admissible : ∃ x, admissible x = true
  acceptance_le : Pr[fun x : HashOutput => admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 1 / 64
  proposal : HashOutput → P
  accepted_proposal : ∀ g : P → ENNReal,
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun x => if admissible x = true then g (proposal x) else 0) =
      BPORS.finiteAverage g * Pr[fun x : HashOutput => admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
  score : List HashOutput → HashOutput → ENNReal
  covered : List HashOutput → HashOutput → Prop
  one_le_score : ∀ X N, admissible N = true → covered X N → 1 ≤ score X N
  score_append_mono : ∀ X Y N, score X N ≤ score (X ++ Y) N
  price : List P → ENNReal
  average_score : ∀ X, BPORS.finiteAverage (fun N : HashOutput => score X N) = price (X.map proposal) / 2 ^ 128
  horizon : Nat
  excessRate : ENNReal
  excess_le : uniformWordAverage horizon (fun W : List P => price W - CaseC.theta) ≤ excessRate
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def decode (x : HashOutput) : Option HashOutput := if S.admissible x then some x else none
noncomputable def acceptance : ENNReal :=
  Pr[fun x : HashOutput => S.admissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)]
def proposals (X : List HashOutput) : List P := X.map S.proposal
theorem proposals_append (X Y : List HashOutput) : S.proposals (X ++ Y) = S.proposals X ++ S.proposals Y :=
  List.map_append
noncomputable def admissibleSet : Finset HashOutput := Finset.univ.filter fun x => S.admissible x = true
theorem decode_elim (w : HashOutput → ENNReal) (x : HashOutput) :
    (S.decode x).elim 0 w = if S.admissible x = true then w x else 0 := by
  unfold decode
  split <;> simp_all
theorem acceptedWeight_eq_sum (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w = (∑ x ∈ S.admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) := by
  have h : Sampling.acceptedWeight S.decode w = BPORS.finiteAverage (fun x => (S.decode x).elim 0 w) := by
    unfold Sampling.acceptedWeight
    exact BPORS.expected_uniform_eq_finiteAverage _
  have hsum : (∑ x, (S.decode x).elim 0 w) = ∑ x ∈ S.admissibleSet, w x := by
    unfold admissibleSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    exact S.decode_elim w x
  rw [h, BPORS.finiteAverage, hsum]
theorem acceptedWeight_eq_expected (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun x => if S.admissible x = true then w x else 0) := by
  unfold Sampling.acceptedWeight
  simp_rw [S.decode_elim]
theorem acceptedWeight_one : Sampling.acceptedWeight S.decode (fun _ => 1) = S.acceptance := by
  rw [acceptedWeight_eq_expected, expectedValue_ite_one]
  rfl
theorem acceptance_eq_card :
    S.acceptance = (S.admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal) := by
  rw [← S.acceptedWeight_one, acceptedWeight_eq_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
theorem admissibleSet_nonempty : S.admissibleSet.Nonempty := by
  obtain ⟨x, hx⟩ := S.exists_admissible
  exact ⟨x, by simp [admissibleSet, hx]⟩
theorem acceptance_ne_zero : S.acceptance ≠ 0 := by
  rw [acceptance_eq_card]
  apply ENNReal.div_ne_zero.mpr
  refine ⟨?_, ENNReal.natCast_ne_top _⟩
  exact_mod_cast (Finset.card_pos.mpr S.admissibleSet_nonempty).ne'
theorem acceptance_le_one : S.acceptance ≤ 1 := probEvent_le_one
theorem acceptance_ne_top : S.acceptance ≠ ⊤ := ne_top_of_le_ne_top (by simp) S.acceptance_le_one
theorem acceptance_le_sixtyfourth : S.acceptance ≤ 1 / 64 := S.acceptance_le
theorem failMass_decode : failMass S.decode = 1 - S.acceptance := by
  have hf : failMass S.decode = Pr[fun answer : HashOutput => S.decode answer = none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent S.decode
  rw [hf]
  have he (answer : HashOutput) : S.decode answer = none ↔ ¬S.admissible answer = true := by
    by_cases h : S.admissible answer = true
    · simp only [decode, h, ite_true, reduceCtorEq, not_true_eq_false]
    · simp only [decode, h, Bool.false_eq_true, ite_false, not_false_eq_true]
  simp_rw [he]
  rw [Sampling.probEvent_not]
  rfl
noncomputable def accepted : PMF HashOutput := PMF.uniformOfFinset S.admissibleSet S.admissibleSet_nonempty
noncomputable def freshPrice (w : HashOutput → ENNReal) : ENNReal :=
  Sampling.acceptedWeight S.decode w / S.acceptance
theorem freshPrice_step (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight S.decode w + failMass S.decode * S.freshPrice w = S.freshPrice w := by
  have hcancel : S.acceptance * S.freshPrice w = Sampling.acceptedWeight S.decode w := by
    unfold freshPrice
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel S.acceptance_ne_zero S.acceptance_ne_top, mul_one]
  rw [failMass_decode, ← hcancel, ← add_mul, add_tsub_cancel_of_le S.acceptance_le_one, one_mul]
theorem expected_accepted (w : HashOutput → ENNReal) : expectedValue S.accepted w = S.freshPrice w := by
  unfold freshPrice
  rw [acceptedWeight_eq_sum, acceptance_eq_card]
  have hcard : (Fintype.card HashOutput : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard' : (Fintype.card HashOutput : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcancel : (∑ x ∈ S.admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) /
      ((S.admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal)) =
      (∑ x ∈ S.admissibleSet, w x) / (S.admissibleSet.card : ENNReal) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hcard)) (Or.inr (ENNReal.inv_ne_zero.mpr hcard')),
      inv_inv, mul_assoc, mul_comm (Fintype.card HashOutput : ENNReal)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hcard hcard', mul_one]
  rw [hcancel]
  unfold expectedValue accepted
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ S.admissibleSet)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun x => x ∉ S.admissibleSet), add_zero]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos hx, mul_comm]
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [if_neg hx.2, zero_mul]
theorem expected_accepted_proposal (g : P → ENNReal) :
    expectedValue S.accepted (fun x => g (S.proposal x)) = BPORS.finiteAverage g := by
  rw [expected_accepted]
  unfold freshPrice
  rw [acceptedWeight_eq_expected, S.accepted_proposal g]
  change BPORS.finiteAverage g * S.acceptance / S.acceptance = _
  rw [mul_div_assoc, ENNReal.div_self S.acceptance_ne_zero S.acceptance_ne_top, mul_one]
end FtsBankSpec
end ClaudeWCT.Bank
