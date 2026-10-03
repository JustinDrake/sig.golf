import SigGolfCandidate.T3.Secc.CaseCScore

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def admissibleSet : Finset HashOutput :=
  Finset.univ.filter fun x => digestAdmissible x = true
theorem acceptedWeight_eq_sum (w : HashOutput → ENNReal) :
    Sampling.acceptedWeight Sampling.digestDecode w =
      (∑ x ∈ admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) := by
  have h : Sampling.acceptedWeight Sampling.digestDecode w =
      BPORS.finiteAverage (fun x => (Sampling.digestDecode x).elim 0 w) := by
    unfold Sampling.acceptedWeight
    exact BPORS.expected_uniform_eq_finiteAverage _
  have hsum : (∑ x, (Sampling.digestDecode x).elim 0 w) = ∑ x ∈ admissibleSet, w x := by
    unfold admissibleSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    unfold Sampling.digestDecode
    split <;> simp_all
  rw [h, BPORS.finiteAverage, hsum]
theorem acceptanceProbability_eq_card :
    acceptanceProbability = (admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal) := by
  have h := acceptedWeight_eq_sum (fun _ => 1)
  have h1 := Sampling.digest_acceptedWeight (fun _ => (1 : ENNReal))
  rw [BPORS.History.finiteAverage_constant, one_mul] at h1
  rw [← h1, h, Finset.sum_const, nsmul_eq_mul, mul_one]
theorem admissibleSet_nonempty : admissibleSet.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  apply Sampling.WeightedSelection.acceptanceProbability_ne_zero
  rw [acceptanceProbability_eq_card, h, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
noncomputable def accepted : PMF HashOutput := PMF.uniformOfFinset admissibleSet admissibleSet_nonempty
theorem expected_accepted (w : HashOutput → ENNReal) :
    expectedValue accepted w = Sampling.WeightedSelection.freshPrice w := by
  unfold Sampling.WeightedSelection.freshPrice
  rw [acceptedWeight_eq_sum, acceptanceProbability_eq_card]
  have hcard : (Fintype.card HashOutput : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcard' : (Fintype.card HashOutput : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcancel : (∑ x ∈ admissibleSet, w x) / (Fintype.card HashOutput : ENNReal) /
      ((admissibleSet.card : ENNReal) / (Fintype.card HashOutput : ENNReal)) =
      (∑ x ∈ admissibleSet, w x) / (admissibleSet.card : ENNReal) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hcard)) (Or.inr (ENNReal.inv_ne_zero.mpr hcard')),
      inv_inv, mul_assoc, mul_comm (Fintype.card HashOutput : ENNReal)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hcard hcard', mul_one]
  rw [hcancel]
  unfold expectedValue accepted
  simp only [PMF.probOutput_eq_apply, PMF.uniformOfFinset_apply, tsum_fintype]
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => x ∈ admissibleSet)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter fun x => x ∉ admissibleSet), add_zero]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos hx, mul_comm]
  · intro x hx
    rw [Finset.mem_filter] at hx
    rw [if_neg hx.2, zero_mul]
theorem expected_accepted_label (g : BPORS.History.Proposal → ENNReal) :
    expectedValue accepted (fun x => g (label x)) = BPORS.finiteAverage g := by
  rw [expected_accepted]
  unfold Sampling.WeightedSelection.freshPrice
  have h := Sampling.digest_acceptedWeight g
  change Sampling.acceptedWeight Sampling.digestDecode (fun x => g (samplingData x).1) / _ = _
  rw [h, mul_div_assoc, ENNReal.div_self Sampling.WeightedSelection.acceptanceProbability_ne_zero
    Sampling.WeightedSelection.acceptanceProbability_ne_top, mul_one]
noncomputable def forecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord accepted R) (fun F => score (X ++ F) N)
theorem forecast_zero (X : List HashOutput) (N : HashOutput) : forecast 0 X N = score X N := by
  unfold forecast
  change expectedValue (pure [] : PMF (List HashOutput)) _ = _
  rw [expectedValue_pure, List.append_nil]
theorem forecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue accepted (fun A => forecast R (X ++ [A]) N) = forecast (R + 1) X N := by
  unfold forecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem score_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) : score X N ≤ forecast R X N := by
  unfold forecast
  calc
    score X N = expectedValue (independentProposalWord accepted R) (fun _ => score X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => score_append_mono X F N
theorem expected_word_labels (R : Nat) (g : List BPORS.History.Proposal → ENNReal) :
    expectedValue (independentProposalWord accepted R) (fun F => g (labels F)) = uniformWordAverage R g := by
  induction R generalizing g with
  | zero =>
      change expectedValue (pure [] : PMF (List HashOutput)) _ = _
      rw [expectedValue_pure]
      simp [uniformWordAverage, SphincsSecurity.Concrete.sampleUniformProposalWord, labels]
  | succ R ih =>
      rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind, BPORS.uniformWordAverage_succ]
      have hstep (A : HashOutput) : expectedValue ((independentProposalWord accepted R).map (A :: ·))
          (fun F => g (labels F)) = uniformWordAverage R (fun W => g (label A :: W)) := by
        rw [← PMF.monad_map_eq_map, expectedValue_map]
        exact ih (fun W => g (label A :: W))
      simp_rw [hstep]
      exact expected_accepted_label (fun p => uniformWordAverage R (fun W => g (p :: W)))
theorem finiteAverage_expectedValue {α β : Type} [Fintype β] (law : PMF α) (f : β → α → ENNReal) :
    BPORS.finiteAverage (fun b => expectedValue law (f b)) =
      expectedValue law (fun a => BPORS.finiteAverage (fun b => f b a)) := by
  unfold BPORS.finiteAverage expectedValue
  simp only [div_eq_mul_inv]
  calc
    (∑ b, ∑' a, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ =
        (∑' a, ∑ b, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ := by
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = ∑' a, (∑ b, Pr[= a | law] * f b a) * (Fintype.card β : ENNReal)⁻¹ := ENNReal.tsum_mul_right.symm
    _ = _ := by
      apply tsum_congr
      intro a
      rw [← Finset.mul_sum, mul_assoc]
theorem average_forecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => forecast R X N) =
      uniformWordAverage R (fun W => BPORS.History.fullPrice (labels X ++ W)) / 2 ^ 128 := by
  unfold forecast
  rw [finiteAverage_expectedValue]
  simp_rw [average_score, labels_append]
  refine (expected_word_labels R (fun W => BPORS.History.fullPrice (labels X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => BPORS.History.fullPrice (labels X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * BPORS.History.fullPrice (labels X ++ W) by
    funext W; exact mul_comm _ _, SphincsSecurity.Concrete.uniformWordAverage_mul_left, mul_comm]
noncomputable def theta : ENNReal := 63 / 64
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  uniformWordAverage R (fun W => BPORS.History.fullPrice (labels X ++ W) - theta)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue accepted (fun A => excessForecast R (X ++ [A])) = excessForecast (R + 1) X := by
  unfold excessForecast
  rw [BPORS.uniformWordAverage_succ]
  have hA (A : HashOutput) : uniformWordAverage R
      (fun W => BPORS.History.fullPrice (labels (X ++ [A]) ++ W) - theta) =
      (fun p : BPORS.History.Proposal => uniformWordAverage R
        (fun W => BPORS.History.fullPrice (labels X ++ p :: W) - theta)) (label A) := by
    simp [labels, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact expected_accepted_label (fun p => uniformWordAverage R
    (fun W => BPORS.History.fullPrice (labels X ++ p :: W) - theta))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => forecast R X N) ≤ (theta + excessForecast R X) / 2 ^ 128 := by
  rw [average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ uniformWordAverage R (fun W => theta + (BPORS.History.fullPrice (labels X ++ W) - theta)) :=
      SphincsSecurity.Concrete.uniformWordAverage_mono R fun W => le_add_tsub
    _ = _ := by
      rw [SphincsSecurity.Concrete.uniformWordAverage_add, BPORS.History.uniformWordAverage_constant]
end SigGolfCandidate.T3.Security.CaseC
