import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CacheIndexMultiplicity
import SigGolfCandidate.SphincsSecurity.Proof.Fts.AdmissibleCount
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestSelectionIndex

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem enncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (hfresh : cache input = none) :
    QueryCache.enncard (cache.cacheQuery input output) = QueryCache.enncard cache + 1 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro pair (heq | hold)
    · subst pair
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ cache.toSet := by
    simp only [QueryCache.mem_toSet, hfresh, reduceCtorEq, not_false_eq_true]
  unfold QueryCache.enncard
  rw [hset, Set.encard_insert_of_notMem hnot]
  simp
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
theorem cachedIndexMultiplicity_le_enncard (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤ QueryCache.enncard cache := by
  unfold cachedIndexMultiplicity cacheMessageWeight
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hnone : cache input = none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp only [cacheMessageEntryWeight, hnone])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold cacheMessageEntryWeight
      cases cache input <;> simp only
      · exact zero_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard
theorem cachedIndexMultiplicity_ne_top (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) : cachedIndexMultiplicity parameter cache index ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedIndexMultiplicity_le_enncard parameter cache hfinite index)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
noncomputable def cachedIndexExcessScore (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (index : Index) : ℝ :=
  (cachedIndexMultiplicity parameter cache index).toReal - (QueryCache.enncard cache).toReal * cachedIndexRate.toReal
theorem cachedIndexExcessScore_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (input : HashInput) (output : HashOutput)
    (hfresh : cache input = none) (index : Index) :
    cachedIndexExcessScore parameter (cache.cacheQuery input output) index =
      cachedIndexExcessScore parameter cache index +
        (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧
          (hashOutputFewTimeView output).1 = index then 1 else 0) - cachedIndexRate.toReal := by
  have hcount := cachedIndexMultiplicity_ne_top parameter cache hfinite index
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  unfold cachedIndexExcessScore
  rw [cachedIndexMultiplicity_cacheQuery parameter cache input output hfresh,
    enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add hcard (by finiteness), ENNReal.toReal_one]
  split_ifs <;> simp only [add_zero, ENNReal.toReal_add hcount (by finiteness), ENNReal.toReal_one] <;> ring
theorem cachedIndexExcessScore_nonpos_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (index : Index) : cachedIndexExcessScore parameter cache index ≤ 0 := by
  rw [cachedIndexExcessScore, cachedIndexMultiplicity, cacheMessageWeight_of_no_message parameter _ cache hnone,
    ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
def CachedIndexExcessExceptional (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ index, (2 ^ 72 : ℝ) < cachedIndexExcessScore parameter cache index
theorem cachedIndexExcessExceptional_of_bound_failure (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (spent : Nat)
    (hcache : QueryCache.enncard cache ≤ spent) (index : Index)
    (hbad : (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) <
      cachedIndexMultiplicity parameter cache index) : CachedIndexExcessExceptional parameter cache := by
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hreal := (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by finiteness) cachedIndexRate_ne_top, by finiteness⟩)
    (cachedIndexMultiplicity_ne_top parameter cache hfinite index)).mpr hbad
  have hcacheReal := (ENNReal.toReal_le_toReal hcard (by finiteness)).mpr hcache
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by finiteness) cachedIndexRate_ne_top) (by finiteness),
    ENNReal.toReal_mul] at hreal
  norm_num at hreal hcacheReal
  refine ⟨index, ?_⟩
  unfold cachedIndexExcessScore
  have hscaled := mul_le_mul_of_nonneg_right hcacheReal (ENNReal.toReal_nonneg (a := cachedIndexRate))
  norm_num at hscaled ⊢
  linarith
theorem cachedIndex_bound_of_no_excess (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (spent : Nat) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ CachedIndexExcessExceptional parameter cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) := by
  by_contra hbad
  exact hclean (cachedIndexExcessExceptional_of_bound_failure parameter cache hfinite spent hcache index
    (lt_of_not_ge hbad))
end SphincsSecurity.Concrete
end

section

namespace SphincsSecurity
theorem positivePart_shift_even_le (score shift : ℝ) (power : Nat) (heven : Even power) :
    max (score + shift) 0 ^ power ≤ (max score 0 + shift) ^ power := by
  by_cases hnonneg : 0 ≤ score + shift
  · rw [max_eq_left hnonneg]
    exact pow_le_pow_left₀ hnonneg (add_le_add (le_max_left score 0) le_rfl) power
  · rw [max_eq_right (le_of_not_ge hnonneg)]
    by_cases hpower : power = 0
    · simp [hpower]
    · rw [zero_pow hpower]
      exact heven.pow_nonneg _
theorem bernoulliExcess_secondMoment_le (score probability : ℝ)
    (hprob : 0 ≤ probability) (hprob_one : probability ≤ 1) :
    probability * max (score + (1 - probability)) 0 ^ 2 +
        (1 - probability) * max (score + (-probability)) 0 ^ 2 ≤
      max score 0 ^ 2 + probability := by
  let d := max score 0
  have hmiss : 0 ≤ 1 - probability := sub_nonneg.mpr hprob_one
  calc
    _ ≤ probability * (d + (1 - probability)) ^ 2 +
        (1 - probability) * (d + (-probability)) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (1 - probability) 2 (by decide)) hprob)
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (-probability) 2 (by decide)) hmiss)
    _ = d ^ 2 + probability * (1 - probability) := by ring
    _ ≤ _ := by dsimp only [d]; nlinarith [sq_nonneg probability]
end SphincsSecurity
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
def AdmissibleIndexOutput (index : Index) (output : HashOutput) : Prop :=
  Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index
theorem probEvent_uniformHashOutput_admissible_index (index : Index) :
    Pr[AdmissibleIndexOutput index | ($ᵗ HashOutput : ProbComp HashOutput)] =
      cachedIndexRate := by
  change Pr[fun output : HashOutput =>
    Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index |
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have h := probEvent_uniformHashOutput_admissible_view (fun view => view.1 = index)
  rw [probEvent_signerView_index] at h
  simpa only [signAttemptResultOfOutput_ne_none_iff, cachedIndexRate] using h
theorem expected_uniformHashOutput_index_choice (index : Index) (accepted rejected : ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if AdmissibleIndexOutput index output then accepted else rejected)) =
      cachedIndexRate * accepted +
        (1 - cachedIndexRate) * rejected := by
  have hnot : Pr[fun output => ¬ AdmissibleIndexOutput index output |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 1 - cachedIndexRate := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (AdmissibleIndexOutput index)
    rw [probFailure_of_liftM_PMF, tsub_zero, probEvent_uniformHashOutput_admissible_index, add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hsplit (output : HashOutput) :
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if AdmissibleIndexOutput index output then accepted else rejected) =
        (if AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬ AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    by_cases h : AdmissibleIndexOutput index output <;>
      simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false, zero_mul, zero_add, add_zero]
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite,
    probEvent_uniformHashOutput_admissible_index, hnot]
theorem bernoulliExcess_secondMoment_ennreal (score : ℝ) (probability : ENNReal)
    (hprob : probability ≤ 1) :
    probability * positiveScoreMoment (score + (1 - probability.toReal)) 2 +
        (1 - probability) * positiveScoreMoment (score + (-probability.toReal)) 2 ≤
      positiveScoreMoment score 2 + probability := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hprob
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness)
    (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hprob (by finiteness), ENNReal.toReal_one,
    positiveScoreMoment, ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _)]
  exact bernoulliExcess_secondMoment_le score probability.toReal ENNReal.toReal_nonneg
    ((ENNReal.toReal_mono (by finiteness) hprob).trans_eq ENNReal.toReal_one)
theorem positiveScoreMoment_mono (power : Nat) {before after : ℝ} (hle : before ≤ after) :
    positiveScoreMoment before power ≤ positiveScoreMoment after power :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _) (max_le_max hle le_rfl) power)
private theorem expected_cachedIndexScore_nonmessage_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hmessage : ¬ FtsProbeSimulation.MessageHashInput parameter input) (index : Index) (power : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) power) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
  simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
    hmessage, false_and, if_false, add_zero]
  calc
    _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
      apply ENNReal.tsum_le_tsum
      intro output
      exact mul_le_mul' le_rfl (positiveScoreMoment_mono power (sub_le_self _ (by positivity)))
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
theorem expected_cachedIndexScore_second_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (index : Index) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 + cachedIndexRate := by
  by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input
  · simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
      hmessage, true_and]
    have hchoice (output : HashOutput) :
        positiveScoreMoment (cachedIndexExcessScore parameter cache index +
          (if Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) -
          cachedIndexRate.toReal) 2 =
        if AdmissibleIndexOutput index output then
          positiveScoreMoment (cachedIndexExcessScore parameter cache index + (1 - cachedIndexRate.toReal)) 2
        else positiveScoreMoment (cachedIndexExcessScore parameter cache index + (-cachedIndexRate.toReal)) 2 := by
      unfold AdmissibleIndexOutput
      split_ifs <;> congr 1 <;> ring
    simp_rw [hchoice]
    rw [expected_uniformHashOutput_index_choice]
    exact bernoulliExcess_secondMoment_ennreal (cachedIndexExcessScore parameter cache index)
      cachedIndexRate cachedIndexRate_le_one
  · exact (expected_cachedIndexScore_nonmessage_le parameter cache hfinite input hfresh hmessage index 2).trans le_self_add
end SphincsSecurity.Concrete
end
