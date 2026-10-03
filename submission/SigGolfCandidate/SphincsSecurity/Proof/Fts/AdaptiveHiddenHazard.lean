import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableRestriction
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedObservation

section



namespace SphincsSecurity.Concrete.HiddenLabelProbe
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
noncomputable def law (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) : PMF ((Coordinate → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)
def Match (child parent : Coordinate) (candidate : Digest)
    (result : (Coordinate → Digest) × HashOutput) : Prop :=
  result.1 child = candidate ∨ truncateHash result.2 = result.1 parent
theorem prob_truncate_eq (target : Digest) :
    Pr[fun answer => truncateHash answer = target | PMF.uniformOfFintype HashOutput] =
      (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply] using probEvent_uniform_truncateHash_eq target
theorem prob_truncate_ne (target : Digest) :
    Pr[fun answer => truncateHash answer ≠ target | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  have h := probEvent_compl (PMF.uniformOfFintype HashOutput) (fun answer => truncateHash answer = target)
  rw [prob_truncate_eq, probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by finiteness) (by rwa [add_comm])
theorem prob_survive (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest) :
    Pr[fun result => ¬Match child parent candidate result | law allowed ha] =
      Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] *
        (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun result => ¬Match child parent candidate result |
    (uniformTable allowed ha) >>= fun labels =>
      (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (labels : Coordinate → Digest) :
      Pr[(fun result => ¬Match child parent candidate result) ∘ (fun answer => (labels, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if labels child ≠ candidate then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hc : labels child = candidate
    · simp [Function.comp_def, Match, hc]
    · simpa only [Function.comp_def, Match, hc, false_or, if_pos hc] using prob_truncate_ne (labels parent)
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]
theorem prob_child_miss (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest) :
    Pr[fun labels => labels child ≠ candidate | uniformTable allowed ha] =
      1 - Pr[fun labels => labels child = candidate | uniformTable allowed ha] := by
  have h := probEvent_compl (uniformTable allowed ha) (fun labels => labels child = candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) (by rwa [add_comm])
theorem prob_child_hit_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[fun labels => labels child = candidate | uniformTable allowed ha] ≤ (minimum : ENNReal)⁻¹ := by
  rw [probEvent_uniformTable_eq]
  split
  · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmin)
  · exact bot_le
theorem prob_survive_ge (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    (1 - (minimum : ENNReal)⁻¹) ^ 2 ≤
      Pr[fun result => ¬Match child parent candidate result | law allowed ha] := by
  have hspace : minimum ≤ Fintype.card Digest := hmin.trans (Finset.card_le_univ _)
  rw [prob_survive, prob_child_miss, pow_two]
  exact mul_le_mul' (tsub_le_tsub_left (prob_child_hit_le allowed ha child candidate minimum hmin) _)
    (tsub_le_tsub_left (ENNReal.inv_le_inv.mpr (by exact_mod_cast hspace)) _)
theorem prob_match_le (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (minimum : Nat) (hmin : minimum ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤ 1 - (1 - (minimum : ENNReal)⁻¹) ^ 2 := by
  have h := probEvent_compl (law allowed ha) (Match child parent candidate)
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq' (by simp) h
  rw [heq]
  exact tsub_le_tsub_left (prob_survive_ge allowed ha child parent candidate minimum hmin) _
theorem prob_match_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (candidate : Digest)
    (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    Pr[Match child parent candidate | law allowed ha] ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 :=
  prob_match_le allowed ha child parent candidate _ hmin
end SphincsSecurity.Concrete.HiddenLabelProbe
end

section



namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_failure (labels : Coordinate → Digest) (probe : Probe Coordinate) :
    (response labels probe).toPMF none =
      Pr[fun answer => ¬probe.keep labels answer | PMF.uniformOfFintype HashOutput] := by
  rw [response, toPMF_bind_lift, PMF.bind_apply, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, not_true_eq_false, if_false, SPMF.toPMF_pure, PMF.pure_apply,
      reduceCtorEq, mul_zero]
  · simp only [h, if_false, not_false_eq_true, if_true, SPMF.toPMF_failure, PMF.pure_apply,
      mul_one, PMF.probOutput_eq_apply]
theorem lazyResponse_pair_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none =
      Pr[HiddenLabelProbe.Match child parent candidate | HiddenLabelProbe.law allowed ha] := by
  rw [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[HiddenLabelProbe.Match child parent candidate |
    (uniformTable allowed ha) >>= fun labels => (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro labels
  apply congrArg (uniformTable allowed ha labels * ·)
  rw [response_failure]
  apply congrArg (fun event => Pr[event | PMF.uniformOfFintype HashOutput])
  funext answer
  apply propext
  simp only [Probe.keep, HiddenLabelProbe.Match, Function.comp_def, not_and_or, not_not, eq_comm]
theorem lazyResponse_pair_failure_le_rounds (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (child parent : Coordinate) (hne : child ≠ parent)
    (candidate : Digest) (rounds : Nat) (hmin : 2 ^ digestBits - rounds ≤ (allowed child).card) :
    (lazyResponse allowed (.pair child parent hne candidate)).toPMF none ≤
      1 - (1 - ((2 ^ digestBits - rounds : Nat) : ENNReal)⁻¹) ^ 2 := by
  rw [lazyResponse_pair_failure allowed ha child parent hne candidate]
  exact HiddenLabelProbe.prob_match_le_rounds allowed ha child parent candidate rounds hmin
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_output_failure (labels : Coordinate → Digest) (parent : Coordinate) :
    (response labels (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [response_failure]
  simpa only [Probe.keep, not_not, eq_comm] using HiddenLabelProbe.prob_truncate_eq (labels parent)
theorem lazyResponse_output_failure (allowed : Coordinate → Finset Digest)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) (parent : Coordinate) :
    (lazyResponse allowed (.output parent)).toPMF none = (Fintype.card Digest : ENNReal)⁻¹ := by
  simp only [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply,
    response_output_failure, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end SphincsSecurity.Concrete.HiddenLabelObservation
namespace SphincsSecurity.Concrete.AdaptiveHiddenLabels
open _root_.OracleComp OracleSpec ENNReal HiddenLabelObservation
end SphincsSecurity.Concrete.AdaptiveHiddenLabels
end
