import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableCompletion
import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement

section



namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
inductive Probe (Coordinate : Type) where
  | pair (child parent : Coordinate) (distinct : child ≠ parent) (candidate : Digest)
  | output (parent : Coordinate)
variable {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
def Probe.keep (probe : Probe Coordinate) (labels : Coordinate → Digest) (answer : HashOutput) : Prop :=
  match probe with
  | .pair child parent _ candidate => labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
  | .output parent => labels parent ≠ truncateHash answer
def Probe.restrict (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) : Coordinate → Finset Digest :=
  match probe with
  | .pair child parent _ candidate => pairedMissAllowed allowed child candidate parent (truncateHash answer)
  | .output parent => eraseTableValue allowed parent (truncateHash answer)
omit [Fintype Coordinate] in
theorem Probe.card_lower (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (coordinate : Coordinate) :
    (allowed coordinate).card - 1 ≤ (probe.restrict allowed answer coordinate).card := by
  cases probe with
  | pair child parent distinct candidate =>
      exact pairedMissAllowed_card_lower allowed child parent distinct candidate (truncateHash answer) coordinate
  | output parent =>
      by_cases heq : coordinate = parent
      · subst coordinate
        simpa only [Probe.restrict, eraseTableValue, Function.update_self] using
          (Finset.pred_card_le_card_erase (s := allowed parent) (a := truncateHash answer))
      · simpa only [Probe.restrict, eraseTableValue, Function.update_of_ne heq] using Nat.sub_le (allowed coordinate).card 1
theorem Probe.mass (probe : Probe Coordinate) (allowed : Coordinate → Finset Digest)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels := by
  cases probe with
  | pair child parent distinct candidate =>
      have h := paired_mass allowed child parent distinct candidate (truncateHash answer) labels
      by_cases hk : labels child ≠ candidate ∧ labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h
  | output parent =>
      have h := single_mass allowed parent (truncateHash answer) labels
      by_cases hk : labels parent ≠ truncateHash answer
      · simpa only [Probe.keep, Probe.restrict, if_pos hk] using h
      · simpa only [Probe.keep, Probe.restrict, if_neg hk] using h
noncomputable def response (labels : Coordinate → Digest) (probe : Probe Coordinate) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure
omit [Fintype Coordinate] [DecidableEq Coordinate] in
theorem response_apply (labels : Coordinate → Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    response labels probe answer = if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
noncomputable def lazyResponse (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe
theorem lazyResponse_apply (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate) (answer : HashOutput) :
    lazyResponse allowed probe answer = PMF.uniformOfFintype HashOutput answer *
      restrictionWeight allowed (probe.restrict allowed answer) := by
  rw [lazyResponse, SPMF.bind_apply_eq_tsum]
  simp only [response_apply, mul_ite, mul_zero]
  calc
    _ = PMF.uniformOfFintype HashOutput answer *
        ∑' labels, restrictionWeight allowed (probe.restrict allowed answer) *
          complete (probe.restrict allowed answer) labels := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro labels
      rw [← Probe.mass]
      split <;> simp only [mul_comm, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_left, weight_tsum_complete]
theorem posterior_mass (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (labels : Coordinate → Digest) :
    lazyResponse allowed probe answer * complete (probe.restrict allowed answer) labels =
      complete allowed labels * response labels probe answer := by
  rw [lazyResponse_apply, mul_assoc, ← Probe.mass, response_apply]
  split <;> simp only [mul_comm, zero_mul]
theorem lazyResponse_nonempty (allowed : Coordinate → Finset Digest) (probe : Probe Coordinate)
    (answer : HashOutput) (h : lazyResponse allowed probe answer ≠ 0) :
    ∀ coordinate, (probe.restrict allowed answer coordinate).Nonempty := by
  by_contra hnonempty
  rw [lazyResponse_apply, weight_of_empty _ _ hnonempty, mul_zero] at h
  exact h rfl
end SphincsSecurity.Concrete.HiddenLabelObservation
end

section


namespace SphincsSecurity.Concrete.RetainedObservation
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Label Answer Result : Type}
theorem bind_comm (p : SPMF Label) (q : SPMF Answer) (next : Label → Answer → SPMF Result) :
    (p >>= fun label => q >>= next label) = (q >>= fun answer => p >>= fun label => next label answer) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro answer
  apply tsum_congr
  intro label
  exact mul_left_comm _ _ _
theorem bind_congr (p : SPMF Label) (f g : Label → SPMF Result)
    (h : ∀ label, p label ≠ 0 → f label = g label) : (p >>= f) = (p >>= g) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum]
  apply tsum_congr
  intro label
  by_cases hp : p label = 0
  · simp only [hp, zero_mul]
  · rw [h label hp]
theorem bind_nonzero (p : SPMF Label) (next : Label → SPMF Result) (result : Result) :
    (p >>= next) result ≠ 0 ↔ ∃ label, p label ≠ 0 ∧ next label result ≠ 0 := by
  rw [← SPMF.mem_support_iff, SPMF.support_bind]
  simp only [Set.mem_iUnion, SPMF.mem_support_iff, exists_prop]
theorem lift_bind_const (p : PMF Label) (next : SPMF Result) :
    ((liftM p : SPMF Label) >>= fun _ => next) = next := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
theorem toPMF_bind_lift (p : PMF Label) (next : Label → SPMF Answer) :
    ((liftM p : SPMF Label) >>= next).toPMF = p.bind (fun label => (next label).toPMF) := by
  rw [SPMF.toPMF_bind, SPMF.liftM_eq_map, SPMF.toPMF_mk]
  simp only [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
  rfl
noncomputable def observe (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) : SPMF Result :=
  (liftM response.toPMF : SPMF (Option Answer)) >>= fun
    | none => stopped
    | some answer => next answer
theorem observe_apply (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result = response.toPMF none * stopped result +
      ∑' answer, response answer * next answer result := by
  rw [observe, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.liftM_apply]
  rw [tsum_option _ ENNReal.summable]
  rfl
theorem observe_nonzero (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (result : Result) :
    observe response stopped next result ≠ 0 ↔
      (response.toPMF none ≠ 0 ∧ stopped result ≠ 0) ∨
        ∃ answer, response answer ≠ 0 ∧ next answer result ≠ 0 := by
  rw [observe, bind_nonzero]
  constructor
  · rintro ⟨answer, hanswer, hresult⟩
    cases answer with
    | none => exact Or.inl ⟨by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    | some answer =>
        refine Or.inr ⟨answer, ?_, hresult⟩
        rw [SPMF.apply_eq_toPMF_some response answer]
        simpa only [SPMF.liftM_apply] using hanswer
  · rintro (⟨hanswer, hresult⟩ | ⟨answer, hanswer, hresult⟩)
    · exact ⟨none, by simpa only [SPMF.liftM_apply] using hanswer, hresult⟩
    · refine ⟨some answer, ?_, hresult⟩
      rw [SPMF.liftM_apply, ← SPMF.apply_eq_toPMF_some response answer]
      exact hanswer
theorem observe_bind {Other : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (after : Result → SPMF Other) :
    (observe response stopped next >>= after) =
      observe response (stopped >>= after) (fun answer => next answer >>= after) := by
  simp only [observe, bind_assoc]
  congr 1
  funext answer
  cases answer <;> rfl
theorem observe_congr (response : SPMF Answer) (stopped : SPMF Result)
    (f g : Answer → SPMF Result) (h : ∀ answer, response answer ≠ 0 → f answer = g answer) :
    observe response stopped f = observe response stopped g := by
  apply SPMF.ext
  intro result
  simp only [observe_apply]
  apply congrArg (response.toPMF none * stopped result + ·)
  apply tsum_congr
  intro answer
  by_cases hp : response answer = 0
  · simp only [hp, zero_mul]
  · rw [h answer hp]
theorem posterior_observe (prior : PMF Label) (response : Label → SPMF Answer)
    (predictive : SPMF Answer) (posterior : Answer → SPMF Label)
    (hpredictive : predictive = ((liftM prior : SPMF Label) >>= response))
    (hmass : ∀ answer label, predictive answer * posterior answer label = prior label * response label answer)
    (stopped : SPMF Result) (next : Answer → Label → SPMF Result) :
    ((liftM prior : SPMF Label) >>= fun label => observe (response label) stopped (fun answer => next answer label)) =
      observe predictive stopped (fun answer => posterior answer >>= next answer) := by
  have hnone : (∑' label, prior label * (response label).toPMF none) = predictive.toPMF none := by
    rw [hpredictive, toPMF_bind_lift, PMF.bind_apply]
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, SPMF.liftM_apply, observe_apply, mul_add, ENNReal.tsum_add]
  apply congrArg₂ (· + ·)
  · simpa only [← mul_assoc, ENNReal.tsum_mul_right] using congrArg (· * stopped result) hnone
  · simp only [← ENNReal.tsum_mul_left, ← mul_assoc, hmass]
    rw [ENNReal.tsum_comm]
end SphincsSecurity.Concrete.RetainedObservation
namespace SphincsSecurity.Concrete.HiddenLabelObservation
open _root_.OracleComp UniformTableCompletion RetainedObservation
theorem bind_response_stopped {Coordinate Result : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (allowed : Coordinate → Finset Digest) (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (probe : Probe Coordinate) (stopped : SPMF Result) (next : HashOutput → (Coordinate → Digest) → SPMF Result) :
    (complete allowed >>= fun labels => observe (response labels probe) stopped (fun answer => next answer labels)) =
      observe (lazyResponse allowed probe) stopped (fun answer => complete (probe.restrict allowed answer) >>= next answer) := by
  have h := posterior_observe (uniformTable allowed ha) (fun labels => response labels probe)
    (lazyResponse allowed probe) (fun answer => complete (probe.restrict allowed answer))
    (by rw [lazyResponse, complete_of_nonempty allowed ha])
    (fun answer labels => by
      simpa only [complete_of_nonempty allowed ha, SPMF.liftM_apply] using posterior_mass allowed probe answer labels)
    stopped next
  simpa only [complete_of_nonempty allowed ha] using h
end SphincsSecurity.Concrete.HiddenLabelObservation
end
