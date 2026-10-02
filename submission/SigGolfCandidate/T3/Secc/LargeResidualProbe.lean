import SigGolfCandidate.T3.Secc.LargePotential
import SigGolfCandidate.T3.BPORS

/-!
# LR-34 (1/4): residual probes of the T3 large route

A residual query of the large route may test two things at once (BP-C's "every query costs at most two units"):

* a **guess**: the query input carries a candidate value in the slot of one hidden coordinate (a hidden child label,
  a hidden secret, or the hidden honest message of an encoding row);
* a **hit**: the low half of the fresh answer equals a hidden-or-known label (`Hit.label`) or a known target digest
  (`Hit.target`, the presampled encoding reference digest).

This generalises the record's `HiddenLabelObservation.Probe` (pinned; `pair`/`output`) by the target hit. The
hidden coordinates are a product of uniform laws on candidate sets (`UniformTableCompletion.complete`); a surviving
probe restricts the candidate sets (`Probe.restrict`) and the posterior stays of product form
(`posterior_mass`, `bind_response_stopped`). The failure probability of a probe whose guessed coordinate keeps at
least `2^128 − probes` candidates is at most `hazard (2^128) probes` (`lazyResponse_failure_le_hazard`).
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev Digest := SphincsSecurity.Digest
abbrev HashOutput := SphincsSecurity.HashOutput

/-- Low half of an oracle answer (the honest value of a position). -/
def low (answer : HashOutput) : Digest := SphincsSecurity.truncateHash answer

/-- What the answer of a probe is compared with. -/
inductive Hit (Coord : Type) where
  /-- the label of a (hidden or disclosed) coordinate -/
  | label (parent : Coord)
  /-- a known digest (e.g. the presampled encoding reference digest) -/
  | target (value : Digest)

/-- A residual probe: an optional guess of one coordinate, and a hit test of the fresh answer. -/
structure Probe (Coord : Type) where
  guess : Option (Coord × Digest)
  hit : Hit Coord

section Defs
variable {Coord : Type}

/-- The hit test misses. -/
def Hit.miss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target t, _, value => t ≠ value

/-- The part of the hit test that constrains the labels. -/
def Hit.labelMiss : Hit Coord → (Coord → Digest) → Digest → Prop
  | .label parent, labels, value => labels parent ≠ value
  | .target _t, _, _ => True

/-- The part of the hit test that constrains only the answer. -/
def Hit.answerOk : Hit Coord → Digest → Prop
  | .label _p, _ => True
  | .target t, value => t ≠ value

theorem Hit.miss_iff (hit : Hit Coord) (labels : Coord → Digest) (value : Digest) :
    hit.miss labels value ↔ hit.labelMiss labels value ∧ hit.answerOk value := by
  cases hit <;> simp [Hit.miss, Hit.labelMiss, Hit.answerOk]

/-- The guess misses (or there is none). -/
def Probe.guessMiss (probe : Probe Coord) (labels : Coord → Digest) : Prop :=
  ∀ g ∈ probe.guess, labels g.1 ≠ g.2

/-- The probe survives: no guess, no hit. -/
def Probe.keep (probe : Probe Coord) (labels : Coord → Digest) (answer : HashOutput) : Prop :=
  probe.guessMiss labels ∧ probe.hit.miss labels (low answer)

variable [DecidableEq Coord]

/-- Candidate sets after a missed guess. -/
def Probe.guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) : Coord → Finset Digest :=
  match probe.guess with
  | none => allowed
  | some g => eraseTableValue allowed g.1 g.2

/-- Candidate sets after a missed label hit. -/
def Hit.restrict : Hit Coord → (Coord → Finset Digest) → Digest → Coord → Finset Digest
  | .label parent, allowed, value => eraseTableValue allowed parent value
  | .target _, allowed, _ => allowed

/-- The posterior candidate sets after a surviving probe with this answer. -/
def Probe.restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) :
    Coord → Finset Digest :=
  probe.hit.restrict (probe.guessRestrict allowed) (low answer)

/-- A guess is admissible when its coordinate still has at least two candidates (is hidden) and is not the hit
parent. -/
def Probe.Admissible (candidates : Coord → Finset Digest) (hit : Hit Coord) (g : Coord × Digest) : Prop :=
  2 ≤ (candidates g.1).card ∧ ∀ parent, hit = Hit.label parent → g.1 ≠ parent

/-- The state guard: drop an inadmissible guess. Every probe the T3 router issues is admissible, so the guard never
changes it there. -/
noncomputable def Probe.effective (candidates : Coord → Finset Digest) (probe : Probe Coord) : Probe Coord :=
  ⟨probe.guess.filter (fun g => decide (Probe.Admissible candidates probe.hit g)), probe.hit⟩

end Defs

/-! ## Membership and restriction -/

section Restrict
variable {Coord : Type} [DecidableEq Coord]

theorem mem_eraseTableValue (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest)
    (labels : Coord → Digest) (c : Coord) :
    labels c ∈ eraseTableValue allowed c0 v c ↔ labels c ∈ allowed c ∧ (c = c0 → labels c ≠ v) := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self, Finset.mem_erase, true_implies]
    exact and_comm
  · simp only [eraseTableValue, Function.update_of_ne h, h, false_implies, and_true]

theorem eraseTableValue_subset (allowed : Coord → Finset Digest) (c0 : Coord) (v : Digest) (c : Coord) :
    eraseTableValue allowed c0 v c ⊆ allowed c := by
  by_cases h : c = c0
  · subst h
    simp only [eraseTableValue, Function.update_self]
    exact Finset.erase_subset _ _
  · simp only [eraseTableValue, Function.update_of_ne h, subset_refl]

theorem guessRestrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (c : Coord) :
    probe.guessRestrict allowed c ⊆ allowed c := by
  unfold Probe.guessRestrict
  cases probe.guess with
  | none => exact subset_refl _
  | some g => exact eraseTableValue_subset _ _ _ _

theorem Hit.restrict_subset (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest) (c : Coord) :
    hit.restrict allowed value c ⊆ allowed c := by
  cases hit with
  | label parent => exact eraseTableValue_subset _ _ _ _
  | target t => exact subset_refl _

theorem restrict_subset (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput) (c : Coord) :
    probe.restrict allowed answer c ⊆ allowed c :=
  (Hit.restrict_subset _ _ _ c).trans (guessRestrict_subset probe allowed c)

theorem mem_guessRestrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.guessRestrict allowed c) ↔ (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels := by
  unfold Probe.guessRestrict Probe.guessMiss
  cases hg : probe.guess with
  | none => simp
  | some g =>
      simp only [mem_eraseTableValue, Option.mem_def, Option.some.injEq, forall_eq']
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h g.1).2 rfl⟩
      · rintro ⟨h, hg'⟩ c
        exact ⟨h c, fun hc => hc ▸ hg'⟩

theorem mem_hitRestrict (hit : Hit Coord) (allowed : Coord → Finset Digest) (value : Digest)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ hit.restrict allowed value c) ↔ (∀ c, labels c ∈ allowed c) ∧ hit.labelMiss labels value := by
  cases hit with
  | label parent =>
      simp only [Hit.restrict, Hit.labelMiss, mem_eraseTableValue]
      constructor
      · intro h
        exact ⟨fun c => (h c).1, (h parent).2 rfl⟩
      · rintro ⟨h, hp⟩ c
        exact ⟨h c, fun hc => hc ▸ hp⟩
  | target t => simp [Hit.restrict, Hit.labelMiss]

theorem mem_restrict (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (∀ c, labels c ∈ probe.restrict allowed answer c) ↔
      (∀ c, labels c ∈ allowed c) ∧ probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer) := by
  unfold Probe.restrict
  rw [mem_hitRestrict, mem_guessRestrict, and_assoc]

end Restrict

/-! ## Lazy response and posterior -/

section Posterior
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- The probe's response for fixed labels: a uniform fresh answer, or a stop (`failure`). -/
noncomputable def response (labels : Coord → Digest) (probe : Probe Coord) : SPMF HashOutput := do
  let answer ← (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)
  if probe.keep labels answer then pure answer else failure

/-- The probe's response with the labels drawn from the posterior candidate sets. -/
noncomputable def lazyResponse (allowed : Coord → Finset Digest) (probe : Probe Coord) : SPMF HashOutput :=
  complete allowed >>= fun labels => response labels probe

omit [Fintype Coord] [DecidableEq Coord] in
theorem response_apply (labels : Coord → Digest) (probe : Probe Coord) (answer : HashOutput) :
    response labels probe answer =
      if probe.keep labels answer then PMF.uniformOfFintype HashOutput answer else 0 := by
  rw [response, SPMF.bind_apply_eq_tsum]
  rw [tsum_eq_single answer]
  · by_cases h : probe.keep labels answer <;> simp only [h, if_true, if_false, SPMF.liftM_apply,
      SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    by_cases h : probe.keep labels other <;> simp only [h, if_true, if_false, SPMF.pure_apply,
      if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]

theorem Probe.mass (probe : Probe Coord) (allowed : Coord → Finset Digest) (answer : HashOutput)
    (labels : Coord → Digest) :
    (if probe.keep labels answer then complete allowed labels else 0) =
      if probe.hit.answerOk (low answer) then
        restrictionWeight allowed (probe.restrict allowed answer) * complete (probe.restrict allowed answer) labels
      else 0 := by
  by_cases ha : probe.hit.answerOk (low answer)
  · rw [if_pos ha]
    have h := restrict_guard allowed (probe.restrict allowed answer) (restrict_subset probe allowed answer)
      (fun labels => probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer))
      (fun labels => mem_restrict probe allowed answer labels) labels
    have hkeep : probe.keep labels answer ↔ probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer) := by
      simp only [Probe.keep, Hit.miss_iff, ha, and_true]
    by_cases hc : probe.guessMiss labels ∧ probe.hit.labelMiss labels (low answer)
    · rw [if_pos (hkeep.mpr hc)]
      rw [if_pos hc] at h
      exact h
    · rw [if_neg (fun h' => hc (hkeep.mp h'))]
      rw [if_neg hc] at h
      exact h
  · have hk : ¬probe.keep labels answer := fun h => ha ((Hit.miss_iff _ _ _).mp h.2).2
    simp only [hk, ha, if_false]

theorem lazyResponse_apply (allowed : Coord → Finset Digest) (probe : Probe Coord) (answer : HashOutput) :
    lazyResponse allowed probe answer = PMF.uniformOfFintype HashOutput answer *
      (if probe.hit.answerOk (low answer) then restrictionWeight allowed (probe.restrict allowed answer) else 0) := by
  rw [lazyResponse, SPMF.bind_apply_eq_tsum]
  simp only [response_apply, mul_ite, mul_zero]
  calc
    _ = PMF.uniformOfFintype HashOutput answer *
        ∑' labels, (if probe.keep labels answer then complete allowed labels else 0) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro labels
      split <;> simp only [mul_comm, zero_mul]
    _ = _ := by
      simp only [Probe.mass]
      by_cases ha : probe.hit.answerOk (low answer)
      · simp only [ha, if_true]
        rw [ENNReal.tsum_mul_left, weight_tsum_complete]
      · simp only [ha, if_false, tsum_zero, mul_zero]

theorem posterior_mass (allowed : Coord → Finset Digest) (probe : Probe Coord)
    (answer : HashOutput) (labels : Coord → Digest) :
    lazyResponse allowed probe answer * complete (probe.restrict allowed answer) labels =
      complete allowed labels * response labels probe answer := by
  rw [lazyResponse_apply, response_apply]
  have h := Probe.mass probe allowed answer labels
  by_cases hk : probe.keep labels answer
  · rw [if_pos hk] at h
    rw [if_pos hk, h]
    split <;> simp only [mul_comm, mul_assoc, zero_mul, mul_left_comm]
  · rw [if_neg hk] at h
    rw [if_neg hk, mul_zero]
    by_cases ha : probe.hit.answerOk (low answer)
    · rw [if_pos ha] at h
      rw [if_pos ha, mul_assoc, ← h, mul_zero]
    · rw [if_neg ha, mul_zero, zero_mul]

theorem lazyResponse_nonempty (allowed : Coord → Finset Digest) (probe : Probe Coord)
    (answer : HashOutput) (h : lazyResponse allowed probe answer ≠ 0) :
    ∀ c, (probe.restrict allowed answer c).Nonempty := by
  by_contra hnonempty
  rw [lazyResponse_apply] at h
  by_cases ha : probe.hit.answerOk (low answer)
  · rw [if_pos ha, weight_of_empty _ _ hnonempty, mul_zero] at h
    exact h rfl
  · rw [if_neg ha, mul_zero] at h
    exact h rfl

/-- Posterior identity of one probe (as the record's `bind_response_stopped`). -/
theorem bind_response_stopped {Result : Type} (allowed : Coord → Finset Digest)
    (ha : ∀ c, (allowed c).Nonempty) (probe : Probe Coord) (stopped : SPMF Result)
    (next : HashOutput → (Coord → Digest) → SPMF Result) :
    (complete allowed >>= fun labels => observe (response labels probe) stopped (fun answer => next answer labels)) =
      observe (lazyResponse allowed probe) stopped
        (fun answer => complete (probe.restrict allowed answer) >>= next answer) := by
  have h := posterior_observe (uniformTable allowed ha) (fun labels => response labels probe)
    (lazyResponse allowed probe) (fun answer => complete (probe.restrict allowed answer))
    (by rw [lazyResponse, complete_of_nonempty allowed ha])
    (fun answer labels => by
      simpa only [complete_of_nonempty allowed ha, SPMF.liftM_apply] using posterior_mass allowed probe answer labels)
    stopped next
  simpa only [complete_of_nonempty allowed ha] using h

end Posterior

/-! ## Failure probability (the two-unit hazard) -/

section Hazard
variable {Coord : Type} [Fintype Coord] [DecidableEq Coord]

/-- The joint law of hidden labels (posterior candidates) and a fresh uniform answer. -/
noncomputable def law (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty) :
    PMF ((Coord → Digest) × HashOutput) :=
  (uniformTable allowed ha).bind fun labels =>
    (PMF.uniformOfFintype HashOutput).map fun answer => (labels, answer)

omit [Fintype Coord] [DecidableEq Coord] in
theorem response_failure (labels : Coord → Digest) (probe : Probe Coord) :
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

theorem lazyResponse_failure (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty)
    (probe : Probe Coord) :
    (lazyResponse allowed probe).toPMF none = Pr[fun x => ¬probe.keep x.1 x.2 | law allowed ha] := by
  rw [lazyResponse, complete_of_nonempty allowed ha, toPMF_bind_lift, PMF.bind_apply]
  change _ = Pr[fun x => ¬probe.keep x.1 x.2 |
    (uniformTable allowed ha) >>= fun labels => (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput]
  rw [probEvent_bind_eq_tsum]
  simp only [PMF.probOutput_eq_apply, probEvent_map]
  apply tsum_congr
  intro labels
  rw [response_failure]
  rfl

omit [Fintype Coord] [DecidableEq Coord] in
/-- For fixed labels, the hit test of a uniform answer misses with probability exactly `1 − 2^-128`. -/
theorem hit_miss_prob (hit : Hit Coord) (labels : Coord → Digest) :
    Pr[fun answer => hit.miss labels (low answer) | PMF.uniformOfFintype HashOutput] =
      1 - (Fintype.card Digest : ENNReal)⁻¹ := by
  cases hit with
  | label parent =>
      have he : (fun answer => Hit.miss (.label parent) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ labels parent) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne (labels parent)
  | target t =>
      have he : (fun answer => Hit.miss (.target t) labels (low answer)) =
          (fun answer => SphincsSecurity.truncateHash answer ≠ t) := by
        funext answer
        simp only [Hit.miss, low, ne_eq, eq_comm]
      rw [he]
      exact HiddenLabelProbe.prob_truncate_ne t

theorem keep_prob (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty) (probe : Probe Coord) :
    Pr[fun x => probe.keep x.1 x.2 | law allowed ha] =
      Pr[fun labels => probe.guessMiss labels | uniformTable allowed ha] * (1 - (Fintype.card Digest : ENNReal)⁻¹) := by
  change Pr[fun x => probe.keep x.1 x.2 |
    (uniformTable allowed ha) >>= fun labels => (fun answer => (labels, answer)) <$> PMF.uniformOfFintype HashOutput] = _
  rw [probEvent_bind_eq_tsum]
  have hinner (labels : Coord → Digest) :
      Pr[(fun x : (Coord → Digest) × HashOutput => probe.keep x.1 x.2) ∘ (fun answer => (labels, answer)) |
        PMF.uniformOfFintype HashOutput] =
      if probe.guessMiss labels then 1 - (Fintype.card Digest : ENNReal)⁻¹ else 0 := by
    by_cases hg : probe.guessMiss labels
    · rw [if_pos hg, ← hit_miss_prob probe.hit labels]
      have he : ((fun x : (Coord → Digest) × HashOutput => probe.keep x.1 x.2) ∘ (fun answer => (labels, answer))) =
          (fun answer => probe.hit.miss labels (low answer)) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, true_and]
      rw [he]
    · rw [if_neg hg]
      have he : ((fun x : (Coord → Digest) × HashOutput => probe.keep x.1 x.2) ∘ (fun answer => (labels, answer))) =
          (fun _ => False) := by
        funext answer
        simp only [Function.comp_def, Probe.keep, hg, false_and]
      rw [he, probEvent_eq_tsum_ite]
      simp
  simp only [probEvent_map, hinner, PMF.probOutput_eq_apply, mul_ite, mul_zero]
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  simp only [PMF.probOutput_eq_apply, ite_mul, zero_mul]

theorem guessMiss_prob_ge (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty) (probe : Probe Coord)
    (minimum : Nat) (hmin : ∀ g ∈ probe.guess, minimum ≤ (allowed g.1).card) :
    1 - (minimum : ENNReal)⁻¹ ≤ Pr[fun labels => probe.guessMiss labels | uniformTable allowed ha] := by
  cases hg : probe.guess with
  | none =>
      have he : (fun labels => probe.guessMiss labels) = (fun _ => True) := by
        funext labels
        simp only [Probe.guessMiss, hg, Option.mem_def, reduceCtorEq, false_implies, implies_true]
      rw [he, probEvent_eq_tsum_ite]
      simp only [if_true, PMF.probOutput_eq_apply, PMF.tsum_coe]
      exact tsub_le_self
  | some g =>
      have hmin' := hmin g (by rw [hg]; rfl)
      have hcompl := probEvent_compl (uniformTable allowed ha) (fun labels => labels g.1 = g.2)
      rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
      have hhit : Pr[fun labels => labels g.1 = g.2 | uniformTable allowed ha] ≤ (minimum : ENNReal)⁻¹ := by
        rw [probEvent_uniformTable_eq]
        split
        · exact ENNReal.inv_le_inv.mpr (by exact_mod_cast hmin')
        · exact bot_le
      have hmiss : (fun labels => probe.guessMiss labels) = (fun labels => ¬labels g.1 = g.2) := by
        funext labels
        simp only [Probe.guessMiss, hg, Option.mem_def, Option.some.injEq, forall_eq', ne_eq]
      rw [hmiss]
      have heq : Pr[fun labels => ¬labels g.1 = g.2 | uniformTable allowed ha] =
          1 - Pr[fun labels => labels g.1 = g.2 | uniformTable allowed ha] :=
        ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
      rw [heq]
      exact tsub_le_tsub_left hhit 1

/-- **The two-unit hazard.** A probe whose guessed coordinate keeps at least `2^128 − probes` candidates stops with
probability at most `hazard (2^128) probes = 1 − (1 − 1/(2^128 − probes))²`. -/
theorem lazyResponse_failure_le_hazard (allowed : Coord → Finset Digest) (ha : ∀ c, (allowed c).Nonempty)
    (probe : Probe Coord) (probes : Nat)
    (hmin : ∀ g ∈ probe.guess, 2 ^ 128 - probes ≤ (allowed g.1).card) :
    (lazyResponse allowed probe).toPMF none ≤ LargePotential.hazard (2 ^ 128) probes := by
  rw [lazyResponse_failure allowed ha probe]
  have hcompl := probEvent_compl (law allowed ha) (fun x => probe.keep x.1 x.2)
  rw [probFailure_of_liftM_PMF, tsub_zero] at hcompl
  have heq : Pr[fun x => ¬probe.keep x.1 x.2 | law allowed ha] = 1 - Pr[fun x => probe.keep x.1 x.2 | law allowed ha] :=
    ENNReal.eq_sub_of_add_eq' (by simp) (by rw [add_comm]; exact hcompl)
  rw [heq, LargePotential.hazard]
  apply tsub_le_tsub_left _ 1
  rw [keep_prob allowed ha probe, pow_two]
  apply mul_le_mul' (guessMiss_prob_ge allowed ha probe _ hmin)
  apply tsub_le_tsub_left
  have hcard : (Fintype.card Digest : ENNReal) = ((2 ^ 128 : Nat) : ENNReal) := by
    simp [SphincsSecurity.digestBits]
  rw [hcard]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.sub_le _ _)

end Hazard

end SigGolfCandidate.T3.Security.LargeResidual
