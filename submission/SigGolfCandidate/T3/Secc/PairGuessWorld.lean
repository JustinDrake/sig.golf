import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedObservation
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessForced
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessObservation
import SigGolfCandidate.T3.Secc.CanonGraph
import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessErasure

section

namespace SphincsSecurity.Concrete.WeightedQuery
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {Index State : Type} {spec : OracleSpec Index}
noncomputable def implementation (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) : QueryImpl spec (StateT (State × ENNReal) SPMF) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2 * factor state.1 input))) <$> (base input).run state.1
noncomputable def run {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :=
  (simulateQ (implementation base factor) computation).run state
theorem run_forget {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :
    (fun result => (result.1, result.2.1)) <$> run base factor computation state =
      (simulateQ base computation).run state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, map_bind]
      exact congrArg ((base input).run state.1 >>= ·) (funext fun result => ih result.1 _)
theorem run_payoff {Result : Type} (left right : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal)
    (hstep : ∀ state input result, (left input).run state result = factor state input * (right input).run state result)
    (computation : OracleComp spec Result) (state : State) (weight : ENNReal) (payoff : Result × State → ENNReal) :
    weight * (∑' result, Pr[= result | (simulateQ left computation).run state] * payoff result) =
      ∑' result, Pr[= result | run right factor computation (state, weight)] *
        (result.2.2 * payoff (result.1, result.2.1)) := by
  induction computation using OracleComp.inductionOn generalizing state weight with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, tsum_probOutput_bind_mul]
      simp only [run] at ih
      simp_rw [← ih]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      simp only [SPMF.probOutput_eq_apply, hstep]
      ring
theorem run_preserves {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (invariant : State × ENNReal → Prop)
    (hstep : ∀ state, invariant state → ∀ input result, (base input).run state.1 result ≠ 0 →
      invariant (result.2, state.2 * factor state.1 input))
    (computation : OracleComp spec Result) (state : State × ENNReal) (hs : invariant state)
    (result : Result × State × ENNReal) (hr : run base factor computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [run, simulateQ_pure, StateT.run_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hs
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation, StateT.run_mk,
        bind_map_left, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 (middle.2, state.2 * factor state.1 input) (hstep state hs input middle hm) result hr
end SphincsSecurity.Concrete.WeightedQuery
end

section


namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def hitTrial (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  if state.probes = slot then
    trial state.allowed coordinate candidate >>= fun hit =>
      if hit = true ∧ coordinate ∉ state.retired then pure hit else failure
  else trial state.allowed coordinate candidate
noncomputable def trialFactor (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) : ENNReal :=
  if state.probes = slot then
    if coordinate ∉ state.retired then trial state.allowed coordinate candidate true else 0
  else 1
theorem hitTrial_apply (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    hitTrial slot state coordinate candidate hit =
      trialFactor slot state coordinate candidate * forcedTrial slot state coordinate candidate hit := by
  by_cases hs : state.probes = slot
  · by_cases hc : coordinate ∉ state.retired
    · have hmass : hitTrial slot state coordinate candidate hit =
          if hit = true then trial state.allowed coordinate candidate true else 0 := by
        rw [hitTrial, if_pos hs, SPMF.bind_apply_eq_tsum]
        simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, false_and, if_false, true_and,
          hc, SPMF.failure_apply, mul_zero, add_zero]
        split <;> simp_all
      rw [hmass]
      by_cases hp : trial state.allowed coordinate candidate true = 0
      · simp only [trialFactor, if_pos hs, if_pos hc, hp, zero_mul, ite_self]
      · have he : EligibleAt slot state coordinate candidate := ⟨hs, hc, hp⟩
        simp only [trialFactor, if_pos hs, if_pos hc, forcedTrial, if_pos he, SPMF.pure_apply,
          mul_ite, mul_one, mul_zero]
    · simp only [hitTrial, trialFactor, if_pos hs, hc, and_false, if_false, SPMF.bind_apply_eq_tsum,
        SPMF.failure_apply, mul_zero, tsum_zero, zero_mul]
  · have he : ¬EligibleAt slot state coordinate candidate := fun h => hs h.1
    simp only [hitTrial, trialFactor, if_neg hs, forcedTrial, if_neg he, one_mul]
theorem hitTrial_bind_apply {Result : Type} (slot : Nat) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → SPMF Result) (result : Result) :
    (hitTrial slot state coordinate candidate >>= next) result =
      trialFactor slot state coordinate candidate * (forcedTrial slot state coordinate candidate >>= next) result := by
  simp only [SPMF.bind_apply_eq_tsum, hitTrial_apply, mul_assoc, ENNReal.tsum_mul_left]
noncomputable def hitImpl (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => lazyImpl environment (.inl input)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> hitTrial slot state coordinate candidate
  | .inr (.inr coordinate) => lazyImpl environment (.inr (.inr coordinate))
noncomputable def forceFactor (slot : Nat) (state : State Coordinate Value Memory) :
    (World auxSpec Coordinate Value).Domain → ENNReal
  | .inr (.inl (coordinate, candidate)) => trialFactor slot state coordinate candidate
  | _ => 1
theorem hitImpl_apply (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory) :
    (hitImpl environment slot input).run state result =
      forceFactor slot state input * (forcedImpl environment slot input).run state result := by
  cases input with
  | inl input => simp only [hitImpl, forcedImpl, forceFactor, one_mul]
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [hitImpl, forcedImpl, forceFactor, StateT.run_mk, map_eq_bind_pure_comp,
            Function.comp_def]
          exact hitTrial_bind_apply slot state coordinate candidate
            (fun hit : Bool => pure (hit, afterTrial environment state coordinate candidate hit)) result
      | inr coordinate => simp only [hitImpl, forcedImpl, forceFactor, one_mul]
theorem hitImplRun_weighted_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | runWith (hitImpl environment slot) computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (state, 1)] *
        (result.2.2 * payoff (result.1, result.2.1)) := by
  have h := WeightedQuery.run_payoff (hitImpl environment slot) (forcedImpl environment slot) (forceFactor slot)
    (hitImpl_apply environment slot) computation state 1 payoff
  simpa only [one_mul, runWith] using h
noncomputable def hitRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (hitImpl environment slot) computation state >>= fun result =>
    if slot < result.2.probes then pure result else (failure : SPMF _)
noncomputable def forceWeight (slot : Nat) (state : State Coordinate Value Memory × ENNReal) : ENNReal :=
  if slot < state.1.probes then state.2 else 0
theorem hitRun_weighted_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitRun environment slot computation state] * payoff result) =
      ∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (state, 1)] *
        (forceWeight slot result.2 * payoff (result.1, result.2.1)) := by
  have h := hitImplRun_weighted_forced environment slot computation state
    (fun result => if slot < result.2.probes then payoff result else 0)
  rw [hitRun, tsum_probOutput_bind_mul]
  convert h using 1
  · apply tsum_congr
    intro result
    congr 1
    by_cases hp : slot < result.2.probes
    · simp only [if_pos hp, tsum_probOutput_pure_mul]
    · simp only [if_neg hp, SPMF.probOutput_eq_apply, SPMF.failure_apply, zero_mul, tsum_zero]
  · apply tsum_congr
    intro result
    congr 1
    simp only [forceWeight, mul_ite, ite_mul, mul_zero, zero_mul]
end SphincsSecurity.Concrete.SecretGuessObservation
end

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
theorem forceFactor_le_one (slot : Nat) (state : State Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) : forceFactor slot state input ≤ 1 := by
  cases input with
  | inl input => exact le_rfl
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [forceFactor, trialFactor]
          split
          · split
            · simpa only [SPMF.probOutput_eq_apply] using
                (show Pr[= true | trial state.allowed coordinate candidate] ≤ 1 from probOutput_le_one)
            · exact bot_le
          · exact le_rfl
      | inr coordinate => exact le_rfl
theorem forceFactor_weight_bound (environment : Environment auxSpec Coordinate Value Memory) (size budget slot : Nat)
    (hslot : slot ≤ budget) (state : State Coordinate Value Memory) (weight : ENNReal)
    (hs : Invariant size state) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hw : weight ≤ 1) (hlate : slot < state.probes → weight ≤ ((size - budget : Nat) : ENNReal)⁻¹)
    (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (forcedImpl environment slot input).run state result ≠ 0) :
    weight * forceFactor slot state input ≤ 1 ∧
      (slot < result.2.probes → weight * forceFactor slot state input ≤ ((size - budget : Nat) : ENNReal)⁻¹) := by
  have hm : weight * forceFactor slot state input ≤ weight := mul_le_of_le_one_right' (forceFactor_le_one slot state input)
  refine ⟨hm.trans hw, ?_⟩
  intro hafter
  by_cases hb : slot < state.probes
  · exact hm.trans (hlate hb)
  have hp := forcedImpl_probes environment slot state input result hr
  cases input with
  | inl input => simp only [probeStep, Nat.add_zero] at hp; omega
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          change result.2.probes = state.probes + 1 at hp
          have he : state.probes = slot := by omega
          simp only [forceFactor, trialFactor, if_pos he]
          split
          next hc =>
            exact (mul_le_of_le_one_left' hw).trans
              (trial_true_le size budget state hs ha (he ▸ hslot) coordinate hc candidate)
          next hc => simp only [mul_zero]; exact bot_le
      | inr coordinate => simp only [probeStep, Nat.add_zero] at hp; omega
theorem weightedForcedRun_weight_bound [Fintype Value] [Nonempty Value] {Result : Type}
    (environment : Environment auxSpec Coordinate Value Memory) (budget slot : Nat) (hslot : slot ≤ budget)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory)
    (result : Result × State Coordinate Value Memory × ENNReal)
    (hr : WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1) result ≠ 0) :
    forceWeight slot result.2 ≤ ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ := by
  let valid (state : State Coordinate Value Memory × ENNReal) : Prop :=
    Invariant (Fintype.card Value) state.1 ∧ (∀ coordinate, (state.1.allowed coordinate).Nonempty) ∧
      state.2 ≤ 1 ∧ (slot < state.1.probes → state.2 ≤ ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹)
  have hstep (state : State Coordinate Value Memory × ENNReal) (hs : valid state)
      (input : (World auxSpec Coordinate Value).Domain)
      (middle : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
      (hm : (forcedImpl environment slot input).run state.1 middle ≠ 0) :
      valid (middle.2, state.2 * forceFactor slot state.1 input) := by
    have hlazy : lazyRun environment (liftM ((World auxSpec Coordinate Value).query input)) state.1 middle ≠ 0 := by
      simpa only [lazyRun, runWith, simulateQ_spec_query] using forcedImpl_nonzero environment slot state.1 input middle hm
    exact ⟨lazyRun_invariant environment (Fintype.card Value) _ state.1 hs.1 middle hlazy,
      lazyRun_nonempty environment _ state.1 hs.2.1 middle hlazy,
      forceFactor_weight_bound environment (Fintype.card Value) budget slot hslot state.1 state.2 hs.1 hs.2.1
        hs.2.2.1 hs.2.2.2 input middle hm⟩
  have hinitial : valid (initialState memory, 1) :=
    ⟨initialState_invariant memory, fun _ => Finset.univ_nonempty, le_rfl, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  have h := WeightedQuery.run_preserves (forcedImpl environment slot) (forceFactor slot) valid hstep
    computation (initialState memory, 1) hinitial result hr
  rw [forceWeight]
  split
  · exact h.2.2.2 ‹_›
  · exact bot_le
theorem hitRun_payoff_le_forced [Fintype Value] [Nonempty Value] {Result : Type}
    (environment : Environment auxSpec Coordinate Value Memory) (budget slot : Nat) (hslot : slot ≤ budget)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result) ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        (∑' result, Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result) := by
  rw [hitRun_weighted_forced]
  have hforget := congrArg (fun law : SPMF (Result × State Coordinate Value Memory) =>
    ∑' result, Pr[= result | law] * payoff result)
    (WeightedQuery.run_forget (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1))
  rw [tsum_probOutput_map_mul] at hforget
  rw [← show (∑' result, Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot)
      computation (initialState memory, 1)] * payoff (result.1, result.2.1)) =
      (∑' result, Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result) from hforget,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : WeightedQuery.run (forcedImpl environment slot) (forceFactor slot) computation (initialState memory, 1) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, mul_zero, le_refl]
  · calc
      _ ≤ Pr[= result | WeightedQuery.run (forcedImpl environment slot) (forceFactor slot)
          computation (initialState memory, 1)] *
          (((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ * payoff (result.1, result.2.1)) :=
        mul_le_mul' le_rfl (mul_le_mul' (weightedForcedRun_weight_bound environment budget slot hslot computation memory result hz) le_rfl)
      _ = _ := by ring
end SphincsSecurity.Concrete.SecretGuessObservation
end

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
theorem lazyRun_probes_mono {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (hr : lazyRun environment computation state result ≠ 0) :
    state.probes ≤ result.2.probes := by
  apply lazyRun_preserves environment (fun next => state.probes ≤ next.probes) _ computation state le_rfl result hr
  intro middle hm input next hn
  rw [lazyImpl_probes environment middle input next hn]
  exact hm.trans (Nat.le_add_right _ _)
theorem hitImpl_eq_lazy (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (state : State Coordinate Value Memory) (hne : state.probes ≠ slot) (input : (World auxSpec Coordinate Value).Domain) :
    (hitImpl environment slot input).run state = (lazyImpl environment input).run state := by
  cases input with
  | inl input => rfl
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [hitImpl, lazyImpl, StateT.run_mk, hitTrial, if_neg hne]
      | inr coordinate => rfl
theorem hitImplRun_after {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) : runWith (hitImpl environment slot) computation state = lazyRun environment computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [lazyRun, runWith_pure]
  | query_bind input next ih =>
      rw [runWith_query_bind, lazyRun, runWith_query_bind, hitImpl_eq_lazy environment slot state (Nat.ne_of_gt hslot)]
      apply RetainedObservation.bind_congr
      intro middle hm
      have hp := lazyImpl_probes environment state input middle hm
      apply ih middle.1 middle.2
      rw [hp]
      exact hslot.trans_le (Nat.le_add_right _ _)
theorem hitRun_apply {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) : hitRun environment slot computation state result =
      if slot < result.2.probes then runWith (hitImpl environment slot) computation state result else 0 := by
  rw [hitRun, SPMF.bind_apply_eq_tsum, tsum_eq_single result]
  · split <;> simp only [SPMF.pure_apply_self, SPMF.failure_apply, mul_one, mul_zero]
  · intro other hother
    split <;> simp only [SPMF.pure_apply, if_neg (Ne.symm hother), SPMF.failure_apply, mul_zero]
theorem hitRun_after {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hslot : slot < state.probes) : hitRun environment slot computation state = lazyRun environment computation state := by
  apply SPMF.ext
  intro result
  rw [hitRun_apply, hitImplRun_after environment slot computation state hslot]
  by_cases hp : slot < result.2.probes
  · exact if_pos hp
  · rw [if_neg hp]
    symm
    by_contra hr
    exact hp (hslot.trans_le (lazyRun_probes_mono environment computation state result hr))
theorem hitRun_query_bind {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    hitRun environment slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((hitImpl environment slot input).run state >>= fun middle => hitRun environment slot (next middle.1) middle.2) := by
  simp only [hitRun, runWith_query_bind, bind_assoc]
theorem hitRun_probe_at {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    hitRun environment state.probes
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (trial state.allowed coordinate candidate >>= fun hit =>
        if hit = true ∧ coordinate ∉ state.retired then lazyRun environment (next hit) (afterTrial environment state coordinate candidate hit)
        else failure) := by
  rw [hitRun_query_bind]
  simp only [hitImpl, StateT.run_mk, bind_map_left, hitTrial, ite_true, bind_assoc]
  apply congrArg (trial state.allowed coordinate candidate >>= ·)
  funext hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · rw [if_pos hh, pure_bind, hitRun_after environment state.probes _ _ (Nat.lt_succ_self _)]
    rw [if_pos hh]
  · simp only [if_neg hh, failure_bind]
theorem hitRun_probe_other {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (coordinate : Coordinate) (candidate : Value)
    (next : Bool → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hne : state.probes ≠ slot) :
    hitRun environment slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state =
      (trial state.allowed coordinate candidate >>= fun hit => hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit)) := by
  rw [hitRun_query_bind, hitImpl_eq_lazy environment slot state hne]
  simp only [lazyImpl, StateT.run_mk, bind_map_left]
  rfl
end SphincsSecurity.Concrete.SecretGuessObservation
end

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
private theorem sum_bind_apply {Index First Result : Type} (indices : Finset Index) (law : SPMF First)
    (next : Index → First → SPMF Result) (result : Result) :
    (∑ index ∈ indices, (law >>= next index) result) =
      ∑' first, law first * ∑ index ∈ indices, next index first result := by
  simp only [SPMF.bind_apply_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [Finset.mul_sum]
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
theorem hitImpl_no_probe (environment : Environment auxSpec Coordinate Value Memory) (slot : Nat)
    (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0) :
    hitImpl environment slot input = lazyImpl environment input := by
  cases input with
  | inl input => rfl
  | inr input =>
      cases input with
      | inl probe => cases hn
      | inr coordinate => rfl
theorem lazyImpl_no_probe_guesses (environment : Environment auxSpec Coordinate Value Memory)
    (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (state : State Coordinate Value Memory) (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (lazyImpl environment input).run state result ≠ 0) : result.2.guesses = state.guesses := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      rfl
  | inr input =>
      cases input with
      | inl probe => cases hn
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          rfl
theorem hitRun_sum_no_probe {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (slots : Finset Nat) (input : (World auxSpec Coordinate Value).Domain) (hn : probeStep input = 0)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) :
    (∑ slot ∈ slots, hitRun environment slot (liftM ((World auxSpec Coordinate Value).query input) >>= next) state result) =
      ∑' middle, (lazyImpl environment input).run state middle *
        ∑ slot ∈ slots, hitRun environment slot (next middle.1) middle.2 result := by
  simp_rw [hitRun_query_bind, hitImpl_no_probe environment _ input hn]
  exact sum_bind_apply slots _ _ result
theorem hitRun_sum_probe {Result : Type} (environment : Environment auxSpec Coordinate Value Memory) (budget : Nat)
    (coordinate : Coordinate) (candidate : Value) (next : Bool → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (result : Result × State Coordinate Value Memory) (hbudget : state.probes < budget) :
    (∑ slot ∈ Finset.Ico state.probes budget, hitRun environment slot
      (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, trial state.allowed coordinate candidate hit *
        ((if hit = true ∧ coordinate ∉ state.retired then lazyRun environment (next hit) (afterTrial environment state coordinate candidate hit) result else 0) +
          ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
            hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit) result) := by
  rw [Finset.sum_eq_sum_Ico_succ_bot hbudget, hitRun_probe_at, SPMF.bind_apply_eq_tsum]
  have htail :
      (∑ slot ∈ Finset.Ico (state.probes + 1) budget, hitRun environment slot
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result) =
      ∑' hit, trial state.allowed coordinate candidate hit *
        ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit) result := by
    calc
      _ = ∑ slot ∈ Finset.Ico (state.probes + 1) budget,
          (trial state.allowed coordinate candidate >>= fun hit =>
            hitRun environment slot (next hit) (afterTrial environment state coordinate candidate hit)) result := by
        apply Finset.sum_congr rfl
        intro slot hslot
        rw [hitRun_probe_other environment slot coordinate candidate next state (by
          have h := (Finset.mem_Ico.mp hslot).1
          omega)]
      _ = _ := sum_bind_apply _ _ _ result
  rw [htail, ← ENNReal.tsum_add]
  apply tsum_congr
  intro hit
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · simp only [if_pos hh, mul_add]
  · simp only [if_neg hh, SPMF.failure_apply, mul_zero, zero_add]
theorem lazyRun_new_guesses_le_sum {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (result : Result × State Coordinate Value Memory) (budget : Nat) (hbudget : result.2.probes ≤ budget)
    (hnew : result.2.guesses ≠ state.guesses) :
    lazyRun environment computation state result ≤
      ∑ slot ∈ Finset.Ico state.probes budget, hitRun environment slot computation state result := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      by_cases he : result = (value, state)
      · subst result
        exact False.elim (hnew rfl)
      · simp only [lazyRun, runWith_pure, SPMF.pure_apply, if_neg he]
        exact bot_le
  | query_bind input next ih =>
      by_cases hn : probeStep input = 0
      · rw [hitRun_sum_no_probe environment _ input hn, lazyRun, runWith_query_bind, SPMF.bind_apply_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro middle
        by_cases hm : (lazyImpl environment input).run state middle = 0
        · simp only [hm, zero_mul, le_refl]
        · have hp := lazyImpl_probes environment state input middle hm
          rw [hn, Nat.add_zero] at hp
          have hg := lazyImpl_no_probe_guesses environment input hn state middle hm
          have h := ih middle.1 middle.2 (hg ▸ hnew)
          rw [hp] at h
          exact mul_le_mul' le_rfl h
      · cases input with
        | inl input => exact False.elim (hn rfl)
        | inr input =>
            cases input with
            | inr coordinate => exact False.elim (hn rfl)
            | inl probe =>
                rcases probe with ⟨coordinate, candidate⟩
                by_cases hz : lazyRun environment
                    (liftM ((World auxSpec Coordinate Value).query (.inr (.inl (coordinate, candidate)))) >>= next) state result = 0
                · rw [hz]
                  exact bot_le
                have hpositive := hz
                rw [lazyRun, runWith_query_bind] at hpositive
                simp only [lazyImpl, StateT.run_mk, bind_map_left, RetainedObservation.bind_nonzero] at hpositive
                obtain ⟨hit, _, htail⟩ := hpositive
                have hp := lazyRun_probes_mono environment (next hit) (afterTrial environment state coordinate candidate hit) result htail
                have hroom : state.probes < budget := by
                  change state.probes + 1 ≤ result.2.probes at hp
                  omega
                rw [hitRun_sum_probe environment budget coordinate candidate next state result hroom]
                simp only [lazyRun, runWith_query_bind, lazyImpl, StateT.run_mk, bind_map_left, SPMF.bind_apply_eq_tsum]
                apply ENNReal.tsum_le_tsum
                intro hit
                apply mul_le_mul' le_rfl
                by_cases hh : hit = true ∧ coordinate ∉ state.retired
                · rw [if_pos hh]
                  exact le_add_right le_rfl
                · rw [if_neg hh, zero_add]
                  apply ih hit (afterTrial environment state coordinate candidate hit)
                  simpa only [afterTrial, if_neg hh] using hnew
end SphincsSecurity.Concrete.SecretGuessObservation
end

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value] [Nonempty Value]
omit [Nonempty Value] in
theorem lazyRun_guess_payoff_le_sum {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty then payoff result else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hz : lazyRun environment computation (initialState memory) result = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul]
    exact bot_le
  by_cases hg : result.2.guesses.Nonempty
  · rw [if_pos hg]
    have h := lazyRun_new_guesses_le_sum environment computation (initialState memory) result budget (hbudget result hz)
      (show result.2.guesses ≠ (initialState memory : State Coordinate Value Memory).guesses from hg.ne_empty)
    have hp := mul_le_mul' h (le_rfl : payoff result ≤ payoff result)
    simpa only [initialState, ← Finset.range_eq_Ico, Finset.sum_mul, SPMF.probOutput_eq_apply] using hp
  · simp only [if_neg hg, mul_zero]
    exact bot_le
theorem lazyRun_guess_payoff_le_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (payoff : Result × State Coordinate Value Memory → ENNReal) :
    (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty then payoff result else 0)) ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  apply (lazyRun_guess_payoff_le_sum environment computation memory budget hbudget payoff).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro slot hslot
  exact hitRun_payoff_le_forced environment budget slot (Finset.mem_range.mp hslot).le computation memory payoff
theorem lazyRun_event_le_forced {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget)
    (event : Result × State Coordinate Value Memory → Prop) (payoff : Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ 1 ≤ payoff result) :
    Pr[event | lazyRun environment computation (initialState memory)] ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if result.2.guesses.Nonempty then payoff result else 0) ?_).trans
      (lazyRun_guess_payoff_le_forced environment computation memory budget hbudget payoff)
  intro result hr he
  have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
  simpa only [if_pos h.1] using h.2
end SphincsSecurity.Concrete.SecretGuessObservation
end

section

namespace SphincsSecurity.Concrete.SecretGuessObservation
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable def pairValue (rate : ENNReal) (remaining : Nat) : Nat → ENNReal
  | 0 => remaining.choose 2 * rate ^ 2
  | 1 => remaining * rate
  | _ + 2 => 1
theorem pairValue_mono (rate : ENNReal) (hits : Nat) {first second : Nat} (h : first ≤ second) :
    pairValue rate first hits ≤ pairValue rate second hits := by
  cases hits with
  | zero => exact mul_le_mul' (by exact_mod_cast Nat.choose_le_choose 2 h) le_rfl
  | succ hits =>
      cases hits with
      | zero => exact mul_le_mul' (by exact_mod_cast h) le_rfl
      | succ hits => exact le_rfl
private theorem expectation_const_le {Result : Type} (law : SPMF Result) (value : ENNReal) :
    (∑' result, Pr[= result | law] * value) ≤ value := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem pairValue_trial (law : SPMF Bool) (rate : ENNReal) (hrate : law true ≤ rate) (remaining hits : Nat) :
    (∑' hit, Pr[= hit | law] * pairValue rate remaining (hits + if hit then 1 else 0)) ≤
      pairValue rate (remaining + 1) hits := by
  have hfalse : law false ≤ 1 := by
    simpa only [SPMF.probOutput_eq_apply] using (show Pr[= false | law] ≤ 1 from probOutput_le_one)
  cases hits with
  | zero =>
      simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.zero_add,
        pairValue, SPMF.probOutput_eq_apply]
      calc
        _ ≤ rate * (remaining * rate) + ((remaining.choose 2 : Nat) : ENNReal) * rate ^ 2 :=
          add_le_add (mul_le_mul' hrate le_rfl) (mul_le_of_le_one_left' hfalse)
        _ = _ := by
          rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
          ring
  | succ hits =>
      cases hits with
      | zero =>
          simp only [tsum_fintype, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true, Nat.add_zero,
            pairValue, SPMF.probOutput_eq_apply, mul_one]
          calc
            _ ≤ rate + (remaining : ENNReal) * rate := add_le_add hrate (mul_le_of_le_one_left' hfalse)
            _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring
      | succ hits =>
          calc
            _ = ∑' hit, Pr[= hit | law] * 1 := by
              apply tsum_congr
              intro hit
              cases hit <;> rfl
            _ ≤ 1 := expectation_const_le law 1
variable {Coordinate Value Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]
noncomputable def pairPotential (size budget : Nat) (state : State Coordinate Value Memory) : ENNReal :=
  if state.probes ≤ budget then pairValue ((size - budget : Nat) : ENNReal)⁻¹ (budget - state.probes) state.guesses.card else 0
theorem pairPotential_afterTrial (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (coordinate : Coordinate) (candidate : Value) :
    (∑' hit, Pr[= hit | trial state.allowed coordinate candidate] *
      pairPotential size budget (afterTrial environment state coordinate candidate hit)) ≤ pairPotential size budget state := by
  classical
  by_cases hroom : state.probes < budget
  · have hwithin : state.probes ≤ budget := Nat.le_of_lt hroom
    have hafter : state.probes + 1 ≤ budget := hroom
    have hremaining : budget - state.probes = (budget - (state.probes + 1)) + 1 := by omega
    have hp (hit : Bool) : (afterTrial environment state coordinate candidate hit).probes = state.probes + 1 := rfl
    simp only [pairPotential, hp, afterTrial_guesses_card environment state hs.2, if_pos hafter, if_pos hwithin]
    by_cases hc : coordinate ∈ state.retired
    · simp only [hc, not_true_eq_false, and_false, if_false, Nat.add_zero]
      exact (expectation_const_le _ _).trans (pairValue_mono _ _ (Nat.sub_le_sub_left (by omega) _))
    · simp only [hc, not_false_eq_true, and_true]
      rw [hremaining]
      exact pairValue_trial _ _ (trial_true_le size budget state hs ha hwithin coordinate hc candidate) _ _
  · have hafter : ¬state.probes + 1 ≤ budget := by omega
    simp only [pairPotential, afterTrial, if_neg hafter, mul_zero, tsum_zero]
    exact bot_le
theorem lazyImpl_pairPotential (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (input : (World auxSpec Coordinate Value).Domain) :
    (∑' result, Pr[= result | (lazyImpl environment input).run state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
      exact expectation_const_le _ _
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact pairPotential_afterTrial environment size budget state hs ha coordinate candidate
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, tsum_probOutput_map_mul]
          exact expectation_const_le _ _
theorem lazyRun_pairPotential {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (size budget : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Invariant size state)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (∑' result, Pr[= result | lazyRun environment computation state] * pairPotential size budget result.2) ≤
      pairPotential size budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [lazyRun, runWith_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [lazyRun, runWith_query_bind, tsum_probOutput_bind_mul]
      apply le_trans _ (lazyImpl_pairPotential environment size budget state hs ha input)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : (lazyImpl environment input).run state middle = 0
      · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
      · have hrun : lazyRun environment (liftM ((World auxSpec Coordinate Value).query input)) state middle ≠ 0 := by
          simpa only [lazyRun, runWith, simulateQ_spec_query] using hm
        exact mul_le_mul' le_rfl (ih middle.1 middle.2
          (lazyRun_invariant environment size _ state hs middle hrun) (lazyRun_nonempty environment _ state ha middle hrun))
omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem pairPotential_two (size budget : Nat) (state : State Coordinate Value Memory)
    (hbudget : state.probes ≤ budget) (hhits : 2 ≤ state.guesses.card) : 1 ≤ pairPotential size budget state := by
  rw [pairPotential, if_pos hbudget]
  obtain ⟨hits, heq⟩ := Nat.exists_eq_add_of_le hhits
  rw [heq, Nat.add_comm]
  exact le_rfl
theorem lazyRun_two_guesses [Fintype Value] [Nonempty Value] {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (hbudget : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → result.2.probes ≤ budget) :
    Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun environment computation (initialState memory)] ≤
      (budget.choose 2 : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotential (Fintype.card Value) budget result.2) ?_).trans
      (lazyRun_pairPotential environment (Fintype.card Value) budget computation (initialState memory)
        (initialState_invariant memory) (fun _ => Finset.univ_nonempty))
  intro result hr htwo
  apply pairPotential_two _ _ result.2 _ htwo
  exact hbudget result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr)
end SphincsSecurity.Concrete.SecretGuessObservation
end

section





namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Generic
open SecretGuessObservation
variable {Coordinate Value Memory AuxIndex Result : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] [Fintype Value]
theorem lazyRun_pair_le [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat) :
    Pr[fun result => 2 ≤ result.2.guesses.card ∧ result.2.probes ≤ budget |
      lazyRun environment computation (initialState memory)] ≤
      (budget.choose 2 : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ ^ 2 := by
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => pairPotential (Fintype.card Value) budget result.2) ?_).trans
  · refine (lazyRun_pairPotential environment (Fintype.card Value) budget computation (initialState memory)
      (initialState_invariant memory) (fun _ => Finset.univ_nonempty)).trans (le_of_eq ?_)
    simp [pairPotential, initialState, pairValue]
  · intro result _ h
    exact pairPotential_two _ _ result.2 h.2 h.1
theorem lazyRun_event_le_forced_of [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat)
    (event : Result × State Coordinate Value Memory → Prop) (payoff : Result × State Coordinate Value Memory → ENNReal)
    (hevent : ∀ result, lazyRun environment computation (initialState memory) result ≠ 0 → event result →
      result.2.guesses.Nonempty ∧ result.2.probes ≤ budget ∧ 1 ≤ payoff result) :
    Pr[event | lazyRun environment computation (initialState memory)] ≤
      ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, ∑' result,
          Pr[= result | forcedRun environment slot computation (initialState memory)] * payoff result := by
  have hstep : (∑' result, Pr[= result | lazyRun environment computation (initialState memory)] *
      (if result.2.guesses.Nonempty ∧ result.2.probes ≤ budget then payoff result else 0)) ≤
      ∑ slot ∈ Finset.range budget, ∑' result,
        Pr[= result | hitRun environment slot computation (initialState memory)] * payoff result := by
    rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    apply ENNReal.tsum_le_tsum
    intro result
    by_cases hz : lazyRun environment computation (initialState memory) result = 0
    · simp only [SPMF.probOutput_eq_apply, hz, zero_mul]
      exact bot_le
    by_cases hg : result.2.guesses.Nonempty ∧ result.2.probes ≤ budget
    · rw [if_pos hg]
      have h := lazyRun_new_guesses_le_sum environment computation (initialState memory) result budget hg.2
        (show result.2.guesses ≠ (initialState memory : State Coordinate Value Memory).guesses from hg.1.ne_empty)
      have hp := mul_le_mul' h (le_rfl : payoff result ≤ payoff result)
      simpa only [initialState, ← Finset.range_eq_Ico, Finset.sum_mul, SPMF.probOutput_eq_apply] using hp
    · simp only [if_neg hg, mul_zero]
      exact bot_le
  apply (probEvent_le_tsum_probOutput_mul_cost_of_mem_support _ _
    (fun result => if result.2.guesses.Nonempty ∧ result.2.probes ≤ budget then payoff result else 0) ?_).trans
  · apply hstep.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro slot hslot
    exact hitRun_payoff_le_forced environment budget slot (Finset.mem_range.mp hslot).le computation memory payoff
  · intro result hr he
    have h := hevent result (by simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr) he
    rw [if_pos ⟨h.1, h.2.1⟩]
    exact h.2.2
theorem lazyRun_guess_le [Nonempty Value] (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (memory : Memory) (budget : Nat) :
    Pr[fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ budget |
      lazyRun environment computation (initialState memory)] ≤
      (budget : ENNReal) * ((Fintype.card Value - budget : Nat) : ENNReal)⁻¹ := by
  refine (lazyRun_event_le_forced_of environment computation memory budget
    (fun result => result.2.guesses.Nonempty ∧ result.2.probes ≤ budget) (fun _ => 1)
    (fun _ _ h => ⟨h.1, h.2, le_rfl⟩)).trans ?_
  rw [mul_comm]
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ ∑ _slot ∈ Finset.range budget, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro slot _
      simpa only [mul_one] using
        (tsum_probOutput_le_one (mx := forcedRun environment slot computation (initialState memory)))
    _ = budget := by simp
end Generic
abbrev FtsCoord := Fin (2^31) × Fin 7 × Fin 2048
def toLeafPos (f : FtsCoord) : CanonGraph.FtsLeafPos := ⟨f.1, f.2.1, f.2.2⟩
def ofLeafPos (p : CanonGraph.FtsLeafPos) : FtsCoord := (p.index, p.coord, p.leaf)
@[simp] theorem ofLeafPos_toLeafPos (f : FtsCoord) : ofLeafPos (toLeafPos f) = f := rfl
@[simp] theorem toLeafPos_ofLeafPos (p : CanonGraph.FtsLeafPos) : toLeafPos (ofLeafPos p) = p := rfl
abbrev WSpec := SecretGuessObservation.World unifSpec FtsCoord Digest
abbrev WState := SecretGuessObservation.State FtsCoord Digest PUnit
noncomputable def coinImpl : QueryImpl unifSpec ProbComp := fun n => liftM (unifSpec.query n)
noncomputable def env : SecretGuessObservation.Environment unifSpec FtsCoord Digest PUnit :=
  SecretGuessObservation.environment coinImpl
def init : WState := SecretGuessObservation.initialState PUnit.unit
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
def probeInput (f : FtsCoord) (c : Digest) : HashInput :=
  pad64 (ftsLeafInputP f.1.val f.2.1.val f.2.2.val 0 c 0)
theorem probeInput_eq (f : FtsCoord) (c : Digest) :
    probeInput f c = block4 0 (header 9 f.2.1.val f.1.val 0 f.2.2.val) c 0 := by
  unfold probeInput ftsLeafInputP
  exact pad64_block4 _ _ _ _
@[simp] theorem probeInput_length (f : FtsCoord) (c : Digest) : (probeInput f c).length = 64 := by
  rw [probeInput_eq]; exact block4_length _ _ _ _
theorem probeInput_injective {f f' : FtsCoord} {c c' : Digest} (h : probeInput f c = probeInput f' c') :
    f = f' ∧ c = c' := by
  rw [probeInput_eq, probeInput_eq] at h
  obtain ⟨-, hh, hc, -⟩ := block4_injective h
  have hf1 := f.1.isLt
  have hf2 := f.2.1.isLt
  have hf3 := f.2.2.isLt
  have hg1 := f'.1.isLt
  have hg2 := f'.2.1.isLt
  have hg3 := f'.2.2.isLt
  have := header_injective (by decide : 9 < 256) (by omega : f.2.1.val < 256) (by omega : f.1.val < 2 ^ 40)
    (by decide : 0 < 2 ^ 32) (by omega : f.2.2.val < 2 ^ 32) (by decide : 9 < 256) (by omega : f'.2.1.val < 256)
    (by omega : f'.1.val < 2 ^ 40) (by decide : 0 < 2 ^ 32) (by omega : f'.2.2.val < 2 ^ 32) hh
  exact ⟨Prod.ext (Fin.ext this.2.2.1) (Prod.ext (Fin.ext this.2.1) (Fin.ext this.2.2.2.2)), hc⟩
noncomputable def decodeProbe (x : HashInput) : Option (FtsCoord × Digest) :=
  haveI := Classical.propDecidable (∃ p : FtsCoord × Digest, x = probeInput p.1 p.2)
  if h : ∃ p : FtsCoord × Digest, x = probeInput p.1 p.2 then some (Classical.choose h) else none
theorem decodeProbe_probeInput (f : FtsCoord) (c : Digest) : decodeProbe (probeInput f c) = some (f, c) := by
  have h : ∃ p : FtsCoord × Digest, probeInput f c = probeInput p.1 p.2 := ⟨(f, c), rfl⟩
  rw [decodeProbe, dif_pos h]
  obtain ⟨h1, h2⟩ := probeInput_injective (Classical.choose_spec h).symm
  exact congrArg some (Prod.ext h1 h2)
theorem eq_of_decodeProbe {x : HashInput} {p : FtsCoord × Digest} (h : decodeProbe x = some p) :
    x = probeInput p.1 p.2 := by
  unfold decodeProbe at h
  split at h
  · rename_i hx
    cases h
    exact Classical.choose_spec hx
  · cases h
theorem decodeProbe_eq_none {x : HashInput} : decodeProbe x = none ↔ ∀ f c, x ≠ probeInput f c := by
  constructor
  · intro h f c hx
    rw [hx, decodeProbe_probeInput] at h
    cases h
  · intro h
    rw [decodeProbe, dif_neg]
    rintro ⟨p, hp⟩
    exact h p.1 p.2 hp
theorem hdrBlock_probeInput (f : FtsCoord) (c : Digest) :
    Extract.hdrBlock (probeInput f c) = bytesLE 16 (header 9 f.2.1.val f.1.val 0 f.2.2.val) := by
  rw [probeInput_eq]; exact FtsExtract.hdrBlock_block4 _ _ _ _
theorem decodeProbe_of_hdr {x : HashInput} {t l tr p ix : Nat} (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr p ix))
    (ht : t % 256 ≠ 9) : decodeProbe x = none := by
  rw [decodeProbe_eq_none]
  intro f c he
  rw [he, hdrBlock_probeInput] at hx
  have hh := bytesLE_injective hx
  apply ht
  have h1 := congrArg (fun v : BitVec 128 => v.toNat % 2 ^ 16 / 2 ^ 8) hh
  have hw := nodeWord_lt t p ix
  have hw9 := nodeWord_lt 9 0 f.2.2.val
  simp only [header, BitVec.toNat_ofNat] at h1
  generalize nodeWord t p ix = g at *
  generalize nodeWord 9 0 f.2.2.val = g9 at *
  split_ifs at h1 <;> omega
def secretAt (answers : Answers) (f : FtsCoord) : Digest := CanonGraph.ftsSecretOf answers (toLeafPos f)
def secretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
section Rows
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          secretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = secretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, secretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, secretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl
theorem buildFts_secret (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0 = secretNat answers index coord leaf := by
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf
theorem buildFts_secrets_length (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (buildFts index coord)).2.length = 2048 := by
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).1
end Rows
theorem secretAt_eq (answers : Answers) (f : FtsCoord) :
    secretAt answers f = secretNat answers f.1.val f.2.1.val f.2.2.val := rfl
theorem honestInput_ftsLeaf (answers : Answers) (f : FtsCoord) :
    Extract.honestInput answers (.ftsLeaf f.1.val f.2.1.val f.2.2.val) = probeInput f (secretAt answers f) := by
  simp only [Extract.honestInput]
  have h := buildFts_secret answers f.1.val f.2.1.val f.2.2.val f.2.2.isLt
  unfold Extract.ftsSecret
  rw [h]
  rfl
def leafIndex (bucket leaf : Nat) : Fin 2048 := ⟨(bucket * 128 + leaf) % 2048, Nat.mod_lt _ (by decide)⟩
def outputIndex (output : HashOutput) : Fin (2^31) := ⟨output.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩
def openedPositions (output : HashOutput) : List FtsCoord :=
  (List.finRange 7).flatMap fun c =>
    ((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
      (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)
noncomputable def signedOutput (answers : Answers) (message : Message) (signature : Signature) :
    Option HashOutput :=
  (evalWithAnswerFn answers (digestSearch signature.rho message 0 attemptLimit)).map Prod.snd
def Disclosed (answers : Answers) (log : QueryLog Requests) (f : FtsCoord) : Prop :=
  ∃ entry ∈ log, ∃ signature output, entry.2 = some signature ∧
    signedOutput answers entry.1.message signature = some output ∧ f ∈ openedPositions output
def GuessedIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) (f : FtsCoord) : Prop :=
  ¬Disclosed answers log f ∧ ∃ answer, (probeInput f (secretAt answers f), answer) ∈ entries
def OneGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f, GuessedIn answers log entries f
def PairGuessIn (answers : Answers) (log : QueryLog Requests) (entries : List Wots.Entry) : Prop :=
  ∃ f g, f ≠ g ∧ GuessedIn answers log entries f ∧ GuessedIn answers log entries g
noncomputable def pairTerm (q : Nat) : ENNReal := (q.choose 2 : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ ^ 2
noncomputable def guessTerm (q : Nat) : ENNReal := (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹
section World
variable (U : Finset HashInput) (hU : CanonGraph.canonInputs ⊆ U)
structure Omega where
  seeds : ChainGraph.Seeds
  other : CanonGraph.OtherHalves
  labels : CanonGraph.Labels
  residual : U → HashOutput
variable {U}
def Omega.secrets (ω : Omega U) (fts : FtsCoord → Digest) : CanonGraph.Secrets
  | .inl a => ω.seeds a
  | .inr p => fts (ofLeafPos p)
noncomputable def Omega.answers (ω : Omega U) (fts : FtsCoord → Digest) : Answers :=
  CanonGraph.eagerAnswers (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)) U
    (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual)
noncomputable def hashW (ω : Omega U) (x : HashInput) : OracleComp WSpec HashOutput :=
  match decodeProbe x with
  | none => pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))
  | some p => do
      let hit ← (liftM (WSpec.query (.inr (.inl p))) : OracleComp WSpec Bool)
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else
        SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual x)
noncomputable def openedFor (ω : Omega U) (published : T3.Cache) (request : Request) : List FtsCoord :=
  match evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (FullGame.authenticatedSign published request) with
  | none => []
  | some signature =>
      match signedOutput (Omega.answers hU ω (fun _ => 0)) request.message signature with
      | none => []
      | some output => openedPositions output
def overwrite (positions : List FtsCoord) (values : List Digest) (f : FtsCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = f))).elim 0 Prod.snd
noncomputable def signW (ω : Omega U) (published : T3.Cache) (request : Request) :
    OracleComp WSpec (Option Signature) := do
  let positions := openedFor hU ω published request
  let values ← positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)
  pure (evalWithAnswerFn (Omega.answers hU ω (overwrite positions values))
    (FullGame.authenticatedSign published request))
noncomputable def interactionW (ω : Omega U) (published : T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp WSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signW hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programW (ω : Omega U) {β : Type} : M β → OracleComp WSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldGame (ω : Omega U) (adversary : AdversaryP) :
    OracleComp WSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen
  let interaction ← interactionW hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programW hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
end World
noncomputable def interactionT (T : Answers) (published : T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → ProbComp (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let rest ← next (T (.inl (.inr x)))
          pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)
      | .inr request => do
          let rest ← next (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ :: rest.2.1,
            rest.2.2))
noncomputable def pairRun (T : Answers) (adversary : AdversaryP) :
    ProbComp (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn T keygen
  let interaction ← interactionT T generated.2 (adversary generated.1 generated.2)
  let verdict := GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1)
  pure (evalWithAnswerFn T verdict, interaction.2.1,
    interaction.2.2 ++ Wots.entriesOf T (SourceReplay.queried T verdict))
end SigGolfCandidate.T3.Security.BPair
end
