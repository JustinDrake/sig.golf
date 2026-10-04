import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedObservation
import SigGolfCandidate.SphincsSecurity.Proof.Forced.SecretGuessForced

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
