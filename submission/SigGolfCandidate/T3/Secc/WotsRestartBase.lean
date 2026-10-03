import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapErasure
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPause
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCheckpoint
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPauseInvariant

section

namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (selected : Index → Prop) [DecidablePred selected]
theorem run_state_eq_counted (impl : QueryImpl spec (StateT Memory PMF))
    (computation : OracleComp spec Result) (budget : Nat) (memory : Memory) :
    ((simulateQ impl (run selected computation budget)).run memory).map Prod.fst =
      ((simulateQ impl (counted selected computation)).run memory).map (fun result => finish budget result.1) := by
  induction computation using OracleComp.inductionOn generalizing budget memory with
  | pure result =>
      simp only [run_pure, counted_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.map, PMF.pure_bind, Function.comp_def, finish, Nat.zero_le, if_true, Nat.sub_zero]
  | query_bind input next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
              Function.comp_def, finish, if_pos hs, Nat.add_comm 1, Nat.add_one_le_iff, Nat.not_lt_zero, if_false, PMF.bind_const]
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
            apply congrArg ((impl input).run memory).bind
            funext middle
            rw [ih middle.1 budget middle.2]
            simp only [PMF.map, PMF.pure_bind, Function.comp_def, finish, if_pos hs,
              Nat.add_comm 1, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
        apply congrArg ((impl input).run memory).bind
        funext middle
        rw [ih middle.1 budget middle.2]
        simp only [PMF.map, PMF.pure_bind, Function.comp_def, finish, Nat.zero_add]
theorem counted_state_le_of_cap_valid (impl : QueryImpl spec (StateT Memory PMF))
    (computation : OracleComp spec Result) (budget : Nat) (memory : Memory)
    (hvalid : ∀ result ∈ ((simulateQ impl (run selected computation budget)).run memory).support, result.1 ≠ none)
    (result : (Result × Nat) × Memory)
    (hresult : result ∈ ((simulateQ impl (counted selected computation)).run memory).support) : result.1.2 ≤ budget := by
  by_contra hlarge
  have hmap : finish budget result.1 ∈
      (((simulateQ impl (counted selected computation)).run memory).map (fun result => finish budget result.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [← run_state_eq_counted selected impl computation budget memory, PMF.mem_support_map_iff] at hmap
  obtain ⟨capped, hcapped, heq⟩ := hmap
  exact hvalid capped hcapped (heq.trans (if_neg hlarge))
end SphincsSecurity.QueryCap
end

section



namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Memory : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)
include hcharge hreal hsmall
theorem lazyRun_counted_le_of_real (endpoint : State) (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support) :
    result.1.2 ≤ budget := by
  apply QueryCap.counted_state_le_of_cap_valid IsPrefixQuery (lazyImpl (auxiliary endpoint)) (computation endpoint) budget
    (fun _ _ => none) _ result hresult
  intro capped hcapped
  have hsource : (endpoint, capped) ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).support := by
    rw [idealRun, PMF.mem_support_bind_iff]
    refine ⟨endpoint, PMF.mem_support_uniformOfFintype endpoint, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨capped, hcapped, rfl⟩
  obtain ⟨finished, hfinished, _⟩ := idealRun_cap_valid auxiliary computation cost budget hcharge hreal hsmall (endpoint, capped) hsource
  change capped.1 = some finished at hfinished
  rw [hfinished]
  exact Option.some_ne_none finished
theorem lazyRun_pause_budget_of_real (endpoint : State) (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : (auxSpec + PrefixSpec n State).Domain) → (auxSpec + PrefixSpec n State).Range input → Memory → Memory)
    (memory : Memory)
    (middle : ((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State))
    (hmiddle : middle ∈ (lazyRun (auxiliary endpoint)
      (QueryCap.counted IsPrefixQuery (QueryPause.run stop step (computation endpoint) memory)) (fun _ _ => none)).support)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery middle.1.1.2) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ budget ∧ queryCount result.2 ≤ budget := by
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support := by
    rw [← QueryPause.counted_resume stop step IsPrefixQuery (computation endpoint) memory]
    simp only [lazyRun, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨middle, hmiddle, result, hresult, rfl⟩
  have htotal := lazyRun_counted_le_of_real auxiliary computation cost budget hcharge hreal hsmall endpoint _ hfull
  have hpast := lazyRun_counted_queryCount_le (auxiliary endpoint) (QueryPause.run stop step (computation endpoint) memory)
    (fun _ _ => none) middle hmiddle
  simp only [queryCount_empty, Nat.zero_add] at hpast
  have hrows := lazyRun_counted_queryCount_le (auxiliary endpoint) middle.1.1.2 middle.2 result hresult
  exact ⟨(Nat.add_le_add_right hpast _).trans htotal, hrows.trans ((Nat.add_le_add_right hpast _).trans htotal)⟩
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem scaled_expectation_le {Result : Type} (law : PMF Result) (factor : ENNReal)
    (left right : Result → ENNReal) (h : ∀ result ∈ law.support, factor * left result ≤ right result) :
    factor * (∑' result, law result * left result) ≤ ∑' result, law result * right result := by
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (h result hr)
  · have hz : law result = 0 := not_not.mp hr
    simp only [hz, zero_mul, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
  (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
  (observed : Fin n → State → Option State)
  (marked : State → Checkpoint × (Fin n → State → Option State) → Prop)
theorem realCheckpointRun_mark_probability :
    Pr[fun result => marked result.1 result.2.1 | realCheckpointRun auxiliary before after observed] =
      Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  have h := congrArg (fun law : PMF (State × (Checkpoint × (Fin n → State → Option State))) =>
    Pr[fun result => marked result.1 result.2 | law]) (realCheckpointRun_before auxiliary before after observed)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realCheckpointRun_contact_charge (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      ∑' result, realCheckpointRun auxiliary before after observed result *
        (((queryCount result.2.1.2 + 2 * result.2.2.1.2 : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
  rw [show Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
      realCheckpointRun auxiliary before after observed] =
      (∑' result, realCheckpointRun auxiliary before after observed result *
        if marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 then 1 else 0) by
          simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realCheckpointRun_density, realCheckpointRun_expectation, ← mul_assoc]
  apply scaled_expectation_le
  intro endpoint _
  apply scaled_expectation_le
  intro middle hmiddle
  by_cases hm : marked endpoint middle
  · simp only [hm, true_and, if_true, mul_one]
    simpa only [mul_assoc] using run_contact_charge_transfer (auxiliary endpoint) (after endpoint middle) middle.2 endpoint
      (hmarked endpoint middle hm) budget (hbudget endpoint middle hmiddle hm)
  · simp only [hm, false_and, if_false, mul_zero, tsum_zero, le_refl]
theorem realCheckpointRun_contact_le_mark (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget)
    (hcost : ∀ result ∈ (realCheckpointRun auxiliary before after observed).support,
      marked result.1 result.2.1 → queryCount result.2.1.2 + result.2.2.1.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      (2 * budget : Nat) * Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  apply (realCheckpointRun_contact_charge auxiliary before after observed marked budget hmarked hbudget).trans
  calc
    _ ≤ ∑' result, realCheckpointRun auxiliary before after observed result *
        (((2 * budget : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (realCheckpointRun auxiliary before after observed).support
      · apply mul_le_mul' le_rfl
        by_cases hm : marked result.1 result.2.1
        · simp only [if_pos hm, mul_one]
          have hc := hcost result hr hm
          exact_mod_cast (show queryCount result.2.1.2 + 2 * result.2.2.1.2 ≤ 2 * budget by omega)
        · simp only [if_neg hm, mul_zero, le_refl]
      · have hz : realCheckpointRun auxiliary before after observed result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by
      rw [expectation_scale, ← realCheckpointRun_mark_probability auxiliary before after observed marked]
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result Output : Type}
omit [Fintype State] [Nonempty State] in
theorem observedRun_bind (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (before >>= after) observed =
      (observedRun auxiliary tables before observed).bind (fun middle => observedRun auxiliary tables (after middle.1) middle.2) := by
  simp only [observedRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
omit [Fintype State] [Nonempty State] in
theorem checkpointObservedRun_project (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : Checkpoint → Result → Output) :
    (checkpointObservedRun auxiliary tables before (fun middle => after middle.1) observed).map
      (fun result => (project result.1.1 result.2.1.1, result.2.2)) =
    observedRun auxiliary tables (do let middle ← before; let result ← after middle; pure (project middle result)) observed := by
  simp only [checkpointObservedRun, PMF.map_bind, PMF.map_comp, Function.comp_def,
    observedRun_bind, bind_pure_comp, observedRun_map]
  apply congrArg (observedRun auxiliary tables before observed).bind
  funext middle
  rw [← observedRun_map auxiliary tables (QueryCap.counted IsPrefixQuery (after middle.1))
    (fun result => project middle.1 result.1) middle.2]
  rw [← Functor.map_map, QueryCap.counted_forget, observedRun_map]
theorem realCheckpointRun_project (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (project : State → Checkpoint → Result → Output) :
    (realCheckpointRun auxiliary before (fun endpoint middle => after endpoint middle.1) observed).map
      (fun result => (result.1, project result.1 result.2.1.1 result.2.2.1.1, result.2.2.2)) =
    realRun auxiliary (fun endpoint => do
      let middle ← before endpoint
      let result ← after endpoint middle
      pure (project endpoint middle result)) observed := by
  simp only [realCheckpointRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg (EndpointPreimageDensity.real (completeTables observed) evaluate).bind
  funext pair
  have h := congrArg (fun law => law.map (fun result => (pair.2, result)))
    (checkpointObservedRun_project (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed (project pair.2))
  simpa only [PMF.map_comp, Function.comp_def] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section





namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
def entryOf : (query : RefWorld.Domain) → RefWorld.Range query → List Entry
  | .inl (.inr input), answer => [(input, (answer : HashOutput))]
  | .inl (.inl _), _ => []
  | .inr _, _ => []
def stepTrace (query : RefWorld.Domain) (answer : RefWorld.Range query) (memory : List Entry) : List Entry :=
  memory ++ entryOf query answer
def refAnswer (T : Answers) : (query : RefWorld.Domain) → RefWorld.Range query
  | .inl query => T (.inl query)
  | .inr _ => ()
theorem traceOf_cons (T : Answers) (query : RefWorld.Domain) (qs : List RefWorld.Domain) :
    traceOf T (query :: qs) = entryOf query (refAnswer T query) ++ traceOf T qs := by
  rcases query with (n | input) | u <;> rfl
theorem entryOf_refImpl (T : Answers) (query : RefWorld.Domain) (answer : RefWorld.Range query)
    (h : answer ∈ support (refImpl T query)) : entryOf query answer = entryOf query (refAnswer T query) := by
  rcases query with (n | input) | u
  · rfl
  · simp only [refImpl, mem_support_pure_iff] at h
    subst h
    rfl
  · rfl
theorem entryOf_length_le (query : RefWorld.Domain) (answer : RefWorld.Range query) :
    (entryOf query answer).length ≤ 1 := by
  rcases query with (n | input) | u <;> simp [entryOf]
variable {β : Type}
noncomputable def pausedFull (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    OracleComp RefWorld (List Entry × (β × List RefWorld.Domain)) := do
  let paused ← SphincsSecurity.QueryPause.run stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory
  let result ← paused.2
  pure (paused.1, result)
theorem pausedFull_snd (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    Prod.snd <$> pausedFull stop G memory = SphincsSecurity.QueryCap.recorded G := by
  unfold pausedFull
  simp only [map_bind, map_pure]
  conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory]
  congr 1
  funext paused
  simp only [bind_pure]
theorem run_map {Index Memory α γ : Type} {spec : OracleSpec Index} (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : spec.Domain) → spec.Range input → Memory → Memory) (f : α → γ)
    (computation : OracleComp spec α) (memory : Memory) :
    SphincsSecurity.QueryPause.run stop step (f <$> computation) memory =
      (fun paused => (paused.1, f <$> paused.2)) <$> SphincsSecurity.QueryPause.run stop step computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value =>
      simp only [map_pure, SphincsSecurity.QueryPause.run_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.QueryPause.run_query_bind, SphincsSecurity.QueryPause.run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, map_pure, map_bind]
      · simp only [if_neg hs, map_bind, ih]
theorem pausedFull_query_bind (stop : List Entry → Prop) (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld β) (memory : List Entry) :
    pausedFull stop (liftM (RefWorld.query input) >>= next) memory =
      if stop memory then
        (fun result => (memory, result)) <$> SphincsSecurity.QueryCap.recorded (liftM (RefWorld.query input) >>= next)
      else liftM (RefWorld.query input) >>= fun answer =>
        (fun paused => (paused.1, (paused.2.1, input :: paused.2.2))) <$>
          pausedFull stop (next answer) (stepTrace input answer memory) := by
  unfold pausedFull
  rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.run_query_bind]
  by_cases hs : stop memory
  · rw [if_pos hs, if_pos hs, pure_bind, ← SphincsSecurity.QueryCap.recorded_query_bind]
    simp only [bind_pure_comp]
  · rw [if_neg hs, if_neg hs, bind_assoc]
    congr 1
    funext answer
    have hmap : (SphincsSecurity.QueryCap.recorded (next answer) >>= fun result =>
        (pure (result.1, input :: result.2) : OracleComp RefWorld _)) =
        (fun result => (result.1, input :: result.2)) <$> SphincsSecurity.QueryCap.recorded (next answer) := by
      simp only [bind_pure_comp]
    rw [hmap, run_map]
    simp only [map_bind, bind_map_left, map_pure]
theorem paused_structure (T : Answers) (stop : List Entry → Prop) (G : OracleComp RefWorld β) :
    ∀ (memory : List Entry) (result : List Entry × (β × List RefWorld.Domain)),
      result ∈ support (simulateQ (refImpl T) (pausedFull stop G memory)) →
        memory.length ≤ result.1.length ∧
        result.1 = (memory ++ traceOf T result.2.2).take result.1.length ∧
        (∀ j, memory.length ≤ j → j < result.1.length → ¬stop ((memory ++ traceOf T result.2.2).take j)) ∧
        (stop result.1 ∨ result.1 = memory ++ traceOf T result.2.2) := by
  induction G using OracleComp.inductionOn with
  | pure value =>
      intro memory result hr
      simp only [pausedFull, SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.run_pure, pure_bind,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst hr
      refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inr ?_⟩
      · simp
      · show memory = memory ++ traceOf T []
        rw [show traceOf T [] = [] from rfl, List.append_nil]
  | query_bind input next ih =>
      intro memory result hr
      rw [pausedFull_query_bind] at hr
      by_cases hs : stop memory
      · rw [if_pos hs] at hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨tail, -, rfl⟩ := hr
        refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inl hs⟩
        show memory = List.take memory.length (memory ++ _)
        rw [List.take_left' rfl]
      · rw [if_neg hs, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hr
        obtain ⟨answer, hanswer, hr⟩ := hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨paused, hpaused, rfl⟩ := hr
        obtain ⟨h1, h2, h3, h4⟩ := ih answer (stepTrace input answer memory) paused hpaused
        have hentry := entryOf_refImpl T input answer hanswer
        have htrace : stepTrace input answer memory ++ traceOf T paused.2.2 =
            memory ++ traceOf T (input :: paused.2.2) := by
          rw [traceOf_cons, stepTrace, hentry, List.append_assoc]
        rw [htrace] at h2 h3 h4
        have hlen : (stepTrace input answer memory).length ≤ memory.length + 1 := by
          have := entryOf_length_le input answer
          simp only [stepTrace, List.length_append]
          omega
        have hlen' : memory.length ≤ (stepTrace input answer memory).length := by
          simp only [stepTrace, List.length_append]
          omega
        refine ⟨le_trans hlen' h1, h2, ?_, h4⟩
        intro j hj1 hj2
        by_cases hj : (stepTrace input answer memory).length ≤ j
        · exact h3 j hj hj2
        · have hjm : j = memory.length := by omega
          rw [hjm, List.take_left' rfl]
          exact hs
variable {adversary : AdversaryP}
noncomputable def pausedSeed (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  simulateQ (routeImpl a (restDepth a R) R) (pausedFull stop (referenceGame (fillTable a R endpoint) adversary q) [])
theorem pausedSeed_snd (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) : Prod.snd <$> pausedSeed adversary q a R stop endpoint = seedGame adversary q a R endpoint := by
  unfold pausedSeed seedGame
  rw [← simulateQ_map, pausedFull_snd]
noncomputable def seedBefore (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) ((List Entry × OracleComp RefWorld SeedResult) × Nat) :=
  SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryPause.run stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
noncomputable def seedAfter (a : ChainAddr) (R : RefTables adversary)
    (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat) :
    OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (routeImpl a (restDepth a R) R) middle.1.2
theorem seedBefore_after (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) :
    (do
      let middle ← seedBefore adversary q a R stop endpoint
      let result ← seedAfter a R middle
      pure (middle.1.1, result)) = pausedSeed adversary q a R stop endpoint := by
  unfold seedBefore seedAfter pausedSeed pausedFull
  simp only [simulateQ_bind, simulateQ_pure]
  conv_rhs => rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))]
  rw [bind_map_left]
theorem seedGame_support_cost (q : Nat) (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest)
    (result : SeedResult) (h : result ∈ support (seedGame adversary q a R endpoint)) : seedCost a R result ≤ q := by
  have hrec : result ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (fillTable a R endpoint) adversary q)) := by
    unfold seedGame at h
    revert h
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) result
  have hcount : (result.1, SphincsSecurity.QueryCap.calls RefCharged result.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (fillTable a R endpoint) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result, hrec, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (fillTable a R endpoint) adversary q) _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
theorem lazyRun_bind {d : Nat} {α γ : Type} (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) γ)
    (observed : Fin d → Digest → Option Digest) :
    lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (first >>= next) observed =
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl first observed).bind fun r =>
        lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (next r.1) r.2 := by
  simp only [lazyRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]
theorem checkpoint_budget (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ q ∧ queryCount result.2 ≤ q := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hmem := lazyRun_mem_support _ _ _ hfull
  have htotal : middle.1.2 + result.1.2 ≤ q := by
    have hc := seedGame_charge adversary q a R endpoint _ hmem
    have hs := seedGame_support_cost q a R endpoint result.1.1 (by
      have := SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (seedGame adversary q a R endpoint)
      rw [← this, support_map]
      exact ⟨_, hmem, rfl⟩)
    simp only at hc
    omega
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  have hrows := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ middle.2 result hresult
  constructor <;> omega
theorem checkpoint_charge (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + 2 * result.1.2 ≤ 2 * seedCost a R result.1.1 := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hc := seedGame_charge adversary q a R endpoint _ (lazyRun_mem_support _ _ _ hfull)
  simp only at hc
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  omega
def RowsInv (a : ChainAddr) {d : Nat} (memory : List Entry) (observed : Fin d → Digest → Option Digest) : Prop :=
  ∀ (i : Fin d) (v w : Digest), observed i v = some w ↔ ∃ answer, (chainRow a i v, answer) ∈ memory ∧ low answer = w
theorem rowsInv_nil (a : ChainAddr) (d : Nat) : RowsInv a (d := d) [] (fun _ _ => none) := by
  intro i v w
  simp
theorem route_step_lazy (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (input : RefWorld.Domain)
    (memory : List Entry) (observed : Fin d → Digest → Option Digest) (hinv : RowsInv a memory observed)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (routeImpl a d R input) observed).support) :
    RowsInv a (stepTrace input result.1 memory) result.2 := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
    simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simpa [stepTrace, entryOf] using hinv
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        intro i v w
        rw [hinv i v w]
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨answer, hm, hl⟩
          exact ⟨answer, Or.inl hm, hl⟩
        · rintro ⟨answer, hm | hm, hl⟩
          · exact ⟨answer, hm, hl⟩
          · exact absurd (congrArg Prod.fst hm).symm (rowOf_none hp (i, v))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
        simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
        obtain ⟨w₀, hw₀, rfl⟩ := hr
        have hin := rowOf_some hp
        subst hin
        intro i v w
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [record, Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨_, Or.inr rfl, ?_⟩
            simp only [low, ChainGraph.joinOutput_low]
          · rintro ⟨answer, hm | hm, hl⟩
            ·
              have hold := (hinv i v w).mpr ⟨answer, hm, hl⟩
              simp only [hold, SphincsSecurity.Concrete.PartialChainEndpoint.rowLaw, PMF.mem_support_pure_iff] at hw₀
              exact hw₀
            · have := congrArg Prod.snd hm
              simp only at this
              rw [← hl, this, low, ChainGraph.joinOutput_low]
        · have hne : chainRow a p.1 p.2 ≠ chainRow a i v := by
            intro he
            obtain ⟨hs, hv⟩ := Mask.chainRow_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          have hrec : record observed p w₀ i v = observed i v := by
            simp only [record]
            by_cases h1 : i = p.1
            · subst h1
              have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
              simp only [Function.update_self, Function.update_of_ne h2]
            · simp only [Function.update_of_ne h1]
          rw [hrec, hinv i v w]
          constructor
          · rintro ⟨answer, hm, hl⟩
            exact ⟨answer, Or.inl hm, hl⟩
          · rintro ⟨answer, hm | hm, hl⟩
            · exact ⟨answer, hm, hl⟩
            · exact absurd (congrArg Prod.fst hm).symm hne
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simpa [stepTrace, entryOf] using hinv
theorem checkpoint_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support) :
    RowsInv a middle.1.1.1 middle.2 := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hplain : (middle.1.1, middle.2) ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none)).support := by
    rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])),
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_map, PMF.mem_support_map_iff]
    exact ⟨middle, hmiddle, rfl⟩
  have hcomp : lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none) =
      (simulateQ ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
        (SphincsSecurity.QueryPause.run stop stepTrace
          (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])).run
        (fun _ _ => none) := by
    unfold lazyRun
    rw [QueryImpl.simulateQ_compose]
  rw [hcomp] at hplain
  exact SphincsSecurity.QueryPause.run_simulation_invariant stop stepTrace
    ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
    (fun memory observed => RowsInv a memory observed)
    (fun memory observed hinv _ input result hresult =>
      route_step_lazy a hd R input memory observed hinv result (by
        simpa only [QueryImpl.apply_compose, lazyRun] using hresult))
    _ [] (fun _ _ => none) (rowsInv_nil a _) _ hplain
end PrefixGame
end SigGolfCandidate.T3.Security.Wots
end
