import SigGolfCandidate.T3.Secc.WotsReference

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def fixedWorld (F : Answers) : QueryImpl T3.Spec ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr input) => pure (F (.inl (.inr input)))
  | .inr coordinate => pure (F (.inr coordinate))
noncomputable def fixedRecord {α : Type} (F : Answers) (program : M α) :
    LazyPrivate.State → ProbComp (FirstHit.Recorded α) :=
  OracleComp.construct
    (fun value state => pure ⟨value, [], state⟩)
    (fun input _ next state => do
      let answer ← fixedWorld F input
      (fun last => ⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩) <$>
        next answer (FirstHit.advance state input answer)) program
theorem fixedRecord_pure {α : Type} (F : Answers) (value : α) (state : LazyPrivate.State) :
    fixedRecord F (pure value : M α) state = pure ⟨value, [], state⟩ := rfl
theorem fixedRecord_query_bind {α : Type} (F : Answers) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    fixedRecord F (liftM (T3.Spec.query input) >>= next) state = (do
      let answer ← fixedWorld F input
      (fun last => ⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩) <$>
        fixedRecord F (next answer) (FirstHit.advance state input answer)) := rfl
theorem fixedRecord_bind {α β : Type} (F : Answers) (program : M α) (next : α → M β)
    (state : LazyPrivate.State) :
    fixedRecord F (program >>= next) state = (do
      let first ← fixedRecord F program state
      let last ← fixedRecord F (next first.value) first.state
      pure ⟨last.value, first.events ++ last.events, last.state⟩) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [pure_bind, fixedRecord_pure, List.nil_append]; simp
  | query_bind input rest ih =>
      rw [bind_assoc, fixedRecord_query_bind, fixedRecord_query_bind]
      simp only [bind_map_left, bind_assoc]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [map_bind, map_pure]
      apply bind_congr
      intro first
      apply bind_congr
      intro last
      rfl
theorem fixedRecord_map {α β : Type} (F : Answers) (f : α → β) (program : M α) (state : LazyPrivate.State) :
    fixedRecord F (f <$> program) state =
      (fun result : FirstHit.Recorded α => (⟨f result.value, result.events, result.state⟩ : FirstHit.Recorded β)) <$>
        fixedRecord F program state := by
  rw [map_eq_bind_pure_comp, fixedRecord_bind]
  simp only [Function.comp_def, fixedRecord_pure, pure_bind, map_pure, List.append_nil, bind_pure_comp]
noncomputable def pureRecord {α : Type} (F : Answers) (program : M α) :
    LazyPrivate.State → FirstHit.Recorded α :=
  OracleComp.construct
    (fun value state => ⟨value, [], state⟩)
    (fun input _ next state =>
      ⟨(next (F input) (FirstHit.advance state input (F input))).value,
        ⟨state, input, F input⟩ :: (next (F input) (FirstHit.advance state input (F input))).events,
        (next (F input) (FirstHit.advance state input (F input))).state⟩) program
theorem pureRecord_pure {α : Type} (F : Answers) (value : α) (state : LazyPrivate.State) :
    pureRecord F (pure value : M α) state = ⟨value, [], state⟩ := rfl
theorem pureRecord_query_bind {α : Type} (F : Answers) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    pureRecord F (liftM (T3.Spec.query input) >>= next) state =
      ⟨(pureRecord F (next (F input)) (FirstHit.advance state input (F input))).value,
        ⟨state, input, F input⟩ :: (pureRecord F (next (F input)) (FirstHit.advance state input (F input))).events,
        (pureRecord F (next (F input)) (FirstHit.advance state input (F input))).state⟩ := rfl
theorem eval_query (F : Answers) (input : T3.Spec.Domain) :
    evalWithAnswerFn F (liftM (T3.Spec.query input)) = F input :=
  simulateQ_spec_query F input
theorem fixedWorld_hash (F : Answers) (input : T3.Spec.Domain) (hi : SourceReplay.IsHash input) :
    fixedWorld F input = pure (F input) := by
  rcases input with (n | x) | c
  · exact False.elim hi
  · rfl
  · rfl
theorem fixedRecord_hashOnly {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program)
    (state : LazyPrivate.State) : fixedRecord F program state = pure (pureRecord F program state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [fixedRecord_query_bind, pureRecord_query_bind, fixedWorld_hash F input hi, pure_bind,
        ih (F input) (hn _), map_pure]
theorem pureRecord_value {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (pureRecord F program state).value = evalWithAnswerFn F program := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [pureRecord_query_bind, evalWithAnswerFn_bind, eval_query]
      exact ih (F input) _
theorem pureRecord_inputs {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (pureRecord F program state).events.map FirstHit.QueryEvent.input = SourceReplay.queried F program := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [pureRecord_query_bind, SourceReplay.queried_query_bind, List.map_cons]
      exact congrArg (List.cons input) (ih (F input) _)
def chargeSum (events : List FirstHit.QueryEvent) : Nat :=
  (events.map fun event => FullGame.queryCharge event.input).sum
@[simp] theorem chargeSum_nil : chargeSum [] = 0 := rfl
@[simp] theorem chargeSum_cons (event : FirstHit.QueryEvent) (events : List FirstHit.QueryEvent) :
    chargeSum (event :: events) = FullGame.queryCharge event.input + chargeSum events := by
  simp [chargeSum]
@[simp] theorem chargeSum_append (left right : List FirstHit.QueryEvent) :
    chargeSum (left ++ right) = chargeSum left + chargeSum right := by
  simp [chargeSum]
theorem queryCharge_hash (input : T3.Spec.Domain) (hi : SourceReplay.IsHash input) :
    FullGame.queryCharge input = 1 := by
  simp only [FullGame.queryCharge, if_pos (SourceReplay.hash_charged input hi)]
theorem pureRecord_charge {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program)
    (state : LazyPrivate.State) :
    chargeSum (pureRecord F program state).events = (SourceReplay.queried F program).length := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [pureRecord_query_bind, SourceReplay.queried_query_bind, List.length_cons]
      simp only [chargeSum_cons, queryCharge_hash input hi]
      rw [ih (F input) (hn _)]
      omega
theorem fixedRecord_counted {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State) :
    (fun result : FirstHit.Recorded α => (result.value, chargeSum result.events)) <$> fixedRecord F program state =
      simulateQ (fixedWorld F) (SphincsSecurity.QueryCap.counted Derivation.charged program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [fixedRecord_pure, SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      rw [fixedRecord_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
      simp only [map_bind, Functor.map_map, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      apply bind_congr
      intro answer
      rw [← ih answer (FirstHit.advance state input answer)]
      simp only [chargeSum_cons, map_eq_bind_pure_comp, Function.comp_def, FullGame.queryCharge, bind_assoc,
        pure_bind]
theorem fixedWorld_counted_hashOnly {α : Type} (F : Answers) (program : M α) (hp : SourceReplay.HashOnly program) :
    simulateQ (fixedWorld F) (SphincsSecurity.QueryCap.counted Derivation.charged program) =
      pure (evalWithAnswerFn F program, (SourceReplay.queried F program).length) := by
  rw [← fixedRecord_counted F program (∅, ∅), fixedRecord_hashOnly F program hp, map_pure,
    pureRecord_value, pureRecord_charge F program hp]
def Agrees (F : Answers) (state : LazyPrivate.State) : Prop :=
  ∀ input answer, SourceReplay.known state input = some answer → F input = answer
theorem agrees_empty (F : Answers) : Agrees F (∅, ∅) := by
  intro input answer h
  rcases input with (n | x) | c <;> cases h
theorem agrees_advance {F : Answers} {state : LazyPrivate.State} (hF : Agrees F state) (input : T3.Spec.Domain) :
    Agrees F (FirstHit.advance state input (F input)) := by
  intro query answer h
  rcases input with (n | x) | c
  · exact hF query answer h
  · rcases query with (m | y) | d
    · cases h
    · change (state.2.cacheQuery x (F (.inl (.inr x)))) y = some answer at h
      by_cases hy : y = x
      · subst y
        rw [QueryCache.cacheQuery_self] at h
        exact Option.some.inj h
      · rw [QueryCache.cacheQuery_of_ne _ _ hy] at h
        exact hF _ _ h
    · exact hF _ _ h
  · rcases query with (m | y) | d
    · cases h
    · exact hF _ _ h
    · change (state.1.cacheQuery c (F (.inr c))) d = some answer at h
      by_cases hd : d = c
      · subst d
        rw [QueryCache.cacheQuery_self] at h
        exact Option.some.inj h
      · rw [QueryCache.cacheQuery_of_ne _ _ hd] at h
        exact hF _ _ h
theorem advance_coin (state : LazyPrivate.State) (n : Nat) (answer : Fin (n + 1)) :
    FirstHit.advance state (.inl (.inl n)) answer = state := rfl
theorem lazy_query_mem (state : LazyPrivate.State) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : ∀ cached, SourceReplay.known state input = some cached → cached = answer) :
    (answer, FirstHit.advance state input answer) ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state) := by
  rw [LazyPrivate.run_query]
  rcases input with (n | x) | c
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    refine ⟨(answer, state.2), ?_, rfl⟩
    change (answer, state.2) ∈ support ((fun a => (a, state.2)) <$>
      ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _))
    rw [support_map]
    exact ⟨answer, mem_support_uniformSample _, rfl⟩
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    cases hc : state.2 x with
    | some cached =>
        have he : cached = answer := h cached hc
        subst he
        refine ⟨(cached, state.2), ?_, ?_⟩
        · change (cached, state.2) ∈ support ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2)
          rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff]
        · change (cached, (state.1, state.2.cacheQuery x cached)) = (cached, (state.1, state.2))
          rw [PrivateTable.cacheQuery_cached state.2 x cached hc]
    | none =>
        refine ⟨(answer, state.2.cacheQuery x answer), ?_, rfl⟩
        change (answer, state.2.cacheQuery x answer) ∈
          support ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2)
        rw [QueryImpl.withCaching_run_none _ hc, support_map]
        exact ⟨answer, mem_support_uniformSample _, rfl⟩
  · simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, mem_support_pure_iff]
    cases hc : state.1 c with
    | some cached =>
        have he : cached = answer := h cached hc
        subst he
        refine ⟨(cached, state.1), ?_, ?_⟩
        · change (cached, state.1) ∈ support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run state.1)
          rw [QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff]
        · change (cached, (state.1.cacheQuery c cached, state.2)) = (cached, (state.1, state.2))
          rw [PrivateTable.cacheQuery_cached state.1 c cached hc]
    | none =>
        refine ⟨(answer, state.1.cacheQuery c answer), ?_, rfl⟩
        change (answer, state.1.cacheQuery c answer) ∈
          support ((randomOracle (spec := Coordinate →ₒ HashOutput) c).run state.1)
        rw [QueryImpl.withCaching_run_none _ hc, support_map]
        exact ⟨answer, mem_support_uniformSample _, rfl⟩
theorem fixedWorld_mem (F : Answers) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : answer ∈ support (fixedWorld F input)) : SourceReplay.IsHash input → answer = F input := by
  intro hi
  rw [fixedWorld_hash F input hi, mem_support_pure_iff] at h
  exact h
theorem fixedRecord_mem_record {α : Type} (F : Answers) (program : M α) (state : LazyPrivate.State)
    (hF : Agrees F state) (result : FirstHit.Recorded α) (hr : result ∈ support (fixedRecord F program state)) :
    result ∈ support (FirstHit.record program state) ∧ Agrees F result.state := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [fixedRecord_pure, mem_support_pure_iff] at hr
      subst result
      exact ⟨by rw [FirstHit.record_pure, mem_support_pure_iff], hF⟩
  | query_bind input next ih =>
      rw [fixedRecord_query_bind, mem_support_bind_iff] at hr
      obtain ⟨answer, hanswer, hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      have hadv : Agrees F (FirstHit.advance state input answer) := by
        rcases input with (n | x) | c
        · exact hF
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact agrees_advance hF _
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact agrees_advance hF _
      obtain ⟨hrec, hagree⟩ := ih answer _ hadv last hlast
      refine ⟨?_, hagree⟩
      rw [FirstHit.record_query_bind, mem_support_bind_iff]
      refine ⟨(answer, FirstHit.advance state input answer), lazy_query_mem state input answer ?_, ?_⟩
      · intro cached hc
        rcases input with (n | x) | c
        · cases hc
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact (hF _ _ hc).symm
        · rw [fixedWorld_mem F _ answer hanswer trivial]; exact (hF _ _ hc).symm
      · rw [support_map]
        exact ⟨last, hrec, rfl⟩
end SigGolfCandidate.T3.Security.Wots.Ref
