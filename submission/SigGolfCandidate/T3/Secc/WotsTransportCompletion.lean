import SigGolfCandidate.T3.Secc.WotsTransportBase

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs finiteHashAnswer)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs
noncomputable local instance instFintypeCoordinate_wotsTransportCompletion : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCompletion : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def fillAnswers (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (finiteHashAnswer ∅ inputs publicTable input)
  | .inr coordinate => (state.1 coordinate).getD (privateTable coordinate)
theorem fillAnswers_empty (inputs : Finset HashInput) (privateTable : FullGame.FullTable)
    (publicTable : inputs → HashOutput) :
    fillAnswers inputs (∅, ∅) privateTable publicTable = eagerAnswers inputs privateTable publicTable := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem fillAnswers_known (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) (h : SourceReplay.known state input = some answer) :
    fillAnswers inputs state privateTable publicTable input = answer := by
  rcases input with (n | x) | c
  · cases h
  · change (state.2 x).getD _ = answer
    change state.2 x = some answer at h
    rw [h, Option.getD_some]
  · change (state.1 c).getD _ = answer
    change state.1 c = some answer at h
    rw [h, Option.getD_some]
theorem fillAnswers_public_update (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (x : HashInput) (hx : x ∈ inputs)
    (h : state.2 x = none) (value : HashOutput) :
    fillAnswers inputs (state.1, state.2.cacheQuery x value) privateTable publicTable =
      fillAnswers inputs state privateTable (Function.update publicTable ⟨x, hx⟩ value) := by
  funext query
  rcases query with (n | y) | c
  · rfl
  · change ((state.2.cacheQuery x value) y).getD (finiteHashAnswer ∅ inputs publicTable y) =
      (state.2 y).getD (finiteHashAnswer ∅ inputs (Function.update publicTable ⟨x, hx⟩ value) y)
    by_cases hy : y = x
    · subst y
      rw [QueryCache.cacheQuery_self, h, Option.getD_some, Option.getD_none,
        SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ x hx rfl, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hy]
      cases hc : state.2 y with
      | some v => rfl
      | none =>
          simp only [Option.getD_none]
          by_cases hyi : y ∈ inputs
          · rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ y hyi rfl,
              SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ y hyi rfl,
              Function.update_of_ne (fun heq => hy (congrArg Subtype.val heq))]
          · simp [finiteHashAnswer, hyi]
  · rfl
theorem fillAnswers_private_update (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (c : Coordinate)
    (h : state.1 c = none) (value : HashOutput) :
    fillAnswers inputs (state.1.cacheQuery c value, state.2) privateTable publicTable =
      fillAnswers inputs state (Function.update privateTable c value) publicTable := by
  funext query
  rcases query with (n | y) | d
  · rfl
  · rfl
  · change ((state.1.cacheQuery c value) d).getD (privateTable d) = (state.1 d).getD (Function.update privateTable c value d)
    by_cases hd : d = c
    · subst d
      rw [QueryCache.cacheQuery_self, h, Option.getD_some, Option.getD_none, Function.update_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ hd, Function.update_of_ne hd]
theorem hashInputs_map {α β : Type} (f : α → β) (computation : OracleComp OracleWorld α) :
    hashInputs (f <$> computation) = hashInputs computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [map_pure, SphincsSecurity.Concrete.hashInputs_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.Concrete.hashInputs_query_bind,
        SphincsSecurity.Concrete.hashInputs_query_bind]
      simp only [ih]
      cases input <;> rfl
def InputsIn (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State) : Prop :=
  ∀ privateTable : FullGame.FullTable, (∀ c v, state.1 c = some v → privateTable c = v) →
    hashInputs (Derivation.tableRun privateTable (FirstHit.sourceRecord program state)) ⊆ inputs
theorem tableRun_sourceRecord_query_bind {α : Type} (privateTable : FullGame.FullTable) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    Derivation.tableRun privateTable (FirstHit.sourceRecord (liftM (T3.Spec.query input) >>= next) state) =
      (Derivation.tableHandler privateTable input >>= fun answer =>
        (fun last => (⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩ : FirstHit.Recorded α)) <$>
          Derivation.tableRun privateTable (FirstHit.sourceRecord (next answer) (FirstHit.advance state input answer))) := by
  rw [FirstHit.sourceRecord_query_bind]
  unfold Derivation.tableRun
  rw [simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map]
  rfl
theorem tableHandler_world (privateTable : FullGame.FullTable) (input : OracleWorld.Domain) :
    Derivation.tableHandler privateTable (.inl input) = liftM (OracleWorld.query input) := rfl
theorem tableHandler_private (privateTable : FullGame.FullTable) (c : Coordinate) :
    Derivation.tableHandler privateTable (.inr c) = pure (privateTable c) := rfl
theorem exists_consistent (state : LazyPrivate.State) :
    ∃ privateTable : FullGame.FullTable, ∀ c v, state.1 c = some v → privateTable c = v := by
  refine ⟨fun c => (state.1 c).getD 0, fun c v hc => ?_⟩
  change (state.1 c).getD 0 = v
  rw [hc, Option.getD_some]
theorem InputsIn.public {inputs : Finset HashInput} {α : Type} {x : HashInput}
    {next : T3.Spec.Range (.inl (.inr x)) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inl (.inr x))) >>= next) state) :
    x ∈ inputs ∧ ∀ value : T3.Spec.Range (.inl (.inr x)),
      InputsIn inputs (next value) (FirstHit.advance state (.inl (.inr x)) value) := by
  obtain ⟨privateTable, hpriv⟩ := exists_consistent state
  constructor
  · apply h privateTable hpriv
    rw [tableRun_sourceRecord_query_bind, tableHandler_world]
    exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
  · intro value table htable
    have hstate : ∀ c v, state.1 c = some v → table c = v := htable
    have hsub := h table hstate
    rw [tableRun_sourceRecord_query_bind, tableHandler_world] at hsub
    intro row hrow
    apply hsub
    apply SphincsSecurity.Concrete.hashInputs_next_subset (.inr x) _ value
    rw [hashInputs_map]
    exact hrow
theorem InputsIn.coin {inputs : Finset HashInput} {α : Type} {n : Nat}
    {next : Fin (n + 1) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inl (.inl n))) >>= next) state) (value : Fin (n + 1)) :
    InputsIn inputs (next value) state := by
  intro table htable row hrow
  apply h table htable
  rw [tableRun_sourceRecord_query_bind, tableHandler_world]
  apply SphincsSecurity.Concrete.hashInputs_next_subset (.inl n) _ value
  rw [hashInputs_map]
  exact hrow
theorem InputsIn.priv {inputs : Finset HashInput} {α : Type} {c : Coordinate}
    {next : T3.Spec.Range (.inr c) → M α} {state : LazyPrivate.State}
    (h : InputsIn inputs (liftM (T3.Spec.query (.inr c)) >>= next) state) (value : T3.Spec.Range (.inr c))
    (hcached : ∀ v, state.1 c = some v → v = value) :
    InputsIn inputs (next value) (FirstHit.advance state (.inr c) value) := by
  intro table htable row hrow
  have hc : table c = value := by
    apply htable c value
    change (state.1.cacheQuery c value) c = some value
    rw [QueryCache.cacheQuery_self]
  have hstate : ∀ d v, state.1 d = some v → table d = v := by
    intro d v hd
    apply htable d v
    change (state.1.cacheQuery c value) d = some v
    by_cases hdc : d = c
    · subst d
      rw [QueryCache.cacheQuery_self, hcached v hd]
    · rw [QueryCache.cacheQuery_of_ne _ _ hdc]
      exact hd
  apply h table hstate
  rw [tableRun_sourceRecord_query_bind, tableHandler_private, pure_bind, hashInputs_map, hc]
  exact hrow
theorem advance_cached (state : LazyPrivate.State) (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : SourceReplay.known state input = some answer) : FirstHit.advance state input answer = state := by
  rcases input with (n | x) | c
  · rfl
  · change (state.1, state.2.cacheQuery x answer) = state
    rw [PrivateTable.cacheQuery_cached state.2 x answer h]
  · change (state.1.cacheQuery c answer, state.2) = state
    rw [PrivateTable.cacheQuery_cached state.1 c answer h]
noncomputable def completedTail {α : Type} (inputs : Finset HashInput) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) (middle : T3.Spec.Range input × LazyPrivate.State) :
    ProbComp (FirstHit.Recorded α × Answers) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, input, middle.1⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
          fillAnswers inputs middle.2 privateTable publicTable)) <$>
        fixedRecord (fillAnswers inputs middle.2 privateTable publicTable) (next middle.1) middle.2
theorem lazy_coin (state : LazyPrivate.State) (n : Nat) :
    LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) state =
      (fun c => (c, state)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := by
  rw [LazyPrivate.run_query]
  rfl
theorem lazy_public_fresh (state : LazyPrivate.State) (x : HashInput) (h : state.2 x = none) :
    LazyPrivate.run (liftM (T3.Spec.query (.inl (.inr x)))) state =
      (fun v => (v, (state.1, state.2.cacheQuery x v))) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
  have hq : liftM (T3.Spec.query (.inl (.inr x))) = (Sampling.publicHandler x : M HashOutput) := rfl
  rw [hq, LazyPrivate.run_publicQuery]
  change ((randomOracle (spec := SphincsSecurity.HashSpec) x).run state.2 >>= fun result =>
    pure (result.1, (state.1, result.2))) = _
  rw [QueryImpl.withCaching_run_none _ h]
  simp only [bind_pure_comp]
  rfl
theorem lazy_private_fresh (state : LazyPrivate.State) (c : Coordinate) (h : state.1 c = none) :
    LazyPrivate.run (liftM (T3.Spec.query (.inr c))) state =
      (fun v => (v, (state.1.cacheQuery c v, state.2))) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
  have hq : liftM (T3.Spec.query (.inr c)) = (privateHash c : M HashOutput) := rfl
  rw [hq, LazyPrivate.run_privateHash]
  rw [QueryImpl.withCaching_run_none _ h]
  simp only [bind_map_left, bind_pure_comp]
  rfl
theorem fixedWorld_public (F : Answers) (x : HashInput) :
    fixedWorld F (.inl (.inr x)) = pure (F (.inl (.inr x))) := rfl
theorem fixedWorld_private (F : Answers) (c : Coordinate) :
    fixedWorld F (.inr c) = pure (F (.inr c)) := rfl
noncomputable def eagerSide (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State) :
    ProbComp (FirstHit.Recorded α × Answers) :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun result => (result, fillAnswers inputs state privateTable publicTable)) <$>
        fixedRecord (fillAnswers inputs state privateTable publicTable) program state
theorem eagerSide_query_bind (inputs : Finset HashInput) {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    eagerSide inputs (liftM (T3.Spec.query input) >>= next) state =
      (($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
        ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
          fixedWorld (fillAnswers inputs state privateTable publicTable) input >>= fun answer =>
            (fun last => ((⟨last.value, ⟨state, input, answer⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
                fillAnswers inputs state privateTable publicTable)) <$>
              fixedRecord (fillAnswers inputs state privateTable publicTable) (next answer)
                (FirstHit.advance state input answer)) := by
  unfold eagerSide
  simp only [fixedRecord_query_bind, map_bind, Functor.map_map]
theorem completion_coin (inputs : Finset HashInput) {α : Type} (n : Nat) (next : Fin (n + 1) → M α)
    (state : LazyPrivate.State) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inl (.inl n)))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inl (.inl n))) >>= next) state] := by
  rw [lazy_coin, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro publicTable
  rfl
theorem completion_cached (inputs : Finset HashInput) {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) (answer : T3.Spec.Range input)
    (hk : SourceReplay.known state input = some answer) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query input)) state >>= completedTail inputs input next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query input) >>= next) state] := by
  have hi : SourceReplay.IsHash input := by
    rcases input with (n | x) | c
    · cases hk
    · trivial
    · trivial
  rw [SourceReplay.known_query_run state input answer hk, pure_bind, eagerSide_query_bind]
  unfold completedTail
  apply evalSPMF_bind_congr'
  intro privateTable
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_hash _ input hi, pure_bind, fillAnswers_known inputs state privateTable publicTable input answer hk,
    advance_cached state input answer hk]
theorem fillAnswers_public_fresh (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (x : HashInput) (hx : x ∈ inputs)
    (h : state.2 x = none) :
    fillAnswers inputs state privateTable publicTable (.inl (.inr x)) = publicTable ⟨x, hx⟩ := by
  change (state.2 x).getD (finiteHashAnswer ∅ inputs publicTable x) = _
  rw [h, Option.getD_none, SphincsSecurity.Concrete.finiteHashAnswer_none ∅ inputs _ x hx rfl]
theorem completion_public_fresh (inputs : Finset HashInput) {α : Type} (x : HashInput)
    (next : T3.Spec.Range (.inl (.inr x)) → M α) (state : LazyPrivate.State) (hx : x ∈ inputs)
    (hc : state.2 x = none) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inl (.inr x)))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inl (.inr x))) >>= next) state] := by
  rw [lazy_public_fresh state x hc, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  simp only [fillAnswers_public_update inputs state _ _ x hx hc]
  refine (evalSPMF_bind_bind_swap _ _ _).trans ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  let K : (inputs → HashOutput) → ProbComp (FirstHit.Recorded α × Answers) := fun table =>
    (fun last => ((⟨last.value, ⟨state, .inl (.inr x), table ⟨x, hx⟩⟩ :: last.events, last.state⟩ :
        FirstHit.Recorded α), fillAnswers inputs state privateTable table)) <$>
      fixedRecord (fillAnswers inputs state privateTable table) (next (table ⟨x, hx⟩))
        (state.1, state.2.cacheQuery x (table ⟨x, hx⟩))
  have hpoint : ∀ value table, ((fun last => ((⟨last.value, ⟨state, .inl (.inr x), value⟩ :: last.events,
      last.state⟩ : FirstHit.Recorded α),
        fillAnswers inputs state privateTable (Function.update table ⟨x, hx⟩ value))) <$>
      fixedRecord (fillAnswers inputs state privateTable (Function.update table ⟨x, hx⟩ value)) (next value)
        (state.1, state.2.cacheQuery x value)) = K (Function.update table ⟨x, hx⟩ value) := by
    intro value table
    simp only [K, Function.update_self]
  simp only [hpoint]
  refine Eq.trans (PrivateTable.refresh_table (⟨x, hx⟩ : inputs) K) ?_
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_public, pure_bind, fillAnswers_public_fresh inputs state privateTable publicTable x hx hc]
  rfl
theorem fillAnswers_private_fresh (inputs : Finset HashInput) (state : LazyPrivate.State)
    (privateTable : FullGame.FullTable) (publicTable : inputs → HashOutput) (c : Coordinate)
    (h : state.1 c = none) :
    fillAnswers inputs state privateTable publicTable (.inr c) = privateTable c := by
  change (state.1 c).getD (privateTable c) = _
  rw [h, Option.getD_none]
theorem completion_private_fresh (inputs : Finset HashInput) {α : Type} (c : Coordinate)
    (next : T3.Spec.Range (.inr c) → M α) (state : LazyPrivate.State) (hc : state.1 c = none) :
    𝒮[LazyPrivate.run (liftM (T3.Spec.query (.inr c))) state >>= completedTail inputs _ next state] =
      𝒮[eagerSide inputs (liftM (T3.Spec.query (.inr c)) >>= next) state] := by
  rw [lazy_private_fresh state c hc, bind_map_left, eagerSide_query_bind]
  unfold completedTail
  simp only [fillAnswers_private_update inputs state _ _ c hc]
  let K : FullGame.FullTable → ProbComp (FirstHit.Recorded α × Answers) := fun table =>
    ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, .inr c, table c⟩ :: last.events, last.state⟩ :
          FirstHit.Recorded α), fillAnswers inputs state table publicTable)) <$>
        fixedRecord (fillAnswers inputs state table publicTable) (next (table c))
          (state.1.cacheQuery c (table c), state.2)
  have hpoint : ∀ value table, (($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun last => ((⟨last.value, ⟨state, .inr c, value⟩ :: last.events, last.state⟩ : FirstHit.Recorded α),
        fillAnswers inputs state (Function.update table c value) publicTable)) <$>
      fixedRecord (fillAnswers inputs state (Function.update table c value) publicTable) (next value)
        (state.1.cacheQuery c value, state.2)) = K (Function.update table c value) := by
    intro value table
    simp only [K, Function.update_self]
  simp only [hpoint]
  refine Eq.trans (PrivateTable.refresh_table c K) ?_
  apply evalSPMF_bind_congr'
  intro privateTable
  simp only [K]
  apply evalSPMF_bind_congr'
  intro publicTable
  rw [fixedWorld_private, pure_bind, fillAnswers_private_fresh inputs state privateTable publicTable c hc]
  rfl
theorem record_completion (inputs : Finset HashInput) {α : Type} (program : M α) (state : LazyPrivate.State)
    (h : InputsIn inputs program state) :
    𝒮[FirstHit.record program state >>= fun result =>
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
          ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
            pure (result, fillAnswers inputs result.state privateTable publicTable)] =
      𝒮[eagerSide inputs program state] := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [eagerSide, FirstHit.record_pure, fixedRecord_pure, pure_bind, map_pure]
  | query_bind input next ih =>
      have htail : ∀ middle ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state),
          𝒮[(fun last => (⟨last.value, ⟨state, input, middle.1⟩ :: last.events, last.state⟩ :
              FirstHit.Recorded α)) <$> FirstHit.record (next middle.1) middle.2 >>= fun result =>
            ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
              ($ᵗ (inputs → HashOutput) : ProbComp _) >>= fun publicTable =>
                pure (result, fillAnswers inputs result.state privateTable publicTable)] =
          𝒮[completedTail inputs input next state middle] := by
        intro middle hm
        have hadv := FirstHit.query_advance state input middle hm
        have hin : InputsIn inputs (next middle.1) middle.2 := by
          rw [hadv]
          rcases input with (n | x) | c
          · exact h.coin middle.1
          · exact h.public.2 middle.1
          · apply h.priv middle.1
            intro v hv
            have hk := SourceReplay.known_query_run state (.inr c) v hv
            rw [hk, mem_support_pure_iff] at hm
            rw [hm]
        have hi := ih middle.1 middle.2 hin
        unfold eagerSide at hi
        rw [bind_map_left]
        have hmap := congrArg (fun law => (fun pair : FirstHit.Recorded α × Answers =>
          ((⟨pair.1.value, ⟨state, input, middle.1⟩ :: pair.1.events, pair.1.state⟩ : FirstHit.Recorded α),
            pair.2)) <$> law) hi
        simp only [← evalSPMF_map, map_bind, map_pure, Functor.map_map] at hmap
        unfold completedTail
        exact hmap
      rw [FirstHit.record_query_bind, bind_assoc, evalSPMF_bind_congr htail]
      rcases input with (n | x) | c
      · exact completion_coin inputs n next state
      · cases hc : state.2 x with
        | some v => exact completion_cached inputs _ next state v hc
        | none => exact completion_public_fresh inputs x next state h.public.1 hc
      · cases hc : state.1 c with
        | some v => exact completion_cached inputs _ next state v hc
        | none => exact completion_private_fresh inputs c next state hc
end SigGolfCandidate.T3.Security.Wots.Ref
