import SigGolfCandidate.T3.Secc.WotsTransportR3
import SigGolfCandidate.T3.Secc.WotsTransportCompletion

/-!
# F2 (S-1): R3's queries lie in its eager universe

`reference_trace_mem`: every entry of an R3 trace has its input in `referenceInputs adversary`.

Every hash query R3 makes on a table `T` (private part `t`) is a hash query of SEC's recorded ideal game run with the
private table `t` along some path (`hashInputs (tableRun t (sourceRecord idealGame (∅, ∅))) ⊆ recordedInputs`): the
adversary's queries are the same, the offline signer's answers are the real signer's answers on the path where the
public answers are `T`'s (`eval_mem_support_tableRun`), and the verifier forwards the same public queries.
`allQueries` (every query on every path) is the R3-side bookkeeping.
-/

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete (hashInputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SphincsSecurity.Concrete.hashInputs keygen verifyP expandB buildFts buildTree signPayload

/-! ## Every query on every path -/

/-- All queries of a computation, on every path. -/
def allQueries {ι α : Type} {spec : OracleSpec ι} (computation : OracleComp spec α) : Set ι :=
  OracleComp.construct (fun _ => (∅ : Set ι)) (fun input _ next => {input} ∪ ⋃ u, next u) computation

theorem allQueries_pure {ι α : Type} {spec : OracleSpec ι} (value : α) :
    allQueries (pure value : OracleComp spec α) = ∅ := rfl

theorem allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} (input : ι)
    (next : spec.Range input → OracleComp spec α) :
    allQueries (liftM (spec.query input) >>= next) = {input} ∪ ⋃ u, allQueries (next u) := by
  simp only [allQueries, OracleComp.construct_query_bind]

theorem mem_allQueries_query_bind {ι α : Type} {spec : OracleSpec ι} {input : ι}
    {next : spec.Range input → OracleComp spec α} {query : ι}
    (h : query ∈ allQueries (liftM (spec.query input) >>= next)) :
    query = input ∨ ∃ u, query ∈ allQueries (next u) := by
  rw [allQueries_query_bind] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_iUnion.mp h)

theorem recorded_mem_allQueries {ι α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec ProbComp)
    (computation : OracleComp spec α) (result : α × List ι)
    (hr : result ∈ support (simulateQ impl (SphincsSecurity.QueryCap.recorded computation))) :
    ∀ query ∈ result.2, query ∈ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind] at hr
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨answer, -, tail, htail, rfl⟩ := hr
      intro query hq
      rw [allQueries_query_bind]
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_iUnion.mpr ⟨answer, ih answer tail htail query hq⟩)

theorem allQueries_run_subset {ι α : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (computation : OracleComp spec α) (budget : Nat) :
    allQueries (SphincsSecurity.QueryCap.run selected computation budget) ⊆ allQueries computation := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      rw [SphincsSecurity.QueryCap.run_pure, allQueries_pure]
      exact Set.empty_subset _
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind, allQueries_query_bind]
      intro query hq
      by_cases hs : selected input
      · rw [if_pos hs] at hq
        cases budget with
        | zero => exact absurd hq (by rw [allQueries_pure]; exact id)
        | succ remaining =>
            rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
            · exact Or.inl rfl
            · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u remaining hu⟩)
      · rw [if_neg hs] at hq
        rcases mem_allQueries_query_bind hq with rfl | ⟨u, hu⟩
        · exact Or.inl rfl
        · exact Or.inr (Set.mem_iUnion.mpr ⟨u, ih u budget hu⟩)

theorem allQueries_bind {ι α β : Type} {spec : OracleSpec ι} (first : OracleComp spec α)
    (next : α → OracleComp spec β) (query : ι) (h : query ∈ allQueries (first >>= next)) :
    query ∈ allQueries first ∨ ∃ value ∈ support first, query ∈ allQueries (next value) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      rw [pure_bind] at h
      exact Or.inr ⟨value, by simp, h⟩
  | query_bind input rest ih =>
      rw [bind_assoc] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨u, hu⟩
      · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inl rfl)
      · rcases ih u hu with hl | ⟨value, hv, hq⟩
        · exact Or.inl (by rw [allQueries_query_bind]; exact Or.inr (Set.mem_iUnion.mpr ⟨u, hl⟩))
        · refine Or.inr ⟨value, ?_, hq⟩
          rw [mem_support_bind_iff]
          exact ⟨u, by simp, hv⟩

theorem allQueries_map {ι α β : Type} {spec : OracleSpec ι} (f : α → β) (computation : OracleComp spec α)
    (query : ι) (h : query ∈ allQueries (f <$> computation)) : query ∈ allQueries computation := by
  rw [map_eq_bind_pure_comp] at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact h
  · exact absurd h (by simp [Function.comp_def, allQueries_pure])

theorem ticks_allQueries (n : Nat) (query : RefWorld.Domain) (h : query ∈ allQueries (ticks n)) :
    query = .inr () := by
  induction n with
  | zero => exact absurd h (by simp [ticks, allQueries_pure])
  | succ n ih =>
      rw [ticks_succ] at h
      rcases mem_allQueries_query_bind h with rfl | ⟨_, hu⟩
      · rfl
      · exact ih hu

theorem ticks_support (n : Nat) (value : Unit) : value ∈ support (ticks n) := by
  cases value
  induction n with
  | zero => simp [ticks]
  | succ n ih =>
      rw [ticks_succ, mem_support_bind_iff]
      exact ⟨(), by simp, ih⟩

theorem offlineSign_support (T : Answers) (published : T3.Cache) (request : Request) (answer : Option Signature)
    (h : answer ∈ support (offlineSign T published request)) :
    answer = evalWithAnswerFn T (FullGame.authenticatedSign published request) := by
  unfold offlineSign at h
  rw [mem_support_bind_iff] at h
  obtain ⟨_, -, h⟩ := h
  rwa [mem_support_pure_iff] at h

theorem offlineSign_allQueries (T : Answers) (published : T3.Cache) (request : Request) (query : RefWorld.Domain)
    (h : query ∈ allQueries (offlineSign T published request)) : query = .inr () := by
  unfold offlineSign at h
  rcases allQueries_bind _ _ query h with h | ⟨_, _, h⟩
  · exact ticks_allQueries _ query h
  · exact absurd h (by simp [allQueries_pure])

/-! ## The recorded ideal game's hash inputs -/

theorem hashInputs_bind_left {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    hashInputs first ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input rest ih =>
      rw [bind_assoc, SphincsSecurity.Concrete.hashInputs_query_bind, SphincsSecurity.Concrete.hashInputs_query_bind]
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · left
        cases input <;> exact hx
      · right
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨u, -, hu⟩ := hx
        exact ⟨u, Finset.mem_univ _, ih u hu⟩

theorem hashInputs_bind_of_mem {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (value : α) (hv : value ∈ support first) :
    hashInputs (next value) ⊆ hashInputs (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value' =>
      rw [mem_support_pure_iff] at hv
      subst hv
      rw [pure_bind]
  | query_bind input rest ih =>
      rw [mem_support_bind_iff] at hv
      obtain ⟨u, -, hu⟩ := hv
      rw [bind_assoc]
      exact (ih u hu).trans (SphincsSecurity.Concrete.hashInputs_next_subset input (fun x => rest x >>= next) u)

theorem tableRun_query_bind {α : Type} (t : FullGame.FullTable) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) :
    Derivation.tableRun t ((liftM (T3.Spec.query input) >>= next : M α)) =
      (Derivation.tableHandler t input >>= fun answer => Derivation.tableRun t (next answer)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

theorem tableRun_bind {α β : Type} (t : FullGame.FullTable) (first : M α) (next : α → M β) :
    Derivation.tableRun t (first >>= next) =
      (Derivation.tableRun t first >>= fun value => Derivation.tableRun t (next value)) := by
  unfold Derivation.tableRun
  rw [simulateQ_bind]

theorem hashInputs_tableRun_sourceRecord {α : Type} (t : FullGame.FullTable) (program : M α)
    (state : LazyPrivate.State) :
    hashInputs (Derivation.tableRun t (FirstHit.sourceRecord program state)) =
      hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [FirstHit.sourceRecord_pure]
      unfold Derivation.tableRun
      simp only [simulateQ_pure, SphincsSecurity.Concrete.hashInputs_pure]
  | query_bind input next ih =>
      rw [tableRun_sourceRecord_query_bind, tableRun_query_bind]
      rcases input with input | c
      · rw [tableHandler_world, SphincsSecurity.Concrete.hashInputs_query_bind,
          SphincsSecurity.Concrete.hashInputs_query_bind]
        have h : ∀ u, hashInputs ((fun last => (⟨last.value, ⟨state, .inl input, u⟩ :: last.events, last.state⟩ :
            FirstHit.Recorded α)) <$>
            Derivation.tableRun t (FirstHit.sourceRecord (next u) (FirstHit.advance state (.inl input) u))) =
            hashInputs (Derivation.tableRun t (next u)) := fun u => by rw [hashInputs_map, ih]
        simp only [h]
        cases input <;> rfl
      · rw [tableHandler_private, pure_bind, pure_bind, hashInputs_map, ih]

/-- Honest evaluation under `T` follows a path of the table run whose private table is `T`'s private part. -/
theorem eval_mem_support_tableRun {α : Type} (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (program : M α) (hp : SourceReplay.HashOnly program) :
    evalWithAnswerFn T program ∈ support (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [Derivation.tableRun]
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [tableRun_query_bind, evalWithAnswerFn_bind, eval_query]
      rcases input with (n | x) | c
      · exact False.elim hi
      · rw [tableHandler_world, mem_support_bind_iff]
        exact ⟨T (.inl (.inr x)), by simp, ih _ (hn _)⟩
      · rw [tableHandler_private, pure_bind, ht c]
        exact ht c ▸ ih _ (hn _)

/-! ## R3's interaction and verdict against the recorded game -/

theorem interaction_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (published : T3.Cache) {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    (∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineInteraction T published program) →
      x ∈ hashInputs (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program))) ∧
    ∀ value ∈ support (offlineInteraction T published program),
      value ∈ support (Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [offlineInteraction_pure, FullGame.loggedWith_pure]
      refine ⟨fun x hx => absurd hx (by rw [allQueries_pure]; exact id), fun v hv => ?_⟩
      rw [mem_support_pure_iff] at hv
      subst hv
      simp [Derivation.tableRun]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [offlineInteraction_world, FullGame.loggedWith_world]
        have hreal : Derivation.tableRun t (forwardWorld input >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) =
            (liftM (OracleWorld.query input) >>= fun answer =>
              Derivation.tableRun t (FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) := by
          change Derivation.tableRun t ((liftM (T3.Spec.query (.inl input)) >>= _ : M _)) = _
          rw [tableRun_query_bind, tableHandler_world]
          rfl
        rw [hreal]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
          · cases heq
            exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind x _
          · exact SphincsSecurity.Concrete.hashInputs_next_subset input _ u ((ih u).1 x hu)
        · rw [mem_support_bind_iff] at hv ⊢
          obtain ⟨u, -, hu⟩ := hv
          exact ⟨u, by simp, (ih u).2 v hu⟩
      · rw [offlineInteraction_request, FullGame.loggedWith_request]
        have hans := eval_mem_support_tableRun T t ht _ (authenticatedSign_hashOnly published request)
        rw [tableRun_bind]
        refine ⟨fun x hx => ?_, fun v hv => ?_⟩
        · rcases allQueries_bind _ _ _ hx with h | ⟨answer, ha, h⟩
          · exact absurd (offlineSign_allQueries T published request _ h) (by simp)
          · rw [offlineSign_support T published request answer ha] at h
            have h' := (ih _).1 x (allQueries_map _ _ _ h)
            refine hashInputs_bind_of_mem _ _ _ hans ?_
            unfold Derivation.tableRun at h' ⊢
            rw [simulateQ_map, hashInputs_map]
            exact h'
        · rw [mem_support_bind_iff] at hv
          obtain ⟨answer, ha, hv⟩ := hv
          rw [offlineSign_support T published request answer ha] at hv
          rw [support_map] at hv
          obtain ⟨w, hw, rfl⟩ := hv
          rw [mem_support_bind_iff]
          refine ⟨_, hans, ?_⟩
          unfold Derivation.tableRun
          rw [simulateQ_map, support_map]
          exact ⟨w, (ih _).2 w hw, rfl⟩

theorem verdict_queries (t : FullGame.FullTable) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    ∀ x, (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (simulateQ verdictImpl program) →
      x ∈ hashInputs (Derivation.tableRun t program) := by
  induction program using OracleComp.inductionOn with
  | pure value => intro x hx; exact absurd hx (by simp [allQueries_pure])
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | y) | c
      · exact False.elim hi
      · intro x hx
        rw [simulateQ_bind, simulateQ_spec_query] at hx
        change (.inl (.inr x) : RefWorld.Domain) ∈ allQueries
          (liftM (RefWorld.query (.inl (.inr y))) >>= fun answer => simulateQ verdictImpl (next answer)) at hx
        rw [tableRun_query_bind, tableHandler_world]
        rcases mem_allQueries_query_bind hx with heq | ⟨u, hu⟩
        · cases heq
          exact SphincsSecurity.Concrete.mem_hashInputs_hash_bind _ _
        · exact SphincsSecurity.Concrete.hashInputs_next_subset (.inr y) _ u (ih u (hn u) x hu)
      · exact False.elim hi

/-- Every hash query of R3 on the table of private part `t` is a hash input of the recorded ideal game. -/
theorem offlineGame_queries (T : Answers) (t : FullGame.FullTable) (ht : ∀ c, T (.inr c) = t c)
    (adversary : AdversaryP) (x : HashInput)
    (hx : (.inl (.inr x) : RefWorld.Domain) ∈ allQueries (offlineGame T adversary)) :
    x ∈ hashInputs (Derivation.tableRun t (GameWith.idealGame PaddedGame.checker adversary)) := by
  have hkey := eval_mem_support_tableRun T t ht keygen SourceReplay.keygen_hashOnly
  unfold offlineGame at hx
  unfold GameWith.idealGame
  rw [tableRun_bind]
  refine hashInputs_bind_of_mem _ _ _ hkey ?_
  rw [tableRun_bind]
  rcases allQueries_bind _ _ _ hx with h | ⟨_, -, h⟩
  · exact absurd (ticks_allQueries _ _ h) (by simp)
  rcases allQueries_bind _ _ _ h with h | ⟨result, hres, h⟩
  · exact hashInputs_bind_left _ _ ((interaction_queries T t ht _ _).1 x h)
  · exact hashInputs_bind_of_mem _ _ _ ((interaction_queries T t ht _ _).2 result hres)
      (verdict_queries t _ (PaddedGame.verdict_public _ _) x h)

/-- **S-1**: every hash query recorded by R3 lies in R3's eager universe. -/
theorem offlineRun_query_mem (adversary : AdversaryP) (q : Nat) (T : Answers) (privateTable : FullGame.FullTable)
    (ht : ∀ c, T (.inr c) = privateTable c) (run : Option (Bool × Nat) × List RefWorld.Domain)
    (hrun : run ∈ support (offlineRun T adversary q))
    (x : HashInput) (hx : (.inl (.inr x) : RefWorld.Domain) ∈ run.2) : x ∈ referenceInputs adversary := by
  have h1 := recorded_mem_allQueries _ _ run hrun _ hx
  have h2 := allQueries_run_subset RefCharged _ q h1
  have h3 := offlineGame_queries T privateTable ht adversary x h2
  rw [← hashInputs_tableRun_sourceRecord privateTable _ (∅, ∅)] at h3
  exact Finset.mem_union_right _ (ChainGraph.program_subset_recordedInputs _ privateTable h3)

end SigGolfCandidate.T3.Security.Wots.Ref

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload

theorem traceOf_mem {T : Answers} {queries : List RefWorld.Domain} {entry : Entry}
    (h : entry ∈ traceOf T queries) : (.inl (.inr entry.1) : RefWorld.Domain) ∈ queries := by
  unfold traceOf at h
  obtain ⟨query, hq, he⟩ := List.mem_filterMap.mp h
  rcases query with (n | x) | u
  · cases he
  · simp only [Option.some.injEq] at he
    rw [← he]
    exact hq
  · cases he

/-- **S-1 (`reference_trace_mem`)**: R3's trace entries have their inputs in `referenceInputs adversary`. -/
theorem reference_trace_mem (adversary : AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) (entry : Entry) (he : entry ∈ sample.trace) :
    entry.1 ∈ referenceInputs adversary := by
  unfold referenceExperiment at hs
  rw [MonitoredPrivate.pmf_support] at hs
  unfold referenceComp at hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨privateTable, -, hs⟩ := hs
  rw [mem_support_bind_iff] at hs
  obtain ⟨publicTable, -, hs⟩ := hs
  rw [support_map] at hs
  obtain ⟨run, hrun, hsample⟩ := hs
  have htrace : sample.trace = traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2 := by
    rw [← hsample]
  rw [htrace] at he
  exact Ref.offlineRun_query_mem adversary q _ privateTable (fun _ => rfl) run hrun entry.1 (traceOf_mem he)

end SigGolfCandidate.T3.Security.Wots
