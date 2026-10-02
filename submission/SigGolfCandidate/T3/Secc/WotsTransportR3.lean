import SigGolfCandidate.T3.Secc.WotsTransportBase

/-!
# F2 (R3 side): recorded runs of R3 on a fixed table

* `recorded_bind`: `QueryCap.recorded` of a bind concatenates the recorded queries.
* `ticks_recorded`, `ticks_counted`: honest ticks are deterministic, recorded as `.inr ()`, charged one each.
* `verdict_recorded_fixed`: a public-only program forwarded by `verdictImpl` records exactly its own queries
  (`(queried T P).map embed`), with value `evalWithAnswerFn T P`; `traceOf_map_embed`.
* `cap_recorded_le`: on runs whose charged calls stay within the budget, `QueryCap.run` records the same queries.
* `offlineInteraction_world`, `offlineInteraction_request`: one-step equations of R3's interaction.
* `interaction_counted`: **value and charge of SEC's logged interaction in the fixed world equal those of R3's
  offline interaction** (`QueryCap.counted Derivation.charged` vs `QueryCap.counted RefCharged`).
-/

namespace SigGolfCandidate.T3.Security.Wots.Ref
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Recorded queries -/

theorem recorded_bind {ι α β : Type} {spec : OracleSpec ι} (computation : OracleComp spec α)
    (next : α → OracleComp spec β) :
    SphincsSecurity.QueryCap.recorded (computation >>= next) = (do
      let first ← SphincsSecurity.QueryCap.recorded computation
      let second ← SphincsSecurity.QueryCap.recorded (next first.1)
      pure (second.1, first.2 ++ second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [SphincsSecurity.QueryCap.recorded_pure]
  | query_bind input rest ih =>
      rw [bind_assoc, SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro answer
      rw [ih]
      simp only [bind_assoc, pure_bind, List.cons_append]

theorem recorded_map {ι α β : Type} {spec : OracleSpec ι} (f : α → β) (computation : OracleComp spec α) :
    SphincsSecurity.QueryCap.recorded (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> SphincsSecurity.QueryCap.recorded computation := by
  rw [map_eq_bind_pure_comp, recorded_bind]
  simp [SphincsSecurity.QueryCap.recorded_pure]

/-! ## Ticks -/

theorem ticks_succ (n : Nat) : ticks (n + 1) = (liftM (RefWorld.query (.inr ())) >>= fun _ => ticks n) := rfl

theorem ticks_recorded (T : Answers) (n : Nat) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (ticks n)) =
      pure ((), List.replicate n (.inr ())) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ticks_succ, SphincsSecurity.QueryCap.recorded_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
      change (pure () >>= fun _ => (pure ((), List.replicate n (.inr ())) : ProbComp _) >>= fun result =>
        pure (result.1, (.inr () : RefWorld.Domain) :: result.2)) = _
      simp [List.replicate_succ]

theorem ticks_counted (T : Answers) (n : Nat) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (ticks n)) = pure ((), n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ticks_succ, SphincsSecurity.QueryCap.counted_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
      change (pure () >>= fun _ => (pure ((), n) : ProbComp _) >>= fun result =>
        pure (result.1, (if RefCharged (.inr ()) then 1 else 0) + result.2)) = _
      simp only [pure_bind]
      congr 2
      simp only [RefCharged, if_true]
      omega

theorem calls_replicate_tick (n : Nat) :
    SphincsSecurity.QueryCap.calls RefCharged (List.replicate n (.inr () : RefWorld.Domain)) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, SphincsSecurity.QueryCap.calls_cons, ih]
      simp only [RefCharged, if_true]
      omega

/-! ## The verdict -/

/-- The image of a source query in R3's world (public and coin queries unchanged; private ones become ticks,
which never happens for the public-only verdict). -/
def embed : T3.Spec.Domain → RefWorld.Domain
  | .inl input => .inl input
  | .inr _ => .inr ()

theorem traceOf_map_embed (T : Answers) (queries : List T3.Spec.Domain) :
    traceOf T (queries.map embed) = entriesOf T queries := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      rcases query with (n | x) | c
      · simpa [traceOf, entriesOf, embed] using ih
      · simp only [List.map_cons, traceOf, entriesOf, embed, List.filterMap_cons] at ih ⊢
        rw [ih]
      · simp [traceOf, entriesOf, embed] at ih ⊢
        exact ih

theorem traceOf_append (T : Answers) (left right : List RefWorld.Domain) :
    traceOf T (left ++ right) = traceOf T left ++ traceOf T right := by
  simp [traceOf, List.filterMap_append]

theorem traceOf_replicate_tick (T : Answers) (n : Nat) :
    traceOf T (List.replicate n (.inr () : RefWorld.Domain)) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [traceOf, List.replicate_succ] using ih

theorem calls_map_embed_public {β : Type} (T : Answers) (program : M β) (hp : PublicVerdict.Only program) :
    SphincsSecurity.QueryCap.calls RefCharged ((SourceReplay.queried T program).map embed) =
      (SourceReplay.queried T program).length := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [SourceReplay.queried_query_bind, List.map_cons, SphincsSecurity.QueryCap.calls_cons,
        ih (T input) (hn _), List.length_cons]
      rcases input with (n | x) | c
      · exact False.elim hi
      · simp only [embed, RefCharged, if_true]; omega
      · exact False.elim hi

/-- A public-only program forwarded by `verdictImpl`: R3 records exactly its own queries, deterministically. -/
theorem verdict_recorded_fixed {β : Type} (T : Answers) (program : M β) (hp : PublicVerdict.Only program) :
    simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (simulateQ verdictImpl program)) =
      pure (evalWithAnswerFn T program, (SourceReplay.queried T program).map embed) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact False.elim hi
      · rw [simulateQ_bind, simulateQ_spec_query]
        change simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded
          (liftM (RefWorld.query (.inl (.inr x))) >>= fun answer => simulateQ verdictImpl (next answer))) = _
        rw [SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        change (pure (T (.inl (.inr x))) >>= fun answer =>
          simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (simulateQ verdictImpl (next answer))) >>=
            fun result => pure (result.1, (.inl (.inr x) : RefWorld.Domain) :: result.2)) = _
        rw [pure_bind, ih _ (hn _), pure_bind, SourceReplay.queried_query_bind, evalWithAnswerFn_bind, eval_query]
        rfl
      · exact False.elim hi

/-! ## The cap -/

theorem probEvent_bind_mono {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (r : γ → Prop) (h : ∀ x, Pr[p | f x] ≤ Pr[r | g x]) :
    Pr[p | mx >>= f] ≤ Pr[r | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

/-- On runs whose charged calls stay within the budget, the capped run records the same queries. -/
theorem cap_recorded_le {ι β : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (impl : QueryImpl spec ProbComp) (computation : OracleComp spec β) (budget : Nat)
    (event : List ι → Prop) :
    Pr[fun result => event result.2 ∧ SphincsSecurity.QueryCap.calls selected result.2 ≤ budget |
        simulateQ impl (SphincsSecurity.QueryCap.recorded computation)] ≤
      Pr[fun result => event result.2 |
        simulateQ impl (SphincsSecurity.QueryCap.recorded (SphincsSecurity.QueryCap.run selected computation budget))] := by
  induction computation using OracleComp.inductionOn generalizing budget event with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryCap.run_pure, simulateQ_pure,
        probEvent_pure]
      split_ifs with h1 h2 <;> simp_all
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            refine le_trans (le_of_eq ?_) zero_le
            rw [probEvent_eq_zero_iff]
            intro result hresult hevent
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, mem_support_bind_iff,
              mem_support_pure_iff] at hresult
            obtain ⟨answer, -, tail, -, rfl⟩ := hresult
            have h := hevent.2
            rw [SphincsSecurity.QueryCap.calls_cons, if_pos hs] at h
            omega
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
            apply probEvent_bind_mono
            intro answer
            simp only [bind_pure_comp, probEvent_map]
            refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer remaining (fun tail => event (input :: tail)))
            intro tail _
            simp only [Function.comp_apply, SphincsSecurity.QueryCap.calls_cons, if_pos hs]
            constructor
            · rintro ⟨he, hc⟩; exact ⟨he, by omega⟩
            · rintro ⟨he, hc⟩; exact ⟨he, by omega⟩
      · rw [if_neg hs, SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
        apply probEvent_bind_mono
        intro answer
        simp only [bind_pure_comp, probEvent_map]
        refine le_trans (le_of_eq (probEvent_ext ?_)) (ih answer budget (fun tail => event (input :: tail)))
        intro tail _
        simp only [Function.comp_apply, SphincsSecurity.QueryCap.calls_cons, if_neg hs, Nat.zero_add]

/-! ## R3's interaction, one query at a time -/

theorem offlineInteraction_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    offlineInteraction T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, []) := rfl

theorem offlineInteraction_world (T : Answers) (published : T3.Cache) {α : Type}
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inl input)) >>= next) =
      (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [WriterT.run_bind', WriterT.run_liftM, bind_map_left]
  apply bind_congr
  intro answer
  change id <$> _ = _
  rw [id_map]

theorem offlineInteraction_request (T : Answers) (published : T3.Cache) {α : Type}
    (request : Request) (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    offlineInteraction T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (offlineSign T published request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> offlineInteraction T published (next answer)) := by
  unfold offlineInteraction offlineImpl
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp

/-! ## The coupling: value and charge of the logged interaction -/

theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
  · exact SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region
  · intro tag
    rcases Classical.em (request.cache = published) with h | h
    · rw [if_pos h]
      exact SourceQueries.signPayload_allowed SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) request.cache request.message
    · rw [if_neg h]
      exact SourceQueries.pure_allowed _ _

/-- **Value and charge of SEC's logged interaction in the fixed world are those of R3's offline interaction.** -/
theorem interaction_counted (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
        (FullGame.loggedWith (FullGame.authenticatedSign published) program)) =
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged (offlineInteraction T published program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world, offlineInteraction_world]
        change simulateQ (fixedWorld T) (SphincsSecurity.QueryCap.counted Derivation.charged
          (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer))) = _
        rw [SphincsSecurity.QueryCap.counted_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih]
        rcases input with n | x
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
        · apply bind_congr
          intro answer
          simp [Derivation.charged, RefCharged]
      · rw [FullGame.loggedWith_request, offlineInteraction_request]
        rw [SphincsSecurity.QueryCap.counted_bind]
        unfold offlineSign
        simp only [bind_assoc, pure_bind]
        rw [SphincsSecurity.QueryCap.counted_bind]
        simp only [simulateQ_bind, fixedWorld_counted_hashOnly T _ (authenticatedSign_hashOnly published request),
          ticks_counted, pure_bind, SphincsSecurity.QueryCap.counted_map, simulateQ_map, simulateQ_pure, ih]
        rfl

end SigGolfCandidate.T3.Security.Wots.Ref
