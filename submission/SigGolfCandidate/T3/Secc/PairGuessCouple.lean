import SigGolfCandidate.T3.Secc.PairGuessSigner

/-!
# B-PAIR (3/4): the world program and the reference run are coupled

* `fixed_worldGame`: with the true FTS secrets `fts`, the world program `worldGame hU ω adversary` (trials answered
  by `fts`, disclosures by `fts`, coins uniform) is exactly the reference run `pairRun` on G's eager table
  `Omega.answers hU ω fts` — R3's offline game without cap and ticks, outputting (verdict, signing log, adversary and
  verifier entries).
* `worldGame_tracking`: on every fixed run, the probes are at most the recorded entries, and every secret whose
  honest leaf input is recorded and that no returned signature of the log opened is a world guess.
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Couple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

/-- The fixed answers of the world with the FTS secrets `fts`. -/
noncomputable abbrev fixedW (fts : FtsCoord → Digest) : QueryImpl WSpec ProbComp :=
  SecretGuessObservation.fixedAnswers coinImpl fts

theorem keygen_answers (fts : FtsCoord → Digest) :
    evalWithAnswerFn (Omega.answers hU ω fts) keygen = evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen :=
  eval_free hU ω fts (fun _ => 0) keygen_free

/-- A public query of the world with the true secrets returns the table's answer. -/
theorem fixed_hashW (fts : FtsCoord → Digest) (x : HashInput) :
    simulateQ (fixedW fts) (hashW hU ω x) = pure (Omega.answers hU ω fts (.inl (.inr x))) := by
  unfold hashW
  cases hd : decodeProbe x with
  | none =>
      rw [simulateQ_pure, answers_public hU ω (fun _ => 0) fts x hd]
  | some p =>
      have hx := eq_of_decodeProbe hd
      rw [simulateQ_bind, simulateQ_spec_query]
      change (pure (decide (fts p.1 = p.2)) >>= fun hit => simulateQ (fixedW fts) (pure (if hit then
        ω.labels (.ftsLeaf (toLeafPos p.1)) else finiteHashAnswer ∅ U ω.residual x))) = _
      rw [pure_bind, simulateQ_pure, hx, answers_probe]
      by_cases he : fts p.1 = p.2
      · simp only [he, decide_true, if_true]
      · simp only [he, decide_false, Bool.false_eq_true, if_false]

theorem overwrite_map (g : FtsCoord → Digest) (positions : List FtsCoord) (f : FtsCoord) (hf : f ∈ positions) :
    overwrite positions (positions.map g) f = g f := by
  induction positions with
  | nil => cases hf
  | cons first rest ih =>
      unfold overwrite
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      by_cases he : first = f
      · subst he
        simp
      · simp only [he, decide_false]
        exact ih (by simpa [Ne.symm he] using List.mem_cons.mp hf |>.resolve_left (Ne.symm he))

theorem fixed_disclosures (fts : FtsCoord → Digest) (positions : List FtsCoord) :
    simulateQ (fixedW fts) (positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)) =
      pure (positions.map fts) := by
  induction positions with
  | nil => rfl
  | cons first rest ih =>
      rw [List.mapM_cons, simulateQ_bind, simulateQ_spec_query]
      change (pure (fts first) >>= fun value => simulateQ (fixedW fts) (do
        let values ← rest.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest)
        pure (value :: values))) = _
      rw [pure_bind, simulateQ_bind, ih, pure_bind, simulateQ_pure, List.map_cons]

/-- The world signer with the true secrets returns the honest signature. -/
theorem fixed_signW (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) :
    simulateQ (fixedW fts) (signW hU ω published request) =
      pure (evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request)) := by
  unfold signW
  rw [simulateQ_bind, fixed_disclosures, pure_bind, simulateQ_pure]
  congr 1
  apply sign_local
  intro f hf
  exact overwrite_map fts _ f hf


/-! ### Equation lemmas of the world programs and of the reference interaction -/

theorem interactionW_pure (published : T3.Cache) {α : Type} (value : α) :
    interactionW hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl

theorem interactionW_coin (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1))) >>= fun coin =>
        interactionW hU ω published (next coin)) := rfl

theorem interactionW_public (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl

theorem interactionW_request (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signW hU ω published request >>= fun signature => interactionW hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

theorem programW_pure {β : Type} (value : β) : programW hU ω (pure value : M β) = pure (value, []) := rfl

theorem programW_public {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programW hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl

theorem interactionT_pure (T : Answers) (published : T3.Cache) {α : Type} (value : α) :
    interactionT T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl

theorem interactionT_coin (T : Answers) (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin => interactionT T published (next coin)) := rfl

theorem interactionT_public (T : Answers) (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (interactionT T published (next (T (.inl (.inr x)))) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)) := rfl

theorem interactionT_request (T : Answers) (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (interactionT T published (next (evalWithAnswerFn T (FullGame.authenticatedSign published request))) >>=
        fun rest => pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
          rest.2.1, rest.2.2)) := rfl

/-! ### The law coupling -/

theorem fixed_interactionW (fts : FtsCoord → Digest) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedW fts) (interactionW hU ω published program) =
      interactionT (Omega.answers hU ω fts) published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionW_pure, interactionT_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin, interactionT_coin, simulateQ_bind, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionW_public, interactionT_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionW_request, interactionT_request, simulateQ_bind, fixed_signW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]

theorem fixed_programW (fts : FtsCoord → Digest) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    simulateQ (fixedW fts) (programW hU ω program) =
      pure (evalWithAnswerFn (Omega.answers hU ω fts) program,
        Wots.entriesOf (Omega.answers hU ω fts) (SourceReplay.queried (Omega.answers hU ω fts) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programW_pure, simulateQ_pure]; rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih _ (hn _), pure_bind,
          simulateQ_pure, SourceReplay.queried_query_bind, evalWithAnswerFn_bind, eval_query']
        rfl
      · exact hi.elim

/-- **Coupling 1 (law).** With the true FTS secrets, the world program is the reference run on `ω`'s table. -/
theorem simulate_worldGame (fts : FtsCoord → Digest) (adversary : AdversaryP) :
    simulateQ (fixedW fts) (worldGame hU ω adversary) = pairRun (Omega.answers hU ω fts) adversary := by
  unfold worldGame pairRun
  rw [← keygen_answers hU ω fts]
  rw [simulateQ_bind, fixed_interactionW]
  apply bind_congr
  intro interaction
  rw [simulateQ_bind, fixed_programW _ _ _ _ (PaddedGame.verdict_public _ _), pure_bind, simulateQ_pure]

theorem fixed_worldGame (fts : FtsCoord → Digest) (adversary : AdversaryP) :
    Prod.fst <$> SecretGuessObservation.fixedRun env fts (worldGame hU ω adversary) init =
      𝒮[pairRun (Omega.answers hU ω fts) adversary] := by
  rw [env, SecretGuessObservation.fixedRun_projection, simulate_worldGame]

end Couple


/-! ## Tracking: probes and guesses of the fixed run -/

section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

theorem disclosed_append_left (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l1 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_left _ he, rest⟩

theorem disclosed_append_right (A : Answers) (l1 l2 : QueryLog Requests) (f : FtsCoord) (h : Disclosed A l2 f) :
    Disclosed A (l1 ++ l2) f := by
  obtain ⟨entry, he, rest⟩ := h
  exact ⟨entry, List.mem_append_right _ he, rest⟩

/-- What a segment of the fixed run did to the world state, relative to its log and its entries. -/
structure Tracks (fts : FtsCoord → Digest) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  guesses : before.guesses ⊆ after.guesses
  retired : before.retired ⊆ after.retired
  origin : ∀ f ∈ after.retired, f ∈ before.retired ∨ f ∈ after.guesses ∨ Disclosed (Omega.answers hU ω fts) log f
  queried : ∀ f answer, (probeInput f (fts f), answer) ∈ entries → f ∈ after.retired

theorem Tracks.refl (fts : FtsCoord → Digest) (state : WState) : Tracks hU ω fts state state [] [] :=
  ⟨by simp, Finset.Subset.refl _, Finset.Subset.refl _, fun _ h => Or.inl h, fun _ _ h => by cases h⟩

theorem Tracks.trans {fts : FtsCoord → Digest} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω fts s1 s2 l1 e1) (second : Tracks hU ω fts s2 s3 l2 e2) :
    Tracks hU ω fts s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, first.guesses.trans second.guesses, first.retired.trans second.retired, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · intro f hf
    rcases second.origin f hf with h | h | h
    · rcases first.origin f h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (second.guesses h))
      · exact Or.inr (Or.inr (disclosed_append_left _ _ _ _ h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (disclosed_append_right _ _ _ _ h))
  · intro f answer h
    rcases List.mem_append.mp h with h | h
    · exact second.retired (first.queried f answer h)
    · exact second.queried f answer h

theorem runWith_bind' {First Result : Type}
    (implementation : QueryImpl WSpec (StateT WState SPMF))
    (first : OracleComp WSpec First) (next : First → OracleComp WSpec Result) (state : WState) :
    runWith implementation (first >>= next) state =
      runWith implementation first state >>= fun middle => runWith implementation (next middle.1) middle.2 := by
  simp only [runWith, simulateQ_bind, StateT.run_bind]

theorem fixedRun_bind_nonzero {First Result : Type} (fts : FtsCoord → Digest) (first : OracleComp WSpec First)
    (next : First → OracleComp WSpec Result) (state : WState) (result : Result × WState)
    (hr : fixedRun env fts (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun env fts first state middle ≠ 0 ∧ fixedRun env fts (next middle.1) middle.2 result ≠ 0 := by
  unfold fixedRun at hr ⊢
  rw [runWith_bind', RetainedObservation.bind_nonzero] at hr
  exact hr

theorem fixedRun_pure_nonzero {Result : Type} (fts : FtsCoord → Digest) (value : Result) (state : WState)
    (result : Result × WState) (hr : fixedRun env fts (pure value) state result ≠ 0) : result = (value, state) := by
  unfold fixedRun at hr
  rw [SecretGuessObservation.runWith_pure] at hr
  simpa only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hr

/-- A coin query leaves the counted parts of the state unchanged. -/
theorem fixed_coin_tracks (fts : FtsCoord → Digest) (n : Nat) (state : WState) (result : Fin (n + 1) × WState)
    (hr : fixedRun env fts (liftM (WSpec.query (.inl n))) state result ≠ 0) : Tracks hU ω fts state result.2 [] [] := by
  unfold fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [fixedImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  exact Tracks.refl hU ω fts state

/-- A public query: its answer is the table's and it is one entry (one probe if it is an FTS leaf input). -/
theorem fixed_hashW_tracks (fts : FtsCoord → Digest) (x : HashInput) (state : WState) (result : HashOutput × WState)
    (hr : fixedRun env fts (hashW hU ω x) state result ≠ 0) :
    result.1 = Omega.answers hU ω fts (.inl (.inr x)) ∧ Tracks hU ω fts state result.2 [] [(x, result.1)] := by
  unfold hashW at hr
  cases hd : decodeProbe x with
  | none =>
      rw [hd] at hr
      have hres := fixedRun_pure_nonzero fts _ state result hr
      subst hres
      refine ⟨answers_public hU ω _ _ x hd, ⟨by simp, Finset.Subset.refl _, Finset.Subset.refl _,
        fun _ h => Or.inl h, ?_⟩⟩
      intro f answer h
      rw [List.mem_singleton] at h
      have hx := congrArg Prod.fst h
      simp only at hx
      rw [← hx, decodeProbe_probeInput] at hd
      cases hd
  | some p =>
      rw [hd] at hr
      have hx := eq_of_decodeProbe hd
      unfold fixedRun at hr
      rw [SecretGuessObservation.runWith_query_bind] at hr
      simp only [fixedImpl, StateT.run_mk, pure_bind, SecretGuessObservation.runWith_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst hr
      have hans : (if decide (fts p.1 = p.2) = true then ω.labels (.ftsLeaf (toLeafPos p.1))
          else finiteHashAnswer ∅ U ω.residual x) = Omega.answers hU ω fts (.inl (.inr x)) := by
        rw [hx, answers_probe]
        by_cases he : fts p.1 = p.2
        · simp only [he, decide_true, if_true]
        · simp only [he, decide_false, Bool.false_eq_true, if_false]
      refine ⟨hans, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · simp [afterTrial]
      · simp only [afterTrial]
        split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
      · simp only [afterTrial]
        split <;> simp only [Finset.subset_insert, Finset.Subset.refl]
      · intro f hf
        simp only [afterTrial] at hf ⊢
        by_cases hhit : decide (fts p.1 = p.2) = true
        · rw [if_pos hhit, Finset.mem_insert] at hf
          rcases hf with rfl | hf
          · by_cases hr : p.1 ∈ state.retired
            · exact Or.inl hr
            · exact Or.inr (Or.inl (by rw [if_pos ⟨hhit, hr⟩]; exact Finset.mem_insert_self _ _))
          · exact Or.inl hf
        · rw [if_neg hhit] at hf
          exact Or.inl hf
      · intro f answer h
        rw [List.mem_singleton] at h
        have hin := congrArg Prod.fst h
        simp only at hin
        rw [hx] at hin
        obtain ⟨rfl, hc⟩ := probeInput_injective hin
        simp only [afterTrial]
        rw [if_pos (by simp [hc])]
        exact Finset.mem_insert_self _ _

/-- A run of disclosures. -/
theorem fixed_disclosures_run (fts : FtsCoord → Digest) (positions : List FtsCoord) (state : WState)
    (result : List Digest × WState)
    (hr : fixedRun env fts (positions.mapM fun f => (liftM (WSpec.query (.inr (.inr f))) : OracleComp WSpec Digest))
      state result ≠ 0) :
    result.1 = positions.map fts ∧ result.2.probes = state.probes ∧ result.2.guesses = state.guesses ∧
      ∀ f, f ∈ result.2.retired ↔ f ∈ state.retired ∨ f ∈ positions := by
  induction positions generalizing state result with
  | nil =>
      have h := fixedRun_pure_nonzero fts _ state result hr
      subst h
      simp
  | cons first rest ih =>
      rw [List.mapM_cons] at hr
      obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
      unfold fixedRun runWith at hm
      rw [simulateQ_spec_query] at hm
      simp only [fixedImpl, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hm
      subst hm
      obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
      have h := fixedRun_pure_nonzero fts _ _ result hr
      subst h
      obtain ⟨h1, h2, h3, h4⟩ := ih _ tail ht
      refine ⟨by simp [h1], h2, h3, ?_⟩
      intro f
      rw [h4]
      simp only [afterDisclosure, Finset.mem_insert, List.mem_cons]
      tauto

/-- The world signer: its answer is the honest signature and every retired position is disclosed by it. -/
theorem fixed_signW_tracks (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) (state : WState)
    (result : Option Signature × WState) (hr : fixedRun env fts (signW hU ω published request) state result ≠ 0) :
    result.1 = evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) ∧
      Tracks hU ω fts state result.2 [⟨request, result.1⟩] [] := by
  unfold signW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
  have h := fixedRun_pure_nonzero fts _ _ result hr
  subst h
  obtain ⟨h1, h2, h3, h4⟩ := fixed_disclosures_run fts _ state middle hm
  have hsig : evalWithAnswerFn (Omega.answers hU ω (overwrite (openedFor hU ω published request) middle.1))
      (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) := by
    rw [h1]
    exact sign_local hU ω _ _ published request fun f hf => overwrite_map fts _ f hf
  refine ⟨hsig, ⟨by simp [h2], by rw [h3], fun f hf => (h4 f).mpr (Or.inl hf), ?_, fun _ _ h => by cases h⟩⟩
  intro f hf
  rcases (h4 f).mp hf with h | h
  · exact Or.inl h
  · right; right
    obtain ⟨signature, output, hs, ho, hp⟩ := sign_opened hU ω fts published request f h
    refine ⟨⟨request, _⟩, List.mem_singleton_self _, signature, output, ?_, ho, hp⟩
    change evalWithAnswerFn _ _ = some signature
    rw [hsig]
    exact hs

theorem interactionW_tracks (fts : FtsCoord → Digest) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (state : WState)
    (result : (α × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env fts (interactionW hU ω published program) state result ≠ 0) :
    Tracks hU ω fts state result.2 result.1.2.1 result.1.2.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [interactionW_pure] at hr
      have h := fixedRun_pure_nonzero fts _ state result hr
      subst h
      exact Tracks.refl hU ω fts state
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
        have h := Tracks.trans hU ω (fixed_coin_tracks hU ω fts n state middle hm) (ih middle.1 middle.2 result hr)
        simpa only [List.nil_append] using h
      · rw [interactionW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
        have h := fixedRun_pure_nonzero fts _ _ result hr
        subst h
        have h := Tracks.trans hU ω (fixed_hashW_tracks hU ω fts x state middle hm).2 (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · rw [interactionW_request] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
        have h := fixedRun_pure_nonzero fts _ _ result hr
        subst h
        have h := Tracks.trans hU ω (fixed_signW_tracks hU ω fts published request state middle hm).2 (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h

theorem programW_tracks (fts : FtsCoord → Digest) {β : Type} (program : M β) (hp : PublicVerdict.Only program)
    (state : WState) (result : (β × List Wots.Entry) × WState)
    (hr : fixedRun env fts (programW hU ω program) state result ≠ 0) :
    Tracks hU ω fts state result.2 [] result.1.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [programW_pure] at hr
      have h := fixedRun_pure_nonzero fts _ state result hr
      subst h
      exact Tracks.refl hU ω fts state
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero fts _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
        have h := fixedRun_pure_nonzero fts _ _ result hr
        subst h
        have h := Tracks.trans hU ω (fixed_hashW_tracks hU ω fts x state middle hm).2 (ih middle.1 (hn _) middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · exact hi.elim

/-- **Coupling 2 (tracking).** Every probe is a recorded entry; every undisclosed secret whose honest leaf input
is recorded is a world guess. -/
theorem worldGame_tracking (fts : FtsCoord → Digest) (adversary : AdversaryP)
    (result : (Bool × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env fts (worldGame hU ω adversary) init result ≠ 0) :
    result.2.probes ≤ result.1.2.2.length ∧
      ∀ f, GuessedIn (Omega.answers hU ω fts) result.1.2.1 result.1.2.2 f → f ∈ result.2.guesses := by
  unfold worldGame at hr
  obtain ⟨interaction, hi, hr⟩ := fixedRun_bind_nonzero fts _ _ init result hr
  obtain ⟨verdict, hv, hr⟩ := fixedRun_bind_nonzero fts _ _ _ result hr
  have h := fixedRun_pure_nonzero fts _ _ result hr
  subst h
  have t := Tracks.trans hU ω (interactionW_tracks hU ω fts _ _ init interaction hi)
    (programW_tracks hU ω fts _ (PaddedGame.verdict_public _ _) _ verdict hv)
  rw [List.append_nil] at t
  refine ⟨by simpa [init, SecretGuessObservation.initialState] using t.probes, ?_⟩
  intro f ⟨hnd, answer, he⟩
  rw [secretAt_answers] at he
  rcases t.origin f (t.queried f answer he) with h | h | h
  · simp [init, SecretGuessObservation.initialState] at h
  · exact h
  · exact absurd h hnd

end Tracking
end SigGolfCandidate.T3.Security.BPair
