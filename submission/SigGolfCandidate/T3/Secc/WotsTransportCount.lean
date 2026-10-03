import SigGolfCandidate.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransportCount : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCount : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def refCount (cls : Answers → T3.Spec.Domain → Prop) (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (cls sample.answers (.inl (.inr e.1)))).length
def ShortCongruent (cls : Answers → T3.Spec.Domain → Prop) : Prop :=
  ∀ A T, Ref.ShortAgree A T → ∀ input, cls A input ↔ cls T input
namespace Ref
noncomputable def cappedCount {ι : Type} (selected : ι → Prop) [DecidablePred selected] (cls : ι → Prop) :
    Nat → List ι → Nat
  | _, [] => 0
  | budget, input :: rest =>
      if selected input then
        match budget with
        | 0 => 0
        | remaining + 1 => (if cls input then 1 else 0) + cappedCount selected cls remaining rest
      else cappedCount selected cls budget rest
section Capped
variable {ι : Type} (selected : ι → Prop) [DecidablePred selected] (cls : ι → Prop)
theorem cappedCount_cons_def (budget : Nat) (input : ι) (rest : List ι) :
    cappedCount selected cls budget (input :: rest) =
      if selected input then
        (match budget with
        | 0 => 0
        | remaining + 1 => (if cls input then 1 else 0) + cappedCount selected cls remaining rest)
      else cappedCount selected cls budget rest := rfl
theorem cappedCount_zero (inputs : List ι) : cappedCount selected cls 0 inputs = 0 := by
  induction inputs with
  | nil => rfl
  | cons input rest ih =>
      rw [cappedCount_cons_def]
      by_cases hs : selected input
      · rw [if_pos hs]
      · rw [if_neg hs]
        exact ih
theorem cappedCount_cons (budget : Nat) (input : ι) (rest : List ι) :
    cappedCount selected cls budget (input :: rest) =
      (if selected input ∧ 0 < budget ∧ cls input then 1 else 0) +
        cappedCount selected cls (budget - if selected input then 1 else 0) rest := by
  rw [cappedCount_cons_def]
  by_cases hs : selected input
  · rw [if_pos hs, if_pos hs]
    cases budget with
    | zero =>
        rw [if_neg (show ¬(selected input ∧ 0 < 0 ∧ cls input) from fun h => absurd h.2.1 (Nat.lt_irrefl 0)),
          Nat.zero_sub, cappedCount_zero]
    | succ remaining =>
        show (if cls input then 1 else 0) + cappedCount selected cls remaining rest = _
        rw [Nat.add_sub_cancel]
        by_cases hc : cls input
        · rw [if_pos hc, if_pos (show selected input ∧ 0 < remaining + 1 ∧ cls input from ⟨hs, Nat.succ_pos _, hc⟩)]
        · rw [if_neg hc, if_neg (show ¬(selected input ∧ 0 < remaining + 1 ∧ cls input) from fun h => hc h.2.2)]
  · rw [if_neg hs, if_neg hs, if_neg (show ¬(selected input ∧ 0 < budget ∧ cls input) from fun h => hs h.1),
      Nat.sub_zero, Nat.zero_add]
theorem cappedCount_append (budget : Nat) (left right : List ι) :
    cappedCount selected cls budget (left ++ right) =
      cappedCount selected cls budget left +
        cappedCount selected cls (budget - SphincsSecurity.QueryCap.calls selected left) right := by
  induction left generalizing budget with
  | nil => simp [cappedCount, SphincsSecurity.QueryCap.calls_nil]
  | cons input rest ih =>
      rw [List.cons_append, cappedCount_cons, cappedCount_cons, ih, SphincsSecurity.QueryCap.calls_cons,
        Nat.sub_sub, Nat.add_assoc]
theorem cappedCount_le_calls (budget : Nat) (inputs : List ι) :
    cappedCount selected cls budget inputs ≤ SphincsSecurity.QueryCap.calls selected inputs := by
  induction inputs generalizing budget with
  | nil => exact le_rfl
  | cons input rest ih =>
      rw [cappedCount_cons, SphincsSecurity.QueryCap.calls_cons]
      have h := ih (budget - if selected input then 1 else 0)
      by_cases hs : selected input
      · rw [if_pos hs] at h ⊢
        split_ifs <;> omega
      · rw [if_neg hs] at h ⊢
        rw [if_neg (show ¬(selected input ∧ 0 < budget ∧ cls input) from fun h' => hs h'.1)]
        omega
end Capped
theorem expectedValue_const_add {α : Type} (mx : ProbComp α) (c : ℝ≥0∞) (g : α → ℝ≥0∞) :
    expectedValue mx (fun x => c + g x) = c + expectedValue mx g := by
  rw [expectedValue_add, expectedValue_const probFailure_eq_zero]
theorem expectedValue_zero {α : Type} (mx : ProbComp α) : expectedValue mx (fun _ => (0 : ℝ≥0∞)) = 0 := by
  simp [expectedValue_def]
theorem cap_cappedCount {ι β : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    (cls : ι → Prop) (impl : QueryImpl spec ProbComp) (computation : OracleComp spec β) (budget : Nat) :
    expectedValue (simulateQ impl (SphincsSecurity.QueryCap.recorded
        (SphincsSecurity.QueryCap.run selected computation budget)))
        (fun result => (cappedCount selected cls budget result.2 : ℝ≥0∞)) =
      expectedValue (simulateQ impl (SphincsSecurity.QueryCap.recorded computation))
        (fun result => (cappedCount selected cls budget result.2 : ℝ≥0∞)) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      simp only [SphincsSecurity.QueryCap.run_pure, SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        expectedValue_pure, cappedCount]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            simp only [cappedCount_zero, Nat.cast_zero, expectedValue_zero]
        | succ remaining =>
            rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
            simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure]
            congr 1
            funext answer
            simp only [cappedCount_cons_def, if_pos hs, Nat.cast_add]
            rw [expectedValue_const_add, expectedValue_const_add, ih answer remaining]
      · rw [if_neg hs, SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryCap.recorded_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure]
        congr 1
        funext answer
        simp only [cappedCount_cons_def, if_neg hs]
        exact ih answer budget
def RefClass (C : T3.Spec.Domain → Prop) : RefWorld.Domain → Prop
  | .inl (.inr input) => C (.inl (.inr input))
  | _ => False
noncomputable abbrev refCharge (C : T3.Spec.Domain → Prop) (budget : Nat) (queries : List RefWorld.Domain) : Nat :=
  cappedCount RefCharged (RefClass C) budget queries
section Steps
variable (C : T3.Spec.Domain → Prop)
theorem refCharge_coin (budget n : Nat) (rest : List RefWorld.Domain) :
    refCharge C budget (.inl (.inl n) :: rest) = refCharge C budget rest := by
  rw [refCharge, cappedCount_cons_def, if_neg (show ¬RefCharged (.inl (.inl n)) from id)]
theorem refCharge_hash (budget : Nat) (input : HashInput) (rest : List RefWorld.Domain) :
    refCharge C budget (.inl (.inr input) :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + refCharge C (budget - 1) rest := by
  rw [refCharge, cappedCount_cons, if_pos (show RefCharged (.inl (.inr input)) from trivial)]
  congr 1
  by_cases h : 0 < budget ∧ C (.inl (.inr input))
  · rw [if_pos h, if_pos (show RefCharged (.inl (.inr input)) ∧ 0 < budget ∧ RefClass C (.inl (.inr input)) from
      ⟨trivial, h⟩)]
  · rw [if_neg h, if_neg (show ¬(RefCharged (.inl (.inr input)) ∧ 0 < budget ∧ RefClass C (.inl (.inr input))) from
      fun h' => h h'.2)]
theorem refCharge_tick (budget : Nat) (rest : List RefWorld.Domain) :
    refCharge C budget (.inr () :: rest) = refCharge C (budget - 1) rest := by
  rw [refCharge, cappedCount_cons, if_pos (show RefCharged (.inr ()) from trivial),
    if_neg (show ¬(RefCharged (.inr ()) ∧ 0 < budget ∧ RefClass C (.inr ())) from fun h => h.2.2), Nat.zero_add]
theorem refCharge_replicate_tick (budget n : Nat) :
    refCharge C budget (List.replicate n (.inr () : RefWorld.Domain)) = 0 := by
  induction n generalizing budget with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, refCharge_tick, ih]
theorem refCharge_append (budget : Nat) (left right : List RefWorld.Domain) :
    refCharge C budget (left ++ right) =
      refCharge C budget left + refCharge C (budget - SphincsSecurity.QueryCap.calls RefCharged left) right :=
  cappedCount_append _ _ budget left right
theorem calls_coin (n : Nat) (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inl (.inl n) :: rest) =
      SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_neg (show ¬RefCharged (.inl (.inl n)) from id), Nat.zero_add]
theorem calls_hash (input : HashInput) (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inl (.inr input) :: rest) =
      1 + SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_pos (show RefCharged (.inl (.inr input)) from trivial)]
theorem calls_tick (rest : List RefWorld.Domain) :
    SphincsSecurity.QueryCap.calls RefCharged (.inr () :: rest) = 1 + SphincsSecurity.QueryCap.calls RefCharged rest := by
  rw [SphincsSecurity.QueryCap.calls_cons, if_pos (show RefCharged (.inr ()) from trivial)]
theorem queryCharge_coin (n : Nat) : FullGame.queryCharge (.inl (.inl n)) = 0 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem queryCharge_public (input : HashInput) : FullGame.queryCharge (.inl (.inr input)) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem queryCharge_private (coordinate : Coordinate) : FullGame.queryCharge (.inr coordinate) = 1 := by
  simp [FullGame.queryCharge, Derivation.charged]
theorem classCharge_zero (events : List FirstHit.QueryEvent) : SeccLaw.classCharge C 0 events = 0 := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [SeccLaw.classCharge]
      split_ifs with h1 h2
      · have h0 : FullGame.queryCharge event.input = 0 := by omega
        rw [h0, Nat.zero_sub, ih]
      · rw [Nat.zero_sub, ih]
      · rfl
theorem classCharge_cons (budget : Nat) (event : FirstHit.QueryEvent) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) =
      (if FullGame.queryCharge event.input ≤ budget ∧ C event.input then FullGame.queryCharge event.input else 0) +
        SeccLaw.classCharge C (budget - FullGame.queryCharge event.input) rest := by
  simp only [SeccLaw.classCharge]
  by_cases h1 : FullGame.queryCharge event.input ≤ budget
  · rw [if_pos h1]
    by_cases h2 : C event.input
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), Nat.sub_eq_zero_of_le (by omega), classCharge_zero]
theorem classCharge_coin (budget n : Nat) (event : FirstHit.QueryEvent) (he : event.input = .inl (.inl n))
    (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) = SeccLaw.classCharge C budget rest := by
  rw [classCharge_cons, he, queryCharge_coin, Nat.sub_zero]
  split_ifs <;> exact Nat.zero_add _
theorem classCharge_public (budget : Nat) (input : HashInput) (event : FirstHit.QueryEvent)
    (he : event.input = .inl (.inr input)) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (event :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + SeccLaw.classCharge C (budget - 1) rest := by
  rw [classCharge_cons, he, queryCharge_public]
  rfl
theorem classCharge_coin_mk (budget n : Nat) (before : LazyPrivate.State) (answer : T3.Spec.Range (.inl (.inl n)))
    (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (⟨before, .inl (.inl n), answer⟩ :: rest) = SeccLaw.classCharge C budget rest :=
  classCharge_coin C budget n _ rfl rest
theorem classCharge_public_mk (budget : Nat) (input : HashInput) (before : LazyPrivate.State)
    (answer : T3.Spec.Range (.inl (.inr input))) (rest : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (⟨before, .inl (.inr input), answer⟩ :: rest) =
      (if 0 < budget ∧ C (.inl (.inr input)) then 1 else 0) + SeccLaw.classCharge C (budget - 1) rest :=
  classCharge_public C budget input _ rfl rest
theorem classCharge_append (budget : Nat) (left right : List FirstHit.QueryEvent) :
    SeccLaw.classCharge C budget (left ++ right) =
      SeccLaw.classCharge C budget left + SeccLaw.classCharge C (budget - chargeSum left) right := by
  induction left generalizing budget with
  | nil => simp [SeccLaw.classCharge]
  | cons event rest ih =>
      rw [List.cons_append, classCharge_cons, classCharge_cons, ih, chargeSum_cons, Nat.sub_sub, Nat.add_assoc]
theorem refCharge_embed_le (budget : Nat) (events : List FirstHit.QueryEvent) :
    refCharge C budget (events.map fun event => embed event.input) ≤ SeccLaw.classCharge C budget events := by
  induction events generalizing budget with
  | nil => exact le_rfl
  | cons event rest ih =>
      rw [List.map_cons]
      rcases hinput : event.input with (n | x) | c
      · rw [embed, refCharge_coin, classCharge_coin C budget n event hinput]
        exact ih budget
      · rw [embed, refCharge_hash, classCharge_public C budget x event hinput]
        exact Nat.add_le_add_left (ih _) _
      · rw [embed, refCharge_tick, classCharge_cons, hinput, queryCharge_private]
        exact le_add_left (ih _)
theorem calls_embed (events : List FirstHit.QueryEvent) :
    SphincsSecurity.QueryCap.calls RefCharged (events.map fun event => embed event.input) = chargeSum events := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      rw [List.map_cons, chargeSum_cons, ← ih]
      rcases event.input with (n | x) | c
      · rw [embed, calls_coin, queryCharge_coin, Nat.zero_add]
      · rw [embed, calls_hash, queryCharge_public]
      · rw [embed, calls_tick, queryCharge_private]
end Steps
theorem interaction_count_le (T : Answers) (published : T3.Cache) (C : T3.Spec.Domain → Prop) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (state : LazyPrivate.State) (budget : Nat)
    (weight : α × QueryLog Requests → Nat → ℝ≥0∞) :
    expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (offlineInteraction T published program)))
        (fun run => (refCharge C budget run.2 : ℝ≥0∞) +
          weight run.1 (budget - SphincsSecurity.QueryCap.calls RefCharged run.2)) ≤
      expectedValue (fixedRecord T (FullGame.loggedWith (FullGame.authenticatedSign published) program) state)
        (fun result => (SeccLaw.classCharge C budget result.events : ℝ≥0∞) +
          weight result.value (budget - chargeSum result.events)) := by
  induction program using OracleComp.inductionOn generalizing state budget weight with
  | pure value =>
      rw [offlineInteraction_pure, FullGame.loggedWith_pure, fixedRecord_pure, SphincsSecurity.QueryCap.recorded_pure,
        simulateQ_pure, expectedValue_pure, expectedValue_pure]
      simp [SeccLaw.classCharge, cappedCount, SphincsSecurity.QueryCap.calls_nil]
  | query_bind input next ih =>
      rcases input with input | request
      · rw [FullGame.loggedWith_world, offlineInteraction_world]
        change expectedValue (simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded
            (liftM (RefWorld.query (.inl input)) >>= fun answer => offlineInteraction T published (next answer)))) _ ≤
          expectedValue (fixedRecord T (liftM (T3.Spec.query (.inl input)) >>= fun answer =>
            FullGame.loggedWith (FullGame.authenticatedSign published) (next answer)) state) _
        rw [SphincsSecurity.QueryCap.recorded_query_bind, fixedRecord_query_bind]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map]
        rcases input with n | x
        · change expectedValue (liftM (unifSpec.query n) : ProbComp _) _ ≤
            expectedValue (liftM (unifSpec.query n) : ProbComp _) _
          apply expectedValue_mono
          intro answer
          simp only [refCharge_coin, calls_coin, classCharge_coin_mk, chargeSum_cons, queryCharge_coin,
            Nat.zero_add]
          exact ih answer _ budget weight
        · change expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _ ≤
            expectedValue (pure (T (.inl (.inr x))) : ProbComp _) _
          rw [expectedValue_pure, expectedValue_pure]
          simp only [refCharge_hash, calls_hash, classCharge_public_mk, chargeSum_cons, queryCharge_public,
            Nat.cast_add, ← Nat.sub_sub, add_assoc]
          try simp only [expectedValue_const_add]
          exact add_le_add le_rfl (ih _ _ (budget - 1) weight)
      · rw [FullGame.loggedWith_request, offlineInteraction_request]
        unfold offlineSign
        rw [bind_assoc]
        simp only [pure_bind]
        rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_map, fixedRecord_bind,
          fixedRecord_hashOnly T _ (authenticatedSign_hashOnly published request), pure_bind]
        simp only [simulateQ_bind, simulateQ_map, simulateQ_pure, expectedValue_bind, expectedValue_pure,
          expectedValue_map, fixedRecord_map]
        rw [pureRecord_value]
        have hcharge : chargeSum (pureRecord T (FullGame.authenticatedSign published request) state).events =
            signCharge T published request :=
          pureRecord_charge T _ (authenticatedSign_hashOnly published request) state
        refine le_trans (le_of_eq ?_) (le_trans (ih (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          (pureRecord T (FullGame.authenticatedSign published request) state).state
          (budget - signCharge T published request)
          (fun value rest => weight (value.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
            value.2) rest)) ?_)
        · congr 1
          funext run
          rw [refCharge_append, calls_replicate_tick, refCharge_replicate_tick, calls_append, calls_replicate_tick,
            Nat.zero_add, Nat.sub_sub]
        · apply expectedValue_mono
          intro result
          rw [classCharge_append, chargeSum_append, hcharge, Nat.sub_sub]
          gcongr
          exact le_add_left le_rfl
theorem traceOf_coin (T : Answers) (n : Nat) (rest : List RefWorld.Domain) :
    traceOf T (.inl (.inl n) :: rest) = traceOf T rest := rfl
theorem traceOf_hash (T : Answers) (input : HashInput) (rest : List RefWorld.Domain) :
    traceOf T (.inl (.inr input) :: rest) = (input, T (.inl (.inr input))) :: traceOf T rest := rfl
theorem traceOf_tick (T : Answers) (rest : List RefWorld.Domain) : traceOf T (.inr () :: rest) = traceOf T rest := rfl
theorem traceOf_length_le (T : Answers) (queries : List RefWorld.Domain) :
    (traceOf T queries).length ≤ SphincsSecurity.QueryCap.calls RefCharged queries := by
  induction queries with
  | nil => exact le_rfl
  | cons query rest ih =>
      rcases query with (n | x) | ⟨⟩
      · rw [traceOf_coin, calls_coin]; exact ih
      · rw [traceOf_hash, calls_hash, List.length_cons]; omega
      · rw [traceOf_tick, calls_tick]; omega
theorem refCharge_eq_filter (T : Answers) (C : T3.Spec.Domain → Prop) (queries : List RefWorld.Domain)
    (budget : Nat) (h : SphincsSecurity.QueryCap.calls RefCharged queries ≤ budget) :
    refCharge C budget queries = ((traceOf T queries).filter fun e => decide (C (.inl (.inr e.1)))).length := by
  induction queries generalizing budget with
  | nil => rfl
  | cons query rest ih =>
      rcases query with (n | x) | ⟨⟩
      · rw [calls_coin] at h
        rw [refCharge_coin, traceOf_coin]
        exact ih budget h
      · rw [calls_hash] at h
        rw [refCharge_hash, traceOf_hash, List.filter_cons, ih (budget - 1) (by omega)]
        by_cases hc : C (.inl (.inr x))
        · rw [if_pos ⟨by omega, hc⟩, if_pos (decide_eq_true hc), List.length_cons]
          omega
        · rw [if_neg (fun h' => hc h'.2), if_neg (by simpa using hc), Nat.zero_add]
      · rw [calls_tick] at h
        rw [refCharge_tick, traceOf_tick]
        exact ih (budget - 1) (by omega)
theorem offlineRun_calls_le (T : Answers) (adversary : AdversaryP) (q : Nat)
    (run : Option (Bool × Nat) × List RefWorld.Domain) (hrun : run ∈ support (offlineRun T adversary q)) :
    SphincsSecurity.QueryCap.calls RefCharged run.2 ≤ q := by
  have hmem := SphincsSecurity.QueryCap.simulate_oracle_mem_support (refImpl T) _ run hrun
  exact SphincsSecurity.QueryCap.recorded_calls_le RefCharged _ (fun _ => q)
    (fun result hresult => SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
      (SphincsSecurity.QueryCap.run_queryBound RefCharged _ q) result hresult) run hmem
theorem table_count_le (adversary : AdversaryP) (q : Nat) (T : Answers) (C : T3.Spec.Domain → Prop) :
    expectedValue (offlineRun T adversary q) (fun run => (refCharge C q run.2 : ℝ≥0∞)) ≤
      expectedValue (fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅))
        (fun result => (SeccLaw.classCharge C q result.events : ℝ≥0∞)) := by
  unfold offlineRun referenceGame
  rw [cap_cappedCount RefCharged (RefClass C) (refImpl T) (offlineGame T adversary) q]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [expectedValue_bind]
  simp only [expectedValue_pure]
  rw [fixed_game_eq, expectedValue_map]
  unfold fixedInteraction
  refine le_trans (le_of_eq ?_) (le_trans (interaction_count_le T (evalWithAnswerFn T keygen).2 C
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) (pureRecord T keygen (∅, ∅)).state
    (q - keygenCharge T) (fun value rest => (refCharge C rest ((SourceReplay.queried T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 value)).map embed) : ℝ≥0∞))) ?_)
  · congr 1
    funext run
    show (refCharge C q (List.replicate (keygenCharge T) (.inr ()) ++ (run.2 ++ List.map embed
      (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 run.1)))) : ℝ≥0∞) = _
    rw [refCharge_append, refCharge_replicate_tick, calls_replicate_tick, refCharge_append, Nat.zero_add,
      Nat.cast_add]
  · apply expectedValue_mono
    intro interaction
    have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
        SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value) :=
      pureRecord_inputs T _ interaction.state
    have hv := refCharge_embed_le C (q - keygenCharge T - chargeSum interaction.events)
      (verdictRecord T interaction).events
    have hmap : (verdictRecord T interaction).events.map (fun event => embed event.input) =
        (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
          interaction.value)).map embed := by
      rw [← hinputs, List.map_map]
      rfl
    rw [hmap] at hv
    change (SeccLaw.classCharge C (q - keygenCharge T) interaction.events : ℝ≥0∞) +
        (refCharge C (q - keygenCharge T - chargeSum interaction.events) ((SourceReplay.queried T
          (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value)).map embed) : ℝ≥0∞) ≤
      (SeccLaw.classCharge C q ((pureRecord T keygen (∅, ∅)).events ++
        (interaction.events ++ (verdictRecord T interaction).events)) : ℝ≥0∞)
    rw [classCharge_append, classCharge_append, hk]
    exact_mod_cast (show _ ≤ _ by omega)
end Ref
theorem reference_trace_length (adversary : AdversaryP) (q : Nat) (sample : RefSample)
    (hs : sample ∈ (referenceExperiment adversary q).support) : sample.trace.length ≤ q := by
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
  rw [htrace]
  exact (Ref.traceOf_length_le _ run.2).trans (Ref.offlineRun_calls_le _ adversary q run hrun)
theorem refCount_le_length (cls : Answers → T3.Spec.Domain → Prop) (sample : RefSample) :
    refCount cls sample ≤ sample.trace.length :=
  List.length_filter_le _ _
theorem filter_or_length {β : Type} (p r s : β → Prop) (hs : ∀ x, s x ↔ p x ∨ r x) (hdisj : ∀ x, ¬(p x ∧ r x))
    (l : List β) :
    (l.filter fun x => decide (s x)).length =
      (l.filter fun x => decide (p x)).length + (l.filter fun x => decide (r x)).length := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.filter_cons, decide_eq_true_eq]
      by_cases hp : p x <;> by_cases hr : r x
      · exact absurd ⟨hp, hr⟩ (hdisj x)
      · rw [if_pos ((hs x).mpr (Or.inl hp)), if_pos hp, if_neg hr, List.length_cons, List.length_cons, ih]
        omega
      · rw [if_pos ((hs x).mpr (Or.inr hr)), if_neg hp, if_pos hr, List.length_cons, List.length_cons, ih]
        omega
      · rw [if_neg (fun h => ((hs x).mp h).elim hp hr), if_neg hp, if_neg hr, ih]
theorem refCount_or (P Q : Answers → T3.Spec.Domain → Prop) (hdisj : ∀ A input, ¬(P A input ∧ Q A input))
    (sample : RefSample) :
    refCount (fun A input => P A input ∨ Q A input) sample = refCount P sample + refCount Q sample := by
  unfold refCount
  exact filter_or_length (fun e : Entry => P sample.answers (.inl (.inr e.1)))
    (fun e : Entry => Q sample.answers (.inl (.inr e.1)))
    (fun e : Entry => (fun A input => P A input ∨ Q A input) sample.answers (.inl (.inr e.1))) (fun _ => Iff.rfl)
    (fun e => hdisj _ _) sample.trace
theorem reference_joint_budget (adversary : AdversaryP) (q : Nat) (A B C D : Answers → T3.Spec.Domain → Prop)
    (hAB : ∀ T input, ¬(A T input ∧ B T input)) (hAC : ∀ T input, ¬(A T input ∧ C T input))
    (hAD : ∀ T input, ¬(A T input ∧ D T input)) (hBC : ∀ T input, ¬(B T input ∧ C T input))
    (hBD : ∀ T input, ¬(B T input ∧ D T input)) (hCD : ∀ T input, ¬(C T input ∧ D T input))
    (sample : RefSample) (hs : sample ∈ (referenceExperiment adversary q).support) :
    refCount A sample + refCount B sample + refCount C sample + refCount D sample ≤ q := by
  have h1 := refCount_or A B hAB sample
  have h2 := refCount_or (fun T input => A T input ∨ B T input) C
    (fun T input h => h.1.elim (fun ha => hAC T input ⟨ha, h.2⟩) (fun hb => hBC T input ⟨hb, h.2⟩)) sample
  have h3 := refCount_or (fun T input => (A T input ∨ B T input) ∨ C T input) D
    (fun T input h => h.1.elim (fun h' => h'.elim (fun ha => hAD T input ⟨ha, h.2⟩)
      (fun hb => hBD T input ⟨hb, h.2⟩)) (fun hc => hCD T input ⟨hc, h.2⟩)) sample
  have hle := (refCount_le_length (fun T input => ((A T input ∨ B T input) ∨ C T input) ∨ D T input) sample).trans
    (reference_trace_length adversary q sample hs)
  omega
theorem pmf_tsum_eq_expectedValue {α : Type} (p : PMF α) (g : α → ℝ≥0∞) :
    ∑' x, p x * g x = expectedValue p g := by
  rw [expectedValue_def]
  congr 1
  funext x
  rw [PMF.probOutput_eq_apply]
theorem expectedValue_liftM {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) :
    expectedValue (liftM mx : PMF α) g = expectedValue mx g := by
  rw [expectedValue_def, expectedValue_def]
  congr 1
theorem completed_eager_map (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq =
      (fun x => (x.1, Ref.cut x.1.state x.2)) <$> eagerRecorded adversary := by
  apply PMF.ext
  intro y
  rw [← PMF.probOutput_eq_apply, ← PMF.probOutput_eq_apply, ← probEvent_eq_eq_probOutput,
    ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact completed_eager_cut adversary q hq (fun rec A => (rec, A) = y)
theorem reference_count_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (cls : Answers → T3.Spec.Domain → Prop) (hcls : ShortCongruent cls) :
    ∑' s, referenceExperiment adversary q s * (refCount cls s : ENNReal) ≤
      SeccLaw.expectedCharge adversary q hq (fun z input => cls z.2 input) := by
  unfold SeccLaw.expectedCharge SeccLaw.sampleCharge
  rw [pmf_tsum_eq_expectedValue, pmf_tsum_eq_expectedValue]
  have hR : expectedValue (SeccLaw.completedExperiment adversary q hq)
      (fun z => (SeccLaw.classCharge (fun input => cls z.2 input) q (QueryRecorded.recordedTrace z.1).events : ℝ≥0∞)) =
      expectedValue (eagerRecorded adversary) (fun x => (SeccLaw.classCharge (cls x.2) q x.1.events : ℝ≥0∞)) := by
    have h1 := congrArg (fun p => expectedValue p (fun y : FirstHit.Recorded Bool × Answers =>
      (SeccLaw.classCharge (cls y.2) q y.1.events : ℝ≥0∞))) (completed_eager_map adversary q hq)
    simp only [expectedValue_map] at h1
    rw [h1]
    congr 1
    funext x
    have hc : cls (Ref.cut x.1.state x.2) = cls x.2 :=
      funext fun input => propext (hcls _ _ (Ref.cut_shortAgree _ _) input)
    rw [hc]
  rw [hR]
  unfold referenceExperiment eagerRecorded
  rw [expectedValue_liftM, expectedValue_liftM]
  unfold referenceComp
  simp only [expectedValue_bind, expectedValue_map]
  apply expectedValue_mono
  intro privateTable
  apply expectedValue_mono
  intro publicTable
  refine le_trans (le_of_eq (expectedValue_congr_of_support ?_)) (Ref.table_count_le adversary q _ (cls _))
  intro run hrun
  rw [Ref.refCharge_eq_filter _ _ _ _ (Ref.offlineRun_calls_le _ _ _ run hrun)]
  rfl
theorem reference_shared_budget (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (A B C : Answers → T3.Spec.Domain → Prop) (D : SeccLaw.SampleClass)
    (hA : ShortCongruent A) (hB : ShortCongruent B) (hC : ShortCongruent C)
    (hAB : ∀ T input, ¬(A T input ∧ B T input)) (hAC : ∀ T input, ¬(A T input ∧ C T input))
    (hBC : ∀ T input, ¬(B T input ∧ C T input))
    (hAD : ∀ z input, ¬(A z.2 input ∧ D z input)) (hBD : ∀ z input, ¬(B z.2 input ∧ D z input))
    (hCD : ∀ z input, ¬(C z.2 input ∧ D z input)) :
    ∑' s, referenceExperiment adversary q s * (refCount A s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount B s : ENNReal) +
      ∑' s, referenceExperiment adversary q s * (refCount C s : ENNReal) +
      SeccLaw.expectedCharge adversary q hq D ≤ q :=
  le_trans (add_le_add (add_le_add (add_le_add (reference_count_le adversary q hq A hA)
      (reference_count_le adversary q hq B hB)) (reference_count_le adversary q hq C hC)) le_rfl)
    (SeccLaw.expectedCharge_four_le adversary q hq _ _ _ D (fun z input => hAB z.2 input)
      (fun z input => hAC z.2 input) hAD (fun z input => hBC z.2 input) hBD hCD)
end SigGolfCandidate.T3.Security.Wots
