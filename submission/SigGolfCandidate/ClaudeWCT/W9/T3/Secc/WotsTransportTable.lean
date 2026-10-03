import SigGolfCandidate.T3.Secc.WotsTransportTable
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportR3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportShort
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinate
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
def CaseABAt (adversary : AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) : Prop :=
  ∀ generated interaction checked, GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → VerifierWots answers generated.value.1 forgery
def CaseAB (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  CaseABAt adversary (QueryRecorded.recordedTrace z.1) z.2
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
def Good (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) : Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABAt adversary result answers
theorem verdict_hashOnly (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) :
    Security.SourceReplay.HashOnly (GameWith.verdict PaddedGame.checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (PaddedExtraction.check_hashOnly publicKey result.2 forgery)
        fun _ => SourceQueries.pure_allowed _ _
def Psi (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true ∧
    WotsPrimitive T (entriesOf T (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)))
noncomputable def verdictCharge (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Nat :=
  (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)).length
theorem verdict_accepts (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests)
    (h : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true) :
    ∃ forgery, result.1 = some forgery ∧
      evalWithAnswerFn T (checkForgeryP publicKey result.2 forgery) = true ∧
      ∀ query ∈ SourceReplay.queried T (checkForgeryP publicKey result.2 forgery),
        query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result) := by
  cases hf : result.1 with
  | none =>
      simp only [GameWith.verdict, hf, evalWithAnswerFn_pure] at h
      exact absurd h (by decide)
  | some forgery =>
      refine ⟨forgery, rfl, ?_, ?_⟩
      · simp only [GameWith.verdict, hf, PaddedGame.checker, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      · intro query hq
        simp only [GameWith.verdict, hf, PaddedGame.checker, SourceReplay.queried_bind, SourceReplay.queried_pure,
          List.append_nil]
        exact hq
theorem witnessOf_unique {answers : Answers} {publicKey : Digest} {forgery : ForgeryP} {m m' : Message}
    {w w' : WBytes} (h : PaddedExtraction.WitnessOf answers publicKey forgery m w)
    (h' : PaddedExtraction.WitnessOf answers publicKey forgery m' w') : m = m' ∧ w = w' := by
  cases forgery with
  | witness message witness =>
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩
  | signature message signature =>
      obtain ⟨rfl, hw⟩ := h
      obtain ⟨rfl, hw'⟩ := h'
      exact ⟨rfl, Option.some.inj (hw.symm.trans hw')⟩
theorem psi_of_verifierWots (A T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests)
    (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → VerifierWots A publicKey forgery) :
    Psi T publicKey result := by
  refine ⟨haccept, ?_⟩
  obtain ⟨forgery, hf, hcheck, hsub⟩ := verdict_accepts T publicKey result haccept
  obtain ⟨-, m', w', hof', -, hqsub⟩ := PaddedExtraction.check_accepting T publicKey result.2 forgery hcheck
  obtain ⟨m, w, hof, -, hprim⟩ := hab forgery hf
  have hofT : PaddedExtraction.WitnessOf T publicKey forgery m w := by
    cases forgery with
    | witness message witness => exact hof
    | signature message signature =>
        obtain ⟨hm, hw⟩ := hof
        refine ⟨hm, ?_⟩
        rw [← hw]
        symm
        apply (eval_congr_queried _ A T fun query hq => hverdict query (hsub query ?_)).1
        simp only [checkForgeryP, SourceReplay.queried_bind]
        exact List.mem_append_left _ hq
  obtain ⟨rfl, rfl⟩ := witnessOf_unique hofT hof'
  have hagree : ∀ query ∈ SourceReplay.queried T (verifyP m publicKey w), A query = T query :=
    fun query hq => hverdict query (hsub query (hqsub query hq))
  have hq := (eval_congr_queried _ A T hagree).2
  have he : entriesOf A (SourceReplay.queried A (verifyP m publicKey w)) =
      entriesOf T (SourceReplay.queried T (verifyP m publicKey w)) := by
    rw [hq]
    exact entriesOf_congr A T _ hagree
  change WotsPrimitive A (entriesOf A (SourceReplay.queried A (verifyP m publicKey w))) at hprim
  rw [he] at hprim
  have hprimT := WotsPrimitive.transfer hshort (fun e he' => ?_) hprim
  · exact hprimT.mono (WotsExtract.entriesOf_mono fun query hq' => hsub query (hqsub query hq'))
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1, e.2) ∈ _ from he')
    exact hagree _ hmem
noncomputable def verdictRecord (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  pureRecord T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) interaction.state
noncomputable def combine (T : Answers) (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :
    FirstHit.Recorded Bool :=
  ⟨(verdictRecord T interaction).value,
    (pureRecord T keygen (∅, ∅)).events ++ (interaction.events ++ (verdictRecord T interaction).events),
    (verdictRecord T interaction).state⟩
noncomputable def fixedInteraction (adversary : AdversaryP) (T : Answers) :
    ProbComp (FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) :=
  fixedRecord T (FullGame.loggedWith (FullGame.authenticatedSign (evalWithAnswerFn T keygen).2)
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)) (pureRecord T keygen (∅, ∅)).state
theorem fixed_game_eq (adversary : AdversaryP) (T : Answers) :
    fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅) =
      combine T <$> fixedInteraction adversary T := by
  unfold GameWith.idealGame
  rw [fixedRecord_bind, fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, pure_bind]
  simp only [pureRecord_value]
  rw [fixedRecord_bind]
  simp only [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), pure_bind, bind_assoc]
  unfold fixedInteraction combine verdictRecord
  rw [map_eq_bind_pure_comp]
  rfl
theorem good_imp (adversary : AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (fixedInteraction adversary T))
    (hgood : Good adversary q (combine T interaction) (cut (combine T interaction).state T)) :
    Psi T (evalWithAnswerFn T keygen).1 interaction.value ∧
      keygenCharge T + chargeSum interaction.events +
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value ≤ q := by
  have hg0val : (pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen := pureRecord_value T keygen (∅, ∅)
  have hg0 : pureRecord T keygen (∅, ∅) ∈ support (fixedRecord T keygen (∅, ∅)) := by
    rw [fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]
  obtain ⟨hg0rec, hag0⟩ := fixedRecord_mem_record T keygen (∅, ∅) (agrees_empty T) _ hg0
  unfold fixedInteraction at hi
  rw [← hg0val] at hi
  obtain ⟨hirec, hagi⟩ := fixedRecord_mem_record T _ _ hag0 interaction hi
  have hci : verdictRecord T interaction ∈ support (fixedRecord T (GameWith.verdict PaddedGame.checker
      (pureRecord T keygen (∅, ∅)).value.1 interaction.value) interaction.state) := by
    rw [fixedRecord_hashOnly T _ (verdict_hashOnly _ _), mem_support_pure_iff, hg0val]
    rfl
  obtain ⟨hcirec, -⟩ := fixedRecord_mem_record T _ interaction.state hagi _ hci
  have hsplit : GameSplit adversary (combine T interaction) (pureRecord T keygen (∅, ∅)) interaction
      (verdictRecord T interaction) := ⟨hg0rec, hirec, hcirec, rfl⟩
  obtain ⟨hwin, hcharge, hab⟩ := hgood
  have hacc : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1
      interaction.value) = true := by
    rw [← pureRecord_value]
    exact hwin
  rw [hg0val] at hcirec
  have hknown := FirstHit.recorded_query_known _ (verdict_hashOnly _ _) interaction.state _ hcirec
  have hinputs : (verdictRecord T interaction).events.map FirstHit.QueryEvent.input =
      SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value) :=
    pureRecord_inputs T _ interaction.state
  have hverdict : ∀ query ∈ SourceReplay.queried T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 interaction.value),
      cut (verdictRecord T interaction).state T query = T query := by
    intro query hq
    rw [← hinputs] at hq
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hq
    apply cut_cached
    intro x hx
    have hk := (hknown event hevent).1
    rcases event with ⟨before, input, answer⟩
    change input = .inl (.inr x) at hx
    subst hx
    change (verdictRecord T interaction).state.2 x = some answer at hk
    rw [hk]
    rfl
  refine ⟨psi_of_verifierWots (cut (verdictRecord T interaction).state T) T _ interaction.value
    (cut_shortAgree _ _) hverdict hacc ?_, ?_⟩
  · intro forgery hf
    have h := hab _ interaction _ hsplit forgery hf
    rw [hg0val] at h
    exact h
  · have hk : chargeSum (pureRecord T keygen (∅, ∅)).events = keygenCharge T :=
      pureRecord_charge T keygen SourceReplay.keygen_hashOnly (∅, ∅)
    have hv : chargeSum (verdictRecord T interaction).events =
        verdictCharge T (evalWithAnswerFn T keygen).1 interaction.value :=
      pureRecord_charge T _ (verdict_hashOnly _ _) interaction.state
    have hc : chargeSum (combine T interaction).events = chargeSum (pureRecord T keygen (∅, ∅)).events +
        (chargeSum interaction.events + chargeSum (verdictRecord T interaction).events) := by
      simp only [combine, chargeSum_append]
    omega
theorem offline_le (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => Psi T (evalWithAnswerFn T keygen).1 x.1 ∧
        keygenCharge T + x.2 + verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => WotsPrimitive T (traceOf T run.2) | offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (offlineGame T adversary) q
    (fun queries => WotsPrimitive T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change WotsPrimitive T (traceOf T (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact hprim.mono (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PaddedGame.verdict_public _ _)]
    unfold verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_game_le (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => Good adversary q result (cut result.state T) |
        fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => WotsPrimitive T (traceOf T run.2) | offlineRun T adversary q] := by
  rw [fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => good_imp adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offline_le adversary q T)
  rw [← hcount, probEvent_map]
  rfl
end Ref
end ClaudeWCT.W9.T3.Security.Wots
