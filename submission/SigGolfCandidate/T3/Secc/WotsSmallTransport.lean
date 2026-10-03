import SigGolfCandidate.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.WotsTransportSplit

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsSmallTransport : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsSmallTransport : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace SmallT
open _root_.SigGolfCandidate.T3.Security.Wots.Ref
structure TraceEvent where
  holds : Answers → List Entry → Prop
  mono : ∀ {T : Answers} {trace trace' : List Entry}, holds T trace → (∀ e ∈ trace, e ∈ trace') → holds T trace'
  transfer : ∀ {A T : Answers} {trace : List Entry}, ShortAgree A T →
    (∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1))) → holds A trace → holds T trace
theorem wotsPrimitiveSrc_transfer {A T : Answers} {trace : List Entry} (hAT : ShortAgree A T)
    (htrace : ∀ e ∈ trace, A (.inl (.inr e.1)) = T (.inl (.inr e.1)))
    (h : WotsExtract.WotsPrimitiveSrc A trace) : WotsExtract.WotsPrimitiveSrc T trace := by
  have hdepth : depth A = depth T := funext (depth_short hAT)
  have hfront : frontierValue A = frontierValue T := funext (frontierValue_short hAT)
  have hrefi : referenceInput A = referenceInput T := funext (referenceInput_short hAT)
  have hrefd : referenceDigits A = referenceDigits T := funext (referenceDigits_short hAT)
  rcases h with ⟨L, hsrc, hL⟩ | hS | ⟨a, hsrc, ha⟩ | ⟨a, b, hsa, hsb, hab, ha, hb⟩ | ⟨a, hsrc, ha, hc⟩
  · refine Or.inl ⟨L, hsrc, ?_⟩
    simpa only [EncodingMatchAt, hrefi, hrefd] using hL
  · refine Or.inr (Or.inl ?_)
    obtain ⟨position, input, answer, hmem, hpos, hbounded, hsource, hclass, hhit⟩ := hS
    refine ⟨position, input, answer, hmem, hpos, hbounded, hsource, ?_, ?_⟩
    · cases position <;> simpa only [StructuralClass, OtherChainRow, hdepth] using hclass
    · rw [← honestInput_short hAT position hbounded]
      obtain ⟨hne, heq⟩ := hhit
      refine ⟨hne, ?_⟩
      rw [← htrace (input, answer) hmem, ← hAT.public _ (honestInput_length A position)]
      exact heq
  · refine Or.inr (Or.inr (Or.inl ⟨a, hsrc, ?_⟩))
    simpa only [TwoEdgeAt, hdepth, hfront] using ha
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsa, hsb, hab, ?_, ?_⟩)))
    · simpa only [ContactAt, hdepth, hfront] using ha
    · simpa only [ContactAt, hdepth, hfront] using hb
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hsrc, ?_, ?_⟩)))
    · simpa only [MarkerAt, hrefi, hrefd] using ha
    · simpa only [ContactAt, hdepth, hfront] using hc
def srcEvent : TraceEvent where
  holds := WotsExtract.WotsPrimitiveSrc
  mono := fun h hsub => WotsExtract.WotsPrimitiveSrc.mono h hsub
  transfer := fun hAT htrace h => wotsPrimitiveSrc_transfer hAT htrace h
def VerifierEv (Ev : TraceEvent) (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    Ev.holds answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
def CaseABEvAt (Ev : TraceEvent) (adversary : AdversaryP) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  ∀ generated interaction checked, GameSplit adversary result generated interaction checked →
    ∀ forgery, interaction.value.1 = some forgery → VerifierEv Ev answers generated.value.1 forgery
def CaseABEv (Ev : TraceEvent) (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEvAt Ev adversary (QueryRecorded.recordedTrace z.1) z.2
def GoodEv (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (answers : Answers) :
    Prop :=
  result.value = true ∧ chargeSum result.events ≤ q ∧ CaseABEvAt Ev adversary result answers
def PsiEv (Ev : TraceEvent) (T : Answers) (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true ∧
    Ev.holds T (entriesOf T (SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result)))
theorem psiEv_of_verifierEv (Ev : TraceEvent) (A T : Answers) (publicKey : Digest)
    (result : Option ForgeryP × QueryLog Requests) (hshort : ShortAgree A T)
    (hverdict : ∀ query ∈ SourceReplay.queried T (GameWith.verdict PaddedGame.checker publicKey result),
      A query = T query)
    (haccept : evalWithAnswerFn T (GameWith.verdict PaddedGame.checker publicKey result) = true)
    (hab : ∀ forgery, result.1 = some forgery → VerifierEv Ev A publicKey forgery) :
    PsiEv Ev T publicKey result := by
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
  change Ev.holds A (entriesOf A (SourceReplay.queried A (verifyP m publicKey w))) at hprim
  rw [he] at hprim
  have hprimT := Ev.transfer hshort (fun e he' => ?_) hprim
  · exact Ev.mono hprimT (WotsExtract.entriesOf_mono fun query hq' => hsub query (hqsub query hq'))
  · obtain ⟨hmem, -⟩ := WotsExtract.mem_entriesOf_iff.mp (show (e.1, e.2) ∈ _ from he')
    exact hagree _ hmem
theorem goodEv_imp (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers)
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi : interaction ∈ support (fixedInteraction adversary T))
    (hgood : GoodEv Ev adversary q (combine T interaction) (cut (combine T interaction).state T)) :
    PsiEv Ev T (evalWithAnswerFn T keygen).1 interaction.value ∧
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
  refine ⟨psiEv_of_verifierEv Ev (cut (verdictRecord T interaction).state T) T _ interaction.value
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
theorem offlineEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun x => PsiEv Ev T (evalWithAnswerFn T keygen).1 x.1 ∧
        keygenCharge T + x.2 + verdictCharge T (evalWithAnswerFn T keygen).1 x.1 ≤ q |
      simulateQ (refImpl T) (SphincsSecurity.QueryCap.counted RefCharged
        (offlineInteraction T (evalWithAnswerFn T keygen).2
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)))] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  refine le_trans ?_ (cap_recorded_le RefCharged (refImpl T) (offlineGame T adversary) q
    (fun queries => Ev.holds T (traceOf T queries)))
  rw [← SphincsSecurity.QueryCap.recorded_counted, simulateQ_map, probEvent_map]
  unfold offlineGame
  rw [recorded_bind, simulateQ_bind, ticks_recorded, pure_bind, recorded_bind, simulateQ_bind]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc]
  simp only [verdict_recorded_fixed T _ (PaddedGame.verdict_public _ _), pure_bind]
  rw [bind_pure_comp, probEvent_map]
  apply probEvent_mono
  rintro ⟨result, queries⟩ - ⟨⟨hacc, hprim⟩, hcharge⟩
  refine ⟨?_, ?_⟩
  · change Ev.holds T (traceOf T (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))))
    rw [traceOf_append, traceOf_append, traceOf_replicate_tick, traceOf_map_embed]
    exact Ev.mono hprim (fun e he => List.mem_append_right _ (List.mem_append_right _ he))
  · change SphincsSecurity.QueryCap.calls RefCharged (List.replicate (keygenCharge T) (.inr ()) ++ (queries ++
      List.map embed (SourceReplay.queried T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)))) ≤ q
    rw [calls_append, calls_append, calls_replicate_tick, calls_map_embed_public T _ (PaddedGame.verdict_public _ _)]
    unfold verdictCharge at hcharge
    simp only at hcharge
    omega
theorem fixed_gameEv_le (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (T : Answers) :
    Pr[fun result => GoodEv Ev adversary q result (cut result.state T) |
        fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun run => Ev.holds T (traceOf T run.2) | offlineRun T adversary q] := by
  rw [fixed_game_eq, probEvent_map]
  refine le_trans (probEvent_mono fun interaction hi hgood => goodEv_imp Ev adversary q T interaction hi hgood) ?_
  have hcount := fixedRecord_counted T (FullGame.loggedWith (FullGame.authenticatedSign
    (evalWithAnswerFn T keygen).2) (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2))
    (pureRecord T keygen (∅, ∅)).state
  rw [interaction_counted] at hcount
  refine le_trans (le_of_eq ?_) (offlineEv_le Ev adversary q T)
  rw [← hcount, probEvent_map]
  rfl
theorem caseABEv_le_recorded (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 | recordedCompleted adversary] := by
  calc _ ≤ Pr[fun z => GoodEv Ev adversary q (QueryRecorded.recordedTrace z.1) z.2 |
        SeccLaw.completedExperiment adversary q hq] := by
        apply pmf_probEvent_mono
        intro z hz hev
        obtain ⟨hwin, hab⟩ := hev
        have hr := (SeccLaw.completed_agrees adversary q hq z hz).1
        have hc := PaddedGame.traced_cost_coherent adversary q hq z.1 hr
        refine ⟨hwin.1, ?_, hab⟩
        have h := hwin.2.1
        rw [hc] at h
        exact h
    _ = Pr[fun pair => GoodEv Ev adversary q pair.1 pair.2 |
        (fun z => (QueryRecorded.recordedTrace z.1, z.2)) <$> SeccLaw.completedExperiment adversary q hq] := by
        rw [probEvent_map]
        rfl
    _ = _ := by
        rw [completed_map, MonitoredPrivate.event_lift]
theorem eagerEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) :
    Pr[fun pair => GoodEv Ev adversary q pair.1 (cut pair.1.state pair.2) |
        eagerSide (referenceInputs adversary) (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceComp adversary q] := by
  unfold eagerSide referenceComp
  apply Ref.probEvent_bind_mono
  intro privateTable
  apply Ref.probEvent_bind_mono
  intro publicTable
  rw [probEvent_map, probEvent_map, fillAnswers_empty]
  exact fixed_gameEv_le Ev adversary q _
theorem caseABEv_le_reference (Ev : TraceEvent) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABEv Ev adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => Ev.holds sample.answers sample.trace | referenceExperiment adversary q] := by
  refine (caseABEv_le_recorded Ev adversary q hq).trans ?_
  rw [recorded_eq_eager adversary (GoodEv Ev adversary q)]
  refine (eagerEv_le_reference Ev adversary q).trans (le_of_eq ?_)
  unfold referenceExperiment
  rw [MonitoredPrivate.event_lift]
end SmallT
open SmallT
abbrev VerifierWotsSrc (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  VerifierEv srcEvent answers publicKey forgery
abbrev CaseABSrc (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  CaseABEv srcEvent adversary z
theorem caseABSrc_le_reference (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[fun sample => WotsExtract.WotsPrimitiveSrc sample.answers sample.trace | referenceExperiment adversary q] :=
  caseABEv_le_reference srcEvent adversary q hq
theorem completed_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) :
    CaseABSrc adversary z ∨ CaseCFreshPinned adversary z ∨ CaseCSignedPinned adversary z := by
  by_cases hab : CaseABSrc adversary z
  · exact Or.inl hab
  right
  unfold CaseABSrc CaseABEv CaseABEvAt at hab
  push Not at hab
  obtain ⟨generated, interaction, checked, hsplit, forgery, hf, hnot⟩ := hab
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  set result := QueryRecorded.recordedTrace z.1 with hresult
  have hrs : ∀ input answer, SourceReplay.known result.state input = some answer → z.2 input = answer := ha
  have hsplit' := hsplit
  obtain ⟨hg, hi, hc, heq⟩ := hsplit'
  have hstate : result.state = checked.state := by rw [heq]
  have hvalue : result.value = checked.value := by rw [heq]
  have hgext : SourceReplay.Extends generated.state result.state :=
    (SourceReplay.run_extends _ generated.state (interaction.value, interaction.state)
      (FirstHit.recorded_support _ _ _ hi)).trans hsplit.extends
  have hgen : evalWithAnswerFn z.2 keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hrs input answer (SourceReplay.known_mono generated.state result.state hgext hk))
  have hpk : generated.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → z.2 input = answer := by
    rw [← hstate]; exact hrs
  have hwin : checked.value = true := by rw [← hvalue]; exact hclean.1
  obtain ⟨hlen, forgery', hf', hfresh, message, witness, hof, hconc⟩ :=
    PaddedExtraction.verdict_recorded generated.value.1 interaction.value interaction.state checked hc z.2 hac hpk hwin
  have hff : forgery' = forgery := Option.some.inj (hf'.symm.trans hf)
  subst hff
  have hvd : evalWithAnswerFn z.2 (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value) =
      true := by
    rw [(SourceReplay.resolves_of_run _ (Ref.verdict_hashOnly _ _) interaction.state (checked.value, checked.state)
      (FirstHit.recorded_support _ _ _ hc)).eval z.2 hac]
    exact hwin
  obtain ⟨forgery'', hf'', hcheck, -⟩ := Ref.verdict_accepts z.2 _ _ hvd
  obtain ⟨-, message', witness', hof', hv, -⟩ := PaddedExtraction.check_accepting z.2 _ _ forgery'' hcheck
  have hff' : forgery'' = forgery' := Option.some.inj (hf''.symm.trans hf')
  subst hff'
  obtain ⟨rfl, rfl⟩ := Ref.witnessOf_unique hof' hof
  obtain ⟨N, hdc, hN, -, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_src z.2 message' generated.value.1 witness' hpk hv
  rcases hcase with hprim | ⟨hgood, hfts⟩
  · exact absurd ⟨message', witness', hof', hv, hprim⟩ hnot
  obtain ⟨N', hdc', hN', hevent, hS', -⟩ := hconc
  have hNN : N' = N := hN'.symm.trans hN
  subst hNN
  have hCat : BPB.CaseCAt z.2 message' witness' result.events := by
    refine ⟨N', hdc, hN, ?_, hS, by simpa only [← hN] using verifyP_digestGate z.2 message' generated.value.1 witness' hv, hgood, hfts⟩
    obtain ⟨prior, hp⟩ := hevent
    refine ⟨prior, ?_⟩
    rw [heq]
    exact List.mem_append_right _ (List.mem_append_right _ hp)
  by_cases hsigned : BPB.SignedDigest interaction.value.2 message' witness'
  · exact Or.inr ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
  · exact Or.inl ⟨generated, interaction, checked, hsplit, hpk, hlen, _, hf', hfresh, message', witness',
      hof', hsigned, hCat⟩
end SigGolfCandidate.T3.Security.Wots
