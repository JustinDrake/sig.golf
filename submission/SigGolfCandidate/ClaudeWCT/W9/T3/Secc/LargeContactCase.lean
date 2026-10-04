import SigGolfCandidate.T3.Secc.WotsExtractSplit
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEventsGood
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractLayer
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractVerify
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportSplit
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufSigned
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccSufPayload
import SigGolfCandidate.ClaudeWCT.W9.New.G5.PaddedExtraction
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactMonitor
import SigGolfCandidate.T3.Secc.LargeContactChain
import SigGolfCandidate.T3.Secc.LargeContactWalk
import SigGolfCandidate.T3.Secc.LargeContactEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransport
import SigGolfCandidate.T3.Secc.LargeContactInputs
import SigGolfCandidate.T3.Secc.LargeContactCase

section











namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots (Entry entriesOf)
open SigGolfCandidate.T3.Security.WotsExtract (recordedEntries entries_recorded)
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
def VerifierWotsSrc (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP message publicKey witness)))
theorem VerifierWotsSrc.toVerifierWots {answers : Answers} {publicKey : Digest} {forgery : ForgeryP}
    (h : VerifierWotsSrc answers publicKey forgery) : VerifierWots answers publicKey forgery := by
  obtain ⟨message, witness, hof, hv, hp⟩ := h
  exact ⟨message, witness, hof, hv, hp.toPrimitive⟩
theorem verdict_accepting (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    interaction.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.1 = some forgery ∧ PaddedExtraction.Fresh interaction.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
        evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
        ∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message publicKey witness) →
          ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
            result.events := by
  cases hf : interaction.1 with
  | none =>
      simp only [GameWith.verdict, hf, FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [GameWith.verdict, hf, PaddedGame.checker] at hr
      obtain ⟨checked, hchecked, last, hlast, hvalue, hevents, hstate⟩ :=
        FirstHit.record_bind_support _ _ before result hr
      rw [FirstHit.record_pure, support_pure, Set.mem_singleton_iff] at hlast
      subst last
      simp only [List.append_nil] at hevents
      have hand : (decide (interaction.2.length ≤ 2 ^ 32) && checked.value) = true := hvalue.symm.trans hwin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hand
      obtain ⟨hlength, hcheckedWin⟩ := hand
      have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
        simpa only [hstate] using ha
      have hp := PaddedExtraction.check_hashOnly publicKey interaction.2 forgery
      have hw := (SourceReplay.resolves_of_run _ hp before (checked.value, checked.state)
        (FirstHit.recorded_support _ _ _ hchecked)).eval answers hac
      rw [hcheckedWin] at hw
      obtain ⟨hfresh, message, witness, hof, hv, hsub⟩ :=
        PaddedExtraction.check_accepting answers publicKey interaction.2 forgery hw
      refine ⟨hlength, forgery, rfl, hfresh, message, witness, hof, hv, fun input hq => ?_⟩
      obtain ⟨prior, hev⟩ := PaddedExtraction.public_occurrence _ hp before checked hchecked answers hac input
        (hsub _ hq)
      exact ⟨prior, hevents ▸ hev⟩
theorem game_accepting_linked (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        SourceReplay.Extends interaction.state result.state ∧
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        interaction.value.2.length ≤ 2 ^ 32 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
            evalWithAnswerFn answers (verifyP message generated.value.1 witness) = true ∧
            ∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message generated.value.1 witness) →
              ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
                result.events := by
  unfold GameWith.idealGame at hr
  obtain ⟨generated, hgenerated, rest, hrest, hvalue, hevents, hstate⟩ :=
    FirstHit.record_bind_support _ _ (∅, ∅) result hr
  obtain ⟨interaction, hinteraction, checked, hchecked, hrestValue, hrestEvents, hrestState⟩ :=
    FirstHit.record_bind_support _ _ generated.state rest hrest
  have hgeneratedState : SourceReplay.Extends generated.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ generated.state (rest.value, rest.state)
      (FirstHit.recorded_support _ _ _ hrest)
  have hinteractionState : SourceReplay.Extends interaction.state result.state := by
    rw [hstate, hrestState]
    exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
      (FirstHit.recorded_support _ _ _ hchecked)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.hashOnly_keygen (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hgenerated)).eval answers
        (fun input answer hk => ha input answer
          (SourceReplay.known_mono generated.state result.state hgeneratedState hk))
  have hpk : generated.value.1 = Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk answers
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
    simpa only [hstate, hrestState] using ha
  have hw : checked.value = true := hrestValue.symm.trans (hvalue.symm.trans hwin)
  obtain ⟨hlength, forgery, hforgery, hfresh, message, witness, hof, hv, hrec⟩ :=
    verdict_accepting generated.value.1 interaction.value interaction.state checked hchecked answers hac hw
  refine ⟨generated, hgenerated, interaction, hinteraction, hinteractionState, hpk, hlength, forgery, hforgery,
    hfresh, message, witness, hof, hv, fun input hq => ?_⟩
  obtain ⟨prior, hev⟩ := hrec input hq
  refine ⟨prior, ?_⟩
  rw [hevents, hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ hev)
def GameCaseWots (adversary : AdversaryP) (answers : Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        evalWithAnswerFn answers (verifyP message generated.value.1 witness) = true ∧
        (∀ input, (.inl (.inr input) : Spec.Domain) ∈ queried answers (verifyP message generated.value.1 witness) →
          ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈
            result.events) ∧
        WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP message generated.value.1 witness)))
theorem GameCaseWots.recordedSrc {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitiveSrc answers (recordedEntries answers result.events) := by
  obtain ⟨_generated, _hg, _interaction, _hi, _hext, _hpk, _hlen, _forgery, _hf, _hfresh, _message, _witness, _hof,
    _hv, hrec, hprim⟩ := h
  exact WotsPrimitiveSrc.mono hprim (entries_recorded hrec)
theorem GameCaseWots.recorded {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitive answers (recordedEntries answers result.events) :=
  h.recordedSrc.toPrimitive
theorem GameCaseWots.verifierWots {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          VerifierWots answers generated.value.1 forgery := by
  obtain ⟨generated, hg, interaction, hi, -, hpk, -, forgery, hf, hfresh, message, witness, hof, hv, -, hprim⟩ := h
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, message, witness, hof, hv, hprim.toPrimitive⟩
theorem game_linked_split (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) :
    GameCaseWots adversary answers result ∨ BPB.GameCaseC adversary answers Not result ∨
      BPB.GameCaseC adversary answers id result := by
  obtain ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hv, hrec⟩ :=
    game_accepting_linked adversary result hr answers ha hwin
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_wots_cases_src answers message generated.value.1 witness hpk hv
  rcases hcase with hprim | ⟨hgood, hshape⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hv,
      hrec, hprim⟩
  · have hCat : BPB.CaseCAt answers message witness result.events := by
      obtain ⟨prior, hev⟩ := hrec _ hdq
      have hans : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness))))) = N := hN
      exact ⟨N, hdc, hN, ⟨prior, by simpa only [hans] using hev⟩, hS, hgood, hshape⟩
    by_cases hsd : BPB.SignedDigest interaction.value.2 message witness
    · exact Or.inr (Or.inr ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)
    · exact Or.inr (Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)
theorem completed_linked_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z ∨
      BPB.CaseCSigned adversary z := by
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  exact game_linked_split adversary _ (PaddedExtraction.traced_record_support adversary q hq z.1 hr) z.2 ha hwin.1
theorem completed_linked_split_events (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    WotsPrimitiveSrc z.2 (recordedEntries z.2 (QueryRecorded.recordedTrace z.1).events) ∨
      BPB.CaseCFresh adversary z ∨ BPB.CaseCSigned adversary z :=
  (completed_linked_split adversary q hq z hz hwin).imp_left GameCaseWots.recordedSrc
theorem completed_linked_split_fresh (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z := by
  rcases completed_linked_split adversary q hq z hz hwin with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin h).elim
theorem traced_wots_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult) (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q result) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWotsSrc answers generated.value.1 forgery ∨ VerifierAllGood answers generated.value.1 forgery) := by
  obtain ⟨generated, hgenerated, interaction, hinteraction, -, hpk, -, forgery, hforgery, hfresh, message, witness,
    hof, hv, -⟩ := game_accepting_linked adversary _ (PaddedExtraction.traced_record_support adversary q hq result hr)
      answers ha hwin.1
  refine ⟨generated, hgenerated, interaction, hinteraction, hpk, forgery, hforgery, hfresh, ?_⟩
  obtain ⟨N, -, hN, -, -, hcase⟩ := verifyP_wots_cases_src answers message generated.value.1 witness hpk hv
  rcases hcase with hprim | ⟨hgood, hshape⟩
  · exact Or.inl ⟨message, witness, hof, hv, hprim⟩
  · exact Or.inr ⟨message, witness, N, hof, hN, hgood, hshape⟩
theorem completed_wots_split_src (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot z.2 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWotsSrc z.2 generated.value.1 forgery ∨ VerifierAllGood z.2 generated.value.1 forgery) := by
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  exact traced_wots_split_src adversary q hq z.1 hr hwin z.2 ha
theorem completed_wots_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot z.2 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWots z.2 generated.value.1 forgery ∨ VerifierAllGood z.2 generated.value.1 forgery) := by
  obtain ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase⟩ :=
    completed_wots_split_src adversary q hq z hz hwin
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase.imp_left VerifierWotsSrc.toVerifierWots⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3M.SecurityExtraction
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen verifyP expandB
theorem traced_wots_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult) (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q result) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        generated.value.1 = Extract.honestRoot answers 0 0 ∧
        ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
          (VerifierWots answers generated.value.1 forgery ∨ VerifierAllGood answers generated.value.1 forgery) := by
  obtain ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase⟩ :=
    traced_wots_split_src adversary q hq result hr hwin answers ha
  exact ⟨generated, hg, interaction, hi, hpk, forgery, hf, hfresh, hcase.imp_left VerifierWotsSrc.toVerifierWots⟩
end ClaudeWCT.W9.T3.Security.Wots
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeContactChain : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem known_secret {D : Coord → Prop} {s : CanonGraph.SecretIndex} (h : Known D (.inr s)) : D (.inr s) := by
  cases h with
  | base h => exact h
theorem known_chain_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ p : ChainGraph.Point, c = .inl (.chain p) →
      (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) := by
  induction h with
  | base hc =>
      intro p hp
      subst hp
      exact Or.inl ⟨p.2, le_rfl, hc⟩
  | @node N hall ih =>
      intro p hp
      simp only [Sum.inl.injEq] at hp
      subst hp
      have hmem : (chainChild p, 3) ∈ childSlots (.chain p) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      unfold chainChild at hk hih
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0] at hk
        exact Or.inr (known_secret hk)
      · rw [if_neg h0] at hih
        rcases hih (ChainGraph.predecessor p) rfl with ⟨s, hs, hd⟩ | hd
        · refine Or.inl ⟨s, ?_, hd⟩
          simp only [ChainGraph.predecessor] at hs
          omega
        · exact Or.inr hd
theorem known_chain {D : Coord → Prop} {p : ChainGraph.Point} (h : Known D (.inl (.chain p))) :
    (∃ s : Fin 7, s.val ≤ p.2.val ∧ D (.inl (.chain (p.1, s)))) ∨ D (.inr (.inl p.1)) :=
  known_chain_aux h p rfl
theorem wctItem_zero (a : CanonGraph.WctAddr) : wctItem a 0 = .inr (.inr a) := rfl
theorem wctItem_succ (a : CanonGraph.WctAddr) (s : Fin 3) :
    wctItem a (s.val + 1) = .inl (.wctChain (a, s)) := by
  have h : (⟨(s.val + 1 - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = s :=
    Fin.ext (by rw [Nat.add_sub_cancel]; exact Nat.mod_eq_of_lt s.isLt)
  unfold wctItem
  rw [if_neg (Nat.succ_ne_zero _), h]
theorem wctItem_pos (a : CanonGraph.WctAddr) (p : Nat) (h0 : p ≠ 0) (hp : p ≤ 3) :
    wctItem a p = .inl (.wctChain (a, ⟨p - 1, by omega⟩)) := by
  have h : (⟨(p - 1) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = ⟨p - 1, by omega⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (by omega))
  unfold wctItem
  rw [if_neg h0, h]
theorem known_wct_aux {D : Coord → Prop} {c : Coord} (h : Known D c) :
    ∀ (a : CanonGraph.WctAddr) (s : Fin 3), c = .inl (.wctChain (a, s)) →
      ∃ p' ≤ s.val + 1, D (wctItem a p') := by
  induction h with
  | base hc =>
      intro a s hs
      subst hs
      exact ⟨s.val + 1, le_rfl, by rw [wctItem_succ]; exact hc⟩
  | @node N hall ih =>
      intro a s hN
      simp only [Sum.inl.injEq] at hN
      subst hN
      have hmem : (wctItem a s.val, 3) ∈ childSlots (.wctChain (a, s)) := by simp [childSlots]
      have hk := hall _ hmem
      have hih := ih _ hmem
      by_cases h0 : s.val = 0
      · rw [h0, wctItem_zero] at hk
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [wctItem_zero]
        exact known_secret hk
      · have hs1 : s.val - 1 < 3 := by omega
        have he := wctItem_pos a s.val h0 (by omega)
        obtain ⟨p', hp', hd⟩ := hih a ⟨s.val - 1, hs1⟩ he
        exact ⟨p', by simp only at hp'; omega, hd⟩
theorem known_wctItem {D : Coord → Prop} {a : CanonGraph.WctAddr} {p : Nat} (hp : p ≤ 3)
    (h : Known D (wctItem a p)) : ∃ p' ≤ p, D (wctItem a p') := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero] at h
    exact ⟨0, le_rfl, by rw [wctItem_zero]; exact known_secret h⟩
  · have hs : p - 1 < 3 := by omega
    have he := wctItem_pos a p h0 hp
    rw [he] at h
    obtain ⟨p', hp', hd⟩ := known_wct_aux h a ⟨p - 1, hs⟩ rfl
    exact ⟨p', by simp only at hp'; omega, hd⟩
theorem wctItem_injective {a b : CanonGraph.WctAddr} {p q : Nat} (hp : p ≤ 3) (hq : q ≤ 3)
    (h : wctItem a p = wctItem b q) : a = b ∧ p = q := by
  unfold wctItem at h
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0
  · rw [if_pos hp0, if_pos hq0] at h
    simp only [Sum.inr.injEq] at h
    exact ⟨h, by omega⟩
  · rw [if_pos hp0, if_neg hq0] at h; cases h
  · rw [if_neg hp0, if_pos hq0] at h; cases h
  · rw [if_neg hp0, if_neg hq0] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.wctChain.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h3 := congrArg Fin.val h2
    simp only at h3
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
    exact ⟨h1, by omega⟩
theorem chainItem_chain {L : CanonGraph.LeafPos} {i d : Nat} {p : ChainGraph.Point}
    (h : chainItem L i d = .inl (.chain p)) :
    p.1 = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d ≠ 0 ∧ p.2.val = (d - 1) % 7 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    cases h
  · rw [if_neg hd] at h
    simp only [Sum.inl.injEq, CanonGraph.Node.chain.injEq] at h
    subst h
    exact ⟨rfl, hd, rfl⟩
theorem chainItem_seed {L : CanonGraph.LeafPos} {i d : Nat} {a : ChainGraph.Address}
    (h : chainItem L i d = .inr (.inl a)) : a = ⟨L.lay, L.tree, L.leaf, CanonGraph.fin58 i⟩ ∧ d = 0 := by
  unfold chainItem at h
  by_cases hd : d = 0
  · rw [if_pos hd] at h
    simp only [Sum.inr.injEq, Sum.inl.injEq] at h
    exact ⟨h.symm, hd⟩
  · rw [if_neg hd] at h
    cases h
def NotChain (c : Coord) : Prop := (∀ p, c ≠ .inl (.chain p)) ∧ (∀ a, c ≠ .inr (.inl a))
theorem treeChild_not_chain {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) : NotChain d := by
  unfold treeChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 4096
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsChild_not_chain {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) : NotChain d := by
  unfold ftsChild at hd
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; exact ⟨fun p => by simp, fun a => by simp⟩
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    exact ⟨fun p => by simp, fun a => by simp⟩
theorem wctItem_not_chain (a : CanonGraph.WctAddr) (p : Nat) : NotChain (wctItem a p) := by
  unfold wctItem
  split_ifs
  · exact ⟨fun p => by simp, fun a => by simp⟩
  · exact ⟨fun p => by simp, fun a => by simp⟩
theorem ftsItems_not_chain (index : Fin (2^31)) (N : HashOutput) (c : Coord)
    (hc : c ∈ ftsItems index N) : NotChain c := by
  unfold ftsItems wctOpened wctPath at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
    List.mem_filterMap, List.mem_range] at hc
  obtain ⟨k, hc | ⟨l, _, hl⟩⟩ := hc
  · obtain ⟨t, rfl⟩ := hc
    exact wctItem_not_chain _ _
  · exact ftsChild_not_chain hl
theorem keygen_not_chain (c : Coord) (hc : c ∈ keygenDisclosed) : NotChain c := by
  unfold keygenDisclosed at hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨_, _, _, _, h⟩ := hc
  exact treeChild_not_chain h
theorem layerItems_chain (A : Answers) (index : Fin (2^31)) (c : Coord)
    (hc : c ∈ layerItems (Wots.referenceDigits A) index) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc with hb
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
      have hfin : (CanonGraph.fin58 i).val = i := Nat.mod_eq_of_lt hi58
      have hdepth : ∀ a : ChainGraph.Address,
          a = ⟨lay, ⟨(route index.val lay).2, hb.1⟩, ⟨(route index.val lay).1, hb.2⟩, CanonGraph.fin58 i⟩ →
          Wots.depth A (wotsAddr a) = (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 := by
        intro a ha
        subst ha
        simp only [Wots.depth, wotsAddr, hfin, routeAddr]
      constructor
      · intro p hp
        obtain ⟨h1, hd, h2⟩ := chainItem_chain hp
        rw [hdepth p.1 h1, h2]
        have hle : (Wots.referenceDigits A (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
          WotsExtract.depth_le A ⟨routeAddr index.val lay, i⟩ hi
        have hw : maxDigit lay i ≤ 7 := by
          unfold maxDigit; split_ifs <;> norm_num
        omega
      · intro a ha
        obtain ⟨h1, hd⟩ := chainItem_seed ha
        rw [hdepth a h1, hd]
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc with hb
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      have := treeChild_not_chain hj
      exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
    · cases hc
theorem signDisclosed_chain (A : Answers) (published : SigGolfCandidate.T3.Cache) (request : Security.Request)
    (c : Coord) (hc : c ∈ signDisclosed A published request) :
    (∀ p, c = .inl (.chain p) → p.2.val + 1 = Wots.depth A (wotsAddr p.1)) ∧
      (∀ a, c = .inr (.inl a) → Wots.depth A (wotsAddr a) = 0) := by
  unfold signDisclosed at hc
  split_ifs at hc with hcache
  · split at hc
    · split_ifs at hc with hok
      · unfold signItems signItemsWith at hc
        rcases List.mem_append.mp hc with hc | hc
        · have := ftsItems_not_chain _ _ c hc
          exact ⟨fun p hp => absurd hp (this.1 p), fun a ha => absurd ha (this.2 a)⟩
        · exact layerItems_chain A _ c hc
      · cases hc
    · cases hc
  · cases hc
def Disclosed (A : Answers) (published : SigGolfCandidate.T3.Cache) (c : Coord) : Prop :=
  c ∈ keygenDisclosed ∨ ∃ request, c ∈ signDisclosed A published request
theorem frontier_child_unknown (A : Answers) (published : SigGolfCandidate.T3.Cache) (a : ChainGraph.Address)
    (s : Fin 7) (hs : s.val + 1 = Wots.depth A (wotsAddr a)) :
    ¬Known (Disclosed A published) (chainChild (a, s)) := by
  intro hk
  unfold chainChild at hk
  by_cases h0 : s.val = 0
  · rw [if_pos h0] at hk
    rcases known_secret hk with hd | ⟨request, hd⟩
    · exact (keygen_not_chain _ hd).2 a rfl
    · have := (signDisclosed_chain A published request _ hd).2 a rfl
      omega
  · rw [if_neg h0] at hk
    rcases known_chain hk with ⟨t, ht, hd⟩ | hd
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).1 _ rfl
      · have := (signDisclosed_chain A published request _ hd).1 _ rfl
        simp only [ChainGraph.predecessor] at ht this
        omega
    · rcases hd with hd | ⟨request, hd⟩
      · exact (keygen_not_chain _ hd).2 _ rfl
      · have := (signDisclosed_chain A published request _ hd).2 _ rfl
        simp only [ChainGraph.predecessor] at this
        omega
theorem treeChild_ne_wctItem {lay : Layer} {tree : Fin (2^31)} {level n : Nat} {d : Coord}
    (hd : treeChild lay tree level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold treeChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 4096
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem ftsChild_ne_wctItem {index : Fin (2^31)} {coord : Fin 9} {level n : Nat} {d : Coord}
    (hd : ftsChild index coord level n = some d) (a : CanonGraph.WctAddr) (p : Nat) : d ≠ wctItem a p := by
  unfold ftsChild at hd
  unfold wctItem
  by_cases h0 : level = 0
  · rw [if_pos h0] at hd
    by_cases h1 : n < 128
    · rw [dif_pos h1, Option.some.injEq] at hd; subst hd; split_ifs <;> simp
    · rw [dif_neg h1] at hd; cases hd
  · rw [if_neg h0, Option.map_eq_some_iff] at hd
    obtain ⟨m, _, rfl⟩ := hd
    split_ifs <;> simp
theorem keygen_not_wct (a : CanonGraph.WctAddr) (p : Nat) : wctItem a p ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro hc
  simp only [List.mem_flatMap, List.mem_filterMap] at hc
  obtain ⟨_, _, _, _, h⟩ := hc
  exact treeChild_ne_wctItem h a p rfl
theorem layerItems_not_wct (digitsOf : Wots.LeafAddr → List Nat) (index : Fin (2^31)) (a : CanonGraph.WctAddr)
    (p : Nat) : wctItem a p ∉ layerItems digitsOf index := by
  intro hc
  unfold layerItems at hc
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append] at hc
  obtain ⟨lay, hc | hc⟩ := hc
  · unfold layerChains at hc
    split_ifs at hc
    · simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, -, hi⟩ := hc
      unfold chainItem wctItem at hi
      split_ifs at hi <;> simp at hi
    · cases hc
  · unfold layerPath at hc
    split_ifs at hc
    · simp only [List.mem_filterMap, List.mem_range] at hc
      obtain ⟨j, _, hj⟩ := hc
      exact treeChild_ne_wctItem hj a p rfl
    · cases hc
theorem wctItem_mem_signItemsWith (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) (a : CanonGraph.WctAddr)
    (p : Nat) (hp : p ≤ 3) (h : wctItem a p ∈ signItemsWith digitsOf N) :
    a.1 = digestIndex N ∧ a.2.2.1 = WCT9.child N a.2.1 ∧ p = 3 - WCT9.digit (WCT9.rank N a.2.1) a.2.2.2 := by
  unfold signItemsWith at h
  rcases List.mem_append.mp h with h | h
  · unfold ftsItems wctOpened wctPath at h
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_append, List.mem_ofFn,
      List.mem_filterMap, List.mem_range] at h
    obtain ⟨k, ⟨t, ht⟩ | ⟨l, _, hl⟩⟩ := h
    · have hle : 3 - WCT9.digit (WCT9.rank N k) t ≤ 3 := Nat.sub_le _ _
      obtain ⟨hab, hpq⟩ := wctItem_injective hle hp ht
      subst hab
      exact ⟨rfl, rfl, hpq.symm⟩
    · exact (ftsChild_ne_wctItem hl a p rfl).elim
  · exact (layerItems_not_wct digitsOf _ a p h).elim
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low encodingRow entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wrho wdc wctr layerP layersP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveRoute (index : Nat) (answers : Answers) (trace : List Entry) : Prop :=
  (∃ lay, EncodingMatchAt answers trace (routeLeaf index lay)) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
theorem WotsPrimitiveRoute.mono {index : Nat} {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitiveRoute index answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveRoute index answers trace' := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨lay, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
theorem layer_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : Digest)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ Extract.Good answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (low (answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay)))))) = some digits := hframe.2
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  have hencE : (encodingRow (routeLeaf index lay) msg (wctr w lay),
      answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay))))) ∈ entriesOf answers qs :=
    mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  rcases layerP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    contactAt_mono ((hchains i hi).2 hlt).1 hmono
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  · have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · exact Or.inr ⟨hm, digits, hm ▸ hframe, hshape⟩
    · refine Or.inl (Or.inl ⟨lay, msg, wctr w lay, _, hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ hdec (Or.inl (by rw [leafMsg_route]; exact hm))
      · rw [← heq]; exact hdec
  · have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wctr w lay, _, digits, hencE, referenceInput_ne answers _ msg _ hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact twoEdgeAt_mono (((hchains i.val i.isLt).2 hlt).2 h2) hmono
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)
theorem layersP_wots_walk_route (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : Digest,
    evalWithAnswerFn answers (layersP w index n root) = some (Extract.walkTarget answers index 0) →
    WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersP w index n root))) ∨
    ((∀ l : Layer, l.val < n → Extract.Good answers w index l) ∧ root = Extract.walkTarget answers index n)
  | 0, _, root, h => by
      right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := Extract.layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_wots_walk_route answers w index hidx n (by omega) _ hrest with hprim | ⟨hgood, hv⟩
      · exact Or.inl (hprim.mono (entriesOf_mono hqR))
      · rw [Extract.walkTarget_root answers index n (by omega)] at hv
        rcases layer_wots_route answers w index (Fin.ofNat 4 n) root digits hidx hframe
            (queried answers (layersP w index (n + 1) root)) henc hqL hv with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          have hmsg' : Extract.honestMsg answers index (Fin.ofNat 4 n) = Extract.walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [Extract.walkTarget, dif_pos (show n < 4 by omega), hl]
          refine ⟨fun l hl => ?_, hmsg.trans hmsg'⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
theorem verifyP_walk_wots_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
            Extract.honestForest answers (N.toNat % 2 ^ 31) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have htop : Extract.walkTarget answers (N.toNat % 2 ^ 31) 0 = pk := by
    rw [hpk]; simp only [Extract.walkTarget, route_top_tree _ hidx]
  rcases layersP_wots_walk_route answers w (N.toNat % 2 ^ 31) hidx 4 le_rfl _ (by rw [hlay, htop]) with
    hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [hroot]
    simp [Extract.walkTarget, Extract.honestMsg]
theorem verifyP_wots_cases_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N w ∧
         ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots_route answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape, hqV⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr IsDigestRow)
open SigGolfCandidate.T3.Security.LargeCoupling (wotsAddr gAddr wotsAddr_gAddr chainCount_le58 chainRow_block4
  slotValue_chainRow slotValue_block4_three honestChainValue_zero')
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def AllClear (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) : Prop :=
  ∀ X, (.inl (.inr X) : Spec.Domain) ∈ qs → Clear A K X (A (.inl (.inr X)))
theorem posOf_chainRow (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (s : Nat) (hs : s < 7) (v : Digest) :
    Extract.posOf (Wots.chainRow a s v) = some (CanonGraph.Node.chain (gAddr a ha, ⟨s, hs⟩)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  unfold Wots.chainRow
  rw [show Extract.hdrBlock (chainInput a.key.lay a.key.tree a.key.leaf a.chain s v) =
    bytesLE 16 (chainHeader a.key.lay a.key.tree a.key.leaf a.chain s) from chainInput_header _ _ _ _ _ _]
  rfl
theorem honestInput_chainNode (A : Answers) (p : ChainGraph.Point) :
    Extract.honestInput A (CanonGraph.Node.chain p).toPos =
      Wots.chainRow (wotsAddr p.1) p.2.val (honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val) := by
  show pad64 _ = _
  rw [chainInput_padded]
  rfl
theorem honestValue_chainNode (A : Answers) (p : ChainGraph.Point) :
    honestValue A (.inl (.chain p)) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) (p.2.val + 1) := by
  rw [← honestChainValue_succ, eval_shortHash]
  rfl
theorem honestValue_chainChild (A : Answers) (p : ChainGraph.Point) :
    honestValue A (chainChild p) = honestChainValue A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val
        (leafSeed A p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val) p.2.val := by
  unfold chainChild
  by_cases h0 : p.2.val = 0
  · rw [if_pos h0, h0, honestChainValue_zero']
    rfl
  · rw [if_neg h0, honestValue_chainNode]
    simp only [ChainGraph.predecessor]
    congr 1
    omega
theorem childSlots_chain (p : ChainGraph.Point) : childSlots (.chain p) = [(chainChild p, 3)] := rfl
theorem contactAt_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (a : Wots.ChainAddr) (ha : WotsExtract.SourceChain a) (hc : Wots.ContactAt A (Wots.entriesOf A qs) a)
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  obtain ⟨hd, value, answer, hmem, hlow⟩ := hc
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hd7 : Wots.depth A a ≤ 7 := by
    have := WotsExtract.depth_le A a ha.2
    have hw : maxDigit a.key.lay a.chain ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
    omega
  set s := Wots.depth A a - 1 with hsdef
  have hs7 : s < 7 := by omega
  let p : ChainGraph.Point := (gAddr a ha, ⟨s, hs7⟩)
  have hpos := posOf_chainRow a ha s hs7 value
  obtain ⟨hhit, hsingle, -⟩ := hclear _ hq
  have hcv : honestValue A (chainChild p) = honestChainValue A a.key.lay a.key.tree a.key.leaf a.chain
      (leafSeed A a.key.lay a.key.tree a.key.leaf a.chain) s := honestValue_chainChild A p
  by_cases hv : value = honestValue A (chainChild p)
  · have hk := hsingle (.chain p) hpos (chainChild p) 3 (childSlots_chain p) (by rw [slotValue_chainRow]; exact hv)
    exact frontier_child_unknown A published (gAddr a ha) ⟨s, hs7⟩ (by
      change s + 1 = Wots.depth A (wotsAddr (gAddr a ha))
      rw [wotsAddr_gAddr]; omega) hk
  · apply hhit (.chain p) hpos
    refine ⟨fun heq => hv ?_, ?_⟩
    · have := congrArg (fun X => slotValue X 3) heq
      simp only [slotValue_chainRow] at this
      rw [this, honestInput_chainNode, slotValue_chainRow, hcv]
      rfl
    · rw [hans]
      change Wots.low answer = _
      rw [hlow, honestValue_chainNode]
      unfold Wots.frontierValue
      congr 1
      change Wots.depth A a = s + 1
      omega
theorem structuralHitSrc_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain)
    (h : WotsExtract.StructuralHitSrc A (Wots.entriesOf A qs)) (hclear : AllClear A K qs) : False := by
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, -, hne, hlow⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  have hsp : CanonGraph.SourcePos position := by
    cases position with
    | chain lay tree leaf i step =>
        obtain ⟨h1, h2, h3, h4⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 (chainCount_le58 lay), ?_⟩
        · calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
            _ = 4096 := by norm_num
        · have hw : 2 ^ width lay i ≤ 8 := by unfold width; split_ifs <;> norm_num
          omega
    | leaf lay tree leaf =>
        obtain ⟨h1, h2⟩ := hsrc
        refine ⟨h1, lt_of_lt_of_le h2 ?_⟩
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (SigGolfCandidate.T3M.Extract.height_le _)
          _ = 4096 := by norm_num
    | node lay tree level nd => exact hsrc
    | forest index => exact hsrc
    | wctChain index coord child t step => exact hsrc
    | wctLeaf index coord child => exact hsrc
    | wctNode index coord level nd => exact hsrc
  obtain ⟨N, rfl⟩ := CanonGraph.exists_toPos hsp
  exact (hclear _ hq).1 N hpos ⟨hne, hlow⟩
theorem encodingMatch_route_false (A : Answers) (K : Coord → Prop) (qs : List Spec.Domain) (index : Nat)
    (hidx : index < 2 ^ 31) (lay : Layer)
    (h : Wots.EncodingMatchAt A (Wots.entriesOf A qs) (WotsExtract.routeLeaf index lay))
    (hclear : AllClear A K qs) : False := by
  obtain ⟨m, ctr, answer, hmem, hne, hdec⟩ := h
  obtain ⟨hq, hans⟩ := WotsExtract.mem_entriesOf_iff.mp hmem
  obtain ⟨L, hL⟩ := CanonEncoding.route_source index hidx lay
  have hL' : L.toWots = WotsExtract.routeLeaf index lay := hL
  refine (hclear _ hq).2.2 L m ctr (by rw [hL']) ⟨?_, ?_⟩
  · rw [hL']; exact hne
  · have hlay : L.1.lay = lay := congrArg Wots.LeafAddr.lay hL'
    rw [hans, hL', hlay]; exact hdec
theorem wotsPrimitiveRoute_false (A : Answers) (published : SigGolfCandidate.T3.Cache) (qs : List Spec.Domain)
    (index : Nat) (hidx : index < 2 ^ 31) (h : WotsExtract.WotsPrimitiveRoute index A (Wots.entriesOf A qs))
    (hclear : AllClear A (Known (Disclosed A published)) qs) : False := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, -, -, h, -⟩ | ⟨a, ha, -, h⟩
  · exact encodingMatch_route_false A _ qs index hidx lay h hclear
  · exact structuralHitSrc_false A _ qs h hclear
  · obtain ⟨hd, start, middle, -, hrow⟩ := h
    exact contactAt_false A published qs a ha ⟨by omega, middle, hrow⟩ hclear
  · exact contactAt_false A published qs a ha h hclear
  · exact contactAt_false A published qs a ha h hclear
theorem posOf_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 3) :
    Extract.posOf (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) =
      some (CanonGraph.Node.wctChain (a, s)).toPos :=
  Extract.posOf_eq (CanonGraph.toPos_bounded _) (Extract.hdrBlock_honestInput A _)
theorem honestValue_wctItem (A : Answers) (a : CanonGraph.WctAddr) (p : Nat) (hp : p ≤ 3) :
    honestValue A (wctItem a p) = Extract.wctValue A a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val p := by
  by_cases h0 : p = 0
  · subst h0
    rw [wctItem_zero]
    change CanonGraph.secretsOf A (.inr a) = _
    rw [← CanonGraph.wctSeed_secrets]
    simp [Extract.wctValue, WCT9.chain]
  · rw [wctItem_pos a p h0 hp]
    obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
    change (A (.inl (.inr (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val
      (s + 1 - 1)))))).extractLsb' 0 128 = _
    rw [← WctExtract.wctValue_succ, eval_shortHash, Extract.pad64_wctChainInput, WctExtract.honestInput_wctChain]
    rfl
theorem slotValue_honest_wctChain (A : Answers) (a : CanonGraph.WctAddr) (s : Fin 3) :
    slotValue (Extract.honestInput A (CanonGraph.Node.wctChain (a, s)).toPos) 3 = honestValue A (wctItem a s.val) := by
  rw [honestValue_wctItem A a s.val (by omega)]
  change slotValue (Extract.honestInput A (.wctChain a.1.val a.2.1.val a.2.2.1.val a.2.2.2.val s.val)) 3 = _
  rw [WctExtract.honestInput_wctChain, WctExtract.wctChainInput_block4']
  exact slotValue_block4_three _ _ _ _
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section




namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeCoupling (record_inputs)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem trace_inputs (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary q hq).support) :
    ∀ e ∈ (QueryRecorded.recordedTrace result).events, ∀ x, e.input = .inl (.inr x) →
      x ∈ Wots.referenceInputs adversary :=
  record_inputs _ _ (∅, ∅) (Wots.Ref.referenceInputs_inputsIn adversary) _
    (PaddedExtraction.traced_record_support adversary q hq result hr)
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section





namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (record_events_known chargeOf EventsAgree)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem noContact_caseC (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) : BPB.CaseCFresh adversary z := by
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  simp only [Contact, not_forall] at hno
  obtain ⟨g, t, c, hsplit, hmon⟩ := hno
  have hmon' : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).contact = false := by
    simpa using hmon
  obtain ⟨hg, ht, hc, hres⟩ := hsplit
  have hu := taggedRecord_untag _ _ _ t ht
  have hgt : SourceReplay.Extends g.state t.state :=
    SourceReplay.run_extends _ _ (t.untag.value, t.untag.state) (FirstHit.recorded_support _ _ _ hu)
  have htc : SourceReplay.Extends t.state c.state :=
    SourceReplay.run_extends _ _ (c.value, c.state) (FirstHit.recorded_support _ _ _ hc)
  have hstate : (QueryRecorded.recordedTrace z.1).state = c.state := by rw [hres]
  have hac : ∀ input answer, SourceReplay.known c.state input = some answer → z.2 input = answer := by
    intro input answer h
    apply hagree
    rw [← hstate] at h
    exact h
  have hcval : c.value = true := by
    have h1 : (QueryRecorded.recordedTrace z.1).value = c.value := by rw [hres]
    rw [← h1]; exact hwin.1
  have hgen : evalWithAnswerFn z.2 keygen = g.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅) (g.value, g.state)
      (FirstHit.recorded_support _ _ _ hg)).eval z.2
        (fun input answer hk => hac input answer (SourceReplay.known_mono _ _ (hgt.trans htc) hk))
  have hpk : g.value.1 = Extract.honestRoot z.2 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk z.2
  obtain ⟨hlen, forgery, hf, hfresh, m, w, hof, hv, hsub⟩ :=
    WotsExtract.verdict_accepting g.value.1 t.value t.state c hc z.2 hac hcval
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WotsExtract.verifyP_wots_cases_route z.2 m g.value.1 w hpk hv
  have hsteps : StepsAgree z.2 t.steps := by
    intro step hstep event heq hi
    have hev : event ∈ t.untag.events := by
      change event ∈ t.steps.flatMap TaggedStep.events
      exact List.mem_flatMap.mpr ⟨step, hstep, by rw [heq]; exact List.mem_singleton_self _⟩
    exact hac _ _ (SourceReplay.known_mono _ _ htc (record_events_known _ _ _ hu event hev hi))
  have hverdict : EventsAgree z.2 c.events := fun event he hi =>
    hac _ _ (record_events_known _ _ _ hc event he hi)
  have hcalls : (monitorRun (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events).calls ≤ q := by
    have hcost := PaddedGame.traced_cost_coherent adversary q hq z.1 hz1
    have hle := monitorRun_calls_le (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events
    have hev : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
    have htot : chargeOf (QueryRecorded.recordedTrace z.1).events = z.1.2.2.base.source.1 := hcost.symm
    rw [hev] at htot
    have hw := hwin.2.1
    have hte : t.events = t.steps.flatMap TaggedStep.events := rfl
    simp only [chargeOf, List.map_append, List.sum_append] at htot hle
    rw [hte] at htot
    omega
  have hclear : AllClear z.2 (Known (Disclosed z.2 g.value.2)) (queried z.2 (verifyP m g.value.1 w)) := by
    intro X hX
    obtain ⟨prior, hev⟩ := hsub X hX
    have hseen := events_seen (Wots.referenceInputs adversary) z.2 q c.events _ hmon' _ hev X rfl
    have hXU : X ∈ Wots.referenceInputs adversary := by
      have hmem := List.mem_append_right g.events (List.mem_append_right t.events hev)
      have hev' : (QueryRecorded.recordedTrace z.1).events = g.events ++ (t.events ++ c.events) := by rw [hres]
      rw [← hev'] at hmem
      exact trace_inputs adversary q hq z.1 hz1 _ hmem X rfl
    have hcl := monitorRun_clear (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events hsteps hverdict
      hmon' hcalls X hseen hXU
    exact hcl.mono fun d hd => monitorRun_known (Wots.referenceInputs adversary) z.2 q g.value.2 t.steps c.events d hd
  rcases hcase with hprim | ⟨hgood, hfts, -⟩
  · exact (wotsPrimitiveRoute_false z.2 g.value.2 _ _ (Nat.mod_lt _ (by decide)) hprim hclear).elim
  have hdigest : ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))), N⟩ :
      FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events := by
    obtain ⟨prior, hev⟩ := hsub _ hdq
    refine ⟨prior, ?_⟩
    rw [hres]
    have hNz : z.2 (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w))))) = N := hN
    rw [hNz] at hev
    exact List.mem_append_right _ (List.mem_append_right _ hev)
  have hcaseC : BPB.CaseCAt z.2 m w (QueryRecorded.recordedTrace z.1).events :=
    ⟨N, hdc, hN, hdigest, hS, hgood, hfts⟩
  have hext : SourceReplay.Extends t.untag.state (QueryRecorded.recordedTrace z.1).state := by
    rw [hstate]; exact htc
  by_cases hsd : BPB.SignedDigest t.value.2 m w
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin
      ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩).elim
  · exact ⟨g, hg, t.untag, hu, hext, hpk, hlen, forgery, hf, hfresh, m, w, hof, hsd, hcaseC⟩
theorem wct_noContact_caseC (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) (hno : ¬Contact adversary q z) : BPB.CaseCFresh adversary z :=
  noContact_caseC adversary q hq z hz hwin hno
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
