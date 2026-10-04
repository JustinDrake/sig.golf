import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.New.G5.PaddedExtraction
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.VerifyP
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.PaddedWitness
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace ClaudeWCT.W9.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9seccSufSigned : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
def CaseCAt (answers : Correctness.Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < WCT9.digestAttemptLimit ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
    (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
      FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧
    (∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ answers witness (digestAnswer.toNat % 2 ^ 31) lay) ∧
    ClaudeWCT.W9.T3M.WctExtract.WctHonest answers digestAnswer witness
theorem CaseCAt.mono {answers : Correctness.Answers} {message : Message} {witness : WBytes}
    {events events' : List FirstHit.QueryEvent} (h : CaseCAt answers message witness events)
    (hsub : ∀ e ∈ events, e ∈ events') : CaseCAt answers message witness events' := by
  obtain ⟨N, h1, h2, ⟨prior, hp⟩, h4, h5, h6⟩ := h
  exact ⟨N, h1, h2, ⟨prior, hsub _ hp⟩, h4, h5, h6⟩
def SignedDigest (log : QueryLog Requests) (message : Message) (witness : WBytes) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧
    signature.rho = wrho witness
def GameCaseC (adversary : AdversaryP) (answers : Correctness.Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        signed (SignedDigest interaction.value.2 message witness) ∧
        CaseCAt answers message witness result.events
abbrev CaseCFresh (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseC adversary z.2 Not (QueryRecorded.recordedTrace z.1)
abbrev CaseCSigned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseC adversary z.2 id (QueryRecorded.recordedTrace z.1)
def GameConclusionLinked (adversary : AdversaryP) (answers : Correctness.Answers)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        PaddedExtraction.Conclusion answers message witness result.events
theorem game_recorded_linked (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) : GameConclusionLinked adversary answers result := by
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
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hgenerated)).eval answers
        (fun input answer hk => ha input answer
          (SourceReplay.known_mono generated.state result.state hgeneratedState hk))
  have hpk : generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact ClaudeWCT.W9.T3M.Extract.keygen_pk answers
  have hac : ∀ input answer, SourceReplay.known checked.state input = some answer → answers input = answer := by
    simpa only [hstate, hrestState] using ha
  have hw : checked.value = true := hrestValue.symm.trans (hvalue.symm.trans hwin)
  obtain ⟨hlength, forgery, hforgery, hfresh, message, witness, hof, hconclusion⟩ :=
    PaddedExtraction.verdict_recorded generated.value.1 interaction.value interaction.state checked hchecked
      answers hac hpk hw
  refine ⟨generated, hgenerated, interaction, hinteraction, hinteractionState, hpk, hlength, forgery, hforgery,
    hfresh, message, witness, hof, hconclusion.mono ?_⟩
  intro event he
  rw [hevents, hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ he)
theorem traced_game_linked (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer →
      answers input = answer)
    (hwin : result.1 = true) : GameConclusionLinked adversary answers (QueryRecorded.recordedTrace result) :=
  game_recorded_linked adversary _ (PaddedExtraction.traced_record_support adversary budget hbudget result hr)
    answers ha hwin
def ConclusionAB (answers : Correctness.Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
      (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
        FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧
      (PaddedExtraction.ActualHit answers events ∨
        (∃ lay : Layer, ClaudeWCT.W9.T3M.Extract.Diverge answers witness (digestAnswer.toNat % 2 ^ 31) lay
          (events.map FirstHit.QueryEvent.input) ∧
          ∀ above : Layer, above.val < lay.val →
            ClaudeWCT.W9.T3M.Extract.Good answers witness (digestAnswer.toNat % 2 ^ 31) above) ∨
        PaddedExtraction.PadAt answers witness (digestAnswer.toNat % 2 ^ 31))
def GameCaseAB (adversary : AdversaryP) (answers : Correctness.Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        ConclusionAB answers message witness result.events
theorem linked_split (adversary : AdversaryP) (answers : Correctness.Answers) (result : FirstHit.Recorded Bool)
    (h : GameConclusionLinked adversary answers result) :
    GameCaseAB adversary answers result ∨ GameCaseC adversary answers Not result ∨
      GameCaseC adversary answers id result := by
  obtain ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hc⟩ := h
  obtain ⟨N, hdc, hN, hq, hS, hcase⟩ := hc
  rcases hcase with hA | hB | hP | ⟨hgood, hfts⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof,
      N, hdc, hN, hq, hS, Or.inl hA⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof,
      N, hdc, hN, hq, hS, Or.inr (Or.inl hB)⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof,
      N, hdc, hN, hq, hS, Or.inr (Or.inr hP)⟩
  · by_cases hsd : SignedDigest interaction.value.2 message witness
    · exact Or.inr (Or.inr ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, N, hdc, hN, hq, hS, hgood, hfts⟩)
    · exact Or.inr (Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, N, hdc, hN, hq, hS, hgood, hfts⟩)
theorem logged_resolves {α : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : LazyPrivate.State) (result : (α × QueryLog Requests) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.loggedWith (FullGame.authenticatedSign published) program)
      before)) :
    ∀ entry ∈ result.1.2, SourceReplay.Resolves result.2 (FullGame.authenticatedSign published entry.1) entry.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FullGame.loggedWith_pure, LazyPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [FullGame.loggedWith_world, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, _, hr⟩ := hr
          exact ih middle.1 middle.2 result hr
      | inr request =>
          rw [FullGame.loggedWith_request, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, hm, hr⟩ := hr
          rw [LazyPrivate.run_map, support_map] at hr
          obtain ⟨last, hl, rfl⟩ := hr
          intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            exact (SourceReplay.resolves_of_run _ (CountedPrivate.authenticatedSign_hashOnly published request)
              before middle hm).mono (SourceReplay.run_extends _ middle.2 last hl)
          · exact ih middle.1 middle.2 last hl entry he
def payloadForNonce (cache : SigGolfCandidate.T3.Cache) (rho : Digest) (message : Message) :
    M (Option Signature) := do
  let some (_, output) ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit | pure none
  let forest ← WCT9.signForest (output.toNat % 2 ^ 31) output
  let some pieces ← WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4 (.forest forest.2) | pure none
  pure (some (WCT9.assembledSignature rho forest.1 pieces))
theorem signPayload_nonce (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message =
      (privateNonce message >>= fun rho => payloadForNonce cache rho message) := by
  rw [WCT9.Rev3.signPayload_eq]
  rfl
theorem eval_authenticatedSign (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) :
    evalWithAnswerFn answers (FullGame.authenticatedSign published request) =
      if request.cache = published then
        evalWithAnswerFn answers (payloadForNonce published
          (evalWithAnswerFn answers (privateNonce request.message)) request.message)
      else none := by
  unfold FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    show evalWithAnswerFn answers (WCT9.Rev3.signPayload request.cache request.message) = _
    rw [signPayload_nonce, evalWithAnswerFn_bind, hc]
  · rw [if_neg hc, if_neg hc, evalWithAnswerFn_pure]
theorem authenticatedSign_payload (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (sig : Signature)
    (h : evalWithAnswerFn answers (FullGame.authenticatedSign published request) = some sig) :
    request.cache = published ∧ sig.rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      evalWithAnswerFn answers (payloadForNonce published sig.rho request.message) = some sig := by
  rw [eval_authenticatedSign] at h
  by_cases hc : request.cache = published
  · rw [if_pos hc] at h
    have hrho : sig.rho = evalWithAnswerFn answers (privateNonce request.message) := by
      unfold payloadForNonce at h
      simp only [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn answers (WCT9.digestSearch (evalWithAnswerFn answers (privateNonce request.message))
        request.message 0 WCT9.digestAttemptLimit) = found at h
      rcases found with _ | ⟨_, output⟩
      · simp at h
      · simp only [evalWithAnswerFn_bind] at h
        generalize evalWithAnswerFn answers (WCT9.signLayersBC published (output.toNat % 2 ^ 31) 4
          (.forest (evalWithAnswerFn answers (WCT9.signForest (output.toNat % 2 ^ 31) output)).2)) = layers at h
        rcases layers with _ | pieces
        · simp at h
        · simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
          rw [← h]
          rfl
    exact ⟨hc, hrho, by rw [hrho]; exact h⟩
  · rw [if_neg hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.BPB
