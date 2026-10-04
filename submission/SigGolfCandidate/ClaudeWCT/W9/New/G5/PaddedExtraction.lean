import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.VerifyP
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Rows

namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes Shaped verifyP)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP checkForgeryP)
open Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem verifyP_hashOnly (message : Message) (publicKey : Digest) (witness : WBytes) :
    Security.SourceReplay.HashOnly (verifyP message publicKey witness) := by
  apply SigGolfCandidate.T3M.allQ_mono (ClaudeWCT.W9.T3M.publicOnly_verifyP message publicKey witness)
  intro input h
  rcases input with (sample | query) | coordinate
  · exact h.elim
  · trivial
  · trivial
def ActualHit (answers : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (position : ClaudeWCT.W9.T3M.Extract.Pos) (actual : HashInput) (prior : LazyPrivate.State),
    position.Bounded ∧ ClaudeWCT.W9.T3M.Extract.posOf actual = some position ∧
    (⟨prior, .inl (.inr actual), answers (.inl (.inr actual))⟩ : FirstHit.QueryEvent) ∈ events ∧
    SigGolfCandidate.T3M.SecurityExtraction.HashHit answers
      (ClaudeWCT.W9.T3M.Extract.honestInput answers position) actual
theorem hit_recorded {α : Type} (program : M α) (hp : Security.SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hit : ClaudeWCT.W9.T3M.Extract.HitIn answers (SigGolfCandidate.T3M.SecurityExtraction.queried answers program)) :
    ActualHit answers result.events := by
  obtain ⟨position, actual, hbounded, hquery, hpos, hhit⟩ := ClaudeWCT.W9.T3M.Extract.hitIn_posOf hit
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence program hp before
    result hr answers ha actual hquery
  exact ⟨position, actual, prior, hbounded, hpos, hevent, hhit⟩
def PadAt (answers : Answers) (witness : WBytes) (index : Nat) : Prop :=
  ∃ lay : Layer, lay.val < 3 ∧ ClaudeWCT.W9.T3M.Extract.Good answers witness index lay ∧
    ClaudeWCT.W9.T3M.wbcPad witness lay ≠ 0
def Conclusion (answers : Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
      (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
        FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧
      (ActualHit answers events ∨
        (∃ lay : Layer, ClaudeWCT.W9.T3M.Extract.Diverge answers witness (digestAnswer.toNat % 2 ^ 31) lay
          (events.map FirstHit.QueryEvent.input) ∧
          ∀ above : Layer, above.val < lay.val →
            ClaudeWCT.W9.T3M.Extract.Good answers witness (digestAnswer.toNat % 2 ^ 31) above) ∨
        PadAt answers witness (digestAnswer.toNat % 2 ^ 31) ∨
        ((∀ lay : Layer, ClaudeWCT.W9.T3M.BC.GoodZ answers witness (digestAnswer.toNat % 2 ^ 31) lay) ∧
          ClaudeWCT.W9.T3M.WctExtract.WctHonest answers digestAnswer witness))
theorem verifyP_extracted_in {α : Type} (program : M α) (hp : Security.SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (message : Message) (publicKey : Digest) (witness : WBytes)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP message publicKey witness) = true)
    (hsub : ∀ input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers (verifyP message publicKey witness),
      input ∈ SigGolfCandidate.T3M.SecurityExtraction.queried answers program) :
    Conclusion answers message witness result.events := by
  obtain ⟨N, hcounter, hdigest, hquery, hshape, halt⟩ :=
    ClaudeWCT.W9.T3M.Extract.verifyP_extract_normal answers message publicKey witness hpk hv
  obtain ⟨prior, hevent⟩ := SigGolfCandidate.T3.Security.PaddedExtraction.public_occurrence program hp before
    result hr answers ha _ (hsub _ hquery)
  have hans : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness))))) = N := hdigest
  refine ⟨N, hcounter, hdigest, ⟨prior, by simpa only [hans] using hevent⟩, hshape, ?_⟩
  rcases halt with hhit | ⟨lay, hdiv, hgood⟩ | ⟨hgood, hfts⟩
  · exact Or.inl (hit_recorded program hp before result hr answers ha (hhit.mono hsub))
  · refine Or.inr (Or.inl ⟨lay, hdiv.mono ?_, hgood⟩)
    intro input hin
    rw [FirstHit.recorded_inputs program hp before result hr answers ha,
      SigGolfCandidate.T3.Security.PaddedExtraction.queried_eq]
    exact hsub _ hin
  · by_cases hz : ∀ lay : Layer, lay.val < 3 → ClaudeWCT.W9.T3M.wbcPad witness lay = 0
    · exact Or.inr (Or.inr (Or.inr ⟨fun lay => ⟨hgood lay, hz lay⟩, hfts⟩))
    · push_neg at hz
      obtain ⟨lay, hlay, hpad⟩ := hz
      exact Or.inr (Or.inr (Or.inl ⟨lay, hlay, hgood lay, hpad⟩))
theorem verifyP_recorded (message : Message) (publicKey : Digest) (witness : WBytes)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (verifyP message publicKey witness) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    Conclusion answers message witness result.events := by
  have hp := verifyP_hashOnly message publicKey witness
  have hv := (SourceReplay.resolves_of_run (verifyP message publicKey witness) hp before
    (result.value, result.state) (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hv
  exact verifyP_extracted_in _ hp before result hr answers ha message publicKey witness hpk hv (fun _ h => h)
noncomputable def reference : FirstHit.Reference := fun state input =>
  (ClaudeWCT.W9.T3M.Extract.posOf input).map (ClaudeWCT.W9.T3M.Extract.honestInput (SourceReplay.answers state))
theorem reference_of_pos (state : LazyPrivate.State) (input : HashInput) (position : ClaudeWCT.W9.T3M.Extract.Pos)
    (hpos : ClaudeWCT.W9.T3M.Extract.posOf input = some position) :
    reference state input = some (ClaudeWCT.W9.T3M.Extract.honestInput (SourceReplay.answers state) position) := by
  simp only [reference, hpos, Option.map_some]
def UnresolvedHit (answers : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (position : ClaudeWCT.W9.T3M.Extract.Pos) (actual : HashInput) (prior : LazyPrivate.State), position.Bounded ∧
    ClaudeWCT.W9.T3M.Extract.posOf actual = some position ∧
    (⟨prior, .inl (.inr actual), answers (.inl (.inr actual))⟩ : FirstHit.QueryEvent) ∈ events ∧
    prior.2 actual = none ∧
    SigGolfCandidate.T3M.SecurityExtraction.HashHit answers
      (ClaudeWCT.W9.T3M.Extract.honestInput answers position) actual ∧
    (reference prior actual ≠ some (ClaudeWCT.W9.T3M.Extract.honestInput answers position) ∨
      prior.2 (ClaudeWCT.W9.T3M.Extract.honestInput answers position) = none)
theorem ActualHit.mono {answers : Answers} {events events' : List FirstHit.QueryEvent}
    (hit : ActualHit answers events) (hsub : ∀ event ∈ events, event ∈ events') :
    ActualHit answers events' := by
  obtain ⟨position, actual, prior, hbounded, hpos, hevent, hhit⟩ := hit
  exact ⟨position, actual, prior, hbounded, hpos, hsub _ hevent, hhit⟩
theorem Conclusion.mono {answers : Answers} {message : Message} {witness : WBytes}
    {events events' : List FirstHit.QueryEvent} (h : Conclusion answers message witness events)
    (hsub : ∀ event ∈ events, event ∈ events') : Conclusion answers message witness events' := by
  obtain ⟨N, hcounter, hdigest, ⟨prior, hevent⟩, hshape, halt⟩ := h
  refine ⟨N, hcounter, hdigest, ⟨prior, hsub _ hevent⟩, hshape, ?_⟩
  rcases halt with hhit | ⟨lay, hdiv, hgood⟩ | hpad | hgood
  · exact Or.inl (hhit.mono hsub)
  · refine Or.inr (Or.inl ⟨lay, hdiv.mono ?_, hgood⟩)
    intro input hin
    obtain ⟨event, hevent, rfl⟩ := List.mem_map.mp hin
    exact List.mem_map.mpr ⟨event, hsub _ hevent, rfl⟩
  · exact Or.inr (Or.inr (Or.inl hpad))
  · exact Or.inr (Or.inr (Or.inr hgood))
theorem actualHit_known_or_unresolved {α : Type} (program : M α) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program (∅, ∅))) (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hit : ActualHit answers result.events) :
    FirstHit.KnownPublicHit reference result ∨ UnresolvedHit answers result.events := by
  obtain ⟨position, actual, prior, hbounded, hpos, hevent, hhit⟩ := hit
  obtain ⟨first, hfirst, hfresh⟩ := FirstHit.first_public_occurrence program result hr prior actual _ hevent
  by_cases href : reference first actual = some (ClaudeWCT.W9.T3M.Extract.honestInput answers position)
  · cases hout : first.2 (ClaudeWCT.W9.T3M.Extract.honestInput answers position) with
    | none => exact Or.inr ⟨position, actual, first, hbounded, hpos, hfirst, hfresh, hhit, Or.inr hout⟩
    | some output =>
        have hx := (FirstHit.recorded_public_known program (∅, ∅) result hr first actual _ hfirst).2
        have hk := SourceReplay.known_mono first result.state hx
          (show SourceReplay.known first (.inl (.inr (ClaudeWCT.W9.T3M.Extract.honestInput answers position))) =
            some output from hout)
        have heq := ha _ _ hk
        exact Or.inl ⟨first, actual, answers (.inl (.inr actual)),
          ClaudeWCT.W9.T3M.Extract.honestInput answers position, output,
          hfirst, hfresh, href, hout, by simpa only [heq] using hhit.2⟩
  · exact Or.inr ⟨position, actual, first, hbounded, hpos, hfirst, hfresh, hhit, Or.inl href⟩
theorem padded_known_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun result => result.2.2.base.source.1 ≤ q ∧
      FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) |
      PaddedGame.tracedExperiment adversary q hq] ≤ q / (2 : ENNReal) ^ 128 :=
  GameWith.Recorded.known_public_hit_bound PaddedGame.checker reference adversary q hq
theorem check_recorded (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (checkForgeryP publicKey log forgery) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    Fresh log forgery ∧ ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
      Conclusion answers message witness result.events := by
  have hp := check_hashOnly publicKey log forgery
  have hw := (SourceReplay.resolves_of_run _ hp before (result.value, result.state)
    (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hw
  obtain ⟨hfresh, message, witness, hof, hv, hsub⟩ := check_accepting answers publicKey log forgery hw
  exact ⟨hfresh, message, witness, hof,
    verifyP_extracted_in _ hp before result hr answers ha message publicKey witness hpk hv hsub⟩
theorem verdict_recorded (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hpk : publicKey = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0) (hwin : result.value = true) :
    interaction.2.length ≤ 2 ^ 32 ∧ ∃ forgery, interaction.1 = some forgery ∧ Fresh interaction.2 forgery ∧
      ∃ message witness, WitnessOf answers publicKey forgery message witness ∧
        Conclusion answers message witness result.events := by
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
      have hcheck := check_recorded publicKey interaction.2 forgery before checked hchecked answers
        (by simpa only [hstate] using ha) hpk hcheckedWin
      obtain ⟨hfresh, message, witness, hof, hconclusion⟩ := hcheck
      exact ⟨hlength, forgery, rfl, hfresh, message, witness, hof, hevents ▸ hconclusion⟩
def GameConclusion (adversary : AdversaryP) (answers : Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ Fresh interaction.value.2 forgery ∧
      ∃ message witness, WitnessOf answers generated.value.1 forgery message witness ∧
        Conclusion answers message witness result.events
theorem game_recorded (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)))
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer)
    (hwin : result.value = true) : GameConclusion adversary answers result := by
  unfold GameWith.idealGame at hr
  obtain ⟨generated, hgenerated, rest, hrest, hvalue, hevents, hstate⟩ :=
    FirstHit.record_bind_support _ _ (∅, ∅) result hr
  obtain ⟨interaction, hinteraction, checked, hchecked, hrestValue, hrestEvents, hrestState⟩ :=
    FirstHit.record_bind_support _ _ generated.state rest hrest
  have hgeneratedState : SourceReplay.Extends generated.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ generated.state (rest.value, rest.state)
      (FirstHit.recorded_support _ _ _ hrest)
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
    verdict_recorded generated.value.1 interaction.value interaction.state checked hchecked answers hac hpk hw
  refine ⟨generated, hgenerated, interaction, hinteraction, hpk, hlength, forgery, hforgery, hfresh, message,
    witness, hof, hconclusion.mono ?_⟩
  intro event he
  rw [hevents, hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ he)
theorem traced_record_support (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.recordedTrace result ∈ support
      (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)) := by
  have hm : QueryRecorded.recordedTrace result ∈
      (QueryRecorded.recordedTrace <$> PaddedGame.tracedExperiment adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map, PMF.support_map]
    exact ⟨result, hr, rfl⟩
  rw [PaddedGame.traced_record_erasure, MonitoredPrivate.pmf_support] at hm
  exact hm
theorem traced_game (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer)
    (hwin : result.1 = true) : GameConclusion adversary answers (QueryRecorded.recordedTrace result) :=
  game_recorded adversary _ (traced_record_support adversary budget hbudget result hr) answers ha hwin
theorem traced_hit_split (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer → answers input = answer)
    (hit : ActualHit answers (QueryRecorded.recordedTrace result).events) :
    FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) ∨
      UnresolvedHit answers (QueryRecorded.recordedTrace result).events :=
  actualHit_known_or_unresolved _ _ (traced_record_support adversary budget hbudget result hr) answers ha hit
end ClaudeWCT.W9.T3.Security.PaddedExtraction
