import SigGolfCandidate.T3.Secc.WotsExtractVerify
import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.SeccSufSigned

/-!
# Stream W, part 5: the case split of a clean win (BP-A §3, `traced_wots_split`; linked form for the assembly)

SEC's game decomposition (`PaddedExtraction.game_recorded`, B-SUF's `game_recorded_linked`) re-run to expose, for the
logged forgery under any agreeing completion, the accepting byte verification and the fact that **every public query
of that verification is an event of the recorded trace** (with the completion's answer), together with the trace link
`SourceReplay.Extends interaction.state result.state` (`game_accepting_linked`). Then `verifyP_wots_cases_src` splits
it:

* `completed_linked_split` (the assembly's form, on the shared law `SeccLaw.completedExperiment`): case (A)+(B) linked
  (`GameCaseWots`: a source-sized WOTS primitive event among the verifier's queries of a linked forgery, which are
  recorded events; hence `WotsPrimitive z.2` on the entries of the recorded events, `GameCaseWots.recorded`), or
  `BPB.CaseCFresh`, or `BPB.CaseCSigned` (B-SUF's linked case-C events; `SignedDigest` decided as in `linked_split`).
  `completed_linked_split_events`: the same with (i) flattened to `WotsPrimitive z.2 (recordedEntries …)`;
  `completed_linked_split_fresh`: (iii) removed by `BPB.caseC_signed_impossible`.
* The unlinked prototype forms are kept: `Wots.traced_wots_split`, `completed_wots_split` (+ `_src`).
-/

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB

/-! ## Recorded entries -/

/-- The public entries of a recorded event list, answered by the completion (on a completion agreeing with the final
cache these are the recorded answers). -/
def recordedEntries (answers : Answers) (events : List FirstHit.QueryEvent) : List Entry :=
  entriesOf answers (events.map FirstHit.QueryEvent.input)

/-- If every public query of `qs` is a recorded event with the completion's answer, the entries of `qs` are recorded
entries. -/
theorem entries_recorded {answers : Answers} {qs : List Spec.Domain} {events : List FirstHit.QueryEvent}
    (hrec : ∀ input, (.inl (.inr input) : Spec.Domain) ∈ qs →
      ∃ prior, (⟨prior, .inl (.inr input), answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈ events) :
    ∀ e ∈ entriesOf answers qs, e ∈ recordedEntries answers events := by
  rintro ⟨input, answer⟩ he
  obtain ⟨hq, ha⟩ := mem_entriesOf_iff.mp he
  obtain ⟨prior, hev⟩ := hrec input hq
  exact mem_entriesOf_iff.mpr ⟨List.mem_map.mpr ⟨_, hev, rfl⟩, ha⟩

/-! ## The linked accepting verification -/

/-- Case (A)+(B) with source-sized addresses (unlinked; see `GameCaseWots` for the linked form). -/
def VerifierWotsSrc (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (verifyP message publicKey witness) = true ∧
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP message publicKey witness)))

theorem VerifierWotsSrc.toVerifierWots {answers : Answers} {publicKey : Digest} {forgery : ForgeryP}
    (h : VerifierWotsSrc answers publicKey forgery) : VerifierWots answers publicKey forgery := by
  obtain ⟨message, witness, hof, hv, hp⟩ := h
  exact ⟨message, witness, hof, hv, hp.toPrimitive⟩

/-- The final check of an accepting verdict: the log bound, a fresh logged forgery, an actual accepting byte
verification of its witness, and every public query of that verification is a recorded event of the verdict. -/
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

/-- **The linked accepting verification** (B-SUF's `game_recorded_linked` exposing the byte verification): actual
keygen record, actual adaptive logged interaction **linked to the trace** (`Extends`), honest public key, log bound,
fresh logged forgery, accepting `verifyP` of its witness under `answers`, whose public queries are all recorded
events of `result` with `answers`' answers. -/
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

/-! ## Linked case (A)+(B) -/

/-- **Case (A)+(B), linked** (the assembly's event (i)): a linked fresh logged forgery (as in `BPB.GameCaseC`) with an
accepting byte verification whose public queries are recorded events of `result`, and a source-sized WOTS primitive
event among those queries. -/
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

/-- Linked case (A)+(B) puts a (source-sized) WOTS primitive event on the entries of the recorded events. -/
theorem GameCaseWots.recordedSrc {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitiveSrc answers (recordedEntries answers result.events) := by
  obtain ⟨_generated, _hg, _interaction, _hi, _hext, _hpk, _hlen, _forgery, _hf, _hfresh, _message, _witness, _hof,
    _hv, hrec, hprim⟩ := h
  exact WotsPrimitiveSrc.mono hprim (entries_recorded hrec)

theorem GameCaseWots.recorded {adversary : AdversaryP} {answers : Answers} {result : FirstHit.Recorded Bool}
    (h : GameCaseWots adversary answers result) : WotsPrimitive answers (recordedEntries answers result.events) :=
  h.recordedSrc.toPrimitive

/-- Linked case (A)+(B) gives the unlinked `VerifierWots` of its forgery. -/
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

/-! ## The split -/

/-- **The linked split of a recorded win** (deterministic): case (A)+(B) linked, or B-SUF's linked case (C) with a
fresh or a signed digest. -/
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
      exact ⟨N, hdc, hN, ⟨prior, by simpa only [hans] using hev⟩, hS, by simpa only [← hN] using verifyP_digestGate answers message generated.value.1 witness hv, hgood, hshape⟩
    by_cases hsd : BPB.SignedDigest interaction.value.2 message witness
    · exact Or.inr (Or.inr ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)
    · exact Or.inr (Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, hCat⟩)

/-- **The final split on the shared law** (assembly form): for `z` in the support of `SeccLaw.completedExperiment`
with a clean win, (i) linked case (A)+(B) on the recorded trace (`GameCaseWots`, giving `WotsPrimitive z.2` on the
recorded entries: `GameCaseWots.recorded`), or (ii) `BPB.CaseCFresh adversary z`, or (iii) `BPB.CaseCSigned
adversary z`. -/
theorem completed_linked_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z ∨
      BPB.CaseCSigned adversary z := by
  obtain ⟨hr, ha⟩ := SeccLaw.completed_agrees adversary q hq z hz
  exact game_linked_split adversary _ (PaddedExtraction.traced_record_support adversary q hq z.1 hr) z.2 ha hwin.1

/-- The final split with (i) flattened: a (source-sized) WOTS primitive event on the entries of the recorded events. -/
theorem completed_linked_split_events (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    WotsPrimitiveSrc z.2 (recordedEntries z.2 (QueryRecorded.recordedTrace z.1).events) ∨
      BPB.CaseCFresh adversary z ∨ BPB.CaseCSigned adversary z :=
  (completed_linked_split adversary q hq z hz hwin).imp_left GameCaseWots.recordedSrc

/-- The final split with the signed subcase removed (`BPB.caseC_signed_impossible`). -/
theorem completed_linked_split_fresh (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hwin : QueryRecorded.CleanWin q z.1) :
    GameCaseWots adversary z.2 (QueryRecorded.recordedTrace z.1) ∨ BPB.CaseCFresh adversary z := by
  rcases completed_linked_split adversary q hq z hz hwin with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (BPB.caseC_signed_impossible adversary q hq z hz hwin h).elim

/-! ## Unlinked forms (prototype interface) -/

/-- **W∘SEC split, source-sized form** (unlinked). -/
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

/-- **The split on the shared law, source-sized form** (unlinked). -/
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

/-- **The split on the shared law** (unlinked): on a clean win, the logged forgery is in case (A)+(B) or case (C)
under the sample's own completion `z.2`. -/
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

end SigGolfCandidate.T3.Security.WotsExtract

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] keygen verifyP expandB

/-- **W∘SEC split** (`traced_game` + `verifyP_wots_cases`): on a clean traced win, under every agreeing completion,
the logged forgery is in case (A)+(B) or case (C). (Linked assembly form: `WotsExtract.completed_linked_split`.) -/
theorem traced_wots_split (adversary : Final.AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
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

end SigGolfCandidate.T3.Security.Wots
