import SigGolfCandidate.T3.Secc.SeccSufPayload
import SigGolfCandidate.T3.Secc.SeccLaw

/-! # B-SUF (3/4): signature reuse is impossible in case (C) (strong unforgeability)

BP-B §2.1. On the shared law `SeccLaw.completedExperiment`, case (C) of the extraction on a message whose forgery
randomizer was used by a successful logged signature (`SignedDigest`) contradicts the game's own freshness
predicate, deterministically:

* witness form: `Fresh` excludes every successful signature on the message;
* signature form: the forgery's expansion is the honest payload for its randomizer (`caseC_expansion_is_payload`,
  with the honest key-generation cache), and so is the logged signature (it resolves in the interaction's final
  tables, which the completion agrees with), so the forgery *is* the logged signature.

**Adjustment of the BP-B contract (documented).** The prototype `GameCaseC` quantified the key-generation and
interaction records existentially with no tie to the sampled trace; then the completion `z.2` need not agree with
the interaction's lazy tables, the logged signature need not be the payload under `z.2`, and
`caseC_signed_impossible` is unprovable (a foreign supported interaction can satisfy every clause). Here
`GameCaseC` carries the link `SourceReplay.Extends interaction.state result.state` (the interaction is a prefix of
the recorded trace), which the extraction provides: `traced_game_linked` is `PaddedExtraction.traced_game` with
that link, and `linked_split` routes its conclusion to cases (A)/(B), `CaseCFresh` or `CaseCSigned`. -/

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufSigned : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree

/-! ## Case-(C) vocabulary (BP-B contract, with the trace link) -/

/-- All four layers `Good` and the FTS bytes honest-shaped, for the witness's own recorded digest query. -/
def CaseCAt (answers : Correctness.Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < attemptLimit ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
    (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
      FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧ digestGate digestAnswer = true ∧
    (∀ lay : Layer, Extract.Good answers witness (digestAnswer.toNat % 2 ^ 31) lay) ∧
    FtsExtract.FtsShaped answers digestAnswer witness

/-- The forgery's message carries a successful logged signature with the forgery's randomizer. -/
def SignedDigest (log : QueryLog Requests) (message : Message) (witness : WBytes) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧
    signature.rho = wrho witness

/-- `PaddedExtraction.GameConclusion` restricted to branch (C), with the reuse flag exposed and the interaction
tied to the recorded trace (`Extends`). -/
def GameCaseC (adversary : AdversaryP) (answers : Correctness.Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        signed (SignedDigest interaction.value.2 message witness) ∧
        CaseCAt answers message witness result.events

/-- Case (C) with a digest never signer-accepted under the forgery's randomizer (SEC's charged part). -/
abbrev CaseCFresh (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseC adversary z.2 Not (QueryRecorded.recordedTrace z.1)

/-- Case (C) on a signer-accepted digest: the strong-unforgeability subcase. -/
abbrev CaseCSigned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  GameCaseC adversary z.2 id (QueryRecorded.recordedTrace z.1)

/-! ## The linked game conclusion -/

/-- `PaddedExtraction.GameConclusion` with the interaction tied to the trace. -/
def GameConclusionLinked (adversary : AdversaryP) (answers : Correctness.Answers)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        PaddedExtraction.Conclusion answers message witness result.events

section linked
attribute [local irreducible] keygen verifyP expandB

/-- `PaddedExtraction.game_recorded`, keeping the trace link of the interaction record. -/
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
  have hpk : generated.value.1 = Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk answers
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

/-- **`PaddedExtraction.traced_game` with the trace link.** -/
theorem traced_game_linked (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Correctness.Answers)
    (ha : ∀ input answer, SourceReplay.known result.2.2.base.source.2 input = some answer →
      answers input = answer)
    (hwin : result.1 = true) : GameConclusionLinked adversary answers (QueryRecorded.recordedTrace result) :=
  game_recorded_linked adversary _ (PaddedExtraction.traced_record_support adversary budget hbudget result hr)
    answers ha hwin

end linked

/-- Cases (A) and (B) of the extraction (an actual structural hit, or a divergence below `Good` layers). -/
def ConclusionAB (answers : Correctness.Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = digestAnswer ∧
      (∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), digestAnswer⟩ :
        FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧ digestGate digestAnswer = true ∧
      (PaddedExtraction.ActualHit answers events ∨
        (∃ lay : Layer, Extract.Diverge answers witness (digestAnswer.toNat % 2 ^ 31) lay
          (events.map FirstHit.QueryEvent.input) ∧
          ∀ above : Layer, above.val < lay.val → Extract.Good answers witness (digestAnswer.toNat % 2 ^ 31) above))

/-- `GameConclusionLinked` restricted to cases (A)/(B). -/
def GameCaseAB (adversary : AdversaryP) (answers : Correctness.Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      SourceReplay.Extends interaction.state result.state ∧
      generated.value.1 = Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length ≤ 2 ^ 32 ∧
      ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
      ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
        ConclusionAB answers message witness result.events

/-- **Routing of the linked conclusion**: cases (A)/(B), or case (C) with a fresh or a signed digest. -/
theorem linked_split (adversary : AdversaryP) (answers : Correctness.Answers) (result : FirstHit.Recorded Bool)
    (h : GameConclusionLinked adversary answers result) :
    GameCaseAB adversary answers result ∨ GameCaseC adversary answers Not result ∨
      GameCaseC adversary answers id result := by
  obtain ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hc⟩ := h
  obtain ⟨N, hdc, hN, hq, hS, hgate, hcase⟩ := hc
  rcases hcase with hA | hB | ⟨hgood, hfts⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof,
      N, hdc, hN, hq, hS, hgate, Or.inl hA⟩
  · exact Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness, hof,
      N, hdc, hN, hq, hS, hgate, Or.inr hB⟩
  · by_cases hsd : SignedDigest interaction.value.2 message witness
    · exact Or.inr (Or.inr ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, N, hdc, hN, hq, hS, hgate, hgood, hfts⟩)
    · exact Or.inr (Or.inl ⟨generated, hg, interaction, hi, hext, hpk, hlen, forgery, hf, hfresh, message, witness,
        hof, hsd, N, hdc, hN, hq, hS, hgate, hgood, hfts⟩)

/-! ## Logged signatures resolve in the interaction's final tables -/

/-- Every entry of a logged lazy-table run of the authenticated signer is the signer's deterministic answer in
the run's final tables. -/
theorem logged_resolves {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α)
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

/-- A successful signer answer is the payload record for the signer's nonce. -/
theorem authenticatedSign_payload (answers : Correctness.Answers) (published : T3.Cache) (request : Request)
    (sig : Signature) (h : evalWithAnswerFn answers (FullGame.authenticatedSign published request) = some sig) :
    request.cache = published ∧ sig.rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (evalWithAnswerFn answers (payloadRecordForNonce published sig.rho request.message)).1 = some sig := by
  unfold FullGame.authenticatedSign at h
  simp only [evalWithAnswerFn_bind] at h
  by_cases hc : request.cache = published
  · rw [if_pos hc] at h
    have hp : (evalWithAnswerFn answers (payloadRecord published request.message)).1 = some sig := by
      have := congrArg (evalWithAnswerFn answers) (payloadRecord_erasure published request.message)
      rw [SigGolfCandidate.T3M.eval_map] at this
      rw [this, ← hc]
      exact h
    unfold payloadRecord at hp
    rw [evalWithAnswerFn_bind] at hp
    have hs : (evalWithAnswerFn answers (payloadRecordForNonce published
        (evalWithAnswerFn answers (privateNonce request.message)) request.message)).2 ≠ none :=
      payloadRecord_success_has_digest answers published _ request.message (by rw [hp]; simp)
    obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hs
    have hrho := (SigningRecords.payloadAfterDigest_fields answers published _ output sig
      (SigningRecords.recordForNonce_selected_payload answers published _ request.message sig output hp ho)).1
    refine ⟨hc, hrho, ?_⟩
    rw [hrho]
    exact hp
  · rw [if_neg hc] at h
    simp at h

/-! ## Strong unforgeability in case (C) -/

/-- **Deterministic core.** If the answers agree with the trace's final tables, case (C) with a signed digest is
impossible. -/
theorem gameCaseC_signed_false (adversary : AdversaryP) (answers : Correctness.Answers)
    (result : FirstHit.Recorded Bool)
    (ha : ∀ input answer, SourceReplay.known result.state input = some answer → answers input = answer) :
    ¬GameCaseC adversary answers id result := by
  rintro ⟨generated, hg, interaction, hi, hext, hpk, -, forgery, hforgery, hfresh, message, witness, hof, hsigned,
    hC⟩
  have hirun := FirstHit.recorded_support _ _ _ hi
  have hgext : SourceReplay.Extends generated.state interaction.state :=
    SourceReplay.run_extends _ generated.state _ hirun
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → answers input = answer :=
    fun input answer hk => ha input answer (SourceReplay.known_mono _ _ hext hk)
  have hgen : evalWithAnswerFn answers keygen = generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅, ∅)
      (generated.value, generated.state) (FirstHit.recorded_support _ _ _ hg)).eval answers
        (fun input answer hk => hai input answer (SourceReplay.known_mono _ _ hgext hk))
  have hcache : generated.value.2.region = Correctness.cacheRegion (Correctness.maskedTop answers) := by
    rw [← hgen]
    exact (Correctness.keygen_correct answers).2.1
  obtain ⟨entry, hentry, hmsg, σm, hσm, hrho⟩ := hsigned
  have hres := logged_resolves generated.value.2 _ generated.state _ hirun entry hentry
  have hlog : evalWithAnswerFn answers (FullGame.authenticatedSign generated.value.2 entry.1) = some σm := by
    rw [hres.eval answers hai, hσm]
  obtain ⟨-, -, hpay⟩ := authenticatedSign_payload answers generated.value.2 entry.1 σm hlog
  cases forgery with
  | witness m w =>
      exact hfresh ⟨entry, hentry, by rw [hmsg]; exact hof.1, by rw [hσm]; rfl⟩
  | signature m σ =>
      obtain ⟨hm, hexp⟩ := hof
      rw [eval_expandB] at hexp
      cases hx : evalWithAnswerFn answers (expandN message generated.value.1 σ) with
      | none => rw [hm] at hx; rw [hx] at hexp; simp at hexp
      | some x =>
          obtain ⟨N, wit⟩ := x
          rw [← hm, hx] at hexp
          simp only [Option.map_some, Option.some.injEq] at hexp
          subst hexp
          have F := expandN_facts answers message _ σ N wit hx
          obtain ⟨N', -, hN', -, -, -, hgood, hfts⟩ := hC
          have hNN : N' = N := by
            rw [← hN', wrho_witEnc, wdc_witEnc, F.sig]
            exact F.digest
          subst hNN
          have hpayσ := BSuf.caseC_expansion_is_payload answers generated.value.2 message _ σ N' wit hcache hpk hx
            hgood hfts
          have hrhoσ : σm.rho = σ.rho := by rw [hrho, wrho_witEnc, F.sig]
          rw [hmsg, hrhoσ, hpayσ, Option.some.injEq] at hpay
          subst hpay
          exact hfresh ⟨entry, hentry, by rw [hmsg]; exact hm, hσm⟩

/-- **`caseC_signed_impossible`** (BP-B §2.1, on the shared law): the strong-unforgeability subcase never happens.
The clean-win hypothesis is not needed (kept for interface parity). -/
theorem caseC_signed_impossible (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (_hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSigned adversary z :=
  gameCaseC_signed_false adversary z.2 _ (SeccLaw.completed_agrees adversary q hq z hz).2

end SigGolfCandidate.T3.Security.BPB
