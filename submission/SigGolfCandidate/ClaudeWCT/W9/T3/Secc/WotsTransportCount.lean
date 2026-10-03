import SigGolfCandidate.T3.Secc.WotsTransportCount
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransport
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportTable
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportR3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTransportShort
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReferenceInputs

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildTree ClaudeWCT.WCT9.Rev3.signPayload ClaudeWCT.WCT9.signPayloadWith ClaudeWCT.WCT9.buildCoordinate GameWith.idealGame
noncomputable local instance instFintypeCoordinate_wotsTransportCount : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsTransportCount : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
namespace Ref
open SigGolfCandidate.T3.Security.Wots.Ref
section Capped
variable {ι : Type} (selected : ι → Prop) [DecidablePred selected] (cls : ι → Prop)
end Capped
section Steps
variable (C : T3.Spec.Domain → Prop)
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
end ClaudeWCT.W9.T3.Security.Wots
