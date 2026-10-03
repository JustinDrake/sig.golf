import SigGolfCandidate.T3.Secc.WotsTransportTable
import SigGolfCandidate.T3.Secc.WotsExtractVerify
import SigGolfCandidate.T3.Secc.SeccSufSigned

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB buildFts buildTree signPayload
def GameCaseCPinned (adversary : AdversaryP) (answers : Answers) (signed : Prop → Prop)
    (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated interaction checked, GameSplit adversary result generated interaction checked ∧
    generated.value.1 = Extract.honestRoot answers 0 0 ∧
    interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf answers generated.value.1 forgery message witness ∧
      signed (BPB.SignedDigest interaction.value.2 message witness) ∧
      BPB.CaseCAt answers message witness result.events
abbrev CaseCFreshPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  GameCaseCPinned adversary z.2 Not (QueryRecorded.recordedTrace z.1)
abbrev CaseCSignedPinned (adversary : AdversaryP) (z : PaddedGame.TraceResult × Answers) : Prop :=
  GameCaseCPinned adversary z.2 id (QueryRecorded.recordedTrace z.1)
theorem GameSplit.extends {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × T3.Cache)}
    {interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
theorem GameCaseCPinned.linked {adversary : AdversaryP} {answers : Answers} {signed : Prop → Prop}
    {result : FirstHit.Recorded Bool} (h : GameCaseCPinned adversary answers signed result) :
    BPB.GameCaseC adversary answers signed result := by
  obtain ⟨generated, interaction, checked, hsplit, hpk, hlen, forgery, hf, hfresh, message, witness, hof, hs, hC⟩ := h
  exact ⟨generated, hsplit.1, interaction, hsplit.2.1, hsplit.extends, hpk, hlen, forgery, hf, hfresh, message,
    witness, hof, hs, hC⟩
theorem caseCSignedPinned_impossible (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) : ¬CaseCSignedPinned adversary z :=
  fun h => BPB.caseC_signed_impossible adversary q hq z hz hclean h.linked
theorem completed_split (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hclean : QueryRecorded.CleanWin q z.1) :
    CaseAB adversary z ∨ CaseCFreshPinned adversary z ∨ CaseCSignedPinned adversary z := by
  by_cases hab : CaseAB adversary z
  · exact Or.inl hab
  right
  unfold CaseAB CaseABAt at hab
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
  obtain ⟨N, hdc, hN, -, hS, hcase⟩ := verifyP_wots_cases z.2 message' generated.value.1 witness' hpk hv
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
