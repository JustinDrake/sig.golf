import SigGolfCandidate.ClaudeWCT.W9.T3.BPORS
import SigGolfCandidate.T3.Secc.SeccLaw

namespace ClaudeWCT.W9.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.SeccLaw
open SigGolfCandidate.T3.Correctness
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9SeccLaw : Fintype Coordinate := coordinateFintype
noncomputable def completedExperiment (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    PMF (PaddedGame.TraceResult × Correctness.Answers) :=
  (PaddedGame.tracedExperiment adversary q hq).bind fun result =>
    (PMF.uniformOfFintype CompletionTables).map fun tables =>
      (result, completeWith result.2.2.base.source.2 tables)
theorem completed_agrees (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (completedExperiment adversary q hq).support) :
    z.1 ∈ (PaddedGame.tracedExperiment adversary q hq).support ∧
      ∀ input answer, SourceReplay.known z.1.2.2.base.source.2 input = some answer → z.2 input = answer := by
  unfold completedExperiment at hz
  rw [PMF.mem_support_bind_iff] at hz
  obtain ⟨result, hresult, hz⟩ := hz
  rw [PMF.support_map] at hz
  obtain ⟨tables, -, rfl⟩ := hz
  exact ⟨hresult, fun input answer h => completeWith_agrees _ tables input answer h⟩
theorem completed_trace_event (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (event : PaddedGame.TraceResult → Prop) :
    Pr[fun z => event z.1 | completedExperiment adversary q hq] =
      Pr[event | PaddedGame.tracedExperiment adversary q hq] := by
  have hmap : (Prod.fst <$> completedExperiment adversary q hq : PMF _) =
      PaddedGame.tracedExperiment adversary q hq := by
    unfold completedExperiment
    rw [PMF.monad_map_eq_map, PMF.map_bind]
    conv_rhs => rw [← PMF.bind_pure (PaddedGame.tracedExperiment adversary q hq)]
    congr 1
    funext result
    rw [PMF.map_comp]
    exact PMF.map_const _ _
  rw [← hmap, probEvent_map]
  rfl
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → SigGolfCandidate.T3.Spec.Domain → Prop
noncomputable def sampleCharge (cls : SampleClass) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Nat :=
  classCharge (cls z) q (QueryRecorded.recordedTrace z.1).events
noncomputable def expectedCharge (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (cls : SampleClass) : ENNReal :=
  ∑' z, completedExperiment adversary q hq z * (sampleCharge cls q z : ENNReal)
theorem expectedCharge_four_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (A B C D : SampleClass)
    (hAB : ∀ z input, ¬(A z input ∧ B z input)) (hAC : ∀ z input, ¬(A z input ∧ C z input))
    (hAD : ∀ z input, ¬(A z input ∧ D z input)) (hBC : ∀ z input, ¬(B z input ∧ C z input))
    (hBD : ∀ z input, ¬(B z input ∧ D z input)) (hCD : ∀ z input, ¬(C z input ∧ D z input)) :
    expectedCharge adversary q hq A + expectedCharge adversary q hq B + expectedCharge adversary q hq C +
      expectedCharge adversary q hq D ≤ q := by
  have hpoint : ∀ z, (sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z ≤ q := by
    intro z
    have h1 := classCharge_or (A z) (B z) (hAB z) q (QueryRecorded.recordedTrace z.1).events
    have h2 := classCharge_or (fun input => A z input ∨ B z input) (C z)
      (fun input h => h.1.elim (fun ha => hAC z input ⟨ha, h.2⟩) (fun hb => hBC z input ⟨hb, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have h3 := classCharge_or (fun input => (A z input ∨ B z input) ∨ C z input) (D z)
      (fun input h => h.1.elim (fun h' => h'.elim (fun ha => hAD z input ⟨ha, h.2⟩)
        (fun hb => hBD z input ⟨hb, h.2⟩)) (fun hc => hCD z input ⟨hc, h.2⟩)) q
      (QueryRecorded.recordedTrace z.1).events
    have hle := classCharge_le (fun input => ((A z input ∨ B z input) ∨ C z input) ∨ D z input) q
      (QueryRecorded.recordedTrace z.1).events
    unfold sampleCharge
    exact_mod_cast (show _ ≤ q by omega)
  unfold expectedCharge
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' z, completedExperiment adversary q hq z *
          ((sampleCharge A q z : ENNReal) + sampleCharge B q z + sampleCharge C q z + sampleCharge D q z) := by
      congr 1; funext z; ring
    _ ≤ ∑' z, completedExperiment adversary q hq z * (q : ENNReal) :=
      ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl (hpoint z)
    _ = q := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
end ClaudeWCT.W9.T3.Security.SeccLaw
