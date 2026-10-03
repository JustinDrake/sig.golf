import SigGolfCandidate.T3.BPORS

namespace SigGolfCandidate.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def maxInputLength : Nat := 4096
noncomputable def publicUniverse : Finset HashInput :=
  (Finset.range (maxInputLength + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin k → UInt8)).image fun bytes => List.ofFn bytes
attribute [irreducible] publicUniverse
theorem mem_publicUniverse (input : HashInput) (h : input.length ≤ maxInputLength) : input ∈ publicUniverse := by
  rw [publicUniverse, Finset.mem_biUnion]
  refine ⟨input.length, Finset.mem_range.mpr (by omega), ?_⟩
  rw [Finset.mem_image]
  exact ⟨input.get, Finset.mem_univ _, List.ofFn_get input⟩
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_seccLaw : Fintype Coordinate := coordinateFintype
abbrev PublicTable := publicUniverse → HashOutput
abbrev CompletionTables := FullGame.FullTable × PublicTable
noncomputable instance instFintypeCompletionTables : Fintype CompletionTables := by
  unfold CompletionTables PublicTable FullGame.FullTable
  infer_instance
instance instNonemptyCompletionTables : Nonempty CompletionTables := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def publicFill (table : PublicTable) (input : HashInput) : HashOutput :=
  if h : input ∈ publicUniverse then table ⟨input, h⟩ else 0
noncomputable def completeWith (state : LazyPrivate.State) (tables : CompletionTables) : Correctness.Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (publicFill tables.2 input)
  | .inr coordinate => (state.1 coordinate).getD (tables.1 coordinate)
noncomputable def completedExperiment (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    PMF (PaddedGame.TraceResult × Correctness.Answers) :=
  (PaddedGame.tracedExperiment adversary q hq).bind fun result =>
    (PMF.uniformOfFintype CompletionTables).map fun tables =>
      (result, completeWith result.2.2.base.source.2 tables)
theorem completeWith_agrees (state : LazyPrivate.State) (tables : CompletionTables)
    (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
    (h : SourceReplay.known state input = some answer) : completeWith state tables input = answer := by
  cases input with
  | inl input =>
      cases input with
      | inl n => cases h
      | inr input =>
          change state.2 input = some answer at h
          simp only [completeWith, h, Option.getD_some]
  | inr coordinate =>
      change state.1 coordinate = some answer at h
      simp only [completeWith, h, Option.getD_some]
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
noncomputable def classCharge (cls : T3.Spec.Domain → Prop) : Nat → List FirstHit.QueryEvent → Nat
  | _, [] => 0
  | budget, event :: rest =>
      if FullGame.queryCharge event.input ≤ budget then
        (if cls event.input then FullGame.queryCharge event.input else 0) +
          classCharge cls (budget - FullGame.queryCharge event.input) rest
      else 0
theorem classCharge_or (P Q : T3.Spec.Domain → Prop) (hdisj : ∀ input, ¬(P input ∧ Q input))
    (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge (fun input => P input ∨ Q input) budget events =
      classCharge P budget events + classCharge Q budget events := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hpq hp hq hq' <;> first
        | omega
        | (rw [ih]; omega)
        | (exfalso; exact hdisj _ ⟨hp, hq⟩)
        | (simp_all)
theorem classCharge_le (cls : T3.Spec.Domain → Prop) (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge cls budget events ≤ budget := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hcls
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · have := ih (budget - FullGame.queryCharge event.input); omega
      · omega
theorem classCharge_mono (P Q : T3.Spec.Domain → Prop) (hPQ : ∀ input, P input → Q input)
    (budget : Nat) (events : List FirstHit.QueryEvent) :
    classCharge P budget events ≤ classCharge Q budget events := by
  induction events generalizing budget with
  | nil => simp [classCharge]
  | cons event rest ih =>
      simp only [classCharge]
      split_ifs with hc hp hq hq <;> first
        | (have := ih (budget - FullGame.queryCharge event.input); omega)
        | (exact absurd (hPQ _ hp) hq)
        | omega
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → T3.Spec.Domain → Prop
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
end SigGolfCandidate.T3.Security.SeccLaw
