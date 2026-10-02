import SigGolfCandidate.T3.BPORS

/-!
# SECC shared law: one completed experiment for every case bound

Every case bound of the SecurityP proof (structural hits and `Diverge` [SECC], all-`Good` BPORS [SEC], the
large route) is stated on the **same** joint law `completedExperiment`: SEC's frozen traced padded experiment
`PaddedGame.tracedExperiment`, followed by an independent uniform completion of everything the run never
cached:

* every private coordinate the run did not cache gets an independent uniform output;
* every public input of length at most `maxInputLength` (4096 bytes; the longest honest T3 input, the
  58-endpoint leaf hash, is 960 bytes after `pad64`) that the run did not cache gets an independent
  uniform output; longer uncached public inputs answer 0 (no honest computation ever uses them);
* coins answer 0 (they are never cached and never read by an honest object).

Cached rows are kept, so the completion agrees with the final cache (`completeWith_agrees`) and
`PaddedExtraction.traced_game` applies to it; trace events keep their law (`completed_trace_event`). The
uniform public part is what the eager reference experiment needs (honest objects at never-computed
positions — reference words of unsigned leaves, frontier values, structural targets — keep their generic
uniform laws); the uniform private part makes FTS secrets at unused indices random.

Per-class charges (`classCharge`) count, inside the longest prefix of recorded events whose total charge is
at most `q`, the charge of the events whose input satisfies a class predicate that may read the completion
(chain-prefix vs. other depends on the honest reference word). For disjoint classes the charges add
(`classCharge_or`) and each is at most `q` (`classCharge_le`), which is what turns per-class rates into the
closing's `c·q`.
-/

namespace SigGolfCandidate.T3.Security.SeccLaw
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Public inputs longer than this are never completed uniformly (no honest T3 input is longer than 960 bytes). -/
def maxInputLength : Nat := 4096

/-- The finite universe of public inputs completed uniformly: all byte strings of length ≤ `maxInputLength`. -/
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

/-- Uniform completion tables: private coordinates and the public universe. -/
abbrev PublicTable := publicUniverse → HashOutput
abbrev CompletionTables := FullGame.FullTable × PublicTable

noncomputable instance instFintypeCompletionTables : Fintype CompletionTables := by
  unfold CompletionTables PublicTable FullGame.FullTable
  infer_instance
instance instNonemptyCompletionTables : Nonempty CompletionTables := ⟨(fun _ => 0, fun _ => 0)⟩

/-- Fill an uncached public input from the table (inputs outside the universe answer 0). -/
noncomputable def publicFill (table : PublicTable) (input : HashInput) : HashOutput :=
  if h : input ∈ publicUniverse then table ⟨input, h⟩ else 0

/-- Keep every cached row; fill every uncached private coordinate and public input from the tables. -/
noncomputable def completeWith (state : LazyPrivate.State) (tables : CompletionTables) : Correctness.Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => (state.2 input).getD (publicFill tables.2 input)
  | .inr coordinate => (state.1 coordinate).getD (tables.1 coordinate)

/-- **The shared joint law.** A sample is `(trace result, completion)`. -/
noncomputable def completedExperiment (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    PMF (PaddedGame.TraceResult × Correctness.Answers) :=
  (PaddedGame.tracedExperiment adversary q hq).bind fun result =>
    (PMF.uniformOfFintype CompletionTables).map fun tables =>
      (result, completeWith result.2.2.base.source.2 tables)

/-- Every completion agrees with the final cache, so `PaddedExtraction.traced_game` applies to `z.2`. -/
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

/-- The completion of a sample agrees with that sample's final cache. -/
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

/-- The completion is an independent extension: events of the trace alone keep their law. -/
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

/-! ## Per-class charges -/

/-- Charge of the events of class `cls` inside the longest event prefix of total charge ≤ `budget`. -/
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

/-- A per-sample class predicate (it may read the completion). -/
abbrev SampleClass := PaddedGame.TraceResult × Correctness.Answers → T3.Spec.Domain → Prop

/-- The class charge of a sample, within budget `q`. -/
noncomputable def sampleCharge (cls : SampleClass) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Nat :=
  classCharge (cls z) q (QueryRecorded.recordedTrace z.1).events

/-- The expected class charge on the shared law (the count each class rate multiplies). -/
noncomputable def expectedCharge (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (cls : SampleClass) : ENNReal :=
  ∑' z, completedExperiment adversary q hq z * (sampleCharge cls q z : ENNReal)

/-- Four pairwise disjoint classes share the budget: their expected charges sum to at most `q`. -/
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
