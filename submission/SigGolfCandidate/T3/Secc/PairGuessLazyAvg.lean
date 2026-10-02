import SigGolfCandidate.T3.Secc.PairGuessFinal

/-!
# B-PAIR (CC-2, 1/5): the ω-averaged transport

`pairExperiment` is `omegaLaw ≫ (uniform FTS secrets, reference run)`; hence a reference-experiment event is the
`omegaLaw`-average of its `ftsRun` probabilities (`pairExperiment_avg`), and per-`ω` bounds average
(`pairExperiment_event_le_avg`).
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Avg
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1

/-- The law of `ω` in `pairExperiment` (G's order: seeds, other halves, labels, residual). -/
noncomputable def omegaLaw (adversary : AdversaryP) : ProbComp (Omega (Wots.referenceInputs adversary)) :=
  ($ᵗ ChainGraph.Seeds : ProbComp _) >>= fun seeds =>
    ($ᵗ CanonGraph.OtherHalves : ProbComp _) >>= fun other =>
    ($ᵗ CanonGraph.Labels : ProbComp _) >>= fun labels =>
    (@uniformSample (Wots.referenceInputs adversary → HashOutput)
      (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _) >>=
      fun residual => pure ⟨seeds, other, labels, residual⟩

/-- The FTS-secret part of `pairExperiment` for a fixed `ω`. -/
noncomputable def ftsPart (adversary : AdversaryP) (ω : Omega (Wots.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun fts =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
        (Omega.answers (canon_subset adversary) ω fts, run.2.1, run.2.2)) <$>
      pairRun (Omega.answers (canon_subset adversary) ω fts) adversary

theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw adversary >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]

/-- **The averaged transport**: a reference-experiment event is the `omegaLaw`-average of its `ftsRun`
probabilities. -/
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw adversary] *
      Pr[fun x => E (Omega.answers (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary E]
  rfl

theorem pairExperiment_event_le_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop)
    (bound : Omega (Wots.referenceInputs adversary) → ENNReal)
    (h : ∀ ω, Pr[fun x => E (Omega.answers (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
      ftsRun (canon_subset adversary) ω adversary] ≤ bound ω) :
    Pr[E | pairExperiment adversary] ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * bound ω := by
  rw [pairExperiment_avg]
  exact ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)

end Avg

end SigGolfCandidate.T3.Security.BPair
