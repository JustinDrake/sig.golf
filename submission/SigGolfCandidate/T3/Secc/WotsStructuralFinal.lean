import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
theorem traceInUniverse (adversary : AdversaryP) (q : Nat) : TraceInUniverse adversary q :=
  fun sample hs entry he => reference_trace_mem adversary q sample hs entry he
theorem reference_structural_src_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) :=
  reference_structural_le adversary q (traceInUniverse adversary q)
end SigGolfCandidate.T3.Security.Wots
