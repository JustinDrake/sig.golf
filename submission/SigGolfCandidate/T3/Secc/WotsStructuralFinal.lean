import SigGolfCandidate.T3.Secc.WotsStructural
import SigGolfCandidate.T3.Secc.WotsReferenceInputs

/-!
# Stream S: the structural bound without hypotheses

F2's `reference_trace_mem` (request S-1) discharges `TraceInUniverse`, so `reference_structural_le` holds
unconditionally (`reference_structural_src_le`).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final

/-- R3's trace stays in its eager universe (F2's `reference_trace_mem`). -/
theorem traceInUniverse (adversary : AdversaryP) (q : Nat) : TraceInUniverse adversary q :=
  fun sample hs entry he => reference_trace_mem adversary q sample hs entry he

/-- **`reference_structural_le`, unconditional**: `Pr_R3[StructuralHitSrc] ≤ 2^-128 · E_R3[#O-class queries]`. -/
theorem reference_structural_src_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) :=
  reference_structural_le adversary q (traceInUniverse adversary q)

end SigGolfCandidate.T3.Security.Wots
