import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement

namespace SphincsSecurity
open OracleComp ENNReal
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this
end SphincsSecurity
