import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Slot

namespace SphincsSecurity
open OracleComp ENNReal
variable {D R : Type} [DecidableEq R]
namespace Concrete
noncomputable local instance secretProbeSampleableOfFintype {T : Type} [Fintype T] [Nonempty T] : SampleableType T :=
  SampleableType.ofFintype T
structure FtsSecretProbe where
  index : Index
  tree : FtsTree
  leafIdx : FtsLeaf
  candidate : Digest
def FtsSecretProbe.input (parameter : PublicParameter) (probe : FtsSecretProbe) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf probe.index probe.tree probe.leafIdx.val)
    (digestBytes probe.candidate)
theorem FtsSecretProbe.input_injective (parameter : PublicParameter) :
    Function.Injective (FtsSecretProbe.input parameter) := by
  intro left right heq
  have hparts := tweakableHashInput_injective parameter (HashDomain.ftsLeaf_inRange _ _ _)
    (HashDomain.ftsLeaf_inRange _ _ _) heq
  have hdomain : left.index = right.index ∧ left.tree = right.tree ∧
      left.leafIdx = right.leafIdx := by
    simpa only [HashDomain.ftsLeaf.injEq, Fin.val_inj] using hparts.1
  have hcandidate : left.candidate = right.candidate := digestBytes_injective hparts.2
  cases left
  cases right
  simp only [FtsSecretProbe.mk.injEq] at hdomain hcandidate ⊢
  exact ⟨hdomain.1, hdomain.2.1, hdomain.2.2, hcandidate⟩
end Concrete
end SphincsSecurity
