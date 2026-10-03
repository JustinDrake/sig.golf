import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Replay

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
abbrev SigningEntry := (request : Message) × SigningSpec.Range request
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
abbrev FewTimeView := Index × (IndexGroup → FtsLeaf)
theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * ftsOpenings) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ← pow_mul, ← pow_add]
noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R
end SphincsSecurity.Concrete
end
