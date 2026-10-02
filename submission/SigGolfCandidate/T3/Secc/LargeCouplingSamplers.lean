import SigGolfCandidate.T3.Secc.LargeCouplingPsi

/-!
# LR-34 (law): the uniform samplers of the large-route coupling

One shared (scoped) sampler per table type of the law and the chain modules, so that statements of different
modules use the same instance terms (`open SigGolfCandidate.T3.Security.LargeCoupling.Samplers`). The private table
uses SEC's sampler `Derivation.outputSampler`, every other table `SampleableType.ofFintype`.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling.Samplers
open OracleComp
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open LargeResidual CanonGraph CanonEncoding
attribute [local instance] Classical.propDecidable

noncomputable scoped instance (priority := high) fintypeCoordinate : Fintype Coordinate := coordinateFintype
noncomputable scoped instance (priority := high) samplerFull : SampleableType FullGame.FullTable :=
  Derivation.outputSampler Coordinate
noncomputable scoped instance (priority := high) samplerLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerOthers : SampleableType OtherHalves :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerPublic (U : Finset HashInput) :
    SampleableType (U → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerCell (U : Finset HashInput) :
    SampleableType (Cell U → LargeResidual.HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerLow : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerNonces : SampleableType (Message → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerVals : SampleableType (Coord → Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerWorld : SampleableType (WCoord → LargeResidual.Digest) :=
  SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRows :
    SampleableType (EncLeaf → Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerRowsFlat :
    SampleableType (EncLeaf × Fin (2 ^ 22) → HashOutput) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) decEqNonceOutside :
    DecidableEq (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Classical.decEq _
noncomputable scoped instance (priority := high) fintypeNonceOutside :
    Fintype (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf) := Subtype.fintype _
noncomputable scoped instance (priority := high) samplerNonceOutside :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside nonceHalf → Digest) := SampleableType.ofFintype _
noncomputable scoped instance (priority := high) samplerEncOutside (U : Finset HashInput) (hE : encInputs ⊆ U)
    (labels : Labels) :
    SampleableType (SphincsSecurity.Concrete.UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :=
  SampleableType.ofFintype _

end SigGolfCandidate.T3.Security.LargeCoupling.Samplers
