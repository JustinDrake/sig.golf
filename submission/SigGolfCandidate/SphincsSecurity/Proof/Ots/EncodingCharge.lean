import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingTarget
/-!
# Amortized charge for encoding collisions

The cache-local encoding target at one one-time position is unique. Inputs cached at that encoding
tweak before the target is pinned pay one unit each for the answer that pins it. Once pinned, a
fresh encoding query has only that one target.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

structure EncodingPosition where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  deriving DecidableEq, Fintype

def EncodingPosition.domain (position : EncodingPosition) : HashDomain :=
  .encoding position.lay position.tree position.leafIdx

/-- An encoding input at `position`: the encoding tweak, then any 16 bytes in the parameter slot (the
first half of the message) and any payload. The parameter is not used. -/
def AtEncodingPosition (_parameter : PublicParameter) (input : HashInput)
    (position : EncodingPosition) : Prop :=
  ∃ first payload, input = tweakableHashInput first position.domain payload

theorem atEncodingPosition_unique {parameter : PublicParameter} {input : HashInput}
    {left right : EncodingPosition} (hleft : AtEncodingPosition parameter input left)
    (hright : AtEncodingPosition parameter input right) : left = right := by
  obtain ⟨leftFirst, leftPayload, hleft⟩ := hleft
  obtain ⟨rightFirst, rightPayload, hright⟩ := hright
  have hdomain := (tweakableHashInput_injective' (by trivial) (by trivial)
    (hleft.symm.trans hright)).1
  obtain ⟨leftLay, leftTree, leftLeaf⟩ := left
  obtain ⟨rightLay, rightTree, rightLeaf⟩ := right
  simp only [EncodingPosition.domain, HashDomain.encoding.injEq] at hdomain
  obtain ⟨rfl, rfl, rfl⟩ := hdomain
  rfl

theorem AtEncodingPosition.not_atPosition {parameter : PublicParameter} {input : HashInput}
    {encodingPosition : EncodingPosition} (hencoding : AtEncodingPosition parameter input encodingPosition)
    (position : Position) : ¬ AtPosition parameter input position := by
  rintro ⟨structuralPayload, hstructural⟩
  obtain ⟨encodingFirst, encodingPayload, hencodingInput⟩ := hencoding
  have hdomain := (tweakableHashInput_injective' (by trivial)
    position.domain_inRange (hencodingInput.symm.trans hstructural)).1
  cases position <;> simp [EncodingPosition.domain, Position.domain] at hdomain

end SphincsSecurity.Concrete
