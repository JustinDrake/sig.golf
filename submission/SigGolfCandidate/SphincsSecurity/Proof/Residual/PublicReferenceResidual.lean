import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.CanonicalResidualQuery
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingFamilyOracleSplit
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableOverwrite
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem layerMessagePositions_public (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (index : Index) (lay : Layer) :
    ∀ position ∈ layerMessagePositions index lay,
      ¬CanonicalCoordinate.Hidden words disclosed (.graph position) := by
  intro position hposition
  unfold layerMessagePositions at hposition
  split_ifs at hposition
  · rcases List.mem_pair.mp hposition with rfl | rfl <;>
      simp only [layerTopPosition, CanonicalCoordinate.Hidden, not_false_eq_true]
  · rw [List.mem_singleton.mp hposition]
    simp only [CanonicalCoordinate.Hidden, Position.ftsRoot, not_false_eq_true]

noncomputable def knownEncodingMessage (known : Labels) (position : EncodingPosition) : EncMessage :=
  layerMessageOf (fun graphPosition => known (.graph graphPosition))
    (referenceIndex position.lay position.tree position.leafIdx) position.lay

theorem knownEncodingMessage_eq (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (known : Labels) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    knownEncodingMessage known = canonicalGraphMessage labels := by
  funext position
  exact layerMessageOf_congr fun graphPosition hmem =>
    hagrees _ (layerMessagePositions_public words disclosed _ _ _ hmem)

noncomputable def knownEncodingCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) : EncodingRow → inputs :=
  encodingInputCell parameter inputs hencoding ∘ referenceFamilyCell parameter (knownEncodingMessage known)

theorem knownEncodingCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) :
    Function.Injective (knownEncodingCell parameter inputs hencoding known) :=
  (encodingInputCell_injective parameter inputs hencoding).comp
    (referenceFamilyCell_injective parameter (knownEncodingMessage known))

theorem canonicalEncodingCell_eq_known (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    canonicalEncodingCell parameter inputs hencoding labels = knownEncodingCell parameter inputs hencoding known := by
  funext row
  apply Subtype.ext
  change encodingRetryInput parameter row.1 (canonicalGraphMessage labels row.1) row.2.val =
    encodingRetryInput parameter row.1 (knownEncodingMessage known row.1) row.2.val
  rw [knownEncodingMessage_eq words disclosed known otsSecret ftsSecret labels hagrees]

noncomputable def canonicalReferenceResidual (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) : inputs → HashOutput :=
  UniformTableSplit.overwrite (canonicalEncodingCell parameter inputs hencoding labels)
    (canonicalEncodingCell_injective parameter inputs hencoding labels) rows seed

noncomputable def knownReferenceResidual (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) : inputs → HashOutput :=
  UniformTableSplit.overwrite (knownEncodingCell parameter inputs hencoding known)
    (knownEncodingCell_injective parameter inputs hencoding known) rows seed

theorem canonicalReferenceResidual_eq_known (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels))
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) :
    canonicalReferenceResidual parameter inputs hencoding labels rows seed =
      knownReferenceResidual parameter inputs hencoding known rows seed := by
  unfold canonicalReferenceResidual knownReferenceResidual
  congr 1
  exact canonicalEncodingCell_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret labels hagrees

theorem knownEncodingCell_not_structural (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (input : inputs) (position : Position) (hat : AtPosition parameter input.val position) :
    input ∉ Set.range (knownEncodingCell parameter inputs hencoding known) := by
  rintro ⟨row, heq⟩
  have hencoding : AtEncodingPosition parameter
      (knownEncodingCell parameter inputs hencoding known row).val row.1 := ⟨_, _, rfl⟩
  rw [heq] at hencoding
  exact hencoding.not_atPosition position hat

theorem programmedReferenceResidual_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels))
    (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : HashInput)
    (houtside : decodePosition parameter input = none) :
    programmedHash parameter otsSecret ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels rows seed)) input =
      finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding known rows seed) input := by
  rw [canonicalReferenceResidual_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret labels hagrees]
  simp only [programmedHash, houtside, Option.elim_none]

end SphincsSecurity.Concrete
