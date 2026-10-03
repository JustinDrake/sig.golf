import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability

section



namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem layerHeight_pos (lay : Layer) : 0 < layerHeight lay := by
  unfold layerHeight maxLayerHeight
  split <;> (try split) <;> omega
theorem layerHeight_sub_one_lt (lay : Layer) : layerHeight lay - 1 < maxLayerHeight := by
  have h1 := layerHeight_le lay
  have h2 := layerHeight_pos lay
  omega
def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if hbelow : lay.val + 1 < numLayers then
    .node ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
      ⟨layerHeight ⟨lay.val + 1, hbelow⟩ - 1, layerHeight_sub_one_lt _⟩ ⟨0, by positivity⟩
  else Position.ftsRoot index
theorem layerMessagePosition_of_lt (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    layerMessagePosition index lay =
      .node ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
        ⟨layerHeight ⟨lay.val + 1, hbelow⟩ - 1, layerHeight_sub_one_lt _⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, dif_pos hbelow]
@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = Position.ftsRoot index := by
  rw [layerMessagePosition, dif_neg (by decide)]
theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [layerMessage_of_lt secretKey index lay hbelow, layerMessagePosition_of_lt index lay hbelow,
      honestValue_node]
    have hh : layerHeight ⟨lay.val + 1, hbelow⟩ - 1 + 1 = layerHeight ⟨lay.val + 1, hbelow⟩ := by
      have := layerHeight_pos ⟨lay.val + 1, hbelow⟩
      omega
    simp only [hh]
    rfl
  · have hbottom : lay = bottomLayer := Fin.ext (by
      have := lay.isLt
      simp only [bottomLayer]
      omega)
    subst hbottom
    rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoot]
    rfl
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
structure EncodingPosition where
  lay : Layer
  tree : TreeIndex
  leafIdx : LeafIndex
  deriving DecidableEq, Fintype
def EncodingPosition.domain (position : EncodingPosition) : HashDomain :=
  .encoding position.lay position.tree position.leafIdx
def AtEncodingPosition (parameter : PublicParameter) (input : HashInput)
    (position : EncodingPosition) : Prop :=
  ∃ payload, input = tweakableHashInput parameter position.domain payload
theorem atEncodingPosition_unique {parameter : PublicParameter} {input : HashInput}
    {left right : EncodingPosition} (hleft : AtEncodingPosition parameter input left)
    (hright : AtEncodingPosition parameter input right) : left = right := by
  obtain ⟨leftPayload, hleft⟩ := hleft
  obtain ⟨rightPayload, hright⟩ := hright
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial)
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
  obtain ⟨encodingPayload, hencodingInput⟩ := hencoding
  have hdomain := (tweakableHashInput_injective parameter (by trivial)
    position.domain_inRange (hencodingInput.symm.trans hstructural)).1
  cases position <;> simp [EncodingPosition.domain, Position.domain] at hdomain
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 100000
def encodingRetryInput (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) : HashInput :=
  tweakableHashInput parameter position.domain
    (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))
theorem encodingRetryInput_injective_of_lt
    {parameter : PublicParameter} {position : EncodingPosition} {message : Digest}
    {left right : Nat} (hleft : left < encodingAttemptLimit)
    (hright : right < encodingAttemptLimit)
    (heq : encodingRetryInput parameter position message left =
      encodingRetryInput parameter position message right) :
    left = right := by
  have hpayload :=
    (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
  obtain ⟨_, hcounter⟩ :=
    List.append_inj hpayload (by simp [digestBytes_length])
  apply ofNat_inj_of_lt (w := counterBits)
    (hleft.trans_le (by norm_num [encodingAttemptLimit, counterBits]))
    (hright.trans_le (by norm_num [encodingAttemptLimit, counterBits]))
  exact bytesLE_injective hcounter
end SphincsSecurity.Concrete
end
