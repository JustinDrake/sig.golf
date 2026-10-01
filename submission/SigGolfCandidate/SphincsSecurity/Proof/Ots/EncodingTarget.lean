import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem layerHeight_sub_one_lt (lay : Layer) : layerHeight lay - 1 < maxLayerHeight := by
  have h1 := layerHeight_le lay
  have h2 := layerHeight_pos lay
  omega

/-- A child of the root of the tree below layer `lay`: node `side` of level `h - 1`. -/
def layerTopPosition (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) (side : Fin 2) :
    Position :=
  .node ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
    ⟨layerHeight ⟨lay.val + 1, hbelow⟩ - 2, by
      have := layerHeight_le (⟨lay.val + 1, hbelow⟩ : Layer)
      have := two_le_layerHeight (⟨lay.val + 1, hbelow⟩ : Layer)
      omega⟩
    ⟨side.val, lt_of_lt_of_le side.isLt (by decide)⟩

/-- The positions whose values layer `lay` signs: the two children of the root of the tree below it, or
the PORS root. -/
def layerMessagePositions (index : Index) (lay : Layer) : List Position :=
  if hbelow : lay.val + 1 < numLayers then
    [layerTopPosition index lay hbelow 0, layerTopPosition index lay hbelow 1]
  else [Position.ftsRoot index]

/-- The message of layer `lay` read off a table of position values: the root's two children, or
`(0, PORS root)`. -/
def layerMessageOf (value : Position → Digest) (index : Index) (lay : Layer) : EncMessage :=
  if hbelow : lay.val + 1 < numLayers then
    (value (layerTopPosition index lay hbelow 0), value (layerTopPosition index lay hbelow 1))
  else (0, value (Position.ftsRoot index))

theorem layerMessageOf_congr {value value' : Position → Digest} {index : Index} {lay : Layer}
    (h : ∀ position ∈ layerMessagePositions index lay, value position = value' position) :
    layerMessageOf value index lay = layerMessageOf value' index lay := by
  unfold layerMessageOf
  unfold layerMessagePositions at h
  split_ifs with hbelow
  · rw [dif_pos hbelow] at h
    rw [h _ (List.mem_cons_self ..), h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]
  · rw [dif_neg hbelow] at h
    rw [h _ (List.mem_cons_self ..)]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      layerMessageOf (honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret)
        index lay := by
  unfold layerMessageOf
  split_ifs with hbelow
  · rw [layerMessage_of_lt secretKey index lay hbelow, eval_treeTop, honestPair, layerTopPosition,
      layerTopPosition, honestValue_node, honestValue_node]
    have hh : layerHeight ⟨lay.val + 1, hbelow⟩ - 2 + 1 = layerHeight ⟨lay.val + 1, hbelow⟩ - 1 := by
      have := two_le_layerHeight (⟨lay.val + 1, hbelow⟩ : Layer)
      omega
    simp only [hh]
    rfl
  · have hbottom : lay = bottomLayer := Fin.ext (by
      have := lay.isLt
      simp only [bottomLayer]
      omega)
    subst hbottom
    rw [layerMessage_bottomLayer secretKey index]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [honestValue_ftsRoot]
    rfl

end SphincsSecurity.Concrete
