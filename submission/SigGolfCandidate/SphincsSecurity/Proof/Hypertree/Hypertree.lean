import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
/-!
# The hypertree

Five layers, bottom first. Each layer's fold stops below the root of its tree: the root's two children are
exactly the message the layer above it signs, so the layers chain; layer `0`'s two children hash to the
public root.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

theorem layerMessage_bottomLayer (secretKey : SecretKey) (index : Index) :
    layerMessage (m := m) secretKey index bottomLayer
      = (do
          let key ← ftsKey secretKey.parameter index (secretKey.ftsSecret index)
          return (0, key)) := by
  rw [layerMessage, dif_neg (by decide)]

theorem layerMessage_of_lt (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessage (m := m) secretKey index lay
      = treeTop secretKey.parameter ⟨lay.val + 1, hbelow⟩
          (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
          (secretKey.otsSecret ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)) := by
  rw [layerMessage, dif_pos hbelow]

end SphincsSecurity.Concrete
