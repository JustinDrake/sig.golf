import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualRecovery
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem Context.root_value {inputs : Finset HashInput} (context : Context inputs) :
    canonicalGraphRoot context.graph = honestNode context.oracle context.key.parameter topLayer rootTree
      (context.key.otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
  rw [← context.graph_eq, canonicalGraphLabels_root]
  rfl

theorem Compatible.layer_frame_reference {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (signature : Signature) (pads : ChainPads) (lay : Layer)
    (message target leafValue : Digest)
    (hword : OtsCode.Valid lay (context.words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hframe : LayerFrameP context.oracle memory.external.cache context.key.parameter index signature pads lay message
      target leafValue)
    (hfold : foldValue context.oracle context.key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (signaturePath signature lay) leafValue (layerHeight lay) =
      honestNode context.oracle context.key.parameter lay (treeIndexAt index lay)
        (context.key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn context.oracle (layerMessage context.key index lay) ∧
      HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) ∧
      CachedRun memory.external.cache context.oracle (otsLeafAttempt context.key.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay)) := by
  obtain ⟨hhonest, _, hrun⟩ := hcompatible.layer_honestP lay (treeIndexAt index lay) (leafIndexAt index lay)
    (leafIndexAt_lt index lay) message (signature.counter lay) (signature.chainValue lay) (pads lay)
    (signaturePath signature lay) leafValue hframe.1 hfold hframe.2.2.1 hframe.2.2.2.1
  obtain ⟨_, _, hmessage, _⟩ := hcompatible.layer_reference lay (treeIndexAt index lay) (leafIndexAt index lay)
    message (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) hword hhonest hrun
  have heq := hmessage.trans (context.layer_message index lay)
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact ⟨hhonest, hrun⟩

/-- **`Compatible.verify_honest` with pads** (`Residual/RetainedResidualVerify.lean:76`): the conclusion
is the record's, word for word. -/
theorem Compatible.verify_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, OtsCode.Valid lay (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (message : Message) (signature : Signature)
    (pads : ChainPads)
    (hverify : evalWithAnswerFn context.oracle (verifyP ⟨context.key.root, context.key.parameter⟩ message signature pads) = true)
    (hrun : CachedRun memory.external.cache context.oracle (verifyP ⟨context.key.root, context.key.parameter⟩ message signature pads)) :
    ∃ digest, evalWithAnswerFn context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) = digest ∧
      CachedRun memory.external.cache context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) ∧
      Admissible digest ∧
      FullyHonestOpening context.oracle memory.external.cache context.key (digestIndex digest) (digestLeaves digest) signature ∧
      ∀ slot, memory.routing.disclosed (digestIndex digest) porsTree (digestLeaves digest slot) := by
  obtain ⟨digest, hdigest, hdigestRun, ftsPublicKey, hfts, hlayers, hftsRun, hlayersRun⟩ :=
    verifyP_extract ⟨context.key.root, context.key.parameter⟩ message signature pads hverify hrun
  have hwalk := hypertree_walkP (f := context.oracle) (cache := memory.external.cache) context.key (digestIndex digest)
    signature pads
    (fun lay => HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay
        (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay)
        (evalWithAnswerFn context.oracle (layerMessage context.key (digestIndex digest) lay))
        (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) ∧
      CachedRun memory.external.cache context.oracle (otsLeafAttempt context.key.parameter lay
        (treeIndexAt (digestIndex digest) lay) (leafIndexAt (digestIndex digest) lay)
        (evalWithAnswerFn context.oracle (layerMessage context.key (digestIndex digest) lay))
        (signature.counter lay) (signature.chainValue lay)))
    (fun lay message leafValue hframe hfold =>
      hcompatible.layer_frame_reference (digestIndex digest) signature pads lay message context.key.root leafValue
        (context.words_valid hdummy _ _ _) hframe hfold)
    (by rw [hroot, context.root_value]) ftsPublicKey hlayers hlayersRun
  have hftsKey : ftsPublicKey = honestFtsKey context.oracle context.key.parameter (digestIndex digest)
      (context.key.ftsSecret (digestIndex digest)) := by
    rw [hwalk.2, layerMessage_bottomLayer]
    rfl
  rw [hftsKey] at hfts
  obtain ⟨hadmissible, hftsHonest, _⟩ := hcompatible.ftsRecover_honest (digestIndex digest) (digestLeaves digest)
    signature.fts hfts hftsRun
  exact ⟨digest, hdigest, hdigestRun, hadmissible, ⟨hwalk.1, hftsHonest, hftsRun⟩,
    hcompatible.ftsRecover_disclosed (digestIndex digest) (digestLeaves digest) signature.fts hfts hftsRun⟩

end SphincsSecurity.Concrete.RetainedResidual
