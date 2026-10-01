import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceLayerWitness
import SigGolfCandidate.SphincsSecurity.Proof.Reference.VerifierTraceDescent
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk sequenceFin canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
  (messages : EncodingPosition → Digest) (selections : ReferenceFamily)

/-- The small route's layer exceptions: the record's (an encoding match, or a tree, leaf or chain
event at some layer position), or the padded verifier's new event, a `PaddedChainMatch`. -/
def LayerException (trace : Trace) : Prop :=
  (EncodingOutputMatch key.parameter words messages selections trace ∨
    ∃ lay tree leaf, TreeOutputMatch f key.parameter lay tree (key.otsSecret lay tree) trace ∨
      LeafOutputMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace ∨
        ChainException f key.parameter words lay tree leaf (key.otsSecret lay tree leaf) trace) ∨
    ∃ lay tree leaf, PaddedChainMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace

def ReferenceLayerOpening (index : Index) (signature : Signature) (lay : Layer) : Prop :=
  ∃ selected, selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = some selected ∧
    signature.counter lay = BitVec.ofNat counterBits selected.1.val ∧
    evalWithAnswerFn f (encodeAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay)) = some (words lay (treeIndexAt index lay) (leafIndexAt index lay)) ∧
    (∀ chain, signature.chainValue lay chain = frontier f key.parameter words lay (treeIndexAt index lay) (leafIndexAt index lay)
      (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) chain) ∧
    ∀ level, level < layerHeight lay → signaturePath signature lay level =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) level
        (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1)

/-- One layer of an accepted padded verification, outside the layer exceptions: the record's
reference opening, and the record layer's cached run (inactive pads make the same queries). -/
theorem layer_frame_reference (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily)
    (index : Index) (signature : Signature) (pads : ChainPads) (lay : Layer) (message target leafValue : Digest)
    (trace : Trace)
    (hvalid : OtsCode.Valid lay (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hclean : ¬LayerException f key words messages selections trace)
    (hframe : LayerFrameP f (recordedCache f trace) key.parameter index signature pads lay message target leafValue)
    (hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) (signaturePath signature lay)
      leafValue (layerHeight lay) =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn f (layerMessage key index lay) ∧
      ReferenceLayerOpening f key words selections index signature lay ∧
      CachedRun (recordedCache f trace) f (otsLeafAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        message (signature.counter lay) (signature.chainValue lay)) := by
  cases hencode : evalWithAnswerFn f (encodeAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message (signature.counter lay)) with
  | none =>
      have hots := hframe.1
      simp only [otsLeafAttemptP, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure, reduceCtorEq] at hots
  | some candidate =>
      have h := layer_reference_classificationP f key.parameter words messages selections lay (treeIndexAt index lay)
        (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay)
        (signaturePath signature lay) message (signature.counter lay) (signature.chainValue lay) (pads lay) candidate
        leafValue trace hvalid hencode hframe.1 hfold
        ((recordedCache_run_iff f trace _).mp hframe.2.2.1) ((recordedCache_run_iff f trace _).mp hframe.2.2.2.1)
      rcases h with ⟨hinactive, selected, hs, hm, hc, hw, hv, hp⟩ | ht | hl | hc | he | hpad
      · refine ⟨hm.trans hmessages, ⟨selected, hs, hc, ?_, hv, hp⟩, ?_⟩
        · rw [← hm.trans hmessages, ← hw]
          exact hencode
        · exact (cachedRun_otsLeafAttemptP_iff_of_inactive f key.parameter lay _ _ _ _ _ _ (pads lay) candidate
            hencode hinactive).mp hframe.2.2.1
      · exact False.elim (hclean (Or.inl (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inl ht⟩)))
      · exact False.elim (hclean (Or.inl (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inl hl)⟩)))
      · exact False.elim (hclean (Or.inl (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inr hc)⟩)))
      · exact False.elim (hclean (Or.inl (Or.inl he)))
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, hpad⟩))

end SphincsSecurity.Concrete.OtsVerifierWitness
