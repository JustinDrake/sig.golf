import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.ReferenceHypertreeWitness
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FtsVerifierWitness
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk sequenceFin canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem ReferenceLayerOpening.honest {f : QueryImpl HashSpec Id} {key : SecretKey} {words : OtsReferenceWords} {selections : ReferenceFamily}
    {index : Index} {signature : Signature} {lay : Layer} (h : ReferenceLayerOpening f key words selections index signature lay) :
    HonestLayerOpening f key.parameter key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) := by
  obtain ⟨_, _, _, he, hv, hp⟩ := h
  exact ⟨words lay (treeIndexAt index lay) (leafIndexAt index lay), he, hv, hp⟩

/-- **The small route's verifier classification** (padded verifier): an accepted padded forgery has the
record's honest opening (about the record's unpadded layer computations), or a layer exception (the
record's, or a padded chain match), or an FTS exception. -/
theorem verify_classification (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
    (messages : EncodingPosition → EncMessage) (selections : ReferenceFamily) (message : Message) (signature : Signature)
    (pads : ChainPads) (trace : Trace)
    (hvalid : ∀ lay tree leaf, OtsCode.Valid lay (words lay tree leaf))
    (hmessages : ∀ index lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hverify : evalWithAnswerFn f (verifyP ⟨key.root, key.parameter⟩ message signature pads) = true)
    (hrun : ContainsRun f trace (verifyP ⟨key.root, key.parameter⟩ message signature pads)) :
    ∃ digest, evalWithAnswerFn f (messageDigest key.parameter key.root message signature.randomness) = digest ∧
      ContainsRun f trace (messageDigest key.parameter key.root message signature.randomness) ∧ Admissible digest ∧
      ((FullyHonestOpening f (recordedCache f trace) key (digestIndex digest) (digestLeaves digest) signature ∧
        (∀ lay, ReferenceLayerOpening f key words selections (digestIndex digest) signature lay) ∧
        ∀ slot, FtsVerifierWitness.TrueSecretQuery f key (digestIndex digest) (digestLeaves digest slot) trace) ∨
        LayerException f key words messages selections trace ∨ FtsVerifierWitness.Exception f key (digestIndex digest) trace) := by
  obtain ⟨digest, hd, hdrun, ftsPublicKey, top, hfts, hlayers, htopRoot, hftsrun, hlayersrun, htoprun⟩ :=
    verifyP_extract ⟨key.root, key.parameter⟩ message signature pads hverify hrun.cached
  refine ⟨digest, hd, (recordedCache_run_iff f trace _).mp hdrun, ?_⟩
  have hftsrun' := (recordedCache_run_iff f trace _).mp hftsrun
  by_cases hexc : LayerException f key words messages selections trace
  · exact ⟨PorsMachine.ftsRecover_admissible f key.parameter (digestIndex digest) (digestLeaves digest) signature.fts
      ftsPublicKey hfts, Or.inr (Or.inl hexc)⟩
  have htop : top = honestPair f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) := by
    rcases topRoot_classification f key.parameter (key.otsSecret topLayer rootTree) (digestIndex digest) top trace
        (htopRoot.trans hroot) ((recordedCache_run_iff f trace _).mp htoprun) with h | h
    · exact h
    · exact False.elim (hexc (Or.inl (Or.inr ⟨topLayer, rootTree, leafIndexAt (digestIndex digest) topLayer,
        Or.inl h⟩)))
  have hwalk := hypertree_walkP (f := f) (cache := recordedCache f trace) key (digestIndex digest) signature pads
    (fun lay => ReferenceLayerOpening f key words selections (digestIndex digest) signature lay ∧
      CachedRun (recordedCache f trace) f (otsLeafAttempt key.parameter lay (treeIndexAt (digestIndex digest) lay)
        (leafIndexAt (digestIndex digest) lay)
        (evalWithAnswerFn f (layerMessage key (digestIndex digest) lay)) (signature.counter lay) (signature.chainValue lay)))
    top
    (fun lay message leafValue hframe hfold => by
      have h := layer_frame_reference f key words messages selections (digestIndex digest) signature pads lay message
        top leafValue trace (hvalid _ _ _) (hmessages _ _) hexc hframe hfold
      refine ⟨h.1, h.2.1, ?_⟩
      rw [← h.1]
      exact h.2.2)
    htop _ hlayers hlayersrun
  have hkey : ftsPublicKey = honestFtsKey f key.parameter (digestIndex digest) (key.ftsSecret (digestIndex digest)) := by
    have hbottom := hwalk.2
    rw [layerMessage_bottomLayer] at hbottom
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hbottom
    exact (Prod.mk.inj hbottom).2
  rw [hkey] at hfts
  obtain ⟨hadmissible, hcase⟩ := FtsVerifierWitness.recover_classification f key (digestIndex digest)
    (digestLeaves digest) signature.fts trace hfts hftsrun'
  refine ⟨hadmissible, ?_⟩
  rcases hcase with ⟨hftsOpening, hqueries⟩ | he
  · refine Or.inl ⟨?_, fun lay => (hwalk.1 lay).1, hqueries⟩
    exact ⟨fun lay => ⟨(hwalk.1 lay).1.honest, (hwalk.1 lay).2⟩, hftsOpening, hftsrun⟩
  · exact Or.inr (Or.inr he)

end SphincsSecurity.Concrete.OtsVerifierWitness
