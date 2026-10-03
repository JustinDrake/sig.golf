import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.SignSupport

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
theorem decode_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) :
    OtsCode.decode (truncateHash (f (tweakableHashInput parameter
      (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))))
        = some codeword := by
  simpa only [encodeAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash] using hencode
theorem valid_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) : OtsCode.Valid codeword :=
  OtsCode.decode_valid
    (decode_of_eval_encode_eq_some f parameter lay tree leafIdx message counter codeword hencode)
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeafAttempt secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ signature.fts = evalWithAnswerFn f (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index (slotValue leaves) signature.fts)
theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl
end SphincsSecurity.Concrete
end
