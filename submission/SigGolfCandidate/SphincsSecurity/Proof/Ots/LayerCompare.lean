import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.SignSupport
/-!
# Comparing honest layer openings

Two honest openings at the same one-time position either agree on the signed layer component, use
distinct encoding inputs with the same digest, or the forged codeword starts earlier on some chain.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem decode_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : EncMessage)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) :
    OtsCode.decode lay (selectEncodingDigest (f (tweakableHashInput message.1
      (.encoding lay tree leafIdx) (digestBytes message.2 ++ counterBytes counter))))
        = some codeword := by
  simpa only [encodeAttempt, evalWithAnswerFn_bind, evalWithAnswerFn_pure, oracleHash, evalWithAnswerFn_query] using hencode

theorem valid_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : EncMessage)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter)
      = some codeword) : OtsCode.Valid lay codeword :=
  OtsCode.decode_valid
    (decode_of_eval_encode_eq_some f parameter lay tree leafIdx message counter codeword hencode)

end SphincsSecurity.Concrete
