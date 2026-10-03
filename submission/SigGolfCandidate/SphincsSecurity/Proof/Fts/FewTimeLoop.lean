import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeUniform
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessagePrehit
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SignerDigestSource

namespace SphincsSecurity.Concrete
open OracleComp OracleSpec
set_option maxRecDepth 100000
theorem signAttempt_result_of_cached (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (beforeCache afterCache : QueryCache HashSpec)
    (attempt : Option (Index × (IndexGroup → FtsLeaf))) (output : HashOutput)
    (hcached : afterCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output)
    (hmem : (attempt, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp))
        (signAttempt secretKey message randomness)).run beforeCache)) :
    attempt = signAttemptResultOfOutput output := by
  obtain ⟨_, f, hf, heval⟩ := exists_answerFn_agrees_final_of_mem_support
    (signAttempt secretKey message randomness) beforeCache attempt afterCache hmem
  have hfinput : f (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = output :=
    hf hcached
  simp only [signAttempt, messageDigest, oracleHash, evalWithAnswerFn_bind,
    evalWithAnswerFn_query, hfinput] at heval
  simp only [signAttemptResultOfOutput]
  by_cases hadmissible : Admissible (truncateMessageDigest output)
  · simpa only [hadmissible, if_true, evalWithAnswerFn_pure] using heval.symm
  · simpa only [hadmissible, if_false, evalWithAnswerFn_pure] using heval.symm
end SphincsSecurity.Concrete
