import SigGolfCandidate.ClaudeWCT.W9.T3.BPORS

namespace ClaudeWCT.W9.T3.Security.PaddedExtraction
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open Correctness (Answers)
def Fresh (log : QueryLog Requests) : ForgeryP → Prop
  | .witness message _ => ¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true
  | .signature message signature => ¬∃ entry ∈ log, entry.1.message = message ∧ entry.2 = some signature
def WitnessOf (answers : Answers) (publicKey : Digest) : ForgeryP → Message → WBytes → Prop
  | .witness message witness, m, w => m = message ∧ w = witness
  | .signature message signature, m, w =>
      m = message ∧ evalWithAnswerFn answers (expandB message publicKey signature) = some w
end ClaudeWCT.W9.T3.Security.PaddedExtraction
