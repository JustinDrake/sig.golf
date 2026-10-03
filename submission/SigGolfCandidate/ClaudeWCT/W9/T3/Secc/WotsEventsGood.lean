import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layers
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Wct

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wrho wdc)
open SigGolfCandidate.T3.Correctness (Answers)
def VerifierAllGood (answers : Answers) (publicKey : Digest) (forgery : ForgeryP) : Prop :=
  ∃ message witness N, PaddedExtraction.WitnessOf answers publicKey forgery message witness ∧
    evalWithAnswerFn answers (digest (wrho witness) message (wdc witness)) = N ∧
    (∀ l : Layer, Extract.Good answers witness (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N witness
end ClaudeWCT.W9.T3.Security.Wots
