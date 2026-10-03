import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Witness.Encode

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Signature Cache keygen sign privateInput)
open SigGolfCandidate.T3.Security (Request Requests forwardWorld signingOracle)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)
abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)
noncomputable def checkForgeryP (publicKey : Digest) (log : QueryLog Requests) : ForgeryP → M Bool := by
  classical
  exact fun forgery => do
    match forgery with
    | .witness message wb =>
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2.isSome = true) && verified)
    | .signature message signature =>
        let wb ← expandB message publicKey signature
        let some wb := wb | return false
        let verified ← verifyP message publicKey wb
        pure (decide (¬∃ entry ∈ log, entry.1.message = message ∧ entry.2 = some signature) && verified)
noncomputable def gameP (adversary : AdversaryP) : M Bool := do
    let (publicKey, cache) ← keygen
    let (forgery, log) ← (simulateQ
      ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
        signingOracle) (adversary publicKey cache)).run
    let some forgery := forgery | return false
    let verified ← checkForgeryP publicKey log forgery
    pure (decide (log.length ≤ 2^32) && verified)
noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅
def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ℝ≥0∞) / 2 ^ 127
end SigGolfCandidate.T3M.Final
