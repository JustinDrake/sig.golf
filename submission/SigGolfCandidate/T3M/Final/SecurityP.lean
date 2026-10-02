import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Witness.Encode

/-!
# The padded source game (`SecurityP`, the security stream's target; MACH-PLAN §3.4)

The organizer's verifier hashes the witness bytes where they lie, free bytes included, so the source
game whose security transfers to the organizer's game checks witness forgeries with the byte-level
verifier `verifyP` (stream W) on the submitted **bytes**, and signature forgeries by Core's expansion
followed by the machine witness encoding (`expandB = witEnc ∘ expandN`) and `verifyP`. Everything else
is `T3.Security.game` / `realExperiment` verbatim: the same key generation, the same logged signing oracle
(`T3.Security.signingOracle`, any cache, Core's `sign`), the same freshness relations, the same lifetime
check, the same private-coordinate realization and the same hash-call count.

`SecurityP` is the event form the organizer statement needs: winning **and** at most `q` hash calls has
probability at most `q / 2^127`. The bridge (`BridgeMain`) transfers it to `Legacy.Submission.Secure`.
-/

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 (M Spec Message Digest Signature Cache keygen sign privateInput)
open SigGolfCandidate.T3.Security (Request Requests forwardWorld signingOracle)
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)

/-- The two final submissions: witness **bytes** (the organizer's object, verified by `verifyP`), or a
Core signature (the organizer's signature bytes, decoded by the bijection `sigDec`). -/
inductive ForgeryP where
  | witness (message : Message) (witness : WBytes)
  | signature (message : Message) (signature : Signature)

/-- An adaptive source adversary: coins, the hash, and the logged signing oracle (any cache). -/
abbrev AdversaryP := Digest → Cache → OracleComp (OracleWorld + Requests) (Option ForgeryP)

/-- Both forgery forms against the byte-level verifier. Failed signing responses do not enter the
freshness relation, but count toward the lifetime limit (as `T3.Security.checkForgery`). -/
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

/-- `T3.Security.game` with `checkForgeryP`. -/
noncomputable def gameP (adversary : AdversaryP) : M Bool := do
    let (publicKey, cache) ← keygen
    let (forgery, log) ← (simulateQ
      ((fun input => liftM (forwardWorld input) : QueryImpl OracleWorld (WriterT (QueryLog Requests) M)) +
        signingOracle) (adversary publicKey cache)).run
    let some forgery := forgery | return false
    let verified ← checkForgeryP publicKey log forgery
    pure (decide (log.length ≤ 2^32) && verified)

/-- `T3.Security.realExperiment` with `gameP`: the master secret, the private coordinates realized by
it, every hash call counted, one lazy random oracle. -/
noncomputable def realExperimentP (adversary : AdversaryP) : ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (T3.Derivation.realize (privateInput secret) (gameP adversary)))).run' ∅

/-- **SEC's target** (handoff item 4 on the machine's byte interface): every adversary wins the padded
game **and** uses at most `q` hash calls with probability at most `q / 2^127`. -/
def SecurityP : Prop := ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q →
  Pr[fun result => result.1 = true ∧ result.2 ≤ q | realExperimentP adversary] ≤ (q : ℝ≥0∞) / 2 ^ 127

end SigGolfCandidate.T3M.Final
