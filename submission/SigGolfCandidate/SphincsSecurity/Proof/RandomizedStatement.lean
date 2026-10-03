import SigGolfCandidate.SphincsSecurity.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost
import SigGolfCandidate.SphincsSecurity.Proof.SignatureLayout

section


open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq
abbrev SigningSpec := Message →ₒ Option Signature
structure SigningRequest where
  message : Message
  cache : TopCache
deriving DecidableEq
abbrev RequestSpec := SigningRequest →ₒ Option Signature
namespace SigningTranscript
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit
instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature
instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))
end SigningTranscript
namespace RequestTranscript
def Valid (log : QueryLog RequestSpec) : Prop := log.length ≤ signatureLimit
instance (log : QueryLog RequestSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))
def Contains (log : QueryLog RequestSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature
instance (log : QueryLog RequestSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature))
end RequestTranscript
namespace Security
structure Adversary where
  main : PublicKey → TopCache → OracleComp (OracleWorld + RequestSpec) Forgery
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl RequestSpec (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request.cache request.message : OracleComp HashSpec _)
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, cache, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog RequestSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk cache)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)
end Security
abbrev SphincsSecurityStatement : Prop := Security.HasClassicalSecurityBits 127
end SphincsSecurity
end

section


open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
namespace Concrete
abbrev digestBytes (value : Digest) : HashInput := bytesLE 16 value
abbrev messageBytes (message : Message) : HashInput := bytesLE 32 message
abbrev randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness
end Concrete
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)
noncomputable def Seeded.gameRest {Key : Type} (randomizedScheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle randomizedScheme sk) (adversary.main pk)).run
  let verified ← randomizedScheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  Seeded.gameRest scheme adversary pk sk
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)
end SphincsSecurity
end
