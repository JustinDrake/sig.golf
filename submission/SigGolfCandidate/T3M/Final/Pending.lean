import SigGolfCandidate.T3M.Submission
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Witness.Honest
import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.T3M.Final.Source
import SigGolfCandidate.T3M.Final.SecurityP

/-!
# The interface of the T3 certificate (stream F)

`Main.certificate_of : Pending → SourceFacts → Legacy.Certificate T3M.submission claimedC` proves the
whole certificate from the named statements below; nothing else is assumed.

**`Pending`** — what the machine streams prove about the frozen images (exact statement shapes):

| field | statement | stream |
|---|---|---|
| `keygen_run_counts` | `KeygenRunCounts` (value, calls and compressions = `countBoth (mrealize sk keygen)`) | K (proved, t3m/m0k 924ddbe) |
| `keygen_runWith` | `KeygenRunWith` (every oracle: finished, 39,960,239 cycles) | K (proved, t3m/m0k 924ddbe) |
| `sign_refines` | `SignRefines` (`countBoth (mrealize sk (sign (cacheDec cache) m))`, output `sigB`) | S |
| `sign_terminates` | `SignTerminates` | S |
| `expand_refines` | `ExpandRefines` (`countBoth (mrealize 0 (expandN m pk (sigDec s)))`, output `witEnc`) | E |
| `expand_terminates` | `ExpandTerminates` | E |
| `verify_refines` | `VerifyRefines` (`countCalls (mrealize 0 (verifyP m pk w))`) | V3 |
| `verify_terminates` | `VerifyTerminates` | V3 |
| `verify_accept_cycles` | `VerifyAcceptCycles` (accepting runs take at most `verifyCycleBound = 8772` cycles) | V3 |

**`SourceFacts`** — source-level theorems: CLOSURE's completeness and two compression moments
(stated on the verbatim copies in `Source`), the hash-only facts of Core's four programs (CLOSURE's
`SourceReplay.hashOnly_*`), and SEC's padded-game security `SecurityP`.

The witness layer (stream W: `verifyP_witEnc_eval`, `honestB_eval`, `expand_eq_expandN`, query shapes) is
already proved and is used directly. The signature codec is stream E's `T3M/SigCodec` (`T3M.sigB`, `T3M.sigDec`,
`sigDec_sigB`, `sigB_sigDec`). `C = verifyCycleBound + witnessCycles 25240 = 8772 + 99 = 8871`.
-/

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen sign expand verify Signature Cache Digest Witness realize)

/-- The accepting-verify cycle bound (worst accepting path of the frozen verify image). -/
def verifyCycleBound : Nat := 8772

/-- The claimed `C`: `verifyCycleBound + ⌈25240 / 256⌉`. -/
def claimedC : Nat := 8871

/-! ## Machine statements -/

/-- **Keygen refinement** (K: `T3M.Keygen.keygen_run_counts`). -/
def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
    (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$> countBoth (mrealize sk keygen)

/-- **Keygen under a fixed oracle** (K: `T3M.Keygen.keygen_runWith`): finished, exactly 39,960,239 cycles. -/
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  submission.runWith hash .keygen sk =
    ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
      cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 39960239, 995328, 1048576⟩

/-- **Sign refinement** (S). For every input (arbitrary cache bytes, decoded by `cacheDec`; the source
signer checks the MAC first): value, calls and compressions are those of Core's signer. -/
def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
    (fun p => (p.1.map sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))

/-- **Sign termination** (S): under every fixed oracle and input, finished within the cycle limit. -/
def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
    (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT

/-- **Expand refinement** (E). For every input (arbitrary signature bytes, decoded by the bijection
`sigDec`): value (the witness bytes `witEnc N w`), calls and compressions are those of `expandN`. -/
def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5616),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, s) =
    (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDec s)))

/-- **Expand termination** (E). -/
def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5616),
  (submission.runWith hash .expand (m, pk, s)).finished = true ∧
    (submission.runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT

/-- **Verify refinement** (V). For every input (arbitrary witness bytes): accepts exactly when the
byte-level verifier `verifyP` returns `true`, with the same hash calls. -/
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 25240),
  (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))

/-- **Verify termination** (V). -/
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240),
  (submission.runWith hash .verify (m, pk, w)).finished = true ∧
    (submission.runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT

/-- **Accepting verify cycles** (V): under every fixed oracle, an accepting run takes at most
`verifyCycleBound = 8772` cycles. -/
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240),
  (submission.runWith hash .verify (m, pk, w)).value.isSome = true →
    (submission.runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound

/-- The machine statements. -/
structure Pending : Prop where
  keygen_run_counts : KeygenRunCounts
  keygen_runWith : KeygenRunWith
  sign_refines : SignRefines
  sign_terminates : SignTerminates
  expand_refines : ExpandRefines
  expand_terminates : ExpandTerminates
  verify_refines : VerifyRefines
  verify_terminates : VerifyTerminates
  verify_accept_cycles : VerifyAcceptCycles

/-! ## Source statements -/

/-- **Source completeness** (CLOSURE: `Completeness.source_completeness`). -/
def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1 - 1 / (2 : ℝ≥0∞) ^ 128 ≤
    Pr[= true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅]

/-- **Signing moment** after the actual key generation in the same oracle
(CLOSURE: `BudgetClosure.honest_sign_exponential_budget`). -/
def SignMoment : Prop := ∀ (secret : BitVec 256) (message : T3.Message),
  expectedValue (T3.Sampling.roRun secret (honestSignCount message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2

/-- **Expansion moment** after the actual key generation and signing in the same oracle
(CLOSURE: `ExpansionClosure.honest_expand_exponential_budget`). -/
def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : T3.Message),
  expectedValue (T3.Sampling.roRun secret (honestJointCounts message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2

/-- The source statements. -/
structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  /-- CLOSURE's `SourceReplay.hashOnly_keygen` (no coin queries; `isHash` = `SourceReplay.isHash`). -/
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  /-- CLOSURE's `SourceReplay.hashOnly_sign`. -/
  hashOnly_sign : ∀ (cache : Cache) (message : T3.Message), AllQueriesSatisfy (sign cache message) isHash
  /-- CLOSURE's `SourceReplay.hashOnly_expand`. -/
  hashOnly_expand : ∀ (message : T3.Message) (pk : Digest) (sig : Signature),
    AllQueriesSatisfy (expand message pk sig) isHash
  /-- CLOSURE's `SourceReplay.hashOnly_verify`. -/
  hashOnly_verify : ∀ (message : T3.Message) (pk : Digest) (w : Witness),
    AllQueriesSatisfy (verify message pk w) isHash
  /-- SEC: security of the padded game. -/
  securityP : SecurityP

end SigGolfCandidate.T3M.Final
