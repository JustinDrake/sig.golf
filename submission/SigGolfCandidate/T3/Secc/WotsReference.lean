import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryAllocation

/-!
# Stream F2: the T3 reference experiment R3 (BP-A §4 F2)

R3 is the record's `referenceInstrumentedGame` for T3: eager tables, honest key generation and the authenticated
signer evaluated **offline** (no oracle query; their charge is consumed as `ticks`), the adversary and the final
verdict on the real table with every one of their queries recorded, and one budget `q` shared by everything that
the frozen game counts (`Derivation.charged`: honest calls, adversary and verifier hash calls).

* `referenceInputs adversary` — the eager public universe: all inputs of length ≤ 4096 (`SeccLaw.publicUniverse`)
  and every hash input of the recorded padded game on any path (`ChainGraph.recordedInputs`).
* `eagerAnswers inputs privateTable publicTable` — the eager table (coins `0`, public inputs by
  `finiteHashAnswer ∅ inputs publicTable`, private coordinates by `privateTable`).
* `offlineGame T adversary : OracleComp RefWorld Bool` — `ticks (keygenCharge T)`, offline keygen
  (`evalWithAnswerFn T keygen`), the adversary against `offlineImpl` (world queries forwarded; a signing request
  is answered by `evalWithAnswerFn T (FullGame.authenticatedSign published request)` after `signCharge` ticks, and
  logged), then `GameWith.verdict PaddedGame.checker` with its public queries forwarded.
* `referenceGame T adversary q := QueryCap.run RefCharged (offlineGame T adversary) q` (pinned `QueryCap.run`;
  charged = hash queries and ticks).
* `offlineRun T adversary q := simulateQ (refImpl T) (QueryCap.recorded (referenceGame T adversary q))`
  (record style: `fixedHashWorld`-like world, every R3 query recorded).
* `referenceExperiment adversary q : PMF RefSample` — tables uniform, sample `⟨T, pk, traceOf T queries⟩`.

**Why the budget includes the honest charge** (deviation from "adversary capped at `q`"): the closing needs a
*joint* budget between R3's class counts and the shared law's message count (`SeccLaw.sampleCharge`, which
truncates at `q` charges *including honest calls*). With the honest charge in R3's budget, R3's trace is exactly the
non-honest part of the shared law's `q`-prefix, so R3's class counts are pointwise below `sampleCharge` (F2-3).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable local instance instFintypeCoordinate_wotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsReference : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
-- SEC's sampler constant (`FiniteRowSplit`): every eager public table in F2 uses exactly this instance term, so
-- SEC's row-split lemmas apply syntactically (a different elaboration of `SampleableType.ofFintype` makes the
-- kernel compare `Fintype` instances of 256-bit outputs by evaluation).
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput

/-! ## R3's world: coins, public hash, ticks -/

/-- The tick oracle: one unit of the shared budget consumed by an offline honest computation. -/
abbrev TickSpec : OracleSpec Unit := Unit →ₒ Unit

/-- R3's oracle world. -/
abbrev RefWorld := OracleWorld + TickSpec

/-- Charged R3 queries (as `Derivation.charged`): public hash queries and ticks; coins are free. -/
def RefCharged : RefWorld.Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True

instance instDecidablePredDomainSumNatHashInputUnitRefWorldRefCharged : DecidablePred RefCharged := fun input => by
  rcases input with (n | x) | u <;> unfold RefCharged <;> infer_instance

/-- One tick. -/
def tick : OracleComp RefWorld Unit := liftM (RefWorld.query (.inr ()))

/-- `n` ticks. -/
def ticks : Nat → OracleComp RefWorld Unit
  | 0 => pure ()
  | n + 1 => tick >>= fun _ => ticks n

/-- Honest charge of key generation under `T` (every honest call is charged). -/
noncomputable def keygenCharge (T : Answers) : Nat := (SourceReplay.queried T keygen).length

/-- Honest charge of one authenticated signing request under `T` (the MAC call, and the payload if the cache is
the published one). -/
noncomputable def signCharge (T : Answers) (published : T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length

/-- The offline authenticated signer: consume its honest charge, answer by evaluation under `T`. -/
noncomputable def offlineSign (T : Answers) (published : T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))

/-- The adversary's oracle in R3: world queries forwarded to R3's world, signing requests answered offline
(`offlineSign`) and logged exactly as `FullGame.loggedWith` logs them. -/
noncomputable def offlineImpl (T : Answers) (published : T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)

/-- The verdict's oracle in R3: its public queries are forwarded (the padded verdict makes no private query,
`PaddedGame.verdict_public`; private coordinates would answer `0`). -/
noncomputable def verdictImpl : QueryImpl T3.Spec (OracleComp RefWorld)
  | .inl input => liftM (RefWorld.query (.inl input))
  | .inr _ => pure (0 : HashOutput)

/-- The adversary's interaction in R3: the logged run against `offlineImpl`. -/
noncomputable def offlineInteraction (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + Requests) α) : OracleComp RefWorld (α × QueryLog Requests) :=
  (simulateQ (offlineImpl T published) program).run

/-- **R3's game on a fixed table** (uncapped): offline key generation (charged by ticks), the adversary against
the offline signer, the padded verdict. -/
noncomputable def offlineGame (T : Answers) (adversary : AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)

/-- **R3's capped game**: the pinned `QueryCap.run` with budget `q` over the charged R3 queries. -/
noncomputable def referenceGame (T : Answers) (adversary : AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q

/-- R3's world on a fixed table: coins uniform, public hash queries answered by `T`, ticks trivial. -/
noncomputable def refImpl (T : Answers) : QueryImpl RefWorld ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr input) => pure (T (.inl (.inr input)))
  | .inr _ => pure ()

/-- **R3 on a fixed table**: the capped game with every R3 query recorded, in order. -/
noncomputable def offlineRun (T : Answers) (adversary : AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))

/-- The recorded public hash queries with their answers under `T` (adversary and verifier, in order). -/
def traceOf (T : Answers) (queries : List RefWorld.Domain) : List Entry :=
  queries.filterMap fun query => match query with
    | .inl (.inr input) => some (input, T (.inl (.inr input)))
    | _ => none

/-! ## Eager tables and the reference experiment -/

/-- R3's eager public universe: every input of length ≤ 4096 and every hash input of the recorded padded game. -/
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)

/-- The eager table: coins `0`, public inputs from the finite public table (`0` outside it, as SEC's
`finiteRecorded`), private coordinates from the private table. -/
noncomputable def eagerAnswers (inputs : Finset HashInput) (privateTable : FullGame.FullTable)
    (publicTable : inputs → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => SphincsSecurity.Concrete.finiteHashAnswer ∅ inputs publicTable input
  | .inr coordinate => privateTable coordinate

/-- An R3 sample: the eager table, the honest public key, and the ordered non-honest trace (adversary queries,
then the final verification), within the shared budget. -/
structure RefSample where
  answers : Answers
  publicKey : Digest
  trace : List Entry

/-- R3 as a probabilistic computation. -/
noncomputable def referenceComp (adversary : AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q

/-- **R3, the T3 reference experiment.** -/
noncomputable def referenceExperiment (adversary : AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)

end SigGolfCandidate.T3.Security.Wots
