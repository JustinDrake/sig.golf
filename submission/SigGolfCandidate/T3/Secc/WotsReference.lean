import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryAllocation

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
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
abbrev TickSpec : OracleSpec Unit := Unit →ₒ Unit
abbrev RefWorld := OracleWorld + TickSpec
def RefCharged : RefWorld.Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True
instance instDecidablePredDomainSumNatHashInputUnitRefWorldRefCharged : DecidablePred RefCharged := fun input => by
  rcases input with (n | x) | u <;> unfold RefCharged <;> infer_instance
def tick : OracleComp RefWorld Unit := liftM (RefWorld.query (.inr ()))
def ticks : Nat → OracleComp RefWorld Unit
  | 0 => pure ()
  | n + 1 => tick >>= fun _ => ticks n
noncomputable def keygenCharge (T : Answers) : Nat := (SourceReplay.queried T keygen).length
noncomputable def signCharge (T : Answers) (published : T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def verdictImpl : QueryImpl T3.Spec (OracleComp RefWorld)
  | .inl input => liftM (RefWorld.query (.inl input))
  | .inr _ => pure (0 : HashOutput)
noncomputable def offlineInteraction (T : Answers) (published : T3.Cache) {α : Type}
    (program : OracleComp (OracleWorld + Requests) α) : OracleComp RefWorld (α × QueryLog Requests) :=
  (simulateQ (offlineImpl T published) program).run
noncomputable def offlineGame (T : Answers) (adversary : AdversaryP) : OracleComp RefWorld Bool :=
  ticks (keygenCharge T) >>= fun _ =>
    offlineInteraction T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) >>= fun result =>
    simulateQ verdictImpl (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 result)
noncomputable def referenceGame (T : Answers) (adversary : AdversaryP) (q : Nat) :
    OracleComp RefWorld (Option (Bool × Nat)) :=
  SphincsSecurity.QueryCap.run RefCharged (offlineGame T adversary) q
noncomputable def refImpl (T : Answers) : QueryImpl RefWorld ProbComp
  | .inl (.inl n) => liftM (unifSpec.query n)
  | .inl (.inr input) => pure (T (.inl (.inr input)))
  | .inr _ => pure ()
noncomputable def offlineRun (T : Answers) (adversary : AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
def traceOf (T : Answers) (queries : List RefWorld.Domain) : List Entry :=
  queries.filterMap fun query => match query with
    | .inl (.inr input) => some (input, T (.inl (.inr input)))
    | _ => none
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)
noncomputable def eagerAnswers (inputs : Finset HashInput) (privateTable : FullGame.FullTable)
    (publicTable : inputs → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => SphincsSecurity.Concrete.finiteHashAnswer ∅ inputs publicTable input
  | .inr coordinate => privateTable coordinate
structure RefSample where
  answers : Answers
  publicKey : Digest
  trace : List Entry
noncomputable def referenceComp (adversary : AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end SigGolfCandidate.T3.Security.Wots
