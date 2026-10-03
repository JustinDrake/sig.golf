import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.T3.Secc.WotsReference

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_w9WotsReference : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_w9WotsReference :
    SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
attribute [local instance] FiniteRowSplit.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput
noncomputable def signCharge (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) : Nat :=
  (SourceReplay.queried T (FullGame.authenticatedSign published request)).length
noncomputable def offlineSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp RefWorld (Option Signature) :=
  ticks (signCharge T published request) >>= fun _ =>
    pure (evalWithAnswerFn T (FullGame.authenticatedSign published request))
noncomputable def offlineImpl (T : Answers) (published : SigGolfCandidate.T3.Cache) :
    QueryImpl (OracleWorld + Requests) (WriterT (QueryLog Requests) (OracleComp RefWorld)) :=
  (fun input => (liftM (liftM (RefWorld.query (.inl input)) : OracleComp RefWorld (OracleWorld.Range input)) :
      WriterT (QueryLog Requests) (OracleComp RefWorld) (OracleWorld.Range input))) +
    QueryImpl.withLogging (offlineSign T published)
noncomputable def offlineInteraction (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type}
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
noncomputable def offlineRun (T : Answers) (adversary : AdversaryP) (q : Nat) :
    ProbComp (Option (Bool × Nat) × List RefWorld.Domain) :=
  simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded (referenceGame T adversary q))
noncomputable def referenceInputs (adversary : AdversaryP) : Finset HashInput :=
  SeccLaw.publicUniverse ∪ ChainGraph.recordedInputs (GameWith.idealGame PaddedGame.checker adversary)
noncomputable def referenceComp (adversary : AdversaryP) (q : Nat) : ProbComp RefSample :=
  ($ᵗ FullGame.FullTable : ProbComp _) >>= fun privateTable =>
    ($ᵗ (referenceInputs adversary → HashOutput) : ProbComp _) >>= fun publicTable =>
      (fun run => (⟨eagerAnswers (referenceInputs adversary) privateTable publicTable,
          (evalWithAnswerFn (eagerAnswers (referenceInputs adversary) privateTable publicTable) keygen).1,
          traceOf (eagerAnswers (referenceInputs adversary) privateTable publicTable) run.2⟩ : RefSample)) <$>
        offlineRun (eagerAnswers (referenceInputs adversary) privateTable publicTable) adversary q
noncomputable def referenceExperiment (adversary : AdversaryP) (q : Nat) : PMF RefSample :=
  liftM (referenceComp adversary q)
end ClaudeWCT.W9.T3.Security.Wots
