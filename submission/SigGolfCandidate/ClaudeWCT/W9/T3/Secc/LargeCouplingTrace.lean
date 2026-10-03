import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeResidualT3
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (IsDigestRow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
inductive TaggedStep where
  | world (event : FirstHit.QueryEvent)
  | sign (request : Security.Request) (output : Option Signature) (events : List FirstHit.QueryEvent)
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
  | .world event => [event]
  | .sign _ _ events => events
structure Tagged (α : Type) where
  value : α × QueryLog Requests
  steps : List TaggedStep
  state : LazyPrivate.State
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events
noncomputable def taggedRecord {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (SigGolfCandidate.T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program
def TaggedSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)) (tagged : Tagged (Option ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩
structure Monitor where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  digests : Nat
  contact : Bool
def Monitor.initial : Monitor := ⟨[], [], 0, 0, false⟩
def Monitor.known (monitor : Monitor) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ monitor.disclosed
noncomputable def Monitor.query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (input : HashInput) (answer : HashOutput) : Monitor :=
  if monitor.contact then monitor
  else if input ∉ monitor.seen ∧ input ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known input answer then
    ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1, monitor.digests, true⟩
  else ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1,
    monitor.digests + (if input ∈ U ∧ IsDigestRow input ∧ monitor.calls + 1 ≤ q then 1 else 0), false⟩
noncomputable def Monitor.event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (event : FirstHit.QueryEvent) : Monitor :=
  match event with
  | ⟨_, .inl (.inr input), answer⟩ => monitor.query U A q input answer
  | _ => monitor
noncomputable def Monitor.sign (A : Answers) (published : SigGolfCandidate.T3.Cache) (monitor : Monitor)
    (request : Security.Request) : Monitor :=
  if monitor.contact then monitor
  else ⟨monitor.disclosed ++ signDisclosed A published request, monitor.seen, monitor.calls, monitor.digests, false⟩
noncomputable def Monitor.step (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (monitor : Monitor) : TaggedStep → Monitor
  | .world event => monitor.event U A q event
  | .sign request _ _ => monitor.sign A published request
noncomputable def monitorRun (U : Finset HashInput) (A : Answers) (q : Nat) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : Monitor :=
  verdict.foldl (Monitor.event U A q) (steps.foldl (Monitor.step U A q published) Monitor.initial)
def Contact (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) z.2 q generated.value.2 tagged.steps checked.events).contact = true
noncomputable def digests (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Nat :=
  if h : ∃ generated tagged checked,
      TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked then
    (monitorRun (Wots.referenceInputs adversary) z.2 q (Classical.choose h).value.2 (Classical.choose (Classical.choose_spec h)).steps
      (Classical.choose (Classical.choose_spec (Classical.choose_spec h))).events).digests
  else 0
end ClaudeWCT.W9.T3.Security.LargeCoupling
