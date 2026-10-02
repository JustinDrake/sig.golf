import SigGolfCandidate.T3.Secc.LargeResidualT3
import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsReference

/-!
# LR-34 (trace side): tagged runs, the contact monitor, `Contact` and `digests`

Honest queries are never contacts. The recorded padded game interleaves honest key generation, honest signing and
the adversary's and verifier's queries; a **tagged record** of the interaction keeps each adversary world query as a
single event and each signing request as one block (request, answer, the signer's events). `TaggedSplit` is F2's
`Wots.GameSplit` with the interaction tagged (its untagged events are exactly the recorded interaction events).

The **monitor** walks the adversary and verifier events in order: the knowledge at an event is the closure
(`Known`) of `keygenDisclosed` and of `signDisclosed` of the signing blocks before it; an adversary/verifier public
query is tested by `ContactTest` at the first occurrence of its input among the first `q` calls; `calls` counts the adversary/verifier public
queries and `digests` the digest rows among the first `q` of them before the first contact.

* `Contact adversary q z` — for every tagged split of the recorded trace of `z.1`, the monitor (answers `z.2`) contacts.
* `digests adversary q z` — the monitor's digest count of a tagged split (unique on the support; `0` off it).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Tagged interaction records -/

/-- One element of a tagged interaction: an adversary world query (coin or public hash), or one signing request
with the signer's answer and all of the signer's recorded events. -/
inductive TaggedStep where
  | world (event : FirstHit.QueryEvent)
  | sign (request : Security.Request) (output : Option Signature) (events : List FirstHit.QueryEvent)

/-- The recorded events of a tagged step. -/
def TaggedStep.events : TaggedStep → List FirstHit.QueryEvent
  | .world event => [event]
  | .sign _ _ events => events

/-- A tagged interaction record: the adversary's result with the signing log, the tagged steps, the final caches. -/
structure Tagged (α : Type) where
  value : α × QueryLog Requests
  steps : List TaggedStep
  state : LazyPrivate.State

/-- The untagged events of a tagged interaction. -/
def Tagged.events {α : Type} (tagged : Tagged α) : List FirstHit.QueryEvent :=
  tagged.steps.flatMap TaggedStep.events

/-- The tagged record of `FullGame.loggedWith (FullGame.authenticatedSign published) program`. -/
noncomputable def taggedRecord {α : Type} (published : T3.Cache) (program : OracleComp LazyPrivate.Interaction α) :
    LazyPrivate.State → ProbComp (Tagged α) :=
  OracleComp.construct
    (fun value state => pure ⟨(value, []), [], state⟩)
    (fun input _ next state => match input, next with
      | .inl world, next => do
          let middle ← LazyPrivate.run (liftM (T3.Spec.query (.inl world))) state
          (fun last => (⟨last.value, .world ⟨state, .inl world, middle.1⟩ :: last.steps, last.state⟩ : Tagged α)) <$>
            next middle.1 middle.2
      | .inr request, next => do
          let block ← FirstHit.record (FullGame.authenticatedSign published request) state
          (fun last => (⟨(last.value.1, ⟨request, block.value⟩ :: last.value.2),
              .sign request block.value block.events :: last.steps, last.state⟩ : Tagged α)) <$>
            next block.value block.state)
    program

/-- A decomposition of a recorded padded-game run with the interaction tagged (refines F2's `Wots.GameSplit`). -/
def TaggedSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × T3.Cache)) (tagged : Tagged (Option ForgeryP))
    (checked : FirstHit.Recorded Bool) : Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  tagged ∈ support (taggedRecord generated.value.2 (adversary generated.value.1 generated.value.2) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 tagged.value)
      tagged.state) ∧
  result = ⟨checked.value, generated.events ++ (tagged.events ++ checked.events), checked.state⟩

/-! ## The monitor -/

/-- Monitor state: signature disclosures so far, adversary/verifier inputs seen, calls, digest count, contact flag. -/
structure Monitor where
  disclosed : List Coord
  seen : List HashInput
  calls : Nat
  digests : Nat
  contact : Bool

def Monitor.initial : Monitor := ⟨[], [], 0, 0, false⟩

/-- The adversary's knowledge in a monitor state. -/
def Monitor.known (monitor : Monitor) : Coord → Prop :=
  Known fun c => c ∈ keygenDisclosed ∨ c ∈ monitor.disclosed

/-- One adversary/verifier public query: tested at its first occurrence, within the first `q` calls, when it lies
in the eager universe `U` (R3's `referenceInputs`, which holds every query of the game); digest rows of `U` among the
first `q` calls count. -/
noncomputable def Monitor.query (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (input : HashInput) (answer : HashOutput) : Monitor :=
  if monitor.contact then monitor
  else if input ∉ monitor.seen ∧ input ∈ U ∧ monitor.calls + 1 ≤ q ∧ ContactTest A monitor.known input answer then
    ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1, monitor.digests, true⟩
  else ⟨monitor.disclosed, input :: monitor.seen, monitor.calls + 1,
    monitor.digests + (if input ∈ U ∧ IsDigestRow input ∧ monitor.calls + 1 ≤ q then 1 else 0), false⟩

/-- One adversary/verifier event (coins are free). -/
noncomputable def Monitor.event (U : Finset HashInput) (A : Answers) (q : Nat) (monitor : Monitor)
    (event : FirstHit.QueryEvent) : Monitor :=
  match event with
  | ⟨_, .inl (.inr input), answer⟩ => monitor.query U A q input answer
  | _ => monitor

/-- One signing block: its disclosures join the knowledge. -/
noncomputable def Monitor.sign (A : Answers) (published : T3.Cache) (monitor : Monitor)
    (request : Security.Request) : Monitor :=
  if monitor.contact then monitor
  else ⟨monitor.disclosed ++ signDisclosed A published request, monitor.seen, monitor.calls, monitor.digests, false⟩

/-- One tagged interaction step. -/
noncomputable def Monitor.step (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)
    (monitor : Monitor) : TaggedStep → Monitor
  | .world event => monitor.event U A q event
  | .sign request _ _ => monitor.sign A published request

/-- The monitor over the tagged interaction and the verifier's events. -/
noncomputable def monitorRun (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : Monitor :=
  verdict.foldl (Monitor.event U A q) (steps.foldl (Monitor.step U A q published) Monitor.initial)

/-! ## Contact and digests on the shared law -/

/-- **The large-route contact** of a shared-law sample: on every tagged split of its recorded trace, the monitor
(answers = the completion) finds an adversary or verifier query that guesses a hidden value or hits an honest one. -/
def Contact (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) z.2 q generated.value.2 tagged.steps checked.events).contact = true

/-- **The digest mass** of a shared-law sample: the monitor's count of digest rows among the first `q`
adversary/verifier public queries before the first contact (of the unique tagged split; `0` off the support). -/
noncomputable def digests (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) : Nat :=
  if h : ∃ generated tagged checked,
      TaggedSplit adversary (QueryRecorded.recordedTrace z.1) generated tagged checked then
    (monitorRun (Wots.referenceInputs adversary) z.2 q (Classical.choose h).value.2 (Classical.choose (Classical.choose_spec h)).steps
      (Classical.choose (Classical.choose_spec (Classical.choose_spec h))).events).digests
  else 0

end SigGolfCandidate.T3.Security.LargeCoupling
