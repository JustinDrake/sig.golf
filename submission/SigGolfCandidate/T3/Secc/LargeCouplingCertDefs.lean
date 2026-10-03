import SigGolfCandidate.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.T3.Secc.CaseCCore

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def CertGhost (st : RouterState) : Prop :=
  st.exposures.length ≤ BPORS.Numeric.proposalLength ∧
    (st.reused = true ∨ ∃ p ∈ st.births, admissible (selections p.2) = true ∧ digestGate p.2=true ∧ CaseC.CoveredBy st.exposures p.2)
def CertOut {U : Finset HashInput} (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    Prop :=
  ∃ st, r.1 = some (some (true, st)) ∧ CertGhost st
noncomputable def honestNonce (A : Answers) (m : Message) : Digest := evalWithAnswerFn A (privateNonce m)
noncomputable def routerFold (U : Finset HashInput) (A : Answers) (published : T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) : RouterState :=
  verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published) RouterState.initial)
def CertR (adversary : AdversaryP) (q : Nat) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary rec generated tagged checked →
    checked.value = true ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = false ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).calls ≤ q ∧
    CertGhost (routerFold (Wots.referenceInputs adversary) A generated.value.2 tagged.steps checked.events)
end SigGolfCandidate.T3.Security.LargeCoupling
