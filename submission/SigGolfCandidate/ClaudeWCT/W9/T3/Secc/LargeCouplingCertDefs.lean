import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCLinkInv
import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
def CertGhost (st : RouterState) : Prop :=
  st.exposures.length ≤ CaseC.horizon ∧
    (st.reused = true ∨ ∃ p ∈ st.births, WCT9.admissible p.2 = true ∧ ClaudeWCT.Bank.WCT.Covered st.exposures p.2)
def CertOut {U : Finset HashInput} (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    Prop :=
  ∃ st, r.1 = some (some (true, st)) ∧ CertGhost st
noncomputable def routerFold (U : Finset HashInput) (A : Answers) (published : SigGolfCandidate.T3.Cache)
    (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) : RouterState :=
  verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published) RouterState.initial)
def CertR (adversary : AdversaryP) (q : Nat) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary rec generated tagged checked →
    checked.value = true ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = false ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).calls ≤ q ∧
    CertGhost (routerFold (Wots.referenceInputs adversary) A generated.value.2 tagged.steps checked.events)
end ClaudeWCT.W9.T3.Security.LargeCoupling
