import SigGolfCandidate.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.T3.Secc.CaseCCore

/-!
# LR-34 (certificate, interface): the bank certificate of the router and of the real run

* `CertGhost st` — CC's `core_win` premise for the router's bank ghost: the bank is alive (at most
  `proposalLength` exposures) and either a fresh signing hit the reuse event or some birth is an admissible digest
  output whose opened positions are all opened by exposures (`CaseC.CoveredBy`).
* `CertOut r` — the router finished with an accepting verdict and a certificate.
* `routerFold` — the router-state fold of a tagged split of the real run (honest nonces of the table).
* `CertR adversary q rec A` — on every tagged split of the recorded run: the verdict accepts, the monitor never
  contacts and stays within the budget, and the router fold carries a certificate.

The certificate side of the large route is `Pr[CleanWin ∧ ¬Contact | completed] ≤ Pr[CertOut | lazy router]`
(coupling) and `Pr[CertOut | lazy router] ≤ q·11400/10^8/2^128 + E[mass]/2^128` (the bank in the lazy router).
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

/-- **The bank certificate of a router state** (CC's `core_win` premise). -/
def CertGhost (st : RouterState) : Prop :=
  st.exposures.length ≤ BPORS.Numeric.proposalLength ∧
    (st.reused = true ∨ ∃ p ∈ st.births, admissible (selections p.2) = true ∧ digestGate p.2=true ∧ CaseC.CoveredBy st.exposures p.2)

/-- The router finished with an accepting verdict and a certificate. -/
def CertOut {U : Finset HashInput} (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    Prop :=
  ∃ st, r.1 = some (some (true, st)) ∧ CertGhost st

/-- The honest nonce of a message under a table. -/
noncomputable def honestNonce (A : Answers) (m : Message) : Digest := evalWithAnswerFn A (privateNonce m)

/-- The router-state fold of a tagged split of the real run. -/
noncomputable def routerFold (U : Finset HashInput) (A : Answers) (published : T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) : RouterState :=
  verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published) RouterState.initial)

/-- **The real certificate event** of a recorded run under a table. -/
def CertR (adversary : AdversaryP) (q : Nat) (rec : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary rec generated tagged checked →
    checked.value = true ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = false ∧
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).calls ≤ q ∧
    CertGhost (routerFold (Wots.referenceInputs adversary) A generated.value.2 tagged.steps checked.events)

end SigGolfCandidate.T3.Security.LargeCoupling
