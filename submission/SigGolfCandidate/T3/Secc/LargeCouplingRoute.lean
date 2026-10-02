import SigGolfCandidate.T3.Secc.LargeCouplingContact

/-!
# LR-34 (assembly): the large route from the router's certificate bound

**`large_route_of_cert`**: if the contact-free clean wins of the shared law cost at most the lazy router's expected
digest mass plus the excess, cache and reserve terms (`LargeCertBound`, the case-C certificate charged inside the
router run, CC-1), then `Pr[CleanWin q | tracedExperiment] ≤ largeBound q`.

Route: `completed_trace_event` (the clean win is a trace event of the shared law), the contact split
(`probEvent_le_contact_add`), **`contact_le_lazy`** (contacts are lazy-router stops), **`residual_potential`**
(LR-3/LR-1: stops within the budget plus the expected mass are at most `2x − x²`) and `largeBound_of_parts`.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open LargeResidual
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The lazy router of an adversary. -/
noncomputable abbrev lazyRouter (adversary : AdversaryP) (q : Nat) :=
  lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial

/-- The expected digest mass of the lazy router (one unit per adversary/verifier digest row within the budget). -/
noncomputable def routerMass (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' r, Pr[= r | lazyRouter adversary q] * (r.2.counters.mass : ENNReal)

/-- **The large-route certificate obligation** (inside the router run): contact-free clean wins of the shared law
cost at most the router's expected mass plus the excess, cache and reserve terms. -/
def LargeCertBound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : Prop :=
  Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
    routerMass adversary q / 2 ^ 128 + (q : ENNReal) * excessRate / 2 ^ 128 + (q : ENNReal) * cacheRate / 2 ^ 128 +
      (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute

/-- **The large route from the certificate obligation.** -/
theorem large_route_of_cert (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcert : LargeCertBound adversary q hq) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  apply SeccClosing.largeBound_of_parts q _
    (Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q]) _ (routerMass adversary q)
  · refine (SeccClosing.probEvent_le_contact_add _ (fun z => QueryRecorded.CleanWin q z.1) (Contact adversary q)
      (fun _ => True) (fun _ _ => trivial)).trans ?_
    gcongr
    refine le_trans (probEvent_mono'' fun z hz => hz.2) ?_
    exact contact_le_lazy adversary q hq
  · exact residual_potential (auxLaw initLaw) q hq _
  · exact hcert

end SigGolfCandidate.T3.Security.LargeCoupling
