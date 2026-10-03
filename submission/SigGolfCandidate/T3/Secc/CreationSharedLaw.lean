import SigGolfCandidate.T3.BPORS
import SigGolfCandidate.T3.Secc.SeccLaw

namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The local birth-accounting counter is exactly the shared budget counter. -/
theorem prefixCount_eq_classCharge (cls : T3.Spec.Domain → Prop) (budget : Nat)
    (events : List FirstHit.QueryEvent) :
    prefixCount cls budget events = SeccLaw.classCharge cls budget events := by
  induction events generalizing budget with
  | nil => rfl
  | cons event rest ih => simp only [prefixCount, SeccLaw.classCharge, ih]

/-- Adding SECC's uniform completion preserves every trace-only expectation. -/
theorem completed_trace_expectation (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) (payoff : PaddedGame.TraceResult → ENNReal) :
    expectedValue (SeccLaw.completedExperiment adversary budget hbudget) (fun z => payoff z.1) =
      expectedValue (PaddedGame.tracedExperiment adversary budget hbudget) payoff := by
  unfold SeccLaw.completedExperiment
  rw [← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext result
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  exact expectedValue_const (mx := PMF.uniformOfFintype SeccLaw.CompletionTables)
    (by simp) (payoff result)

/-- The digest-class baseline is measured on the common completed experiment,
so it shares the same budget with SECC's structural and chain classes. -/
theorem expectedClassCount_eq_shared (cls : T3.Spec.Domain → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount cls adversary budget hbudget =
      SeccLaw.expectedCharge adversary budget hbudget (fun _ => cls) := by
  rw [expectedClassCount, ← completed_trace_expectation]
  unfold SeccLaw.expectedCharge expectedValue
  apply tsum_congr
  intro z
  rw [PMF.probOutput_eq_apply]
  congr 1
  change (prefixCount cls budget z.1.2.2.events : ENNReal) =
    (SeccLaw.classCharge cls budget z.1.2.2.events : ENNReal)
  exact_mod_cast prefixCount_eq_classCharge cls budget z.1.2.2.events

theorem expectedBirths_le_shared (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget ≤
      SeccLaw.expectedCharge adversary budget hbudget (fun _ => publicClass cls) := by
  rw [← expectedClassCount_eq_shared]
  exact expectedBirths_le_classCount cls adversary budget hbudget

/-- The completed-proposal full-price charge has SECC's exact class-count
shape, with only the excess charged against the entire compression budget.
This is the charge bound; the future-exposure event bridge is separate. -/
theorem full_charge_le_shared_excess (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedCharge (fun _ => classWeight cls budget) budget BPORS.History.fullPrice
      adversary budget hbudget ≤
      SeccLaw.expectedCharge adversary budget hbudget (fun _ => publicClass cls) +
        (budget : ENNReal) * (13145/100000000) := by
  rw [← expectedClassCount_eq_shared]
  refine (full_charge_le_class_excess cls adversary budget hbudget).trans (add_le_add le_rfl (mul_le_mul' le_rfl ?_))
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

end SigGolfCandidate.T3.Security.CreationGame
