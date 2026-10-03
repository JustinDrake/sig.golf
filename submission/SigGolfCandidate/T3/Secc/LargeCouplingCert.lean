import SigGolfCandidate.T3.Secc.LargeCouplingBankRun
import SigGolfCandidate.T3.Secc.LargeCouplingCertChain
import SigGolfCandidate.T3.Secc.LargeCouplingRoute

/-!
# LR-34 (assembly): the large-route certificate bound and the large route

* `lazy_noFail` — the lazy run from the initial state never fails (its eager average, `run_posterior`, does not);
* **`bank_cert_le`** — CC's bank inside the lazy router: `Pr[CertOut | lazy router] ≤ q·13145/10^8/2^128 +
  E[mass]/2^128` (`bank_router`, `core_win`, `core_initial`, the mass allowance `slackT`);
* **`large_cert_bound : LargeCertBound adversary q hq`** — with the certificate coupling `cert_le_lazy`;
* **`large_route`** — `Pr[CleanWin q | tracedExperiment adversary q hq] ≤ largeBound q` (`large_route_of_cert`), and
  `large_route_hlarge`, the `hlarge` hypothesis of `SeccClosing.securityP_of_routes`.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The lazy run never fails -/

section NoFail
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
  (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

theorem observed_noFail (labels : Coord → LargeResidual.Digest) (table : Cell → LargeResidual.HashOutput) {R : Type}
    (P : OracleComp (World auxSpec Coord Cell) R) :
    ∀ s, Pr[⊥ | observedRun aux q labels table P s] = 0 := by
  induction P using OracleComp.inductionOn with
  | pure v =>
      intro s
      rw [observedRun, runWith_pure]
      simp
  | query_bind input next ih =>
      intro s
      rw [observedRun, runWith_query_bind, probFailure_bind_eq_add_tsum]
      have h1 : Pr[⊥ | (observedImpl aux q labels table input).run.run s] = 0 := by
        rcases input with i | req
        · simp [observedImpl]
        · cases req with
          | read row ch => simp [observedImpl]
          | probe row test =>
              simp only [observedImpl, OptionT.run_mk, StateT.run_mk]
              split
              · simp
              · split <;> simp
          | disclose c ch => simp [observedImpl]
          | tick ch => simp [observedImpl]
      rw [h1, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro r
      rcases r with ⟨o, s'⟩
      cases o with
      | none => simp
      | some v =>
          simp only [Option.elim_some]
          exact mul_eq_zero_of_right _ (ih v s')

theorem lazy_noFail {R : Type} (P : OracleComp (World auxSpec Coord Cell) R) :
    Pr[⊥ | lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)] = 0 := by
  have hpost := run_posterior aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)
    (fun _ => Finset.univ_nonempty)
  have h1 : Pr[⊥ | lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell) >>= finish] = 0 := by
    rw [← hpost]
    have hc : complete (LargeResidual.initial : LargeResidual.State Coord Cell).candidates =
        liftM (uniformTable (fun _ : Coord => (Finset.univ : Finset LargeResidual.Digest)) (fun _ => Finset.univ_nonempty)) :=
      complete_of_nonempty _ _
    have hr : completeRows (LargeResidual.initial : LargeResidual.State Coord Cell).rows =
        liftM (PMF.uniformOfFintype (Cell → LargeResidual.HashOutput)) := completeRows_empty
    rw [hc, hr, probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    apply ENNReal.tsum_eq_zero.mpr
    intro labels
    rw [probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro table
    rw [probFailure_map, observed_noFail, mul_zero]
  have h2 := probFailure_bind_eq_add_tsum
    (lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)) finish
  rw [h1] at h2
  exact (add_eq_zero.mp h2.symm).1

end NoFail

/-! ## The bank bound -/

section Bank
variable {U : Finset HashInput}

/-- The bank potential of a finished router outcome (no allowance). -/
noncomputable def psiOut (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi q st
  | _ => 0

theorem bankPay_eq (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    bankPay q r = psiOut q r + slackT q r.2 := rfl

theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert q st hc
  · exact zero_le

/-- **CC's bank inside the lazy router.** -/
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * (13145 / 100000000) / 2 ^ 128 +
        (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut q r + slackT q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  -- the certificate is paid by the potential
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi q)
  -- the allowance and the mass together are at least `q / 2^128`
  set S := expectedValue L (fun r => slackT q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : (q : ENNReal) / 2 ^ 128 ≤ S + Mass / 2 ^ 128 := by
    have hMass' : Mass / 2 ^ 128 = expectedValue L (fun r => (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv]
      rw [expectedValue_mul_const L (fun r => (r.2.counters.mass : ENNReal))]
      rfl
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail ((q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div]
    apply ENNReal.div_le_div_right
    rw [← Nat.cast_add]
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top q) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut q) + S ≤ (psi q RouterState.initial + Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi q RouterState.initial + (S + Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut q) := hcert
    _ ≤ psi q RouterState.initial + Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial q) le_rfl

end Bank

/-! ## The large route -/

/-- **The large-route certificate bound.** -/
theorem large_cert_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : LargeCertBound adversary q hq := by
  unfold LargeCertBound
  refine (cert_le_lazy adversary q hq).trans ?_
  refine (bank_cert_le (Wots.Ref.referenceInputs_universe adversary) initLaw adversary q).trans ?_
  have hrm : (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
      LargeResidual.initial] * (r.2.counters.mass : ENNReal)) = routerMass adversary q := rfl
  rw [hrm, SeccClosing.excessRate_def]
  calc
    _ = routerMass adversary q / 2 ^ 128 + (q : ENNReal) * (13145 / 100000000) / 2 ^ 128 := add_comm _ _
    _ ≤ _ := by
      simp only [add_assoc]
      exact add_le_add le_rfl le_self_add

/-- **The large route**: `Pr[CleanWin q | tracedExperiment] ≤ largeBound q`. -/
theorem large_route (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  large_route_of_cert adversary q hq (large_cert_bound adversary q hq)

/-- The `hlarge` hypothesis of `SeccClosing.securityP_of_routes`. -/
theorem large_route_hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  fun adversary q hq _ => large_route adversary q hq

end SigGolfCandidate.T3.Security.LargeCoupling
