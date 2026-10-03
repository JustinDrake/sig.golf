import SigGolfCandidate.T3.Secc.CaseCNearBound
import SigGolfCandidate.T3.Secc.PairGuessLazyCouple

/-!
# Stream CC: `NearBoundK 405` from the guess chain (B-PAIR §8.5 shape)

`NearChainHyp`: the pinned near event's probability is at most `(2^128 − q)⁻¹ · Σ_{slot<q} Σ'_ω Pr[= ω | L] ·
E_{forcedRun envL slot (worldGameL ω)}[nearPayoff q]` for some law `L` of `ω` — exactly B-PAIR's `near_chain` with
`payoff := nearPayoff q` (and `L := restLaw adversary`), once its `hevent` side condition is discharged
(`CaseCNearPay.payoff_of_ghosts`, from B-PAIR's ghost facts).

`nearBoundK_of_nearChainHyp`: with CC's near bank (`forced_payoff_le`), `NearChainHyp` gives `NearBoundK K` for every
`K ≥ 404 + 1/16`, in particular `K = 405`; with `caseC_small_bound_K` and `small_route_K` the small route closes.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **The guess chain with CC's near payoff** (B-PAIR's `near_chain` conclusion, `payoff := nearPayoff q`). -/
def NearChainHyp : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127),
    ∃ L : ProbComp (BPair.Omega (Wots.referenceInputs adversary)),
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] ≤
        ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, ∑' ω, Pr[= ω | L] *
          ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot
            (BPair.worldGameL (BPair.canon_subset adversary) ω adversary) BPair.initL] * nearPayoff q r

theorem omega_avg_le {Ω : Type} (L : ProbComp Ω) (f : Ω → ENNReal) (B : ENNReal) (h : ∀ ω, f ω ≤ B) :
    ∑' ω, Pr[= ω | L] * f ω ≤ B :=
  calc
    _ ≤ ∑' ω, Pr[= ω | L] * B := ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)
    _ = (∑' ω, Pr[= ω | L]) * B := ENNReal.tsum_mul_right
    _ ≤ 1 * B := mul_le_mul' tsum_probOutput_le_one le_rfl
    _ = B := one_mul B

/-- **`NearBoundK` from the guess chain and CC's near bank.** -/
theorem nearBoundK_of_nearChainHyp (K : ENNReal) (hK : (404 + 1 / 16 : ENNReal) ≤ K) (h : NearChainHyp) :
    NearBoundK K := by
  intro adversary q hq _ _
  obtain ⟨L, hL⟩ := h adversary q hq
  have hslot : ∀ slot, (∑' ω, Pr[= ω | L] *
      ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot
        (BPair.worldGameL (BPair.canon_subset adversary) ω adversary) BPair.initL] * nearPayoff q r) ≤
      (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128 :=
    fun slot => omega_avg_le L _ _ fun ω => forced_payoff_sum_le (BPair.canon_subset adversary) ω adversary slot q
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ _ := hL
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ _slot ∈ Finset.range q, (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _ => hslot slot)
    _ = (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ((404 + 1 / 16) * q / 2 ^ 128) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (K * q / 2 ^ 128) := by gcongr
    _ ≤ _ := nearTermK_ge K q

/-- **The small route from the guess chain** (`K = 405`). -/
theorem small_route_of_nearChain (h : NearChainHyp) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_K 405 (by norm_num) (caseC_small_bound_K 405 (nearBoundK_of_nearChainHyp 405 near_price_le_104 h))

end SigGolfCandidate.T3.Security.CaseC
