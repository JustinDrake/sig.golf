import SigGolfCandidate.T3.Secc.CaseCNearEvent
import SigGolfCandidate.T3.Secc.CaseCSmallK

/-!
# Stream CC: `NearBoundK` from the guess chain and a per-slot near-bank bound

`nearBoundK_of_chain`: if the pinned near event's probability (through `near_shared`, for every decomposition) is at
most `(2^128 − q)⁻¹ · Σ_{slot < q} bound slot` (B-PAIR's `near_chain` shape), and every slot's expected payoff is at
most `q·(404 + 1/16)/2^128` (CC's near bank in the forced lazy world), then `NearBoundK K` for every `K ≥ 404 + 1/16`
(in particular `K = 405`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The near event read for every decomposition of the run (the left side of B-PAIR's `near_chain`). -/
def NearAll (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  QueryRecorded.CleanWin q z.1 ∧ ∀ generated interaction checked,
    Wots.GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked →
      NearIn z.2 interaction.value.2 (BPair.publicEntries checked.events)

theorem near_le_all (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := by
  apply pmf_probEvent_mono_support
  intro z hz h
  exact ⟨h.1, near_shared adversary q hq z hz h.1 h.2⟩

theorem nearTermK_ge (K : ENNReal) (q : Nat) :
    (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (K * q / 2 ^ 128) ≤ nearTermK K q := by
  unfold nearTermK
  apply mul_le_mul' le_rfl
  rw [add_assoc]
  exact le_self_add

/-- **`NearBoundK` from the guess chain and the per-slot near bank.** -/
theorem nearBoundK_of_chain (K : ENNReal) (hK : (404 + 1 / 16 : ENNReal) ≤ K)
    (bound : AdversaryP → Nat → Nat → ENNReal)
    (hchain : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127),
      Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] ≤
        ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, bound adversary q slot)
    (hbound : ∀ (adversary : AdversaryP) (q slot : Nat), slot < q →
      bound adversary q slot ≤ (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128) :
    NearBoundK K := by
  intro adversary q hq _ _
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ slot ∈ Finset.range q, bound adversary q slot := hchain adversary q hq
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ _slot ∈ Finset.range q, (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128 := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum fun slot hs => hbound adversary q slot (Finset.mem_range.mp hs)
    _ = (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ((404 + 1 / 16) * q / 2 ^ 128) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (K * q / 2 ^ 128) := by
      gcongr
    _ ≤ _ := nearTermK_ge K q

/-- `K = 405` covers the near price `404` and the reuse charge `1/16`. -/
theorem near_price_le_104 : (404 + 1 / 16 : ENNReal) ≤ 405 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_one]
  norm_num

end SigGolfCandidate.T3.Security.CaseC
