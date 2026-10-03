import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainErasure
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapErasure

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem realRun_empty_apply_lower (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (result : State × (Result × (Fin n → State → Option State))) :
    (1 - (budget : ENNReal) / Fintype.card State) * idealRun auxiliary computation (fun _ _ => none) result ≤
      realRun auxiliary computation (fun _ _ => none) result := by
  classical
  have h := realRun_empty_cost_lower auxiliary computation budget hbound (fun output => if output = result then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, tsum_ite_eq] using h
theorem idealRun_empty_support_subset (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (budget : Nat)
    (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget)
    (hsmall : budget < Fintype.card State) :
    (idealRun auxiliary computation (fun _ _ => none)).support ⊆
      (realRun auxiliary computation (fun _ _ => none)).support := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (budget : ENNReal) / Fintype.card State := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  intro result hresult
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hpositive, pos_iff_ne_zero.mpr hresult⟩)
    (realRun_empty_apply_lower auxiliary computation budget hbound result))
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section



namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem fixed_counted_le (tables : Fin n → State → State) (secret : State) (result : Result × Nat)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (QueryCap.counted IsPrefixQuery (computation (evaluate tables secret)))).support) : result.2 ≤ budget := by
  have hcount := hcharge (evaluate tables secret) result (QueryCap.simulate_mem_support _ _ result hresult)
  have houtput := QueryCap.counted_simulate_result_mem IsPrefixQuery _ _ result hresult
  have hsource := realRun_empty_result_mem auxiliary computation tables secret result.1 houtput
  rw [PMF.mem_support_map_iff] at hsource
  obtain ⟨source, hsource, hvalue⟩ := hsource
  exact hcount.trans (by simpa only [hvalue] using hreal source hsource)
theorem realRun_cap_erased :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map Prod.fst result.2.1) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map Prod.fst ∘ (fun result => result.2.1)) =
    (realRun auxiliary computation (fun _ _ => none)).map (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_erased IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)
theorem realRun_cap_recover_count :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map (fun finished => (finished.1, budget - finished.2)) result.2.1) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map (fun finished => (finished.1, budget - finished.2)) ∘ (fun result => result.2.1)) =
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
      (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_recover_count IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)
theorem realRun_cap_valid (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  have hmap : Option.map Prod.fst result.2.1 ∈
      ((realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
        (fun result => Option.map Prod.fst result.2.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [realRun_cap_erased auxiliary computation cost budget hcharge hreal, PMF.mem_support_map_iff] at hmap
  obtain ⟨source, hsource, hvalue⟩ := hmap
  cases hfinished : result.2.1 with
  | none => simp only [hfinished, Option.map_none, Option.some_ne_none] at hvalue
  | some finished =>
      refine ⟨finished, rfl, ?_⟩
      have heq : source.2.1 = finished.1 := by simpa only [hfinished, Option.map_some, Option.some.injEq] using hvalue
      rw [← heq]
      exact hreal source hsource
theorem idealRun_cap_valid (hsmall : budget < Fintype.card State)
    (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  apply realRun_cap_valid auxiliary computation cost budget hcharge hreal result
  exact idealRun_empty_support_subset auxiliary _ budget
    (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget) hsmall hresult
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.QueryCap
open _root_.OracleComp OracleSpec ENNReal
def spent {Result : Type} (budget : Nat) (result : Option (Result × Nat)) : Nat :=
  result.elim 0 (fun finished => budget - finished.2)
theorem scaled_expectation_bind_le {Sample First Second : Type} (prior : SPMF Sample)
    (first : Sample → SPMF First) (second : Sample → SPMF Second)
    (firstCost : First → ENNReal) (secondCost : Second → ENNReal) (factor : ENNReal)
    (h : ∀ sample ∈ support prior,
      factor * (∑' result, Pr[= result | first sample] * firstCost result) ≤
        ∑' result, Pr[= result | second sample] * secondCost result) :
    factor * (∑' result, Pr[= result | prior >>= first] * firstCost result) ≤
      ∑' result, Pr[= result | prior >>= second] * secondCost result := by
  rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro sample
  by_cases hsample : sample ∈ support prior
  · rw [mul_left_comm factor]
    exact mul_le_mul' le_rfl (h sample hsample)
  · rw [probOutput_eq_zero_of_not_mem_support hsample, zero_mul, zero_mul, mul_zero]
end SphincsSecurity.QueryCap
namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_count_payoff (payoff : Result × Nat → ENNReal) :
    (∑' result, realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
        (fun _ _ => none) result * result.2.1.elim 0 (fun finished => payoff (finished.1, budget - finished.2))) =
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * payoff result.2.1 := by
  have h := congrArg (fun law : PMF (Option (Result × Nat)) => ∑' result, law result * result.elim 0 payoff)
    (realRun_cap_recover_count auxiliary computation cost budget hcharge hreal)
  simpa only [expectation_map, Option.elim_map, Option.elim_some, Function.comp_def] using h
theorem idealRun_cap_spent_lower :
    (1 - (budget : ENNReal) / Fintype.card State) *
        (∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
          (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal)) ≤
      ∑' result, realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
        (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  apply (realRun_empty_cost_lower auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
    (fun result => (QueryCap.spent budget result.2.1 : ENNReal))).trans_eq
  have h := realRun_cap_count_payoff auxiliary computation cost budget hcharge hreal (fun result => (result.2 : ENNReal))
  convert h using 1
  apply tsum_congr
  intro result
  congr 1
  cases result.2.1 <;> simp only [QueryCap.spent, Option.elim_none, Option.elim_some, Nat.cast_zero]
end SphincsSecurity.Concrete.PartialChainEndpoint
end
