import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainPotential
import SigGolfCandidate.SphincsSecurity.Proof.Chains.PartialChainContactCount
import SigGolfCandidate.SphincsSecurity.Proof.Chains.PartialChainTwoEdgeCompensation
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_budget_potential_le (auxiliary : QueryImpl auxSpec PMF)
    (potential : Nat → (Fin n → State → Option State) → ENNReal)
    (terminal : (Fin n → State → Option State) → ENNReal) (rate : ENNReal) (limit : Nat)
    (hterminal : ∀ budget observed, terminal observed ≤ potential budget observed)
    (hstep : ∀ input observed budget, budget ≤ limit → (¬IsPrefixQuery input ∨ 0 < budget) →
      (∑' result, (lazyImpl auxiliary input).run observed result *
        potential (if IsPrefixQuery input then budget - 1 else budget) result.2) ≤
          potential budget observed + rate * ((if IsPrefixQuery input then 1 else 0 : Nat) : ENNReal))
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbudget : budget ≤ limit) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * terminal result.2) ≤
      potential budget observed + rate *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.cast_zero, mul_zero, add_zero]
      exact hterminal budget observed
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      have hremaining : (if IsPrefixQuery input then budget - 1 else budget) ≤ limit := by split <;> omega
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, Nat.cast_add, expectation_add, expectation_const]
      calc
        _ ≤ ∑' output, (lazyImpl auxiliary input).run observed output *
            (potential (if IsPrefixQuery input then budget - 1 else budget) output.2 + rate *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal)) :=
          ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl
            (ih output.1 output.2 _ hremaining (hbound.2 output.1))
        _ = (∑' output, (lazyImpl auxiliary input).run observed output *
              potential (if IsPrefixQuery input then budget - 1 else budget) output.2) +
            rate * ∑' output, (lazyImpl auxiliary input).run observed output *
              ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery (next output.1)) output.2 result * (result.1.2 : ENNReal) := by
          rw [expectation_add, expectation_scale]
        _ ≤ _ := by
          rw [mul_add, ← add_assoc]
          exact _root_.add_le_add (hstep input observed budget hbudget hbound.1) le_rfl
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
noncomputable def contactMomentPotential (remaining : Nat) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  (contactFactorial (contactCount observed endpoint) : ENNReal) +
    (2 * remaining : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal)
theorem contactMomentPotential_observe_le (observed : Fin n → State → Option State) (query : Fin n × State)
    (endpoint : State) (remaining limit : Nat) (hremaining : remaining ≤ limit) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * contactMomentPotential remaining (record observed query answer) endpoint) ≤
      contactMomentPotential (remaining + 1) observed endpoint + (2 * limit : Nat) / (Fintype.card State : ENNReal)^2 := by
  simp only [contactMomentPotential, expectation_add, expectation_scale]
  calc
    _ ≤ ((contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * contactCount observed endpoint : Nat) / (Fintype.card State : ENNReal)) +
        ((2 * remaining : Nat) / (Fintype.card State : ENNReal)) *
          ((contactCount observed endpoint : ENNReal) + 1 / Fintype.card State) :=
      _root_.add_le_add (contactFactorial_observe_le observed query endpoint)
        (mul_le_mul' le_rfl (contactCount_observe_le observed query endpoint))
    _ = (contactFactorial (contactCount observed endpoint) : ENNReal) +
          (2 * (remaining + 1) : Nat) / (Fintype.card State : ENNReal) * (contactCount observed endpoint : ENNReal) +
          (2 * remaining : Nat) / (Fintype.card State : ENNReal)^2 := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv, ENNReal.inv_pow]
      ring
    _ ≤ _ := by
      apply _root_.add_le_add le_rfl
      have h : (2 * remaining : Nat) ≤ 2 * limit := Nat.mul_le_mul_left 2 hremaining
      simpa only [div_eq_mul_inv] using mul_le_mul'
        (show ((2 * remaining : Nat) : ENNReal) ≤ (2 * limit : Nat) by exact_mod_cast h)
        (le_refl ((Fintype.card State : ENNReal)^2)⁻¹)
theorem lazyRun_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (contactCount result.2 endpoint : ENNReal)) ≤
      (contactCount observed endpoint : ENNReal) + (1 / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_potential_le auxiliary (fun current => (contactCount current endpoint : ENNReal)) (1 / Fintype.card State)
  intro input current
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one]
      exact contactCount_observe_le current query endpoint
theorem lazyRun_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (endpoint : State) (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      contactMomentPotential budget observed endpoint + ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * (result.1.2 : ENNReal) := by
  apply lazyRun_budget_potential_le auxiliary (fun remaining current => contactMomentPotential remaining current endpoint)
    (fun current => (contactFactorial (contactCount current endpoint) : ENNReal))
    ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) budget
    (fun _ _ => _root_.le_add_of_nonneg_right bot_le) ?_ computation observed budget le_rfl hbound
  intro input current remaining hremaining hpositive
  cases input with
  | inl input => simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | inr query =>
      have hpos : 0 < remaining := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hpositive
      cases remaining with
      | zero => omega
      | succ remaining =>
          simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true, Nat.cast_one, mul_one, Nat.add_sub_cancel]
          exact contactMomentPotential_observe_le current query endpoint remaining budget (by omega)
theorem lazyRun_empty_contactCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactCount result.2 endpoint : ENNReal)) ≤
      (1 / Fintype.card State) * ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (result.1.2 : ENNReal) := by
  simpa only [contactCount_empty, Nat.cast_zero, zero_add] using lazyRun_contactCount_le auxiliary computation (fun _ _ => none) endpoint
theorem lazyRun_empty_contactFactorial_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
      (contactFactorial (contactCount result.2 endpoint) : ENNReal)) ≤
      ((2 * budget : Nat) / (Fintype.card State : ENNReal)^2) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simpa only [contactMomentPotential, contactCount_empty, contactFactorial, Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add] using
    lazyRun_contactFactorial_le auxiliary computation (fun _ _ => none) endpoint budget hbound
theorem lazyRun_empty_contact_correction (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    ((budget : ENNReal) / Fintype.card State) *
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) ≤
      ((4 * ((budget : ENNReal) / Fintype.card State) + 2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
        ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, expectation_add, expectation_scale]
  have h := mul_le_mul' (le_refl ((budget : ENNReal) / Fintype.card State))
    (_root_.add_le_add (lazyRun_empty_contactFactorial_le auxiliary computation endpoint budget hbound)
      (mul_le_mul' (le_refl (4 : ENNReal)) (lazyRun_empty_contactCount_le auxiliary computation endpoint)))
  apply h.trans_eq
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
private theorem compensation_compose {a b c d e f : ENNReal} (hc : c ≠ ⊤)
    (hstep : a + d ≤ b + c) (htail : c + e ≤ d + f) : a + e ≤ b + f := by
  apply (ENNReal.add_le_add_iff_left hc).mp
  calc
    c + (a + e) = a + (c + e) := by ac_rfl
    _ ≤ a + (d + f) := _root_.add_le_add le_rfl htail
    _ = (a + d) + f := by rw [add_assoc]
    _ ≤ (b + c) + f := _root_.add_le_add hstep le_rfl
    _ = c + (b + f) := by ac_rfl
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_compensation (auxiliary : QueryImpl auxSpec PMF)
    (charge weight : Nat → (Fin n → State → Option State) → ENNReal)
    (hfinite : ∀ input observed spent,
      (∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2) ≠ ⊤)
    (hstep : ∀ input observed spent,
      charge spent observed + (∑' output, (lazyImpl auxiliary input).run observed output *
        weight (spent + if IsPrefixQuery input then 1 else 0) output.2) ≤
      weight spent observed + ∑' output, (lazyImpl auxiliary input).run observed output *
        charge (spent + if IsPrefixQuery input then 1 else 0) output.2)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (spent : Nat) :
    charge spent observed + (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      weight (spent + result.1.2) result.2) ≤
    weight spent observed + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
      charge (spent + result.1.2) result.2 := by
  induction computation using OracleComp.inductionOn generalizing observed spent with
  | pure result =>
      simp only [QueryCap.counted_pure, lazyRun_pure, expectation_pure, Nat.add_zero]
      exact le_of_eq (add_comm _ _)
  | query_bind input next ih =>
      simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
        expectation_bind, expectation_map, ← Nat.add_assoc]
      apply compensation_compose (hfinite input observed spent) (hstep input observed spent)
      have h := ENNReal.tsum_le_tsum fun output => mul_le_mul' (le_refl ((lazyImpl auxiliary input).run observed output))
        (ih output.1 output.2 (spent + if IsPrefixQuery input then 1 else 0))
      simpa only [expectation_add] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section




namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
theorem lazyRun_twoEdge_compensation (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (observed : Fin (n + 2) → State → Option State) (spent : Nat) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result * twoEdgeWeight result.2 endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed result *
        ((twoEdgeCharge (spent + result.1.2) result.2 endpoint : ENNReal) / Fintype.card State) := by
  apply lazyRun_compensation auxiliary (fun used current => (twoEdgeCharge used current endpoint : ENNReal) / Fintype.card State)
    (fun _ current => twoEdgeWeight current endpoint) ?_ ?_ computation observed spent
  · intro input current used
    have hn : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        change (∑' answer : State, rowLaw (current query.1 query.2) answer *
          ((twoEdgeCharge (used + 1) (record current query answer) endpoint : ENNReal) / Fintype.card State)) ≠ ⊤
        rw [tsum_fintype]
        apply ENNReal.sum_ne_top.mpr
        intro answer _
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (by norm_num : (1 : ENNReal) ≠ ⊤) (PMF.coe_le_one _ _))
          (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hn)
  · intro input current used
    cases input with
    | inl input =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, expectation_const, IsPrefixQuery, if_false, Nat.add_zero]
        exact le_of_eq (add_comm _ _)
    | inr query =>
        simp only [lazyImpl, StateT.run_mk, expectation_map, IsPrefixQuery, if_true]
        exact twoEdge_observe_compensation used current query endpoint
omit [Nonempty State] in
theorem twoEdgeCharge_div_le (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ spent) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ((3 / 2 : ENNReal) / Fintype.card State) * (spent : ENNReal) +
        ((budget : ENNReal) / Fintype.card State) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
  have hdouble : 2 * (twoEdgeCharge spent observed endpoint : ENNReal) ≤ 3 * (spent : ENNReal) +
      2 * (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    exact_mod_cast (twoEdgeCharge_twice_le spent budget observed endpoint hs (hq.trans hs)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hq) _)
  have hcast : (twoEdgeCharge spent observed endpoint : ENNReal) ≤ (3 / 2 : ENNReal) * (spent : ENNReal) +
      (budget : ENNReal) * ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left (c := 2) (by norm_num) (by norm_num)).mp
    have ht : (3 / 2 : ENNReal) * 2 = 3 := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    calc
      _ = 2 * (twoEdgeCharge spent observed endpoint : ENNReal) := mul_comm _ _
      _ ≤ _ := hdouble
      _ = (3 / 2 * 2) * (spent : ENNReal) + 2 * (budget : ENNReal) *
          ((contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint : Nat) : ENNReal) := by rw [ht]
      _ = _ := by ring
  have h := mul_le_mul' hcast (le_refl (Fintype.card State : ENNReal)⁻¹)
  simpa only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using h
theorem lazyRun_empty_twoEdge_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec (n + 2) State) Result) (endpoint : State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget) :
    (∑' result, lazyRun auxiliary computation (fun _ _ => none) result * twoEdgeWeight result.2 endpoint) ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal) := by
  rw [lazyRun_counted_expectation]
  have hc := lazyRun_twoEdge_compensation auxiliary computation (fun _ _ => none) 0 endpoint
  simp only [twoEdgeCharge_empty, Nat.cast_zero, div_eq_mul_inv, zero_mul, twoEdgeWeight_empty, zero_add] at hc
  apply hc.trans
  calc
    _ ≤ ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result *
        (((3 / 2 : ENNReal) / Fintype.card State) * (result.1.2 : ENNReal) +
          ((budget : ENNReal) / Fintype.card State) *
            ((contactFactorial (contactCount result.2 endpoint) + 4 * contactCount result.2 endpoint : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none)).support
      · apply mul_le_mul' le_rfl
        have hq := lazyRun_counted_queryCount_le auxiliary computation (fun _ _ => none) result hr
        simp only [queryCount_empty, Nat.zero_add] at hq
        exact twoEdgeCharge_div_le result.1.2 budget result.2 endpoint (lazyRun_counted_budget_le auxiliary computation _ budget hbound result hr) hq
      · have hz : lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by rw [expectation_add, expectation_scale, expectation_scale]
    _ ≤ _ := by
      have h := _root_.add_le_add
        (le_refl (((3 / 2 : ENNReal) / Fintype.card State) *
          ∑' result, lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) (fun _ _ => none) result * (result.1.2 : ENNReal)))
        (lazyRun_empty_contact_correction auxiliary computation endpoint budget hbound)
      apply h.trans_eq
      simp only [div_eq_mul_inv]
      ring
theorem realRun_twoEdge_le (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
    (budget : Nat) (hbound : ∀ endpoint, (computation endpoint).IsQueryBoundP IsPrefixQuery budget) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint))
            (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  rw [show Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] =
      (∑' result, realRun auxiliary computation (fun _ _ => none) result * (if TwoEdge result.2.2 result.1 then 1 else 0)) by
        simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realRun_expectation]
  simp only [idealRun, expectation_bind, expectation_map]
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro endpoint
  apply mul_le_mul' le_rfl
  exact lazyRun_empty_twoEdge_le (auxiliary endpoint) (computation endpoint) endpoint budget (hbound endpoint)
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec (n + 2) State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
include hcharge hreal
theorem realRun_cap_twoEdge_eq :
    Pr[fun result => TwoEdge result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin (n + 2) → State → Option State))) =>
    Pr[fun result => TwoEdge result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h
theorem realRun_twoEdge_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdge result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_twoEdge_eq auxiliary computation cost budget hcharge hreal]
  have h := realRun_twoEdge_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
    budget (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget)
  rw [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h
  exact h
omit hcharge hreal in
def TwoEdgeEvent : {depth : Nat} → (Fin depth → State → Option State) → State → Prop
  | 0, _, _ => False
  | 1, _, _ => False
  | _ + 2, observed, endpoint => TwoEdge observed endpoint
omit hcharge hreal in
theorem realRun_twoEdgeEvent_le_cap_cost {depth : Nat} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec depth State) Result)
    (cost : Result → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
      result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < Fintype.card State) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / Fintype.card State) +
        2 * ((budget : ENNReal) / Fintype.card State)^2) / Fintype.card State) *
          ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
            (fun _ _ => none) result * (QueryCap.spent budget result.2.1 : ENNReal) := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
  | succ depth =>
      cases depth with
      | zero => simp only [TwoEdgeEvent, probEvent_eq_tsum_ite, if_false, tsum_zero]; exact bot_le
      | succ depth => exact realRun_twoEdge_le_cap_cost auxiliary computation cost budget hcharge hreal hsmall
end SphincsSecurity.Concrete.PartialChainEndpoint
end
