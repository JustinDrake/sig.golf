import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily

section

namespace SphincsSecurity.Concrete.EndpointPreimageDensity
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Table State : Type} [Fintype State] [Nonempty State] [DecidableEq State] [DecidableEq Table]
noncomputable def preimages (evaluate : Table → State → State) (table : Table) (endpoint : State) : Nat :=
  (Finset.univ.filter (fun secret => evaluate table secret = endpoint)).card
noncomputable def real (prior : PMF Table) (evaluate : Table → State → State) : PMF (Table × State) :=
  prior.bind (fun table => ((PMF.uniformOfFintype State).map (evaluate table)).map (fun endpoint => (table, endpoint)))
noncomputable def ideal (prior : PMF Table) : PMF (Table × State) :=
  prior.bind (fun table => (PMF.uniformOfFintype State).map (fun endpoint => (table, endpoint)))
theorem uniform_image_apply (evaluate : State → State) (endpoint : State) :
    (PMF.uniformOfFintype State).map evaluate endpoint =
      ((Finset.univ.filter (fun secret => evaluate secret = endpoint)).card : ENNReal) / Fintype.card State := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, eq_comm, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem map_pair_apply (law : PMF State) (table target : Table) (endpoint : State) :
    law.map (fun value => (table, value)) (target, endpoint) = if table = target then law endpoint else 0 := by
  rw [PMF.map_apply]
  by_cases htable : table = target
  · subst target
    rw [if_pos rfl, tsum_eq_single endpoint]
    · rw [if_pos rfl]
    · intro value hvalue
      exact if_neg (fun h => hvalue (congrArg Prod.snd h).symm)
  · rw [if_neg htable]
    apply ENNReal.tsum_eq_zero.mpr
    intro value
    exact if_neg (fun h => htable (congrArg Prod.fst h).symm)
omit [Fintype State] [Nonempty State] [DecidableEq State] in
theorem bind_pair_apply (prior : PMF Table) (law : Table → PMF State) (table : Table) (endpoint : State) :
    prior.bind (fun selected => (law selected).map (fun value => (selected, value))) (table, endpoint) =
      prior table * law table endpoint := by
  rw [PMF.bind_apply]
  simp only [map_pair_apply, mul_ite, mul_zero]
  rw [tsum_eq_single table]
  · simp only [if_true]
  · intro selected hselected
    exact if_neg hselected
theorem real_apply (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State) := by
  rw [real, bind_pair_apply, uniform_image_apply]
  rfl
omit [DecidableEq State] in
theorem ideal_apply (prior : PMF Table) (table : Table) (endpoint : State) :
    ideal prior (table, endpoint) = prior table / Fintype.card State := by
  rw [ideal, bind_pair_apply, PMF.uniformOfFintype_apply, div_eq_mul_inv]
theorem real_density (prior : PMF Table) (evaluate : Table → State → State) (table : Table) (endpoint : State) :
    real prior evaluate (table, endpoint) = (preimages evaluate table endpoint : ENNReal) * ideal prior (table, endpoint) := by
  rw [real_apply, ideal_apply]
  simp only [div_eq_mul_inv]
  ring
theorem real_payoff (prior : PMF Table) (evaluate : Table → State → State) (payoff : Table × State → ENNReal) :
    (∑' result, real prior evaluate result * payoff result) =
      ∑' result : Table × State, ideal prior result * (preimages evaluate result.1 result.2 : ENNReal) * payoff result := by
  apply tsum_congr
  rintro ⟨table, endpoint⟩
  rw [real_density]
  ring
omit [DecidableEq Table] in
theorem mean_preimages (prior : PMF Table) (evaluate : Table → State → State) (endpoint : State) :
    (∑' table, prior table * (preimages evaluate table endpoint : ENNReal)) =
      (Fintype.card State : ENNReal) *
        prior.bind (fun table => (PMF.uniformOfFintype State).map (evaluate table)) endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro table
  rw [uniform_image_apply]
  change prior table * (preimages evaluate table endpoint : ENNReal) =
    (Fintype.card State : ENNReal) * (prior table * ((preimages evaluate table endpoint : ENNReal) / Fintype.card State))
  rw [div_eq_mul_inv]
  calc
    _ = ((Fintype.card State : ENNReal) * (Fintype.card State : ENNReal)⁻¹) *
        (prior table * (preimages evaluate table endpoint : ENNReal)) := by
      rw [ENNReal.mul_inv_cancel hcard (by finiteness), one_mul]
    _ = _ := by ring
end SphincsSecurity.Concrete.EndpointPreimageDensity
end

section


namespace SphincsSecurity.Concrete.FinitePmfProduct
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]
theorem marginal (family : Index → PMF Value) (index : Index) :
    (law family).map (fun values => values index) = family index := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro value
  have hfactor (values : Index → Value) :
      (if value = values index then law family values else 0) =
        ∏ other, if other = index then
          (if value = values other then family other (values other) else 0) else family other (values other) := by
    by_cases hvalue : value = values index
    · rw [if_pos hvalue, apply]
      apply Finset.prod_congr rfl
      intro other _
      by_cases hother : other = index
      · subst other
        simp only [if_true, hvalue]
      · simp only [hother, if_false]
    · rw [if_neg hvalue]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp only [if_true, hvalue, if_false])
  rw [PMF.map_apply, tsum_fintype]
  trans ∑ values : Index → Value, ∏ other, if other = index then
    (if value = values other then family other (values other) else 0) else family other (values other)
  · exact Finset.sum_congr rfl (fun values _ => hfactor values)
  rw [← Fintype.prod_sum (fun other (candidate : Value) =>
    if other = index then (if value = candidate then family other candidate else 0) else family other candidate),
    Finset.prod_eq_single index]
  · simp only [if_true]
    simp
  · intro other _ hother
    simp only [hother, if_false]
    simpa only [tsum_fintype] using PMF.tsum_coe (family other)
  · simp
theorem fin_succ {n : Nat} (family : Fin (n + 1) → PMF Value) :
    law family = (family 0).bind (fun first => (law (fun index : Fin n => family index.succ)).map (Fin.cons first)) := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro values
  have hmap (first : Value) :
      (law (fun index : Fin n => family index.succ)).map (Fin.cons first) values =
        if first = values 0 then law (fun index : Fin n => family index.succ) (Fin.tail values) else 0 := by
    rw [PMF.map_apply]
    by_cases hfirst : first = values 0
    · rw [if_pos hfirst, tsum_eq_single (Fin.tail values)]
      · rw [hfirst, Fin.cons_self_tail, if_pos rfl]
      · intro tail htail
        exact if_neg (fun h => htail (by simpa using (congrArg Fin.tail h).symm))
    · rw [if_neg hfirst]
      apply ENNReal.tsum_eq_zero.mpr
      intro tail
      exact if_neg (fun h => hfirst (by simpa using (congrFun h 0).symm))
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single (values 0)]
  · simp only [if_true, apply, Fin.prod_univ_succ, Fin.tail]
  · intro value hvalue
    exact if_neg hvalue
theorem update_apply (family : Index → PMF Value) (index : Index) (replacement : PMF Value)
    (values : Index → Value) :
    law (Function.update family index replacement) values =
      replacement (values index) * ∏ other ∈ Finset.univ.erase index, family other (values other) := by
  rw [apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => Function.update family index replacement other (values other)) (Finset.mem_univ index)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
theorem observe_mass [DecidableEq Value] (family : Index → PMF Value) (index : Index) (value : Value) (values : Index → Value) :
    family index value * law (Function.update family index (PMF.pure value)) values =
      if values index = value then law family values else 0 := by
  classical
  rw [update_apply, apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => family other (values other)) (Finset.mem_univ index)]
  by_cases hvalue : values index = value
  · simp only [hvalue, PMF.pure_apply_self, one_mul, if_true]
  · simp only [PMF.pure_apply, if_false, zero_mul, mul_zero, hvalue]
end SphincsSecurity.Concrete.FinitePmfProduct
end

section



namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def rowLaw : Option State → PMF State
  | none => PMF.uniformOfFintype State
  | some value => PMF.pure value
noncomputable def completeFunction (observed : State → Option State) : PMF (State → State) :=
  FinitePmfProduct.law (fun input => rowLaw (observed input))
theorem completeFunction_marginal (observed : State → Option State) (input : State) :
    (completeFunction observed).map (fun table => table input) = rowLaw (observed input) :=
  FinitePmfProduct.marginal _ input
def evaluate : {n : Nat} → (Fin n → State → State) → State → State
  | 0, _, start => start
  | _ + 1, tables, start => evaluate (Fin.tail tables) (tables 0 start)
noncomputable def completeTables {n : Nat} (observed : Fin n → State → Option State) :
    PMF (Fin n → State → State) := FinitePmfProduct.law (fun step => completeFunction (observed step))
noncomputable def kernel : {n : Nat} → (Fin n → State → Option State) → State → PMF State
  | 0, _, start => PMF.pure start
  | _ + 1, observed, start => (rowLaw (observed 0 start)).bind (kernel (Fin.tail observed))
theorem completeTables_evaluate {n : Nat} (observed : Fin n → State → Option State) (start : State) :
    (completeTables observed).map (fun tables => evaluate tables start) = kernel observed start := by
  induction n generalizing start with
  | zero => exact PMF.map_const _ _
  | succ n ih =>
      rw [completeTables, FinitePmfProduct.fin_succ, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def, evaluate, Fin.tail_cons, Fin.cons_zero]
      change (completeFunction (observed 0)).bind (fun first =>
        (completeTables (Fin.tail observed)).map (fun tables => evaluate tables (first start))) = _
      simp_rw [ih]
      calc
        _ = ((completeFunction (observed 0)).map (fun first => first start)).bind (kernel (Fin.tail observed)) :=
          (PMF.bind_map _ _ _).symm
        _ = _ := by rw [completeFunction_marginal, kernel]
theorem uniform_endpoint {n : Nat} (observed : Fin n → State → Option State) :
    (completeTables observed).bind (fun tables => (PMF.uniformOfFintype State).map (evaluate tables)) =
      (PMF.uniformOfFintype State).bind (kernel observed) := by
  change (completeTables observed).bind (fun tables =>
    (PMF.uniformOfFintype State).bind (fun start => PMF.pure (evaluate tables start))) = _
  rw [PMF.bind_comm]
  change (PMF.uniformOfFintype State).bind
    (fun start => (completeTables observed).map (fun tables => evaluate tables start)) = _
  simp only [completeTables_evaluate]
noncomputable def meanPreimages {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' tables, completeTables observed tables * (EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal)
theorem meanPreimages_eq {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint =
      (Fintype.card State : ENNReal) * ((PMF.uniformOfFintype State).bind (kernel observed)) endpoint := by
  rw [meanPreimages, EndpointPreimageDensity.mean_preimages, uniform_endpoint]
noncomputable def unqueried (observed : State → Option State) : Finset State :=
  Finset.univ.filter (fun input => observed input = none)
noncomputable def freeFraction (observed : State → Option State) : ENNReal :=
  (unqueried observed).card / (Fintype.card State : ENNReal)
omit [DecidableEq State] in
theorem advance_lower (observed : State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * freeFraction observed ≤ prior.bind (fun input => rowLaw (observed input)) endpoint := by
  rw [PMF.bind_apply, tsum_fintype]
  calc
    _ = ∑ input ∈ unqueried observed, bound * (Fintype.card State : ENNReal)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul, freeFraction, div_eq_mul_inv]
      ring
    _ ≤ ∑ input ∈ unqueried observed, prior input * rowLaw (observed input) endpoint := by
      apply Finset.sum_le_sum
      intro input hinput
      have hnone : observed input = none := (Finset.mem_filter.mp hinput).2
      rw [hnone, rowLaw, PMF.uniformOfFintype_apply]
      exact mul_le_mul_left (hlower input) _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)
omit [DecidableEq State] in
theorem kernel_lower {n : Nat} (observed : Fin n → State → Option State) (prior : PMF State) (bound : ENNReal)
    (hlower : ∀ input, bound ≤ prior input) (endpoint : State) :
    bound * (∏ step, freeFraction (observed step)) ≤ prior.bind (kernel observed) endpoint := by
  induction n generalizing prior bound with
  | zero => simpa only [Fin.prod_univ_zero, mul_one, kernel, PMF.bind_pure] using hlower endpoint
  | succ n ih =>
      rw [Fin.prod_univ_succ, ← mul_assoc]
      have h := ih (Fin.tail observed) (prior.bind (fun input => rowLaw (observed 0 input)))
        (bound * freeFraction (observed 0)) (advance_lower (observed 0) prior bound hlower)
      simpa only [PMF.bind_bind, kernel, Fin.tail] using h
theorem meanPreimages_ge_product {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    (∏ step, freeFraction (observed step)) ≤ meanPreimages observed endpoint := by
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [meanPreimages_eq]
  have h := mul_le_mul_right (kernel_lower observed (PMF.uniformOfFintype State) (Fintype.card State : ENNReal)⁻¹
    (fun input => by rw [PMF.uniformOfFintype_apply]) endpoint) (Fintype.card State : ENNReal)
  simpa only [← mul_assoc, ENNReal.mul_inv_cancel hcard (by finiteness), one_mul] using h
end SphincsSecurity.Concrete.PartialChainEndpoint
end
