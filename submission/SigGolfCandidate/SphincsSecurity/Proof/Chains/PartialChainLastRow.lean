import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainLikelihood
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainQueryBound

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
def knownRun : {n : Nat} → (Fin n → State → Option State) → State → Option State
  | 0, _, start => some start
  | _ + 1, observed, start => (observed 0 start).bind (knownRun (Fin.tail observed))
noncomputable def knownCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Nat :=
  ∑ start : State, if knownRun observed start = some endpoint then 1 else 0
noncomputable def knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) : ENNReal :=
  ∑' start, prior start * if knownRun observed start = some endpoint then 1 else 0
noncomputable def properSuffixCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount (Fin.tail observed) endpoint + properSuffixCount (Fin.tail observed) endpoint
omit [Nonempty State] in
theorem knownCount_empty (observed : Fin 0 → State → Option State) (endpoint : State) : knownCount observed endpoint = 1 := by
  simp [knownCount, knownRun]
omit [Nonempty State] in
theorem knownMass_empty (prior : PMF State) (observed : Fin 0 → State → Option State) (endpoint : State) :
    knownMass prior observed endpoint = prior endpoint := by
  simp [knownMass, knownRun]
omit [Fintype State] [Nonempty State] in
theorem knownMass_pure {n : Nat} (value : State) (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.pure value) observed endpoint = if knownRun observed value = some endpoint then 1 else 0 := by
  simpa only [knownMass, PMF.probOutput_eq_apply, PMF.monad_pure_eq_pure] using
    (tsum_probOutput_pure_mul (m := PMF) value (fun start => if knownRun observed start = some endpoint then 1 else 0))
theorem knownMass_uniform {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownMass (PMF.uniformOfFintype State) observed endpoint =
      (knownCount observed endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, tsum_fintype, knownCount, Nat.cast_sum]
  simp only [PMF.uniformOfFintype_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.mul_sum, mul_comm]
theorem advance_knownMass_le {n : Nat} (prior : PMF State) (observed : Fin (n + 1) → State → Option State) (endpoint : State) :
    knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint ≤
      knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
  rw [knownMass, expectation_bind]
  calc
    _ ≤ ∑' input, prior input *
        ((if knownRun observed input = some endpoint then 1 else 0) +
          (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) := by
      apply ENNReal.tsum_le_tsum
      intro input
      apply mul_le_mul' le_rfl
      change knownMass (rowLaw (observed 0 input)) (Fin.tail observed) endpoint ≤ _
      cases hrow : observed 0 input with
      | none => simp only [rowLaw, knownMass_uniform, knownRun, hrow, Option.bind_none, reduceCtorEq, if_false, zero_add, le_refl]
      | some value =>
          simp only [rowLaw, knownMass_pure, knownRun, hrow, Option.bind_some]
          exact _root_.le_add_of_nonneg_right bot_le
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, knownMass]
theorem kernel_le_knownMass {n : Nat} (prior : PMF State) (observed : Fin n → State → Option State) (endpoint : State) :
    prior.bind (kernel observed) endpoint ≤
      knownMass prior observed endpoint + (properSuffixCount observed endpoint : ENNReal) / Fintype.card State := by
  induction n generalizing prior with
  | zero => simp [kernel, knownMass_empty, properSuffixCount]
  | succ n ih =>
      have h := ih (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed)
      have hstep := advance_knownMass_le prior observed endpoint
      calc
        _ ≤ knownMass (prior.bind (fun input => rowLaw (observed 0 input))) (Fin.tail observed) endpoint +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := by
          simpa only [kernel, PMF.bind_bind] using h
        _ ≤ (knownMass prior observed endpoint + (knownCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State) +
            (properSuffixCount (Fin.tail observed) endpoint : ENNReal) / Fintype.card State := _root_.add_le_add hstep le_rfl
        _ = _ := by rw [properSuffixCount, Nat.cast_add, ENNReal.add_div, add_assoc]
theorem meanPreimages_le_suffixCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    meanPreimages observed endpoint ≤ (knownCount observed endpoint + properSuffixCount observed endpoint : Nat) := by
  rw [meanPreimages_eq]
  have h := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) (kernel_le_knownMass (PMF.uniformOfFintype State) observed endpoint)
  have hcard : (Fintype.card State : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [knownMass_uniform, Nat.cast_add, div_eq_mul_inv, mul_add, mul_left_comm (Fintype.card State : ENNReal),
    ENNReal.mul_inv_cancel hcard (by finiteness), mul_one] using h
def Contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) : Prop :=
  ∃ step : Fin n, step.val + 1 = n ∧ ∃ input, observed step input = some endpoint
omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem contact_tail {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : Contact (Fin.tail observed) endpoint) : Contact observed endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := h
  exact ⟨step.succ, by simpa only [Fin.val_succ] using congrArg Nat.succ hstep, input, hinput⟩
omit [Fintype State] [DecidableEq State] [Nonempty State] in
theorem knownRun_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : Contact observed endpoint := by
  induction n generalizing start with
  | zero =>
      have hrow : observed 0 start = some endpoint := by
        cases hstart : observed 0 start <;> simpa only [knownRun, hstart, Option.bind_none, Option.bind_some] using h
      exact ⟨0, rfl, start, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨value, _, hvalue⟩ := h
      exact contact_tail observed endpoint (ih (Fin.tail observed) value hvalue)
omit [Nonempty State] in
theorem knownCount_eq_zero_of_no_contact {n : Nat} (observed : Fin (n + 1) → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_contact observed start endpoint hrun))
omit [Nonempty State] in
theorem suffixCount_le_one_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : knownCount observed endpoint + properSuffixCount observed endpoint ≤ 1 := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, Nat.add_zero, le_refl]
  | succ n ih =>
      rw [knownCount_eq_zero_of_no_contact observed endpoint h, properSuffixCount, Nat.zero_add]
      exact ih (Fin.tail observed) (fun htail => h (contact_tail observed endpoint htail))
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
def Extends {n : Nat} (before after : Fin n → State → Option State) : Prop :=
  ∀ step input answer, before step input = some answer → after step input = some answer
omit [Fintype State] [DecidableEq State] in
theorem Extends.tail {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.tail before) (Fin.tail after) := fun step input answer => h step.succ input answer
omit [Fintype State] [DecidableEq State] in
theorem knownRun_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (start endpoint : State) (hknown : knownRun before start = some endpoint) : knownRun after start = some endpoint := by
  induction n generalizing start with
  | zero => exact hknown
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at hknown ⊢
      obtain ⟨value, hvalue, hknown⟩ := hknown
      exact ⟨value, h 0 start value hvalue, ih h.tail value hknown⟩
theorem knownCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    knownCount before endpoint ≤ knownCount after endpoint := by
  apply Finset.sum_le_sum
  intro start _
  by_cases hknown : knownRun before start = some endpoint
  · simp only [if_pos hknown, if_pos (knownRun_mono h start endpoint hknown), le_refl]
  · simp only [if_neg hknown, Nat.zero_le]
noncomputable def targetCount : {n : Nat} → (Fin n → State → Option State) → State → Nat
  | 0, _, _ => 0
  | _ + 1, observed, endpoint => knownCount observed endpoint + targetCount (Fin.tail observed) endpoint
noncomputable def completedCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  ∑ endpoint : State, targetCount observed endpoint
noncomputable def pendingCount {n : Nat} (observed : Fin n → State → Option State) : Nat :=
  queryCount observed - completedCount observed
theorem suffixCount_eq_targetCount {n : Nat} (observed : Fin n → State → Option State) (endpoint : State) :
    knownCount observed endpoint + properSuffixCount observed endpoint = 1 + targetCount observed endpoint := by
  induction n with
  | zero => simp only [knownCount_empty, properSuffixCount, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [properSuffixCount, targetCount, ih]
      omega
theorem targetCount_eq_zero_of_no_contact {n : Nat} (observed : Fin n → State → Option State) (endpoint : State)
    (h : ¬Contact observed endpoint) : targetCount observed endpoint = 0 := by
  have hbound := suffixCount_le_one_of_no_contact observed endpoint h
  rw [suffixCount_eq_targetCount] at hbound
  omega
theorem targetCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) (endpoint : State) :
    targetCount before endpoint ≤ targetCount after endpoint := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact Nat.add_le_add (knownCount_mono h endpoint) (ih h.tail)
theorem completedCount_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    completedCount before ≤ completedCount after :=
  Finset.sum_le_sum fun endpoint _ => targetCount_mono h endpoint
omit [DecidableEq State] in
theorem queriedCount_eq_sum (observed : State → Option State) :
    queriedCount observed = ∑ input : State, if observed input = none then 0 else 1 := by
  rw [queriedCount, unqueried, Finset.card_filter]
  have hsplit : (∑ input : State, if observed input = none then 1 else 0) +
      (∑ input : State, if observed input = none then 0 else 1) = Fintype.card State := by
    rw [← Finset.sum_add_distrib]
    simp only [ite_add_ite, Nat.add_zero, Nat.zero_add, ite_self, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega
theorem knownCount_sum {n : Nat} (observed : Fin n → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = ∑ start : State, if (knownRun observed start).isSome then 1 else 0 := by
  simp only [knownCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro start _
  cases knownRun observed start <;> simp
theorem knownCount_sum_le_queried {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) ≤ queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro start _
  cases hrow : observed 0 start with
  | none => simp [knownRun, hrow]
  | some value =>
      simp only [reduceCtorEq, if_false]
      split <;> omega
theorem completedCount_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    completedCount observed ≤ queryCount observed := by
  induction n with
  | zero => simp [completedCount, targetCount, queryCount]
  | succ n ih =>
      simp only [completedCount, targetCount, Finset.sum_add_distrib, queryCount, Fin.sum_univ_succ]
      exact Nat.add_le_add (knownCount_sum_le_queried observed) (ih (Fin.tail observed))
theorem pendingCount_partition {n : Nat} (observed : Fin n → State → Option State) :
    pendingCount observed + completedCount observed = queryCount observed :=
  Nat.sub_add_cancel (completedCount_le_queryCount observed)
omit [Fintype State] in
theorem record_extends {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    Extends observed (record observed query answer) := by
  intro step input old hold
  by_cases hstep : step = query.1
  · subst step
    by_cases hinput : input = query.2
    · subst input
      have heq : old = answer := by rcases hconsistent with h | h <;> simp_all
      simp [record, heq]
    · simpa only [record, Function.update_self, Function.update_of_ne hinput] using hold
  · simpa only [record, Function.update_of_ne hstep] using hold
theorem pendingCount_record_le {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    pendingCount (record observed query answer) ≤ pendingCount observed + 1 := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_mono (record_extends observed query answer hconsistent)
  omega
theorem completedCount_add_target_le {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hcontact : ¬Contact before endpoint) :
    completedCount before + targetCount after endpoint ≤ completedCount after := by
  have hzero := targetCount_eq_zero_of_no_contact before endpoint hcontact
  have hrest := Finset.sum_le_sum (s := Finset.univ.erase endpoint) fun other _ => targetCount_mono h other
  rw [completedCount, completedCount,
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount before other) (Finset.mem_univ endpoint),
    ← Finset.add_sum_erase Finset.univ (fun other => targetCount after other) (Finset.mem_univ endpoint), hzero]
  omega
theorem first_contact_density_charge [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (answer endpoint : State) (hcontact : ¬Contact observed endpoint)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    meanPreimages (record observed query answer) endpoint + (pendingCount (record observed query answer) : ENNReal) ≤
      (pendingCount observed + 2 : Nat) := by
  have hbefore := pendingCount_partition observed
  have hafter := pendingCount_partition (record observed query answer)
  have htotal := queryCount_record_le observed query answer
  have hdone := completedCount_add_target_le (record_extends observed query answer hconsistent) endpoint hcontact
  have hcount : 1 + targetCount (record observed query answer) endpoint + pendingCount (record observed query answer) ≤
      pendingCount observed + 2 := by omega
  have hdensity := meanPreimages_le_suffixCount (record observed query answer) endpoint
  rw [suffixCount_eq_targetCount] at hdensity
  exact (_root_.add_le_add hdensity le_rfl).trans (by exact_mod_cast hcount)
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
omit [Fintype State] [DecidableEq State] in
theorem knownRun_isSome_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome)
    (start : State) : (knownRun before start).isSome = (knownRun after start).isSome := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero =>
          simpa [knownRun] using hlast 0 start rfl
      | succ n =>
          have hhead := hearly 0 start (by simp)
          have htail := ih (Fin.tail before) (Fin.tail after)
            (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
            (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))
          simp only [knownRun, hhead]
          cases after 0 start with
          | none => rfl
          | some value => exact htail value
theorem completedCount_eq_of_last {n : Nat} (before after : Fin n → State → Option State)
    (hearly : ∀ step input, step.val + 1 ≠ n → before step input = after step input)
    (hlast : ∀ step input, step.val + 1 = n → (before step input).isSome = (after step input).isSome) :
    completedCount before = completedCount after := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (∑ endpoint : State, (knownCount before endpoint + targetCount (Fin.tail before) endpoint)) =
        ∑ endpoint : State, (knownCount after endpoint + targetCount (Fin.tail after) endpoint)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, knownCount_sum, knownCount_sum]
      congr 1
      · exact Finset.sum_congr rfl fun start _ => congrArg (fun b : Bool => if b then 1 else 0)
          (knownRun_isSome_eq_of_last before after hearly hlast start)
      · exact ih (Fin.tail before) (Fin.tail after)
          (fun step input h => hearly step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ_ne_succ_iff] using h))
          (fun step input h => hlast step.succ input (by simpa only [Fin.val_succ, Nat.succ_add, Nat.succ.injEq] using h))
omit [Fintype State] in
theorem record_isSome_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) (step : Fin n) (input : State) :
    (record observed query first step input).isSome = (record observed query second step input).isSome := by
  by_cases hs : step = query.1
  · subst step
    by_cases hi : input = query.2
    · subst input; simp [record]
    · simp only [record, Function.update_self, Function.update_of_ne hi]
  · simp only [record, Function.update_of_ne hs]
theorem queryCount_record_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (first second : State) : queryCount (record observed query first) = queryCount (record observed query second) := by
  unfold queryCount
  apply Finset.sum_congr rfl
  intro step _
  rw [queriedCount_eq_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  have h := record_isSome_eq observed query first second step input
  cases hfirst : record observed query first step input <;> cases hsecond : record observed query second step input <;> simp_all
theorem pendingCount_record_last_answer_eq {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (hlast : query.1.val + 1 = n) (first second : State) :
    pendingCount (record observed query first) = pendingCount (record observed query second) := by
  unfold pendingCount
  rw [queryCount_record_answer_eq observed query first second]
  congr 1
  apply completedCount_eq_of_last
  · intro step input hearly
    have hs : step ≠ query.1 := fun h => hearly (by simpa only [h] using hlast)
    simp only [record, Function.update_of_ne hs]
  · intro step input _
    exact record_isSome_eq observed query first second step input
omit [Fintype State] [DecidableEq State] in
theorem contact_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after)
    (endpoint : State) (hc : Contact before endpoint) : Contact after endpoint := by
  obtain ⟨step, hstep, input, hinput⟩ := hc
  exact ⟨step, hstep, input, h step input endpoint hinput⟩
omit [Fintype State] in
theorem contact_record_iff {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer endpoint : State) (hc : ¬Contact observed endpoint) :
    Contact (record observed query answer) endpoint ↔ query.1.val + 1 = n ∧ answer = endpoint := by
  constructor
  · rintro ⟨step, hstep, input, hinput⟩
    by_cases hs : step = query.1
    · subst step
      by_cases hi : input = query.2
      · subst input
        exact ⟨hstep, by simpa only [record, Function.update_self, Option.some.injEq] using hinput⟩
      · exact False.elim (hc ⟨query.1, hstep, input, by simpa only [record, Function.update_self, Function.update_of_ne hi] using hinput⟩)
    · exact False.elim (hc ⟨step, hstep, input, by simpa only [record, Function.update_of_ne hs] using hinput⟩)
  · rintro ⟨hlast, rfl⟩
    exact ⟨query.1, hlast, query.2, by simp only [record, Function.update_self]⟩
omit [Fintype State] in
theorem record_of_known {n : Nat} (observed : Fin n → State → Option State) (query : Fin n × State)
    (answer : State) (h : observed query.1 query.2 = some answer) : record observed query answer = observed := by
  simp only [record, ← h, Function.update_eq_self]
theorem meanPreimages_observe [Nonempty State] {n : Nat} (observed : Fin n → State → Option State)
    (query : Fin n × State) (endpoint : State) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * meanPreimages (record observed query answer) endpoint) =
      meanPreimages observed endpoint := by
  simp only [meanPreimages, ← ENNReal.tsum_mul_left, ← mul_assoc, completeTables_observe_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp
end SphincsSecurity.Concrete.PartialChainEndpoint
end
