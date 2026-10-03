import SigGolfCandidate.SphincsSecurity.Proof.Chains.PartialChainContactCount

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
def TwoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Prop :=
  ∃ start middle, observed (Fin.last n).castSucc start = some middle ∧ observed (Fin.last (n + 1)) middle = some endpoint
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (hextends : Extends before after)
    (endpoint : State) (h : TwoEdge before endpoint) : TwoEdge after endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  exact ⟨start, middle, hextends _ _ _ hfirst, hextends _ _ _ hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem twoEdge_tail {n : Nat} (observed : Fin (n + 3) → State → Option State) (endpoint : State)
    (h : TwoEdge (Fin.tail observed) endpoint) : TwoEdge observed endpoint := by
  obtain ⟨start, middle, hfirst, hlast⟩ := h
  have hindex : (Fin.last n).castSucc.succ = (Fin.last (n + 1)).castSucc := by apply Fin.ext; rfl
  exact ⟨start, middle, by simpa only [Fin.tail, hindex] using hfirst, by simpa only [Fin.tail, Fin.succ_last] using hlast⟩
omit [Fintype State] [DecidableEq State] in
theorem knownRun_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (start endpoint : State)
    (h : knownRun observed start = some endpoint) : TwoEdge observed endpoint := by
  induction n generalizing start with
  | zero =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hfirst, hlast⟩ := h
      change (observed 1 middle).bind (fun value => some value) = some endpoint at hlast
      have hrow : observed 1 middle = some endpoint := by
        cases hrow : observed 1 middle <;> simpa only [hrow, Option.bind_none, Option.bind_some] using hlast
      exact ⟨start, middle, hfirst, hrow⟩
  | succ n ih =>
      rw [knownRun, Option.bind_eq_some_iff] at h
      obtain ⟨middle, _, htail⟩ := h
      exact twoEdge_tail observed endpoint (ih (Fin.tail observed) middle htail)
theorem knownCount_eq_zero_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : knownCount observed endpoint = 0 := by
  unfold knownCount
  apply Finset.sum_eq_zero
  intro start _
  exact if_neg (fun hrun => h (knownRun_twoEdge observed start endpoint hrun))
theorem targetCount_eq_contactCount_of_no_twoEdge {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State)
    (h : ¬TwoEdge observed endpoint) : targetCount observed endpoint = contactCount observed endpoint := by
  induction n with
  | zero =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add, targetCount, targetCount, Nat.add_zero,
        ← contactCount_single, contactCount_tail]
  | succ n ih =>
      rw [targetCount, knownCount_eq_zero_of_no_twoEdge observed endpoint h, Nat.zero_add,
        ih (Fin.tail observed) (fun htail => h (twoEdge_tail observed endpoint htail)), contactCount_tail]
theorem meanPreimages_le_contactCount_of_no_twoEdge [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages observed endpoint ≤ (1 + contactCount observed endpoint : Nat) := by
  have hbound := meanPreimages_le_suffixCount observed endpoint
  rwa [suffixCount_eq_targetCount, targetCount_eq_contactCount_of_no_twoEdge observed endpoint h] at hbound
omit [Fintype State] in
theorem twoEdge_record_earlier {n : Nat} (observed : Fin (n + 2) → State → Option State) (query : Fin (n + 2) × State)
    (answer endpoint : State) (hfirst : (Fin.last n).castSucc ≠ query.1) (hlast : Fin.last (n + 1) ≠ query.1) :
    TwoEdge (record observed query answer) endpoint ↔ TwoEdge observed endpoint := by
  simp only [TwoEdge, record, Function.update_of_ne hfirst, Function.update_of_ne hlast]
omit [Fintype State] in
theorem twoEdge_record_last {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint ↔
      answer = endpoint ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  have hindex : (Fin.last n).castSucc ≠ Fin.last (n + 1) := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hfirst' : observed (Fin.last n).castSucc start = some middle := by
      simpa only [record, Function.update_of_ne hindex] using hfirst
    by_cases hm : middle = input
    · subst middle
      exact ⟨by simpa only [record, Function.update_self, Option.some.injEq] using hlast, start, hfirst'⟩
    · exact False.elim (h ⟨start, middle, hfirst', by simpa only [record, Function.update_self, Function.update_of_ne hm] using hlast⟩)
  · rintro ⟨rfl, start, hfirst⟩
    exact ⟨start, input, by simpa only [record, Function.update_of_ne hindex] using hfirst,
      by simp only [record, Function.update_self]⟩
omit [Fintype State] in
theorem twoEdge_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer endpoint : State)
    (h : ¬TwoEdge observed endpoint) :
    TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint ↔ observed (Fin.last (n + 1)) answer = some endpoint := by
  have hindex : Fin.last (n + 1) ≠ (Fin.last n).castSucc := by intro hh; have hv := congrArg Fin.val hh; simp only [Fin.val_castSucc, Fin.val_last] at hv; omega
  constructor
  · rintro ⟨start, middle, hfirst, hlast⟩
    have hlast' : observed (Fin.last (n + 1)) middle = some endpoint := by
      simpa only [record, Function.update_of_ne hindex] using hlast
    by_cases hs : start = input
    · subst start
      have hm : answer = middle := by simpa only [record, Function.update_self, Option.some.injEq] using hfirst
      simpa only [hm] using hlast'
    · exact False.elim (h ⟨start, middle, by simpa only [record, Function.update_self, Function.update_of_ne hs] using hfirst, hlast'⟩)
  · intro hlast
    exact ⟨input, answer, by simp only [record, Function.update_self], by simpa only [record, Function.update_of_ne hindex] using hlast⟩
theorem twoEdge_last_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    Pr[fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint |
      rowLaw (observed (Fin.last (n + 1)) input)] =
        if ∃ start, observed (Fin.last n).castSucc start = some input then 1 / (Fintype.card State : ENNReal) else 0 := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_last observed input _ endpoint h]
  by_cases hp : ∃ start, observed (Fin.last n).castSucc start = some input
  · simp only [hp, and_true, if_true, tsum_ite_eq, PMF.uniformOfFintype_apply, one_div]
  · simp only [hp, and_false, if_false, tsum_zero]
theorem twoEdge_penultimate_probability [Nonempty State] {n : Nat}
    (observed : Fin (n + 2) → State → Option State) (input endpoint : State)
    (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    Pr[fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint |
      rowLaw (observed (Fin.last n).castSucc input)] = (contactCount observed endpoint : ENNReal) / Fintype.card State := by
  classical
  simp only [hfresh, rowLaw, probEvent_eq_tsum_ite, PMF.probOutput_eq_apply,
    twoEdge_record_penultimate observed input _ endpoint h, PMF.uniformOfFintype_apply, tsum_fintype,
    contactCount_succ, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem weighted_event_le_bound {Result : Type} (law : PMF Result) (weight : Result → ENNReal)
    (event : Result → Prop) [DecidablePred event] (bound : ENNReal) (hbound : ∀ result, weight result ≤ bound) :
    (∑' result, law result * (weight result * if event result then 1 else 0)) ≤ bound * Pr[event | law] := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hevent : event result
  · simpa only [hevent, if_true, mul_one, PMF.probOutput_eq_apply, mul_comm] using mul_le_mul' (hbound result) (le_refl (law result))
  · simp only [hevent, if_false, mul_zero, le_refl]
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
omit [DecidableEq State] in
theorem kernel_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    kernel (Fin.snoc before last) = fun start => (kernel before start).bind (fun input => rowLaw (last input)) := by
  induction n with
  | zero => funext start; simp [kernel, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, kernel, Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      simp only [kernel, PMF.bind_bind]
theorem row_update_charge (prior : PMF State) (observed : State → Option State) (next : State → PMF State)
    (input answer endpoint : State) :
    prior.bind (fun start => (rowLaw (Function.update observed input (some answer) start)).bind next) endpoint ≤
      prior.bind (fun start => (rowLaw (observed start)).bind next) endpoint + prior input := by
  rw [PMF.bind_apply]
  calc
    _ ≤ ∑' start, prior start * (((rowLaw (observed start)).bind next) endpoint + if start = input then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro start
      apply mul_le_mul' le_rfl
      by_cases hs : start = input
      · rw [if_pos hs]
        exact (PMF.coe_le_one _ endpoint).trans (_root_.le_add_of_nonneg_left bot_le)
      · simp only [Function.update_of_ne hs, if_neg hs, add_zero, le_refl]
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, tsum_ite_eq, PMF.bind_apply]
theorem meanPreimages_last_update_le {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer endpoint : State) :
    meanPreimages (Fin.snoc before (Function.update last input (some answer))) endpoint ≤
      meanPreimages (Fin.snoc before last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) last PMF.pure input answer endpoint
  simp only [PMF.bind_pure] at h
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_penultimate_update_le {n : Nat} (before : Fin n → State → Option State)
    (penultimate last : State → Option State) (input answer endpoint : State) :
    meanPreimages (Fin.snoc (Fin.snoc before (Function.update penultimate input (some answer))) last) endpoint ≤
      meanPreimages (Fin.snoc (Fin.snoc before penultimate) last) endpoint + meanPreimages before input := by
  have h := row_update_charge ((PMF.uniformOfFintype State).bind (kernel before)) penultimate
    (fun middle => rowLaw (last middle)) input answer endpoint
  have hscaled := mul_le_mul' (le_refl (Fintype.card State : ENNReal)) h
  simpa only [meanPreimages_eq, kernel_snoc, PMF.bind_bind, mul_add] using hscaled
theorem meanPreimages_record_last_le {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed (Fin.last n, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init observed) input := by
  have h := meanPreimages_last_update_le (Fin.init observed) (observed (Fin.last n)) input answer endpoint
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem meanPreimages_record_penultimate_le {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      meanPreimages observed endpoint + meanPreimages (Fin.init (Fin.init observed)) input := by
  have h := meanPreimages_penultimate_update_le (Fin.init (Fin.init observed)) ((Fin.init observed) (Fin.last n))
    (observed (Fin.last (n + 1))) input answer endpoint
  rw [Fin.snoc_init_self, Fin.snoc_init_self] at h
  have hrecord : record observed ((Fin.last n).castSucc, input) answer =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init observed))
        (Function.update ((Fin.init observed) (Fin.last n)) input (some answer))) (observed (Fin.last (n + 1))) := by
    conv_lhs => rw [← Fin.snoc_init_self observed, ← Fin.snoc_init_self (Fin.init observed)]
    simp only [record, Fin.snoc_castSucc, Fin.snoc_last, ← Fin.snoc_update, Fin.update_snoc_last]
  simpa only [hrecord] using h
theorem twoEdge_last_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init observed) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_last_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_penultimate_density_charge {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (h : ¬TwoEdge observed endpoint) :
    meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint ≤
      (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat) := by
  have hprefix := meanPreimages_le_suffixCount (Fin.init (Fin.init observed)) input
  rw [suffixCount_eq_targetCount] at hprefix
  apply (meanPreimages_record_penultimate_le observed input answer endpoint).trans
  have hsum := _root_.add_le_add (meanPreimages_le_contactCount_of_no_twoEdge observed endpoint h) hprefix
  convert hsum using 1
  push_cast
  ring
theorem twoEdge_last_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last (n + 1)) input = none) :
    (∑' answer, rowLaw (observed (Fin.last (n + 1)) input) answer *
      (meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint *
        if TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint then 1 else 0)) ≤
      if ∃ start, observed (Fin.last n).castSucc start = some input then
        (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat) / (Fintype.card State : ENNReal) else 0 := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last (n + 1)) input))
    (fun answer => meanPreimages (record observed (Fin.last (n + 1), input) answer) endpoint)
    (fun answer => TwoEdge (record observed (Fin.last (n + 1), input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init observed) input : Nat)
    (fun answer => twoEdge_last_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_last_probability observed input endpoint h hfresh]
  split <;> simp only [mul_zero, div_eq_mul_inv, one_mul]
theorem twoEdge_penultimate_weighted_risk {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input endpoint : State) (h : ¬TwoEdge observed endpoint) (hfresh : observed (Fin.last n).castSucc input = none) :
    (∑' answer, rowLaw (observed (Fin.last n).castSucc input) answer *
      (meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint *
        if TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint then 1 else 0)) ≤
      (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) : Nat) /
        (Fintype.card State : ENNReal) := by
  classical
  apply (weighted_event_le_bound (rowLaw (observed (Fin.last n).castSucc input))
    (fun answer => meanPreimages (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (fun answer => TwoEdge (record observed ((Fin.last n).castSucc, input) answer) endpoint)
    (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input : Nat)
    (fun answer => twoEdge_penultimate_density_charge observed input answer endpoint h)).trans_eq
  rw [twoEdge_penultimate_probability observed input endpoint h hfresh]
  simp only [Nat.cast_mul, div_eq_mul_inv]
  ring
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def longCompleted : {n : Nat} → (Fin n → State → Option State) → Nat
  | 0, _ => 0
  | 1, _ => 0
  | _ + 2, observed => (∑ endpoint : State, knownCount observed endpoint) + longCompleted (Fin.tail observed)
omit [Fintype State] [DecidableEq State] in
theorem Extends.init {n : Nat} {before after : Fin (n + 1) → State → Option State} (h : Extends before after) :
    Extends (Fin.init before) (Fin.init after) := fun step input answer => h step.castSucc input answer
theorem longCompleted_mono {n : Nat} {before after : Fin n → State → Option State} (h : Extends before after) :
    longCompleted before ≤ longCompleted after := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      cases n with
      | zero => exact le_rfl
      | succ n =>
          exact Nat.add_le_add (Finset.sum_le_sum fun endpoint _ => knownCount_mono h endpoint) (ih h.tail)
theorem knownCount_sum_single (observed : Fin 1 → State → Option State) :
    (∑ endpoint : State, knownCount observed endpoint) = queriedCount (observed 0) := by
  rw [knownCount_sum, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases hrow : observed 0 input <;> simp [knownRun, hrow]
theorem completedCount_eq_longCompleted {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    completedCount observed = longCompleted observed + queriedCount (observed (Fin.last n)) := by
  induction n with
  | zero =>
      simp only [completedCount, targetCount, Nat.add_zero, longCompleted, Nat.zero_add]
      exact knownCount_sum_single observed
  | succ n ih =>
      change (∑ endpoint : State, (knownCount observed endpoint + targetCount (Fin.tail observed) endpoint)) = _
      rw [Finset.sum_add_distrib]
      change (∑ endpoint : State, knownCount observed endpoint) + completedCount (Fin.tail observed) = _
      rw [ih (Fin.tail observed)]
      simp only [longCompleted, Fin.tail, Fin.succ_last, Nat.add_assoc]
omit [DecidableEq State] in
theorem queryCount_split_last {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    queryCount observed = queryCount (Fin.init observed) + queriedCount (observed (Fin.last n)) := by
  simp only [queryCount, Fin.sum_univ_castSucc, Fin.init]
theorem longCompleted_le_prefix_queries {n : Nat} (observed : Fin (n + 1) → State → Option State) :
    longCompleted observed ≤ queryCount (Fin.init observed) := by
  have h := completedCount_le_queryCount observed
  rw [completedCount_eq_longCompleted, queryCount_split_last] at h
  omega
theorem longCompleted_le_queryCount {n : Nat} (observed : Fin n → State → Option State) :
    longCompleted observed ≤ queryCount observed := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
      have h := longCompleted_le_prefix_queries observed
      rw [queryCount_split_last]
      omega
theorem longCompleted_empty {n : Nat} : longCompleted (fun (_ : Fin n) (_ : State) => none) = 0 := by
  have h := longCompleted_le_queryCount (fun (_ : Fin n) (_ : State) => none)
  rw [queryCount_empty] at h
  omega
omit [Fintype State] [DecidableEq State] in
theorem tail_snoc {n : Nat} (before : Fin (n + 1) → State → Option State) (last : State → Option State) :
    @Fin.tail (n + 1) (fun _ => State → Option State) (Fin.snoc before last) =
      (Fin.snoc (Fin.tail before) last : Fin (n + 1) → State → Option State) := by
  have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
    rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
  rw [hs, Fin.tail_cons]
omit [Fintype State] [DecidableEq State] in
theorem knownRun_snoc {n : Nat} (before : Fin n → State → Option State) (last : State → Option State) :
    knownRun (Fin.snoc before last) = fun start => (knownRun before start).bind last := by
  induction n with
  | zero => funext start; simp [knownRun, Fin.snoc_zero]
  | succ n ih =>
      funext start
      have hs : Fin.snoc before last = @Fin.cons (n + 1) (fun _ => State → Option State) (before 0) (Fin.snoc (Fin.tail before) last) := by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]
      rw [hs, knownRun, Fin.cons_zero, Fin.tail_cons, ih]
      simp only [knownRun, Option.bind_assoc]
theorem knownCount_sum_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    (∑ endpoint : State, knownCount (Fin.snoc before (Function.update last input (some answer))) endpoint) =
      (∑ endpoint : State, knownCount (Fin.snoc before last) endpoint) + knownCount before input := by
  rw [knownCount_sum, knownCount_sum]
  simp only [knownCount, ← Finset.sum_add_distrib, knownRun_snoc]
  apply Finset.sum_congr rfl
  intro start _
  cases hrun : knownRun before start with
  | none => simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, if_false, reduceCtorEq, Nat.add_zero]
  | some value =>
      by_cases hv : value = input
      · subst value
        simp only [Option.bind_some, Function.update_self, hfresh, Option.isSome_some, Option.isSome_none,
          Bool.false_eq_true, if_true, if_false, Nat.zero_add]
      · simp only [Option.bind_some, Function.update_of_ne hv, Option.some.injEq, if_neg hv, Nat.add_zero]
theorem longCompleted_last_fresh {n : Nat} (before : Fin n → State → Option State) (last : State → Option State)
    (input answer : State) (hfresh : last input = none) :
    longCompleted (Fin.snoc before (Function.update last input (some answer))) =
      longCompleted (Fin.snoc before last) + targetCount before input := by
  induction n with
  | zero => simp only [longCompleted, targetCount, Nat.add_zero]
  | succ n ih =>
      rw [longCompleted, longCompleted, tail_snoc, tail_snoc, knownCount_sum_last_fresh before last input answer hfresh,
        ih (Fin.tail before), targetCount]
      omega
theorem longCompleted_record_last {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n) input = none) :
    longCompleted (record observed (Fin.last n, input) answer) =
      longCompleted observed + targetCount (Fin.init observed) input := by
  have h := longCompleted_last_fresh (Fin.init observed) (observed (Fin.last n)) input answer hfresh
  rw [Fin.snoc_init_self] at h
  have hrecord : record observed (Fin.last n, input) answer =
      Fin.snoc (Fin.init observed) (Function.update (observed (Fin.last n)) input (some answer)) := by
    conv_lhs => rw [← Fin.snoc_init_self observed]
    simp only [record, Fin.snoc_last, Fin.update_snoc_last]
  simpa only [hrecord] using h
omit [Fintype State] in
theorem init_record {n : Nat} (observed : Fin (n + 1) → State → Option State)
    (step : Fin n) (input answer : State) :
    Fin.init (record observed (step.castSucc, input) answer) = record (Fin.init observed) (step, input) answer := by
  simp only [record, Fin.init_update_castSucc, Fin.init]
theorem longCompleted_prefix_record_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (input answer : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    longCompleted (Fin.init (record observed ((Fin.last n).castSucc, input) answer)) =
      longCompleted (Fin.init observed) + targetCount (Fin.init (Fin.init observed)) input := by
  rw [init_record]
  exact longCompleted_record_last (Fin.init observed) input answer hfresh
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
noncomputable def queriedInputs (row : State → Option State) : Finset State :=
  Finset.univ.filter fun input => row input ≠ none
noncomputable def rowImage (row : State → Option State) : Finset State :=
  Finset.univ.biUnion fun input => (row input).toFinset
omit [DecidableEq State] in
theorem mem_queriedInputs (row : State → Option State) (input : State) :
    input ∈ queriedInputs row ↔ row input ≠ none := by simp [queriedInputs]
omit [DecidableEq State] in
theorem queriedInputs_card (row : State → Option State) : (queriedInputs row).card = queriedCount row := by
  rw [queriedInputs, Finset.card_filter, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases row input <;> simp
theorem mem_rowImage (row : State → Option State) (output : State) :
    output ∈ rowImage row ↔ ∃ input, row input = some output := by
  simp only [rowImage, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset, Option.mem_def]
theorem rowImage_card_le (row : State → Option State) : (rowImage row).card ≤ queriedCount row := by
  apply Finset.card_biUnion_le.trans
  rw [queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro input _
  cases row input <;> simp
noncomputable def productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) : Finset State :=
  queriedInputs (observed (Fin.last (n + 1))) ∩ rowImage (observed (Fin.last n).castSucc)
noncomputable def preparationCount {n : Nat} (observed : Fin (n + 2) → State → Option State) : Nat :=
  (productiveInputs observed).card
theorem mem_productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) (input : State) :
    input ∈ productiveInputs observed ↔
      observed (Fin.last (n + 1)) input ≠ none ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  simp only [productiveInputs, Finset.mem_inter, mem_queriedInputs, mem_rowImage]
theorem productiveInputs_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    productiveInputs before ⊆ productiveInputs after := by
  intro input hi
  rw [mem_productiveInputs] at hi ⊢
  constructor
  · cases hr : before (Fin.last (n + 1)) input with
    | none => exact False.elim (hi.1 hr)
    | some answer => rw [h _ _ _ hr]; exact Option.some_ne_none answer
  · obtain ⟨start, hs⟩ := hi.2
    exact ⟨start, h _ _ _ hs⟩
theorem preparationCount_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    preparationCount before ≤ preparationCount after := Finset.card_le_card (productiveInputs_mono h)
theorem preparationCount_le_last {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last (n + 1))) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (queriedInputs_card _)
theorem preparationCount_le_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last n).castSucc) := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans (rowImage_card_le _)
theorem preparationCount_le_prefix {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queryCount (Fin.init observed) := by
  apply (preparationCount_le_penultimate observed).trans
  change queriedCount ((Fin.init observed) (Fin.last n)) ≤ ∑ step, queriedCount ((Fin.init observed) step)
  exact Finset.single_le_sum (f := fun step => queriedCount ((Fin.init observed) step))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last n))
theorem preparationCount_empty {n : Nat} : preparationCount (n := n) (fun (_ : Fin (n + 2)) (_ : State) => none) = 0 := by
  simp [preparationCount, productiveInputs, queriedInputs]
theorem preparationCount_last_fresh {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer : State)
    (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    preparationCount observed + 1 ≤ preparationCount (record observed (Fin.last (n + 1), input) answer) := by
  have hnot : input ∉ productiveInputs observed := by simp only [mem_productiveInputs, hfresh, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hmem : input ∈ productiveInputs (record observed (Fin.last (n + 1), input) answer) := by
    rw [mem_productiveInputs]
    constructor
    · simp only [record, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · obtain ⟨start, hs⟩ := hprepared
      refine ⟨start, ?_⟩
      rw [record_at_other observed (Fin.last (n + 1), input) ((Fin.last n).castSucc, start) answer]
      · exact hs
      · intro heq
        have hv := congrArg (fun query => query.1.val) heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
  have hsub := productiveInputs_mono (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh))
  have hcard := Finset.card_le_card (Finset.insert_subset hmem hsub)
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact hcard
theorem preparation_charge_le_three_halves {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    2 * (longCompleted observed + 2 * preparationCount observed) ≤ 3 * queryCount observed := by
  have hd := longCompleted_le_prefix_queries observed
  have hp := preparationCount_le_prefix observed
  have hl := preparationCount_le_last observed
  rw [queryCount_split_last]
  omega
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State : Type} [Fintype State] [DecidableEq State]
theorem contactCount_mono {n : Nat} {before after : Fin n → State → Option State}
    (h : Extends before after) (endpoint : State) : contactCount before endpoint ≤ contactCount after endpoint := by
  unfold contactCount
  apply Finset.sum_le_sum
  intro query _
  by_cases hk : query.1.val + 1 = n ∧ before query.1 query.2 = some endpoint
  · have hk' : query.1.val + 1 = n ∧ after query.1 query.2 = some endpoint := ⟨hk.1, h _ _ _ hk.2⟩
    simp only [if_pos hk, if_pos hk', le_refl]
  · simp only [if_neg hk, Nat.zero_le]
noncomputable def twoEdgeCharge {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Nat :=
  longCompleted observed + 2 * preparationCount observed +
    spent * (contactCount observed endpoint * (contactCount observed endpoint + 2)) +
    contactCount observed endpoint * longCompleted (Fin.init observed)
theorem twoEdgeCharge_empty {n : Nat} (endpoint : State) :
    twoEdgeCharge 0 (n := n) (fun _ _ => none) endpoint = 0 := by
  simp only [twoEdgeCharge, longCompleted_empty, preparationCount_empty, contactCount_empty,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
theorem twoEdgeCharge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State}
    {spent next : Nat} (hs : spent ≤ next) (h : Extends before after) (endpoint : State) :
    twoEdgeCharge spent before endpoint ≤ twoEdgeCharge next after endpoint := by
  unfold twoEdgeCharge
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (longCompleted_mono h) (Nat.mul_le_mul_left 2 (preparationCount_mono h)))
      (Nat.mul_le_mul hs (Nat.mul_le_mul (contactCount_mono h endpoint) (Nat.add_le_add_right (contactCount_mono h endpoint) 2))))
    (Nat.mul_le_mul (contactCount_mono h endpoint) (longCompleted_mono h.init))
private theorem charge_increment (d p r k d' p' r' k' spent dd dp dr : Nat)
    (hd : d + dd ≤ d') (hp : p + dp ≤ p') (hr : r + dr ≤ r') (hk : k ≤ k') :
    (d + 2 * p + spent * (k * (k + 2)) + k * r) + dd + 2 * dp + k * (k + 2) + k * dr ≤
      d' + 2 * p' + (spent + 1) * (k' * (k' + 2)) + k' * r' := by
  have hpoly := Nat.mul_le_mul (Nat.le_refl (spent + 1)) (Nat.mul_le_mul hk (Nat.add_le_add_right hk 2))
  have hprod := Nat.mul_le_mul hk hr
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hd (Nat.mul_le_mul_left 2 hp)) hpoly) hprod
  convert hsum using 1
  ring
theorem twoEdgeCharge_record_last {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    twoEdgeCharge spent observed endpoint + (2 + contactCount observed endpoint + targetCount (Fin.init observed) input) ≤
      twoEdgeCharge (spent + 1) (record observed (Fin.last (n + 1), input) answer) endpoint := by
  have hext := record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent (targetCount (Fin.init observed) input) 1 0
    (le_of_eq (longCompleted_record_last observed input answer hfresh).symm)
    (preparationCount_last_fresh observed input answer hfresh hprepared)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext.init) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  have hk : contactCount observed endpoint ≤ contactCount observed endpoint * (contactCount observed endpoint + 2) := by nlinarith
  omega
theorem twoEdgeCharge_record_penultimate {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    twoEdgeCharge spent observed endpoint +
      contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) ≤
      twoEdgeCharge (spent + 1) (record observed ((Fin.last n).castSucc, input) answer) endpoint := by
  have hext := record_extends observed ((Fin.last n).castSucc, input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent 0 0 (targetCount (Fin.init (Fin.init observed)) input)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext)
    (by simpa only [Nat.add_zero] using preparationCount_mono hext)
    (le_of_eq (longCompleted_prefix_record_penultimate observed input answer hfresh).symm) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  convert h using 1
  ring
theorem contact_correction_identity (k : Nat) : k * (k + 2) + k = contactFactorial k + 4 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring
theorem twoEdgeCharge_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    twoEdgeCharge spent observed endpoint ≤ longCompleted observed + 2 * preparationCount observed +
      budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have hr := longCompleted_le_queryCount (Fin.init observed)
  have hsplit := queryCount_split_last observed
  have hrq : longCompleted (Fin.init observed) ≤ budget := by omega
  have hprod := Nat.mul_le_mul_left (contactCount observed endpoint) hrq
  have hspent := Nat.mul_le_mul_right (contactCount observed endpoint * (contactCount observed endpoint + 2)) hs
  have hsum := Nat.add_le_add hspent hprod
  rw [Nat.mul_comm (contactCount observed endpoint) budget, ← Nat.mul_add, contact_correction_identity] at hsum
  unfold twoEdgeCharge
  omega
theorem twoEdgeCharge_twice_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    2 * twoEdgeCharge spent observed endpoint ≤ 3 * queryCount observed +
      2 * budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have h := twoEdgeCharge_le spent budget observed endpoint hs hq
  have hbase := preparation_charge_le_three_halves observed
  nlinarith
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section

namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
noncomputable def twoEdgeWeight {n : Nat} (observed : Fin (n + 2) → State → Option State) (endpoint : State) : ENNReal :=
  meanPreimages observed endpoint * if TwoEdge observed endpoint then 1 else 0
theorem twoEdgeWeight_empty {n : Nat} (endpoint : State) :
    twoEdgeWeight (n := n) (fun _ _ => none) endpoint = 0 := by
  simp [twoEdgeWeight, TwoEdge]
omit [DecidableEq State] [Nonempty State] in
private theorem expected_charge_cover (law : PMF State) (before increment : Nat) (after : State → Nat)
    (weight : State → ENNReal)
    (hrisk : (∑' answer, law answer * weight answer) ≤ (increment : ENNReal) / Fintype.card State)
    (hcharge : ∀ answer, before + increment ≤ after answer) :
    (before : ENNReal) / Fintype.card State + (∑' answer, law answer * weight answer) ≤
      ∑' answer, law answer * ((after answer : ENNReal) / Fintype.card State) := by
  calc
    _ ≤ (before : ENNReal) / Fintype.card State + (increment : ENNReal) / Fintype.card State := _root_.add_le_add le_rfl hrisk
    _ = ((before + increment : Nat) : ENNReal) / Fintype.card State := by simp only [Nat.cast_add, div_eq_mul_inv, add_mul]
    _ = ∑' answer, law answer * (((before + increment : Nat) : ENNReal) / Fintype.card State) := (expectation_const _ _).symm
    _ ≤ _ := ENNReal.tsum_le_tsum fun answer => mul_le_mul' le_rfl (by gcongr; exact_mod_cast hcharge answer)
theorem twoEdgeCharge_observe_mono {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  cases hrow : observed query.1 query.2 with
  | some answer =>
      simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
  | none =>
      rw [← expectation_const (rowLaw (none : Option State)) ((twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State)]
      apply ENNReal.tsum_le_tsum
      intro answer
      apply mul_le_mul' le_rfl
      gcongr
      exact twoEdgeCharge_mono (Nat.le_succ spent) (record_extends observed query answer (Or.inl hrow)) endpoint
theorem twoEdgeWeight_observe_of_bad {n : Nat} (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : TwoEdge observed endpoint) :
    (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) =
      twoEdgeWeight observed endpoint := by
  cases hrow : observed query.1 query.2 with
  | some answer => simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow]
  | none =>
      have hafter (answer : State) : TwoEdge (record observed query answer) endpoint :=
        twoEdge_mono (record_extends observed query answer (Or.inl hrow)) endpoint hbad
      simp only [twoEdgeWeight, if_pos hbad, if_pos (hafter _), mul_one]
      simpa only [hrow] using meanPreimages_observe observed query endpoint
theorem twoEdge_first_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) (hbad : ¬TwoEdge observed endpoint)
    (hfresh : observed query.1 query.2 = none) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  rcases query with ⟨step, input⟩
  by_cases hlast : step = Fin.last (n + 1)
  · subst step
    by_cases hprepared : ∃ start, observed (Fin.last n).castSucc start = some input
    · apply expected_charge_cover _ _ (2 + contactCount observed endpoint + targetCount (Fin.init observed) input)
      · simpa only [twoEdgeWeight, if_pos hprepared] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_last spent observed input answer endpoint hfresh hprepared
    · apply expected_charge_cover _ _ 0
      · simpa only [twoEdgeWeight, if_neg hprepared, Nat.cast_zero, div_eq_mul_inv, zero_mul] using twoEdge_last_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        simpa only [Nat.add_zero] using twoEdgeCharge_mono (Nat.le_succ spent)
          (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)) endpoint
  · by_cases hpen : step = (Fin.last n).castSucc
    · subst step
      apply expected_charge_cover _ _ (contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input))
      · exact twoEdge_penultimate_weighted_risk observed input endpoint hbad hfresh
      · intro answer
        exact twoEdgeCharge_record_penultimate spent observed input answer endpoint hfresh
    · have hafter (answer : State) : ¬TwoEdge (record observed (step, input) answer) endpoint := by
        rw [twoEdge_record_earlier observed (step, input) answer endpoint (Ne.symm hpen) (Ne.symm hlast)]
        exact hbad
      simp only [twoEdgeWeight, if_neg (hafter _), mul_zero, tsum_zero, add_zero]
      exact twoEdgeCharge_observe_mono spent observed (step, input) endpoint
theorem twoEdge_observe_compensation {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (query : Fin (n + 2) × State) (endpoint : State) :
    (twoEdgeCharge spent observed endpoint : ENNReal) / Fintype.card State +
      (∑' answer, rowLaw (observed query.1 query.2) answer * twoEdgeWeight (record observed query answer) endpoint) ≤
      twoEdgeWeight observed endpoint + ∑' answer, rowLaw (observed query.1 query.2) answer *
        ((twoEdgeCharge (spent + 1) (record observed query answer) endpoint : ENNReal) / Fintype.card State) := by
  by_cases hbad : TwoEdge observed endpoint
  · rw [twoEdgeWeight_observe_of_bad observed query endpoint hbad, add_comm]
    exact _root_.add_le_add le_rfl (twoEdgeCharge_observe_mono spent observed query endpoint)
  · have hzero : twoEdgeWeight observed endpoint = 0 := by simp only [twoEdgeWeight, if_neg hbad, mul_zero]
    rw [hzero, zero_add]
    cases hrow : observed query.1 query.2 with
    | none => simpa only [hrow] using twoEdge_first_compensation spent observed query endpoint hbad hrow
    | some answer =>
        simp only [rowLaw, expectation_pure, record_of_known observed query answer hrow, hzero, add_zero]
        gcongr
        exact twoEdgeCharge_mono (Nat.le_succ spent) (fun _ _ _ h => h) endpoint
end SphincsSecurity.Concrete.PartialChainEndpoint
end
