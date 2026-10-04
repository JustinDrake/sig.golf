import SigGolfCandidate.T3.Secc.WotsEncodingResample
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservationErasure
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTracePotential
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
import SigGolfCandidate.T3.Secc.WotsPrefixGame
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
namespace Enc.Lazy
section World
variable {ι : Type} (cellInput : ι → HashInput) (F : Set ι)
abbrev World := RefWorld + UniformTableObservation.TableSpec F HashOutput
def IsCell (input : HashInput) : Prop := ∃ e, e ∈ F ∧ cellInput e = input
noncomputable def cellOf (input : HashInput) (h : IsCell cellInput F input) : F :=
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩
theorem cellOf_input (input : HashInput) (h : IsCell cellInput F input) :
    cellInput (cellOf cellInput F input h).val = input := (Classical.choose_spec h).2
theorem cellOf_eq (hinj : Function.Injective cellInput) (e : F) (h : IsCell cellInput F (cellInput e.val)) :
    cellOf cellInput F (cellInput e.val) h = e :=
  Subtype.ext (hinj (cellOf_input cellInput F _ h))
noncomputable def translate : QueryImpl RefWorld (OracleComp (World F))
  | .inl (.inl n) => liftM ((World F).query (.inl (.inl (.inl n))))
  | .inl (.inr input) =>
      if h : IsCell cellInput F input then liftM ((World F).query (.inr (cellOf cellInput F input h)))
      else liftM ((World F).query (.inl (.inl (.inr input))))
  | .inr u => liftM ((World F).query (.inl (.inr u)))
noncomputable def aux (T : Answers) : QueryImpl RefWorld SPMF := fun q => 𝒮[refImpl T q]
noncomputable def overwrite (T : Answers) (y : F → HashOutput) : Answers
  | .inl (.inl n) => T (.inl (.inl n))
  | .inl (.inr input) => if h : IsCell cellInput F input then y (cellOf cellInput F input h) else T (.inl (.inr input))
  | .inr c => T (.inr c)
theorem fixed_translate (T : Answers) (y : F → HashOutput) (q : RefWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (aux T) y) (translate cellInput F q) =
      𝒮[refImpl (overwrite cellInput F T y) q] := by
  rcases q with (n | input) | u
  · simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl]
  · by_cases h : IsCell cellInput F input
    · simp only [translate, dif_pos h, simulateQ_spec_query, UniformTableObservation.fixedImpl, refImpl,
        overwrite, evalSPMF_pure]
    · simp only [translate, dif_neg h, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl,
        overwrite, evalSPMF_pure]
  · simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, aux, refImpl]
theorem fixed_run {β : Type} (T : Answers) (y : F → HashOutput) (C : OracleComp RefWorld β) :
    simulateQ (UniformTableObservation.fixedImpl (aux T) y) (simulateQ (translate cellInput F) C) =
      𝒮[simulateQ (refImpl (overwrite cellInput F T y)) C] := by
  induction C using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate]
variable [Fintype F] [DecidableEq F]
theorem eager_lazy {β : Type} (T : Answers) (C : OracleComp RefWorld β) :
    (complete (fun _ : F => (Finset.univ : Finset HashOutput)) >>= fun y =>
      𝒮[simulateQ (refImpl (overwrite cellInput F T y)) C]) =
      Prod.fst <$> UniformTableObservation.lazyRun (aux T) (simulateQ (translate cellInput F) C)
        (fun _ => Finset.univ) := by
  rw [← UniformTableObservation.run_marginal (aux T) (simulateQ (translate cellInput F) C) _
    (fun _ => Finset.univ_nonempty)]
  simp only [fixed_run]
noncomputable def lazyImpl (T : Answers) : QueryImpl RefWorld (StateT (F → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (aux T)).compose (translate cellInput F)
theorem lazyRun_eq_simulate {β : Type} (T : Answers) (C : OracleComp RefWorld β) (allowed : F → Finset HashOutput) :
    UniformTableObservation.lazyRun (aux T) (simulateQ (translate cellInput F) C) allowed =
      (simulateQ (lazyImpl cellInput F T) C).run allowed := by
  rw [UniformTableObservation.lazyRun, lazyImpl, QueryImpl.simulateQ_compose]
end World
def obs : (q : RefWorld.Domain) → RefWorld.Range q → FreeMonoid Entry
  | .inl (.inl _), _ => 1
  | .inl (.inr input), answer => FreeMonoid.of (input, answer)
  | .inr _, _ => 1
theorem recorded_traced {α : Type} (T : Answers) (C : OracleComp RefWorld α) :
    (fun r => (r.1, traceOf T r.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded C) =
      (fun r => (r.1, FreeMonoid.toList r.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryPause.traced obs C) := by
  induction C using OracleComp.inductionOn with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.traced_pure, simulateQ_pure,
        map_pure]
      rfl
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.traced_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_map, simulateQ_pure, map_bind]
      rcases input with (n | x) | u
      · congr 1
        funext answer
        have h := congrArg (fun c => (fun r : α × List Entry => (r.1, (obs (.inl (.inl n)) answer).toList ++ r.2)) <$> c)
          (ih answer)
        simp only [Functor.map_map] at h
        simpa [obs, traceOf, bind_pure_comp] using h
      · have h := congrArg (fun c => (fun r : α × List Entry =>
          (r.1, (obs (.inl (.inr x)) (T (.inl (.inr x)))).toList ++ r.2)) <$> c) (ih (T (.inl (.inr x))))
        simp only [Functor.map_map] at h
        simp only [refImpl, pure_bind]
        simpa [obs, traceOf, bind_pure_comp] using h
      · congr 1
        funext answer
        have h := congrArg (fun c => (fun r : α × List Entry => (r.1, (obs (.inr u) answer).toList ++ r.2)) <$> c)
          (ih answer)
        simp only [Functor.map_map] at h
        simpa [obs, traceOf, bind_pure_comp] using h
section Potential
variable {ι : Type} (cellInput : ι → HashInput) (F : Set ι) [Fintype F] [DecidableEq F]
def Consistent (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) : Prop :=
  (∀ e : F, ∀ ans, (cellInput e.val, ans) ∈ h.toList → allowed e = {ans}) ∧
    ∀ e : F, (∀ ans, (cellInput e.val, ans) ∉ h.toList) → allowed e = Finset.univ
theorem consistent_one : Consistent cellInput F 1 (fun _ => Finset.univ) := by
  constructor
  · intro e ans h
    simp at h
  · intro e _
    rfl
theorem Consistent.nonempty {h : FreeMonoid Entry} {allowed : F → Finset HashOutput}
    (hc : Consistent cellInput F h allowed) : ∀ e, (allowed e).Nonempty := by
  intro e
  by_cases hq : ∃ ans, (cellInput e.val, ans) ∈ h.toList
  · obtain ⟨ans, hans⟩ := hq
    rw [hc.1 e ans hans]
    exact Finset.singleton_nonempty ans
  · rw [hc.2 e (fun ans hans => hq ⟨ans, hans⟩)]
    exact Finset.univ_nonempty
noncomputable def marks {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) : Nat :=
  (Finset.univ.filter fun a => ∃ entry ∈ l, M a entry).card
noncomputable def cellCount (l : List Entry) : Nat :=
  (l.filter fun entry => decide (IsCell cellInput F entry.1)).length
noncomputable def charge : RefWorld.Domain → Nat
  | .inl (.inr input) => if IsCell cellInput F input then 1 else 0
  | _ => 0
theorem marks_append_le {A : Type} [Fintype A] [DecidableEq A] (M : A → Entry → Prop) (l : List Entry)
    (x : Entry) : marks M (l ++ [x]) ≤ marks M l + (Finset.univ.filter fun a => M a x).card := by
  unfold marks
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_append, List.mem_singleton] at ha
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨entry, hmem, hm⟩ := ha
  rcases hmem with hmem | rfl
  · exact Or.inl ⟨entry, hmem, hm⟩
  · exact Or.inr hm
theorem marks_append_of_mem {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) (x : Entry)
    (hx : x ∈ l) : marks M (l ++ [x]) = marks M l := by
  unfold marks
  congr 1
  apply Finset.filter_congr
  intro a _
  constructor
  · rintro ⟨entry, hmem, hm⟩
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact ⟨entry, hmem, hm⟩
    · exact ⟨_, hx, hm⟩
  · rintro ⟨entry, hmem, hm⟩
    exact ⟨entry, List.mem_append_left _ hmem, hm⟩
theorem marks_append_of_none {A : Type} [Fintype A] (M : A → Entry → Prop) (l : List Entry) (x : Entry)
    (hx : ∀ a, ¬ M a x) : marks M (l ++ [x]) = marks M l := by
  unfold marks
  congr 1
  apply Finset.filter_congr
  intro a _
  constructor
  · rintro ⟨entry, hmem, hm⟩
    rw [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact ⟨entry, hmem, hm⟩
    · exact absurd hm (hx a)
  · rintro ⟨entry, hmem, hm⟩
    exact ⟨entry, List.mem_append_left _ hmem, hm⟩
theorem cellCount_step (input : RefWorld.Domain) (answer : RefWorld.Range input) (tail : FreeMonoid Entry) :
    cellCount cellInput F (obs input answer * tail).toList =
      charge cellInput F input + cellCount cellInput F tail.toList := by
  rcases input with (n | x) | u
  · simp [obs, charge, cellCount]
  · by_cases hx : IsCell cellInput F x
    · simp [obs, charge, cellCount, hx, Nat.add_comm]
    · simp [obs, charge, cellCount, hx]
  · simp [obs, charge, cellCount]
theorem lazyImpl_coin (T : Answers) (n : Nat) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inl n))).run allowed =
      (fun answer => (answer, allowed)) <$> aux T (.inl (.inl n)) := by
  simp only [lazyImpl, QueryImpl.compose, translate, simulateQ_spec_query, UniformTableObservation.lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyImpl_tick (T : Answers) (u : Unit) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inr u)).run allowed =
      (fun answer => (answer, allowed)) <$> aux T (.inr u) := by
  simp only [lazyImpl, QueryImpl.compose, translate, simulateQ_spec_query, UniformTableObservation.lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyImpl_cell (T : Answers) (x : HashInput) (hx : IsCell cellInput F x) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inr x))).run allowed =
      (fun answer => (answer, discloseTableValue allowed (cellOf cellInput F x hx) answer)) <$>
        cell (allowed (cellOf cellInput F x hx)) := by
  simp only [lazyImpl, QueryImpl.compose, translate, dif_pos hx, simulateQ_spec_query,
    UniformTableObservation.lazyImpl, StateT.run_mk]
  rfl
theorem lazyImpl_other (T : Answers) (x : HashInput) (hx : ¬ IsCell cellInput F x) (allowed : F → Finset HashOutput) :
    (lazyImpl cellInput F T (.inl (.inr x))).run allowed = pure (T (.inl (.inr x)), allowed) := by
  simp only [lazyImpl, QueryImpl.compose, translate, dif_neg hx, simulateQ_spec_query,
    UniformTableObservation.lazyImpl, StateT.run_mk, aux, refImpl, evalSPMF_pure, map_pure]
theorem map_nonzero {α β : Type} (μ : SPMF α) (f : α → β) (result : β) (h : (f <$> μ) result ≠ 0) :
    ∃ a, μ a ≠ 0 ∧ result = f a := by
  rw [← bind_pure_comp] at h
  obtain ⟨a, ha, heq⟩ := (SphincsSecurity.Concrete.RetainedObservation.bind_nonzero _ _ _).mp h
  refine ⟨a, ha, ?_⟩
  simpa only [Function.comp_apply, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using heq
theorem cell_nonzero_mem {allowed : Finset HashOutput} {answer : HashOutput} (h : cell allowed answer ≠ 0) :
    answer ∈ allowed := by
  rw [cell_apply] at h
  by_contra hn
  exact h (if_neg hn)
theorem consistent_step (hinj : Function.Injective cellInput) (T : Answers) (h : FreeMonoid Entry)
    (allowed : F → Finset HashOutput) (hc : Consistent cellInput F h allowed) (input : RefWorld.Domain)
    (result : RefWorld.Range input × (F → Finset HashOutput))
    (hr : (lazyImpl cellInput F T input).run allowed result ≠ 0) :
    Consistent cellInput F (h * obs input result.1) result.2 := by
  rcases input with (n | x) | u
  · rw [lazyImpl_coin] at hr
    obtain ⟨answer, _, rfl⟩ := map_nonzero _ _ _ hr
    simpa only [obs, mul_one] using hc
  · by_cases hx : IsCell cellInput F x
    · rw [lazyImpl_cell cellInput F T x hx] at hr
      obtain ⟨answer, ha, rfl⟩ := map_nonzero _ _ _ hr
      have hmem := cell_nonzero_mem ha
      set e₀ := cellOf cellInput F x hx with he₀
      have hx₀ : cellInput e₀.val = x := cellOf_input cellInput F x hx
      have hne : ∀ e : F, e ≠ e₀ → cellInput e.val ≠ x := by
        intro e he heq
        exact he (Subtype.ext (hinj (heq.trans hx₀.symm)))
      constructor
      · intro e ans hans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
          Prod.mk.injEq] at hans
        by_cases he : e = e₀
        · subst he
          simp only [discloseTableValue, Function.update_self]
          rcases hans with hans | ⟨-, rfl⟩
          · have h1 := hc.1 _ ans hans
            rw [h1, Finset.mem_singleton] at hmem
            rw [hmem]
          · rfl
        · simp only [discloseTableValue, Function.update_of_ne he]
          rcases hans with hans | ⟨heq, -⟩
          · exact hc.1 e ans hans
          · exact absurd heq (hne e he)
      · intro e hfresh
        have he : e ≠ e₀ := by
          intro he
          apply hfresh answer
          simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton]
          right
          rw [he, hx₀]
        simp only [discloseTableValue, Function.update_of_ne he]
        apply hc.2 e
        intro ans hans
        apply hfresh ans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
        exact Or.inl hans
    · rw [lazyImpl_other cellInput F T x hx] at hr
      have hres : result = (T (.inl (.inr x)), allowed) := by
        by_contra hn
        exact hr (by rw [SPMF.pure_apply_eq_zero_iff]; exact hn)
      subst hres
      have hnot : ∀ e : F, cellInput e.val ≠ x := fun e heq => hx ⟨e.val, e.property, heq⟩
      constructor
      · intro e ans hans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
          Prod.mk.injEq] at hans
        rcases hans with hans | ⟨heq, -⟩
        · exact hc.1 e ans hans
        · exact absurd heq (hnot e)
      · intro e hfresh
        apply hc.2 e
        intro ans hans
        apply hfresh ans
        simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
        exact Or.inl hans
  · rw [lazyImpl_tick] at hr
    obtain ⟨answer, _, rfl⟩ := map_nonzero _ _ _ hr
    simpa only [obs, mul_one] using hc
theorem probEvent_cell_univ (p : HashOutput → Prop) :
    Pr[p | cell (Finset.univ : Finset HashOutput)] = Pr[p | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr fun ans => ?_
  split_ifs
  · rw [SPMF.probOutput_eq_apply, cell_apply, if_pos (Finset.mem_univ _), probOutput_uniformSample, Finset.card_univ]
  · rfl
theorem tsum_probOutput_mul_le_self {α : Type} (μ : SPMF α) (c : ENNReal) :
    ∑' a, Pr[= a | μ] * c ≤ c := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
theorem tsum_filter_card {A : Type} [Fintype A] (μ : SPMF HashOutput) (M : A → HashOutput → Prop) :
    ∑' ans, Pr[= ans | μ] * ((Finset.univ.filter fun a => M a ans).card : ENNReal) = ∑ a, Pr[M a | μ] := by
  classical
  have h : ∀ ans, ((Finset.univ.filter fun a => M a ans).card : ENNReal) = ∑ a, if M a ans then 1 else 0 := by
    intro ans
    rw [Finset.card_filter]
    push_cast
    rfl
  simp only [h, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun ans => ?_
  split_ifs <;> simp
theorem lazy_step {A : Type} [Fintype A] [DecidableEq A] (hinj : Function.Injective cellInput) (T : Answers)
    (M : A → Entry → Prop) (rate : ENNReal)
    (hcell : ∀ e : F, ∑ a, Pr[fun ans => M a (cellInput e.val, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hother : ∀ x, ¬ IsCell cellInput F x → ∀ a, ¬ M a (x, T (.inl (.inr x))))
    (h : FreeMonoid Entry) (allowed : F → Finset HashOutput) (hc : Consistent cellInput F h allowed)
    (input : RefWorld.Domain) :
    ∑' result, Pr[= result | (lazyImpl cellInput F T input).run allowed] *
        (marks M (h * obs input result.1).toList : ENNReal) ≤
      (marks M h.toList : ENNReal) + rate * (charge cellInput F input : ENNReal) := by
  rcases input with (n | x) | u
  · rw [lazyImpl_coin, tsum_probOutput_map_mul]
    simp only [obs, mul_one]
    exact (tsum_probOutput_mul_le_self _ _).trans le_self_add
  · by_cases hx : IsCell cellInput F x
    · rw [lazyImpl_cell cellInput F T x hx, tsum_probOutput_map_mul]
      simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, charge, if_pos hx, Nat.cast_one, mul_one]
      set e₀ := cellOf cellInput F x hx with he₀
      have hx₀ : cellInput e₀.val = x := cellOf_input cellInput F x hx
      by_cases hq : ∃ ans₀, (cellInput e₀.val, ans₀) ∈ h.toList
      · obtain ⟨ans₀, hans₀⟩ := hq
        rw [hc.1 e₀ ans₀ hans₀]
        have hsupp : ∀ ans, ans ≠ ans₀ → Pr[= ans | cell ({ans₀} : Finset HashOutput)] = 0 := by
          intro ans hne
          rw [SPMF.probOutput_eq_apply, cell_apply, if_neg (by simpa using hne)]
        calc _ = ∑' ans, Pr[= ans | cell ({ans₀} : Finset HashOutput)] * (marks M h.toList : ENNReal) := by
              refine tsum_congr fun ans => ?_
              by_cases hne : ans = ans₀
              · rw [hne, ← hx₀, marks_append_of_mem M _ _ hans₀]
              · rw [hsupp ans hne, zero_mul, zero_mul]
          _ ≤ _ := (tsum_probOutput_mul_le_self _ _).trans le_self_add
      · rw [hc.2 e₀ (fun ans hans => hq ⟨ans, hans⟩)]
        calc _ ≤ ∑' ans, Pr[= ans | cell (Finset.univ : Finset HashOutput)] *
              ((marks M h.toList : ENNReal) + ((Finset.univ.filter fun a => M a (x, ans)).card : ENNReal)) := by
              refine ENNReal.tsum_le_tsum fun ans => mul_le_mul' le_rfl ?_
              exact_mod_cast marks_append_le M _ _
          _ = ∑' ans, Pr[= ans | cell (Finset.univ : Finset HashOutput)] * (marks M h.toList : ENNReal) +
              ∑' ans, Pr[= ans | cell (Finset.univ : Finset HashOutput)] *
                ((Finset.univ.filter fun a => M a (x, ans)).card : ENNReal) := by
              rw [← ENNReal.tsum_add]
              exact tsum_congr fun ans => mul_add _ _ _
          _ ≤ _ := by
              refine add_le_add (tsum_probOutput_mul_le_self _ _) ?_
              rw [tsum_filter_card (cell (Finset.univ : Finset HashOutput)) (fun a ans => M a (x, ans))]
              simp only [probEvent_cell_univ]
              rw [← hx₀]
              exact hcell e₀
    · rw [lazyImpl_other cellInput F T x hx, tsum_probOutput_pure_mul]
      simp only [obs, FreeMonoid.toList_mul, FreeMonoid.toList_of, charge, if_neg hx]
      rw [marks_append_of_none M _ _ (hother x hx)]
      exact le_self_add
  · rw [lazyImpl_tick, tsum_probOutput_map_mul]
    simp only [obs, mul_one]
    exact (tsum_probOutput_mul_le_self _ _).trans le_self_add
theorem aux_neverFail (T : Answers) (input : RefWorld.Domain) : NeverFail (aux T input) :=
  ⟨probFailure_eq_zero (mx := refImpl T input)⟩
theorem lazy_marks_le {α A : Type} [Fintype A] [DecidableEq A] (hinj : Function.Injective cellInput)
    (T : Answers) (M : A → Entry → Prop) (rate : ENNReal)
    (hcell : ∀ e : F, ∑ a, Pr[fun ans => M a (cellInput e.val, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ rate)
    (hother : ∀ x, ¬ IsCell cellInput F x → ∀ a, ¬ M a (x, T (.inl (.inr x))))
    (C : OracleComp RefWorld α) :
    ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run
        (fun _ => Finset.univ)] * (marks M r.1.2.toList : ENNReal) ≤
      rate * ∑' r, Pr[= r | (simulateQ (lazyImpl cellInput F T) (SphincsSecurity.QueryPause.traced obs C)).run
        (fun _ => Finset.univ)] * (cellCount cellInput F r.1.2.toList : ENNReal) := by
  have key := SphincsSecurity.QueryPause.traced_spmf_potential_le obs (lazyImpl cellInput F T)
    (fun h st => Consistent cellInput F h st)
    (fun h st hc input result hr => consistent_step cellInput F hinj T h st hc input result hr)
    (fun C' h st hc => by
      rw [← lazyRun_eq_simulate]
      exact probFailure_eq_zero' (UniformTableObservation.lazyRun_neverFail (aux T) (aux_neverFail T) _ st
        (hc.nonempty cellInput F)))
    (fun h _ => (marks M h.toList : ENNReal)) rate (fun h => cellCount cellInput F h.toList) (charge cellInput F)
    (by simp [cellCount]) (fun input answer tail => cellCount_step cellInput F input answer tail)
    (fun h st hc input => lazy_step cellInput F hinj T M rate hcell hother h st hc input)
    C 1 (fun _ => Finset.univ) (consistent_one cellInput F)
  simp only [one_mul] at key
  have h0 : marks M (1 : FreeMonoid Entry).toList = 0 := by
    simp [marks]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key
end Potential
end Enc.Lazy
end SigGolfCandidate.T3.Security.Wots
end
section
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
def EncodingInput (input : HashInput) : Prop :=
  ∃ (L : LeafAddr) (message : Digest × BitVec 96 × Digest) (counter : BitVec 32), input = encodingRow L message counter
def EncodingRow : Answers → T3.Spec.Domain → Prop
  | _, .inl (.inr input) => EncodingInput input
  | _, _ => False
noncomputable def encodingCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (EncodingRow s.answers (.inl (.inr e.1)))).length
namespace Enc
theorem counterSearch_first (T : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) :
    ∀ fuel start k digits, k < fuel →
      (∀ i < k, decode lay ((T (.inl (.inr (pad64 (encodingInput lay tree leaf message
        (BitVec.ofNat 32 (start + i))))))).extractLsb' 0 128) = none) →
      decode lay ((T (.inl (.inr (pad64 (encodingInput lay tree leaf message
        (BitVec.ofNat 32 (start + k))))))).extractLsb' 0 128) = some digits →
      evalWithAnswerFn T (counterSearch lay tree leaf message start fuel) =
        some (BitVec.ofNat 32 (start + k), digits) := by
  intro fuel
  induction fuel with
  | zero => intro _ k _ hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [counterSearch, evalWithAnswerFn_bind, eval_shortHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have := ih (start + 1) k digits (by omega)
          (fun i hi => by rw [show start + 1 + i = start + (i + 1) by omega]; exact hprev (i + 1) (by omega))
          (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hvalid)
        rw [show start + (k + 1) = start + 1 + k by omega]
        exact this
theorem reached_valid_reference {T : Answers} {L : LeafAddr} {input : HashInput} (hr : Reached T L input)
    {w : List Nat} (hw : decode L.lay (low (T (.inl (.inr input)))) = some w) :
    referenceInput T L = some input := by
  obtain ⟨c, hc, rfl, hprev⟩ := hr
  have hs : referenceSearch T L = some (BitVec.ofNat 32 c, w) := by
    unfold referenceSearch
    have := counterSearch_first T L.lay L.tree L.leaf (leafMsg T L) counterLimit 0 c w hc
      (fun i hi => by rw [Nat.zero_add]; exact hprev i hi)
      (by rw [Nat.zero_add]; exact hw)
    rw [Nat.zero_add] at this
    exact this
  unfold referenceInput
  rw [hs]
  rfl
def MatchEntry (T : Answers) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : Digest × BitVec 96 × Digest) (counter : BitVec 32),
    entry.1 = encodingRow (leafOf L) message counter ∧
      referenceInput T (leafOf L) ≠ some (encodingRow (leafOf L) message counter) ∧
      decode L.lay (low entry.2) = some (referenceDigits T (leafOf L))
theorem matchAt_iff (T : Answers) (trace : List Entry) :
    (∃ L : CanonGraph.LeafPos, EncodingMatchAt T trace (leafOf L)) ↔ ∃ entry ∈ trace, MatchEntry T entry := by
  constructor
  · rintro ⟨L, message, counter, answer, hmem, hne, hdec⟩
    exact ⟨_, hmem, L, message, counter, rfl, hne, hdec⟩
  · rintro ⟨⟨input, answer⟩, hmem, L, message, counter, rfl, hne, hdec⟩
    exact ⟨L, message, counter, answer, hmem, hne, hdec⟩
theorem matchEntry_cell_le (T : Answers) (e : EncIndex) :
    Pr[fun ans => MatchEntry T (encInput e, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (2 ^ 128 : ENNReal)⁻¹ := by
  classical
  let targets : Finset Digest := Finset.univ.filter fun d => decode e.1.lay d = some (referenceDigits T (leafOf e.1))
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact decode_some_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_mono
        rintro ans - ⟨L, message, counter, he, -, hdec⟩
        have hL : e = (L, message, counter) := encInput_injective he
        subst hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdec⟩
    _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
    _ ≤ 1 / (2 : ENNReal) ^ 128 := ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = (2 ^ 128 : ENNReal)⁻¹ := one_div _
theorem matchEntry_other (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x) :
    ¬ MatchEntry (eagerAnswers U privateTable pub) (x, eagerAnswers U privateTable pub (.inl (.inr x))) := by
  rintro ⟨L, message, counter, he, hne, hdec⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf L) x := by
    by_contra hfree
    exact hx ⟨(L, message, counter), by
      change ¬ Reached _ _ (encInput (L, message, counter))
      rw [show encInput (L, message, counter) = x from he.symm]
      exact hfree, he.symm⟩
  have href := reached_valid_reference hreached hdec
  exact hne (he ▸ href)
section Table
variable (adversary : AdversaryP) (q : Nat)
theorem publicUniverse_sub (adversary : AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem eager_ov_eq (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) =
      Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub)) (eagerAnswers U privateTable pub) y := by
  funext query
  rcases query with (n | x) | c
  · simp only [eagerAnswers, Lazy.overwrite]
  · by_cases hx : Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x
    · have hxU : x ∈ U := by
        obtain ⟨e, -, rfl⟩ := hx
        exact hU (encInput_short e)
      rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
      simp only [Lazy.overwrite, dif_pos hx]
      unfold ov
      have hx' : ∃ e, e ∈ freeSet (eagerAnswers U privateTable pub) ∧ encInput e = (⟨x, hxU⟩ : U).val := hx
      rw [dif_pos hx']
      rfl
    · simp only [Lazy.overwrite, dif_neg hx]
      by_cases hxU : x ∈ U
      · rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩, eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
        exact ov_other _ _ _ _ (fun e he heq => hx ⟨e, he, heq⟩)
      · rw [eagerAnswers_public_not_mem U _ _ x hxU, eagerAnswers_public_not_mem U _ _ x hxU]
  · simp only [eagerAnswers, Lazy.overwrite]
theorem probOutput_complete_univ' {ι : Type} [Fintype ι] [DecidableEq ι] (y : ι → HashOutput) :
    Pr[= y | complete (fun _ : ι => (Finset.univ : Finset HashOutput))] = PMF.uniformOfFintype (ι → HashOutput) y := by
  rw [complete_of_nonempty _ (fun _ => Finset.univ_nonempty), SPMF.probOutput_eq_apply, SPMF.liftM_apply,
    SphincsSecurity.Concrete.uniformTable_univ]
theorem uniformOfFintype_inst {α : Type} [Nonempty α] (i1 i2 : Fintype α) (y : α) :
    @PMF.uniformOfFintype α i1 _ y = @PMF.uniformOfFintype α i2 _ y := by
  rw [Subsingleton.elim i1 i2]
theorem probOutput_complete_univ {ι : Type} [Fintype ι] [DecidableEq ι] (iX : Fintype (ι → HashOutput))
    (y : ι → HashOutput) :
    Pr[= y | complete (fun _ : ι => (Finset.univ : Finset HashOutput))] =
      @PMF.uniformOfFintype (ι → HashOutput) iX _ y :=
  (probOutput_complete_univ' y).trans (uniformOfFintype_inst _ iX y)
theorem free_transfer [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (h : RefSample → ENNReal) (φ : List Entry → ENNReal)
    (hφ : ∀ y r, h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      φ (traceOf (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))).run
          (fun _ => Finset.univ)] * φ z.1.2.toList := by
  have hinner : ∀ y : freeSet (eagerAnswers U privateTable pub) → HashOutput,
      ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList := by
    intro y
    have hgame : referenceGame (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
        adversary q = referenceGame (eagerAnswers U privateTable pub) adversary q :=
      referenceGame_congr_honest (honest_ov U privateTable pub y) adversary q
    simp only [PrefixGame.liftM_apply, hφ, probOutput_evalSPMF]
    unfold offlineRun
    rw [hgame, ← eager_ov_eq U hU privateTable pub y]
    have hmap := Lazy.recorded_traced (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
      (referenceGame (eagerAnswers U privateTable pub) adversary q)
    rw [← tsum_probOutput_map_mul _ (fun r : SeedResult => (r.1, traceOf (eagerAnswers U privateTable
      (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) (fun z : Option (Bool × Nat) × List Entry => φ z.2),
      hmap, tsum_probOutput_map_mul]
  simp only [hinner]
  rw [← Lazy.lazyRun_eq_simulate,
    ← tsum_probOutput_map_mul _ Prod.fst (fun r : Option (Bool × Nat) × FreeMonoid Entry => φ r.2.toList),
    ← Lazy.eager_lazy, tsum_probOutput_bind_mul]
  simp only [probOutput_complete_univ (iX (freeSet (eagerAnswers U privateTable pub)))]
noncomputable def matchInd (s : RefSample) : ENNReal :=
  if ∃ L : CanonGraph.LeafPos, EncodingMatchAt s.answers s.trace (leafOf L) then 1 else 0
theorem marks_unit (P : Entry → Prop) (tr : List Entry) :
    (Lazy.marks (fun (_ : Unit) => P) tr : ENNReal) = if ∃ entry ∈ tr, P entry then 1 else 0 := by
  unfold Lazy.marks
  by_cases h : ∃ entry ∈ tr, P entry
  · rw [if_pos h, Finset.filter_true_of_mem (fun _ _ => h)]
    simp
  · rw [if_neg h, Finset.filter_false_of_mem (fun _ _ => h)]
    simp
theorem encodingMatchAt_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry)
    (L : CanonGraph.LeafPos) : EncodingMatchAt T' trace (leafOf L) ↔ EncodingMatchAt T trace (leafOf L) := by
  unfold EncodingMatchAt
  rw [referenceInput_congr_honest h, referenceDigits_congr_honest h]
theorem encodingCount_mkSample (T : Answers) (r : SeedResult) :
    (encodingCount (mkSample T r) : ENNReal) =
      (((traceOf T r.2).filter fun e => decide (EncodingInput e.1)).length : ENNReal) := rfl
theorem cellCount_le_encoding (F : Set EncIndex) (tr : List Entry) :
    Lazy.cellCount encInput F tr ≤ (tr.filter fun e => decide (EncodingInput e.1)).length := by
  unfold Lazy.cellCount
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  obtain ⟨x, -, hx⟩ := he
  exact ⟨_, _, _, hx.symm⟩
theorem free_match_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          matchInd (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) : ENNReal) := by
  rw [free_transfer adversary q iX U hU privateTable pub matchInd
      (fun tr => (Lazy.marks (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y r => by
        unfold matchInd mkSample
        rw [marks_unit]
        dsimp only
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((matchAt_iff _ _).mp
            (by simpa only [encodingMatchAt_congr (honest_ov U privateTable pub y)] using h1)) h2
        · exact absurd (by simpa only [encodingMatchAt_congr (honest_ov U privateTable pub y)] using
            (matchAt_iff _ _).mpr h2) h1
        · rfl),
    free_transfer adversary q iX U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_le encInput (freeSet (eagerAnswers U privateTable pub)) encInput_injective
    (eagerAnswers U privateTable pub) (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) _
    (fun e => by simpa only [Finset.univ_unique, Finset.sum_singleton] using
      matchEntry_cell_le (eagerAnswers U privateTable pub) e.val)
    (fun x hx _ => matchEntry_other U privateTable pub x hx) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Table
end Enc
end SigGolfCandidate.T3.Security.Wots
end
