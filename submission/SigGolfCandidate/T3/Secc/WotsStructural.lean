import SigGolfCandidate.T3.Secc.WotsStructuralVariant
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservationErasure
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTracePotential
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
import SigGolfCandidate.T3.Secc.WotsExtractChain

section





namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete.UniformTableObservation (lazyImpl lazyRun fixedImpl TableSpec)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def refObs : (q : RefWorld.Domain) → RefWorld.Range q → FreeMonoid Entry
  | .inl (.inr x), answer => FreeMonoid.of (x, answer)
  | .inl (.inl _), _ => 1
  | .inr _, _ => 1
theorem traceOf_cons_hash (T : Answers) (x : HashInput) (rest : List RefWorld.Domain) :
    traceOf T ((.inl (.inr x) : RefWorld.Domain) :: rest) = (x, T (.inl (.inr x))) :: traceOf T rest := rfl
theorem traceOf_cons_coin (T : Answers) (n : Nat) (rest : List RefWorld.Domain) :
    traceOf T ((.inl (.inl n) : RefWorld.Domain) :: rest) = traceOf T rest := rfl
theorem traceOf_cons_tick (T : Answers) (u : Unit) (rest : List RefWorld.Domain) :
    traceOf T ((.inr u : RefWorld.Domain) :: rest) = traceOf T rest := rfl
theorem recorded_traced {α : Type} (T : Answers) (C : OracleComp RefWorld α) :
    (fun run => (run.1, traceOf T run.2)) <$> simulateQ (refImpl T) (SphincsSecurity.QueryCap.recorded C) =
      (fun result => (result.1, result.2.toList)) <$>
        simulateQ (refImpl T) (SphincsSecurity.QueryPause.traced refObs C) := by
  induction C using OracleComp.inductionOn with
  | pure x =>
      simp only [SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.traced_pure,
        simulateQ_pure, map_pure]
      rfl
  | query_bind q next ih =>
      rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.traced_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_map, map_bind, simulateQ_pure]
      rcases q with (n | x) | u
      · refine bind_congr fun answer => ?_
        have h := ih answer
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_coin, refObs, one_mul] at h ⊢
        exact h
      · simp only [refImpl, pure_bind]
        have h := congrArg (Functor.map (fun p : α × List Entry => (p.1, (x, T (.inl (.inr x))) :: p.2)))
          (ih (T (.inl (.inr x))))
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_hash, refObs, FreeMonoid.toList_mul,
          FreeMonoid.toList_of, List.singleton_append] at h ⊢
        exact h
      · refine bind_congr fun answer => ?_
        have h := ih answer
        simp only [map_pure, bind_pure_comp, Functor.map_map, traceOf_cons_tick, refObs, one_mul] at h ⊢
        exact h
section Lazy
variable (Str : Finset HashInput)
abbrev LazySpec := RefWorld + TableSpec Str HashOutput
noncomputable def strTranslate : QueryImpl RefWorld (OracleComp (LazySpec Str))
  | .inl (.inl n) => liftM ((LazySpec Str).query (.inl (.inl (.inl n))))
  | .inl (.inr x) => if h : x ∈ Str then liftM ((LazySpec Str).query (.inr ⟨x, h⟩))
      else liftM ((LazySpec Str).query (.inl (.inl (.inr x))))
  | .inr u => liftM ((LazySpec Str).query (.inl (.inr u)))
noncomputable def lazyAux (T0 : Answers) : QueryImpl RefWorld SPMF := fun q => 𝒮[refImpl T0 q]
theorem uniform_complete :
    (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) =
      complete (fun _ : Str => (Finset.univ : Finset HashOutput)) := by
  rw [complete_of_nonempty _ (fun _ => Finset.univ_nonempty), SphincsSecurity.Concrete.uniformTable_univ]
variable (T : (Str → HashOutput) → Answers)
  (hstr : ∀ ρ x (hx : x ∈ Str), T ρ (.inl (.inr x)) = ρ ⟨x, hx⟩)
  (hout : ∀ ρ x, x ∉ Str → T ρ (.inl (.inr x)) = T (fun _ => 0) (.inl (.inr x)))
include hstr hout
theorem fixed_translate (ρ : Str → HashOutput) (q : RefWorld.Domain) :
    simulateQ (fixedImpl (lazyAux (T (fun _ => 0))) ρ) (strTranslate Str q) = 𝒮[refImpl (T ρ) q] := by
  rcases q with (n | x) | u
  · simp only [strTranslate, simulateQ_spec_query, fixedImpl, lazyAux]
    rfl
  · by_cases hx : x ∈ Str
    · simp only [strTranslate, dif_pos hx, simulateQ_spec_query, fixedImpl, refImpl, evalSPMF_pure, hstr ρ x hx]
    · simp only [strTranslate, dif_neg hx, simulateQ_spec_query, fixedImpl, lazyAux, refImpl, evalSPMF_pure,
        hout ρ x hx]
  · simp only [strTranslate, simulateQ_spec_query, fixedImpl, lazyAux]
    rfl
theorem fixed_run {α : Type} (ρ : Str → HashOutput) (C : OracleComp RefWorld α) :
    simulateQ (fixedImpl (lazyAux (T (fun _ => 0))) ρ) (simulateQ (strTranslate Str) C) =
      𝒮[simulateQ (refImpl (T ρ)) C] := by
  induction C using OracleComp.inductionOn with
  | pure x => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate Str T hstr hout]
theorem uniform_run {α : Type} (C : OracleComp RefWorld α) :
    ((liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) C]) =
      Prod.fst <$> lazyRun (lazyAux (T (fun _ => 0))) (simulateQ (strTranslate Str) C) (fun _ => Finset.univ) := by
  rw [uniform_complete Str]
  have h := SphincsSecurity.Concrete.UniformTableObservation.run_marginal (lazyAux (T (fun _ => 0)))
    (simulateQ (strTranslate Str) C) (fun _ : Str => (Finset.univ : Finset HashOutput)) (fun _ => Finset.univ_nonempty)
  simpa only [fixed_run Str T hstr hout] using h
end Lazy
section Potential
variable (Str : Finset HashInput) (T0 : Answers)
def TraceConsistent (trace : FreeMonoid Entry) (allowed : Str → Finset HashOutput) : Prop :=
  (∀ row : Str, ∀ answer, (row.val, answer) ∈ trace.toList → allowed row = {answer}) ∧
    ∀ row : Str, (∀ answer, (row.val, answer) ∉ trace.toList) → allowed row = Finset.univ
theorem traceConsistent_one : TraceConsistent Str 1 (fun _ => Finset.univ) := by
  constructor
  · intro row answer h
    simp at h
  · intro row _
    rfl
theorem TraceConsistent.outside {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (input : HashInput)
    (hi : input ∉ Str) (output : HashOutput) :
    TraceConsistent Str (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro row answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 row answer hentry
    · exact False.elim (hi (heq ▸ row.property))
  · intro row hfresh
    apply h.2 row
    intro answer hentry
    exact hfresh answer (by
      simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
      exact Or.inl hentry)
theorem TraceConsistent.disclose {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str) (output : HashOutput)
    (houtput : output ∈ allowed row) :
    TraceConsistent Str (trace * FreeMonoid.of (row.val, output))
      (SphincsSecurity.Concrete.discloseTableValue allowed row output) := by
  constructor
  · intro other answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton,
      Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, hans⟩
    · by_cases heq : other = row
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 row answer hentry) ▸ houtput)
        simp only [SphincsSecurity.Concrete.discloseTableValue, Function.update_self, heq]
      · rw [SphincsSecurity.Concrete.discloseTableValue, Function.update_of_ne heq]
        exact h.1 other answer hentry
    · have heq : other = row := Subtype.ext heq
      subst other
      rw [hans]
      exact Function.update_self row {output} allowed
  · intro other hfresh
    have heq : other ≠ row := by
      intro heq
      subst other
      exact hfresh output (by simp)
    rw [SphincsSecurity.Concrete.discloseTableValue, Function.update_of_ne heq]
    apply h.2 other
    intro answer hentry
    exact hfresh answer (by
      simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append]
      exact Or.inl hentry)
theorem TraceConsistent.cached_reply {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str)
    (previous output : HashOutput) (hp : (row.val, previous) ∈ trace.toList) (ho : cell (allowed row) output ≠ 0) :
    output = previous := by
  rw [h.1 row previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho
theorem TraceConsistent.new_reply_le {Str : Finset HashInput} {trace : FreeMonoid Entry}
    {allowed : Str → Finset HashOutput} (h : TraceConsistent Str trace allowed) (row : Str)
    (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] ≤
      Pr[event | cell Finset.univ] := by
  by_cases hfresh : ∀ output, (row.val, output) ∉ trace.toList
  · rw [h.2 row hfresh]
    exact probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (row.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (row.val, output) ∉ trace.toList | cell (allowed row)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply row previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le
noncomputable def lazyWorld : QueryImpl RefWorld (StateT (Str → Finset HashOutput) SPMF) :=
  (lazyImpl (lazyAux T0)) ∘ₛ (strTranslate Str)
theorem lazyRun_eq_simulate {α : Type} (C : OracleComp RefWorld α) (allowed : Str → Finset HashOutput) :
    lazyRun (lazyAux T0) (simulateQ (strTranslate Str) C) allowed = (simulateQ (lazyWorld Str T0) C).run allowed := by
  rw [lazyRun, lazyWorld, QueryImpl.simulateQ_compose]
theorem lazyWorld_hash_mem (x : HashInput) (hx : x ∈ Str) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inr x))).run allowed =
      (fun answer => (answer, SphincsSecurity.Concrete.discloseTableValue allowed ⟨x, hx⟩ answer)) <$>
        cell (allowed ⟨x, hx⟩) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, dif_pos hx, simulateQ_spec_query, lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyWorld_hash_out (x : HashInput) (hx : x ∉ Str) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inr x))).run allowed =
      (fun answer => (answer, allowed)) <$> lazyAux T0 (.inl (.inr x)) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, dif_neg hx, simulateQ_spec_query, lazyImpl,
    StateT.run_mk]
  rfl
theorem lazyWorld_coin (n : Nat) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inl (.inl n))).run allowed = (fun answer => (answer, allowed)) <$> lazyAux T0 (.inl (.inl n)) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, simulateQ_spec_query, lazyImpl, StateT.run_mk]
  rfl
theorem lazyWorld_tick (u : Unit) (allowed : Str → Finset HashOutput) :
    (lazyWorld Str T0 (.inr u)).run allowed = (fun answer => (answer, allowed)) <$> lazyAux T0 (.inr u) := by
  simp only [lazyWorld, QueryImpl.apply_compose, strTranslate, simulateQ_spec_query, lazyImpl, StateT.run_mk]
  rfl
theorem map_pair_nonzero {A B : Type} (p : SPMF A) (f : A → B) (r : A × B) (hr : ((fun a => (a, f a)) <$> p) r ≠ 0) :
    r.2 = f r.1 ∧ p r.1 ≠ 0 := by
  rw [← bind_pure_comp] at hr
  obtain ⟨a, ha, heq⟩ := (SphincsSecurity.Concrete.RetainedObservation.bind_nonzero _ _ _).mp hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
  subst r
  exact ⟨rfl, ha⟩
theorem lazyWorld_traceConsistent (allowed : Str → Finset HashOutput) (trace : FreeMonoid Entry)
    (h : TraceConsistent Str trace allowed) (q : RefWorld.Domain)
    (result : RefWorld.Range q × (Str → Finset HashOutput)) (hr : (lazyWorld Str T0 q).run allowed result ≠ 0) :
    TraceConsistent Str (trace * refObs q result.1) result.2 := by
  rcases q with (n | x) | u
  · rw [lazyWorld_coin] at hr
    obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
    rw [h2]
    simpa only [refObs, mul_one] using h
  · by_cases hx : x ∈ Str
    · rw [lazyWorld_hash_mem Str T0 x hx] at hr
      obtain ⟨h2, h1⟩ := map_pair_nonzero _ _ result hr
      rw [h2]
      have hin : result.1 ∈ allowed ⟨x, hx⟩ := by
        by_contra hn
        rw [cell_apply, if_neg hn] at h1
        exact h1 rfl
      exact h.disclose ⟨x, hx⟩ result.1 hin
    · rw [lazyWorld_hash_out Str T0 x hx] at hr
      obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
      rw [h2]
      exact h.outside x hx result.1
  · rw [lazyWorld_tick] at hr
    obtain ⟨h2, -⟩ := map_pair_nonzero _ (fun _ => allowed) result hr
    rw [h2]
    simpa only [refObs, mul_one] using h
variable (Hit : HashInput → HashOutput → Prop) (Charged : HashInput → Prop)
def Seen (trace : FreeMonoid Entry) : Prop := ∃ e ∈ trace.toList, Hit e.1 e.2
noncomputable def chargedCount (trace : FreeMonoid Entry) : Nat :=
  (trace.toList.filter fun e => decide (Charged e.1)).length
noncomputable def queryCharge : RefWorld.Domain → Nat
  | .inl (.inr x) => if Charged x then 1 else 0
  | _ => 0
theorem seen_one : ¬Seen Hit 1 := by simp [Seen]
theorem seen_mul_of (trace : FreeMonoid Entry) (e : Entry) :
    Seen Hit (trace * FreeMonoid.of e) ↔ Seen Hit trace ∨ Hit e.1 e.2 := by
  simp only [Seen, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append, List.mem_singleton, or_and_right,
    exists_or, exists_eq_left]
theorem chargedCount_one : chargedCount Charged 1 = 0 := rfl
theorem chargedCount_step (q : RefWorld.Domain) (answer : RefWorld.Range q) (tail : FreeMonoid Entry) :
    chargedCount Charged (refObs q answer * tail) = queryCharge Charged q + chargedCount Charged tail := by
  rcases q with (n | x) | u
  · simp [refObs, queryCharge, chargedCount]
  · by_cases hc : Charged x
    · simp [refObs, queryCharge, chargedCount, hc, Nat.add_comm]
    · simp [refObs, queryCharge, chargedCount, hc]
  · simp [refObs, queryCharge, chargedCount]
variable (rate : ENNReal) (hhit : ∀ x a, Hit x a → x ∈ Str)
  (hkernel : ∀ x, x ∈ Str → Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
    rate * (if Charged x then 1 else 0 : ENNReal))
include hhit hkernel in
theorem lazy_step_le (history : FreeMonoid Entry) (allowed : Str → Finset HashOutput)
    (hc : TraceConsistent Str history allowed) (q : RefWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorld Str T0 q).run allowed] *
      (if Seen Hit (history * refObs q result.1) then 1 else 0 : ENNReal)) ≤
      (if Seen Hit history then 1 else 0 : ENNReal) + rate * (queryCharge Charged q : ENNReal) := by
  by_cases hs : Seen Hit history
  · simp only [if_pos hs]
    refine le_add_right (le_trans (ENNReal.tsum_le_tsum fun result => mul_le_of_le_one_right' ?_) tsum_probOutput_le_one)
    split <;> simp
  · simp only [if_neg hs, zero_add, mul_ite, mul_one, mul_zero]
    rw [← probEvent_eq_tsum_ite]
    rcases q with (n | x) | u
    · have hz : Pr[fun result => Seen Hit (history * refObs (.inl (.inl n)) result.1) |
          (lazyWorld Str T0 (.inl (.inl n))).run allowed] = 0 :=
        probEvent_eq_zero fun result _ h => hs (by simpa only [refObs, mul_one] using h)
      rw [hz]
      exact bot_le
    · by_cases hx : x ∈ Str
      · rw [lazyWorld_hash_mem Str T0 x hx, probEvent_map]
        calc Pr[(fun result => Seen Hit (history * refObs (.inl (.inr x)) result.1)) ∘
              (fun answer => (answer, SphincsSecurity.Concrete.discloseTableValue allowed ⟨x, hx⟩ answer)) |
              cell (allowed ⟨x, hx⟩)]
            ≤ Pr[fun answer => Hit x answer ∧ ((⟨x, hx⟩ : Str).val, answer) ∉ history.toList |
              cell (allowed ⟨x, hx⟩)] := by
              apply probEvent_mono
              intro answer _ h
              change Seen Hit (history * FreeMonoid.of ((x, answer) : Entry)) at h
              rcases (seen_mul_of Hit history (x, answer)).mp h with h | h
              · exact absurd h hs
              · exact ⟨h, fun hmem => hs ⟨(x, answer), hmem, h⟩⟩
          _ ≤ Pr[Hit x | cell Finset.univ] := hc.new_reply_le ⟨x, hx⟩ (Hit x)
          _ ≤ rate * (queryCharge Charged (.inl (.inr x)) : ENNReal) := by
              have hk := hkernel x hx
              rw [cell, dif_pos Finset.univ_nonempty]
              change Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤ _
              refine hk.trans (le_of_eq ?_)
              simp only [queryCharge]
              split <;> simp
      · have hz : Pr[fun result => Seen Hit (history * refObs (.inl (.inr x)) result.1) |
            (lazyWorld Str T0 (.inl (.inr x))).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ h
          change Seen Hit (history * FreeMonoid.of ((x, result.1) : Entry)) at h
          rcases (seen_mul_of Hit history (x, result.1)).mp h with h | h
          · exact hs h
          · exact hx (hhit x result.1 h)
        rw [hz]
        exact bot_le
    · have hz : Pr[fun result => Seen Hit (history * refObs (.inr u) result.1) |
          (lazyWorld Str T0 (.inr u)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ h => hs (by simpa only [refObs, mul_one] using h)
      rw [hz]
      exact bot_le
end Potential
end SigGolfCandidate.T3.Security.Wots.Structural
namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableObservation (lazyImpl lazyRun fixedImpl TableSpec)
open SphincsSecurity.Concrete.UniformTableCompletion
attribute [local instance] Classical.propDecidable
theorem lazyAux_neverFail (T0 : Answers) (q : RefWorld.Domain) : NeverFail (lazyAux T0 q) :=
  ⟨probFailure_eq_zero (mx := refImpl T0 q)⟩
section Main
variable (Str : Finset HashInput) (T : (Str → HashOutput) → Answers)
  (hstr : ∀ ρ x (hx : x ∈ Str), T ρ (.inl (.inr x)) = ρ ⟨x, hx⟩)
  (hout : ∀ ρ x, x ∉ Str → T ρ (.inl (.inr x)) = T (fun _ => 0) (.inl (.inr x)))
  (Hit : HashInput → HashOutput → Prop) (Charged : HashInput → Prop) (rate : ENNReal)
  (hhit : ∀ x a, Hit x a → x ∈ Str)
  (hkernel : ∀ x, x ∈ Str → Pr[Hit x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
    rate * (if Charged x then 1 else 0 : ENNReal))
include hstr hout hhit hkernel
theorem lazy_seen_le {α : Type} (C : OracleComp RefWorld α) :
    Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs C)]] ≤
      rate * ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs C)]] *
          (chargedCount Charged r.2 : ENNReal) := by
  rw [uniform_run Str T hstr hout, lazyRun_eq_simulate, probEvent_map, tsum_probOutput_map_mul]
  have hpot := SphincsSecurity.QueryPause.traced_spmf_potential_le refObs (lazyWorld Str (T fun _ => 0))
    (fun history allowed => TraceConsistent Str history allowed ∧ ∀ row, (allowed row).Nonempty)
    (fun history allowed hi q result hr =>
      ⟨lazyWorld_traceConsistent Str (T fun _ => 0) allowed history hi.1 q result hr,
        SphincsSecurity.Concrete.UniformTableObservation.lazyRun_nonempty (lazyAux (T fun _ => 0))
          (strTranslate Str q) allowed hi.2 result hr⟩)
    (fun computation history allowed hi => by
      rw [← lazyRun_eq_simulate]
      exact probFailure_eq_zero' (SphincsSecurity.Concrete.UniformTableObservation.lazyRun_neverFail
        (lazyAux (T fun _ => 0)) (lazyAux_neverFail _) _ allowed hi.2))
    (fun history _ => if Seen Hit history then 1 else 0) rate (chargedCount Charged) (queryCharge Charged)
    (chargedCount_one Charged) (chargedCount_step Charged)
    (fun history allowed hi q => lazy_step_le Str (T fun _ => 0) Hit Charged rate hhit hkernel history allowed hi.1 q)
    C 1 (fun _ => Finset.univ) ⟨traceConsistent_one Str, fun _ => Finset.univ_nonempty⟩
  simp only [one_mul, if_neg (seen_one Hit), zero_add] at hpot
  rw [probEvent_eq_tsum_ite]
  simpa only [Function.comp_apply, mul_ite, mul_one, mul_zero] using hpot
end Main
end SigGolfCandidate.T3.Security.Wots.Structural
end

section


namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def OtherInput (answers : Answers) (input : HashInput) : Prop :=
  ∃ position, Extract.posOf input = some position ∧ position.Bounded ∧ WotsExtract.PosSource position ∧
    StructuralClass answers input position
def OtherQuery (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => OtherInput answers input
  | _ => False
noncomputable def otherCount (sample : RefSample) : Nat :=
  (sample.trace.filter fun e => decide (OtherQuery sample.answers (.inl (.inr e.1)))).length
def TraceInUniverse (adversary : AdversaryP) (q : Nat) : Prop :=
  ∀ sample ∈ (referenceExperiment adversary q).support, ∀ entry ∈ sample.trace,
    entry.1 ∈ referenceInputs adversary
def StructuralHitIn (inputs : Finset HashInput) (answers : Answers) (trace : List Entry) : Prop :=
  ∃ position input answer, (input, answer) ∈ trace ∧ input ∈ inputs ∧ Extract.posOf input = some position ∧
    position.Bounded ∧ WotsExtract.PosSource position ∧ StructuralClass answers input position ∧
    HashHit answers (Extract.honestInput answers position) input
namespace Structural
open CanonGraph (Node Labels Secrets OtherHalves cell programmed canonInputs privateEquiv)
theorem exists_node_of_posSource {p : Extract.Pos} (h : WotsExtract.PosSource p) : ∃ node : Node, node.toPos = p := by
  apply CanonGraph.exists_toPos
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
      have hc := Extract.chainCount_le lay
      exact ⟨h1, by omega, by omega, by omega⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := h
      have hh : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      exact ⟨h1, by omega⟩
  | node lay tree level nd => exact h
  | forest index => exact h
  | ftsLeaf index coord leaf => exact h
  | ftsNode index coord level nd => exact h
theorem structuralClass_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') {x : HashInput}
    {p : Extract.Pos} (hpos : Extract.posOf x = some p) (hsrc : WotsExtract.PosSource p) :
    StructuralClass T x p ↔ StructuralClass T' x p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨htree, hleaf, -, -⟩ := hsrc
      have key : ∀ (a : ChainAddr) (step' : Nat),
          Extract.posOf x = some (.chain a.key.lay a.key.tree a.key.leaf a.chain step') → depth T a = depth T' a := by
        intro a step' h
        rw [hpos] at h
        simp only [Option.some.injEq, Extract.Pos.chain.injEq] at h
        obtain ⟨hl, ht, hlf, -, -⟩ := h
        exact depth_variant hv a (by rw [← ht]; exact htree) (by rw [← hlf, ← hl]; exact hleaf)
      change OtherChainRow T x ↔ OtherChainRow T' x
      constructor
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [← key a step' h]; exact hd)⟩
      · rintro ⟨a, step', h, hc⟩
        exact ⟨a, step', h, hc.imp id (fun hd => by rw [key a step' h]; exact hd)⟩
  | leaf => exact Iff.rfl
  | node => exact Iff.rfl
  | forest => exact Iff.rfl
  | ftsLeaf => exact Iff.rfl
  | ftsNode => exact Iff.rfl
theorem otherInput_variant {labels : Labels} {T T' : Answers} (hv : Variant labels T T') (x : HashInput) :
    OtherInput T x ↔ OtherInput T' x := by
  constructor
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mp hc⟩
  · rintro ⟨p, hpos, hb, hsrc, hc⟩
    exact ⟨p, hpos, hb, hsrc, (structuralClass_variant hv hpos hsrc).mpr hc⟩
section Fixed
variable (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets) (o : OtherHalves) (labels : Labels)
noncomputable def strRows : Finset HashInput :=
  V.filter fun x => ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels
theorem mem_strRows (x : HashInput) :
    x ∈ strRows V s labels ↔ x ∈ V ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ x ≠ cell s node labels :=
  Finset.mem_filter
theorem strRows_not_cell {x : HashInput} (hx : x ∈ strRows V s labels) (node : Node) : x ≠ cell s node labels := by
  obtain ⟨-, node₀, hpos, hne⟩ := (mem_strRows V s labels x).mp hx
  intro heq
  have := CanonGraph.cell_eq_of_posOf s labels hpos heq
  subst this
  exact hne heq
def strEmbed : strRows V s labels → V := fun x => ⟨x.val, ((mem_strRows V s labels x.val).mp x.property).1⟩
theorem strEmbed_injective : Function.Injective (strEmbed V s labels) := by
  intro a b h
  exact Subtype.ext (congrArg (fun y : V => y.val) h)
abbrev Rest := SphincsSecurity.Concrete.UniformTableSplit.Outside (strEmbed V s labels) → HashOutput
noncomputable def strTable (rest : Rest V s labels) (ρ : strRows V s labels → HashOutput) : Answers :=
  eagerAnswers V (privateEquiv.symm (s, o))
    (programmed V hU s labels
      (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest))
variable (rest : Rest V s labels)
theorem strTable_eq_canon (ρ : strRows V s labels → HashOutput) :
    strTable V hU s o labels rest ρ = CanonGraph.eagerAnswers (privateEquiv.symm (s, o)) V
      (programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)) := by
  funext query
  rcases query with (n | x) | c <;> rfl
theorem strTable_agrees (ρ : strRows V s labels → HashOutput) :
    CanonGraph.Agrees (strTable V hU s o labels rest ρ) labels := by
  rw [strTable_eq_canon]
  exact CanonGraph.eager_programmed_agrees V hU s o labels _
theorem secretsOf_strTable (ρ : strRows V s labels → HashOutput) :
    CanonGraph.secretsOf (strTable V hU s o labels rest ρ) = s := by
  rw [strTable_eq_canon, CanonGraph.secretsOf_eager, CanonGraph.privateSecrets_symm]
theorem strTable_public_mem (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ V) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) =
      programmed V hU s labels
        (SphincsSecurity.Concrete.UniformTableSplit.join (strEmbed V s labels) (strEmbed_injective V s labels) ρ rest)
        ⟨x, hx⟩ :=
  SphincsSecurity.Concrete.finiteHashAnswer_none ∅ V _ x hx rfl
theorem strTable_str (ρ : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∈ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = ρ ⟨x, hx⟩ := by
  have hV := ((mem_strRows V s labels x).mp hx).1
  rw [strTable_public_mem V hU s o labels rest ρ x hV,
    CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ (strRows_not_cell V s labels hx)]
  exact SphincsSecurity.Concrete.UniformTableSplit.join_embed (strEmbed V s labels) (strEmbed_injective V s labels)
    ρ rest ⟨x, hx⟩
theorem strTable_out (ρ ρ' : strRows V s labels → HashOutput) (x : HashInput) (hx : x ∉ strRows V s labels) :
    strTable V hU s o labels rest ρ (.inl (.inr x)) = strTable V hU s o labels rest ρ' (.inl (.inr x)) := by
  by_cases hV : x ∈ V
  · rw [strTable_public_mem V hU s o labels rest ρ x hV, strTable_public_mem V hU s o labels rest ρ' x hV]
    by_cases hcell : ∃ node, x = cell s node labels
    · obtain ⟨node, rfl⟩ := hcell
      have he : (⟨cell s node labels, hV⟩ : V) = CanonGraph.cellIn V hU s node labels := rfl
      rw [he, CanonGraph.programmed_at, CanonGraph.programmed_at]
    · have hn : ∀ node, x ≠ cell s node labels := fun node h => hcell ⟨node, h⟩
      rw [CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn,
        CanonGraph.programmed_other V hU s labels _ ⟨x, hV⟩ hn]
      have hout : (⟨x, hV⟩ : V) ∉ Set.range (strEmbed V s labels) := by
        rintro ⟨y, hy⟩
        apply hx
        have : y.val = x := congrArg Subtype.val hy
        rw [← this]
        exact y.property
      exact (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ rest ⟨⟨x, hV⟩, hout⟩).trans
        (SphincsSecurity.Concrete.UniformTableSplit.join_outside _ _ ρ' rest ⟨⟨x, hV⟩, hout⟩).symm
  · change SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x = SphincsSecurity.Concrete.finiteHashAnswer ∅ V _ x
    simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hV]
theorem strTable_variant (ρ ρ' : strRows V s labels → HashOutput) :
    Variant labels (strTable V hU s o labels rest ρ) (strTable V hU s o labels rest ρ') where
  agrees := strTable_agrees V hU s o labels rest ρ
  coin := fun _ => rfl
  priv := fun _ => rfl
  pub := fun x hx => by
    apply strTable_out V hU s o labels rest ρ ρ' x
    intro hmem
    obtain ⟨-, node, hpos, hne⟩ := (mem_strRows V s labels x).mp hmem
    have := hx node hpos
    rw [secretsOf_strTable] at this
    exact hne this
def strHit (T0 : Answers) (x : HashInput) (a : HashOutput) : Prop :=
  x ∈ strRows V s labels ∧ OtherInput T0 x ∧ ∃ node : Node, Extract.posOf x = some node.toPos ∧ low a = low (labels node)
theorem card_digest : (Fintype.card SphincsSecurity.Digest : ℝ≥0∞) = 2 ^ 128 := by
  simp [SphincsSecurity.digestBits]
  norm_num
theorem strHit_kernel (T0 : Answers) (x : HashInput) (hx : x ∈ strRows V s labels) :
    Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (if OtherInput T0 x then 1 else 0 : ℝ≥0∞) := by
  by_cases hO : OtherInput T0 x
  · rw [if_pos hO, mul_one]
    obtain ⟨-, node₀, hpos₀, -⟩ := (mem_strRows V s labels x).mp hx
    calc Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)]
        ≤ Pr[fun a : HashOutput => SphincsSecurity.truncateHash a = low (labels node₀) |
            PMF.uniformOfFintype HashOutput] := by
          apply probEvent_mono
          rintro a - ⟨-, -, node, hpos, hlow⟩
          have hn : node = node₀ :=
            CanonGraph.toPos_injective (Option.some.inj (hpos.symm.trans hpos₀))
          subst hn
          exact hlow
      _ = (2 ^ 128 : ℝ≥0∞)⁻¹ := by
          have h := SphincsSecurity.Concrete.HiddenLabelProbe.prob_truncate_eq (low (labels node₀))
          rw [card_digest] at h
          exact h
  · have hz : Pr[strHit V s labels T0 x | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => hO h.2.1
    rw [hz]
    exact bot_le
theorem mem_traceOf {T : Answers} {qs : List RefWorld.Domain} {e : Entry} (he : e ∈ traceOf T qs) :
    e.2 = T (.inl (.inr e.1)) := by
  unfold traceOf at he
  obtain ⟨query, -, hq⟩ := List.mem_filterMap.mp he
  rcases query with (n | x) | u
  · simp at hq
  · simp only [Option.some.injEq] at hq
    rw [← hq]
  · simp at hq
theorem hit_bridge (ρ : strRows V s labels → HashOutput) (qs : List RefWorld.Domain)
    (h : StructuralHitIn V (strTable V hU s o labels rest ρ) (traceOf (strTable V hU s o labels rest ρ) qs)) :
    ∃ e ∈ traceOf (strTable V hU s o labels rest ρ) qs,
      strHit V s labels (strTable V hU s o labels rest (fun _ => 0)) e.1 e.2 := by
  obtain ⟨p, x, a, hmem, hxV, hpos, hb, hsrc, hc, hne, hlow⟩ := h
  refine ⟨(x, a), hmem, ?_, ?_, ?_⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    rw [CanonGraph.honestInput_eq (strTable_agrees V hU s o labels rest ρ), secretsOf_strTable] at hne
    exact (mem_strRows V s labels x).mpr ⟨hxV, node, hpos, hne⟩
  · exact ⟨p, hpos, hb, hsrc, (structuralClass_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0))
      hpos hsrc).mp hc⟩
  · obtain ⟨node, rfl⟩ := exists_node_of_posSource hsrc
    refine ⟨node, hpos, ?_⟩
    have ha : a = strTable V hU s o labels rest ρ (.inl (.inr x)) := mem_traceOf hmem
    rw [CanonGraph.honest_answer (strTable_agrees V hU s o labels rest ρ)] at hlow
    change low a = low (labels node)
    rw [ha]
    exact hlow
theorem count_bridge (ρ : strRows V s labels → HashOutput) (pk : Digest) (trace : List Entry) :
    otherCount ⟨strTable V hU s o labels rest ρ, pk, trace⟩ =
      (trace.filter fun e => decide (OtherInput (strTable V hU s o labels rest (fun _ => 0)) e.1)).length := by
  unfold otherCount
  congr 1
  apply List.filter_congr
  intro e _
  exact decide_eq_decide.mpr (otherInput_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)) e.1)
end Fixed
noncomputable def sampleComp (adversary : AdversaryP) (q : Nat) (T : Answers) : ProbComp RefSample :=
  (fun run => (⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩ : RefSample)) <$> offlineRun T adversary q
section Bound
variable (adversary : AdversaryP) (q : Nat) (V : Finset HashInput) (hU : canonInputs ⊆ V) (s : Secrets)
  (o : OtherHalves) (labels : Labels) (rest : Rest V s labels)
theorem sampleComp_recorded (ρ : strRows V s labels → HashOutput) :
    𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)] =
      (fun run => (⟨strTable V hU s o labels rest ρ, (evalWithAnswerFn (strTable V hU s o labels rest ρ) keygen).1,
          traceOf (strTable V hU s o labels rest ρ) run.2⟩ : RefSample)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  unfold sampleComp offlineRun
  rw [referenceGame_variant (strTable_variant V hU s o labels rest ρ (fun _ => 0)), evalSPMF_map]
theorem recorded_pair (ρ : strRows V s labels → HashOutput) :
    (fun run => (run.1, traceOf (strTable V hU s o labels rest ρ) run.2)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryCap.recorded (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] =
      (fun r => (r.1, r.2.toList)) <$>
        𝒮[simulateQ (refImpl (strTable V hU s o labels rest ρ))
          (SphincsSecurity.QueryPause.traced refObs (referenceGame (strTable V hU s o labels rest (fun _ => 0)) adversary q))] := by
  rw [← evalSPMF_map, ← evalSPMF_map, recorded_traced]
theorem fixed_bound :
    Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (strTable V hU s o labels rest ρ)]] * (otherCount sample : ℝ≥0∞) := by
  set T := strTable V hU s o labels rest with hT
  set G0 := referenceGame (T fun _ => 0) adversary q with hG0
  set Hit := strHit V s labels (T fun _ => 0) with hHit
  set Charged := OtherInput (T fun _ => 0) with hCharged
  have hlazy := lazy_seen_le (strRows V s labels) T (fun ρ x hx => strTable_str V hU s o labels rest ρ x hx)
    (fun ρ x hx => strTable_out V hU s o labels rest ρ (fun _ => 0) x hx) Hit Charged (2 ^ 128 : ℝ≥0∞)⁻¹
    (fun x a h => h.1) (fun x hx => strHit_kernel V s labels (T fun _ => 0) x hx) G0
  have hevent : Pr[fun sample => StructuralHitIn V sample.answers sample.trace |
        (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] ≤
      Pr[fun r => Seen Hit r.2 | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul' le_rfl ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, probEvent_map]
    have hpair := recorded_pair adversary q V hU s o labels rest ρ
    have hseen : Pr[fun r => Seen Hit r.2 |
        𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] =
        Pr[fun z => ∃ e ∈ z.2, Hit e.1 e.2 | (fun run => (run.1, traceOf (T ρ) run.2)) <$>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryCap.recorded G0)]] := by
      rw [hpair, probEvent_map]
      rfl
    rw [hseen, probEvent_map]
    apply probEvent_mono
    intro run _ h
    exact hit_bridge V hU s o labels rest ρ run.2 h
  have hcount : (∑' sample,
        Pr[= sample | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[sampleComp adversary q (T ρ)]] * (otherCount sample : ℝ≥0∞)) =
      ∑' r, Pr[= r | (liftM (PMF.uniformOfFintype (strRows V s labels → HashOutput)) : SPMF _) >>= fun ρ =>
          𝒮[simulateQ (refImpl (T ρ)) (SphincsSecurity.QueryPause.traced refObs G0)]] *
            (chargedCount Charged r.2 : ℝ≥0∞) := by
    rw [tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
    refine tsum_congr fun ρ => congrArg _ ?_
    rw [sampleComp_recorded adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    have hA : ∀ run : Option (Bool × Nat) × List RefWorld.Domain,
        (otherCount (⟨T ρ, (evalWithAnswerFn (T ρ) keygen).1, traceOf (T ρ) run.2⟩ : RefSample) : ℝ≥0∞) =
          (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞))
            ((fun run => (run.1, traceOf (T ρ) run.2)) run) := by
      intro run
      rw [count_bridge V hU s o labels rest ρ]
    refine (tsum_congr fun run => congrArg _ (hA run)).trans ?_
    rw [← tsum_probOutput_map_mul _ (fun run : Option (Bool × Nat) × List RefWorld.Domain =>
        (run.1, traceOf (T ρ) run.2))
      (fun z : Option (Bool × Nat) × List Entry => ((z.2.filter fun e => decide (Charged e.1)).length : ℝ≥0∞)),
      recorded_pair adversary q V hU s o labels rest ρ, tsum_probOutput_map_mul]
    rfl
  rw [hcount]
  exact hevent.trans hlazy
end Bound
def BoundOn (V : Finset HashInput) (p : SPMF RefSample) : Prop :=
  Pr[fun sample => StructuralHitIn V sample.answers sample.trace | p] ≤
    (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | p] * (otherCount sample : ℝ≥0∞)
theorem boundOn_bind {X : Type} (V : Finset HashInput) (μ : SPMF X) (K : X → SPMF RefSample)
    (h : ∀ x, BoundOn V (K x)) : BoundOn V (μ >>= K) := by
  unfold BoundOn
  rw [probEvent_bind_eq_tsum, tsum_probOutput_bind_mul]
  calc (∑' x, Pr[= x | μ] * Pr[fun sample => StructuralHitIn V sample.answers sample.trace | K x])
      ≤ ∑' x, Pr[= x | μ] * ((2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, Pr[= sample | K x] * (otherCount sample : ℝ≥0∞)) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by simp only [mul_left_comm _ (2 ^ 128 : ℝ≥0∞)⁻¹, ENNReal.tsum_mul_left]
theorem uniform_split_bind {Index Cell R : Type} [Fintype Index] [Fintype Cell] [DecidableEq Index]
    [DecidableEq Cell] (embed : Index → Cell) (hinj : Function.Injective embed) (g : (Cell → HashOutput) → SPMF R) :
    ((liftM (PMF.uniformOfFintype (Cell → HashOutput)) : SPMF (Cell → HashOutput)) >>= g) =
      ((liftM (PMF.uniformOfFintype (SphincsSecurity.Concrete.UniformTableSplit.Outside embed → HashOutput)) :
          SPMF _) >>= fun rest =>
        (liftM (PMF.uniformOfFintype (Index → HashOutput)) : SPMF (Index → HashOutput)) >>= fun ρ =>
          g (SphincsSecurity.Concrete.UniformTableSplit.join embed hinj ρ rest)) := by
  rw [SphincsSecurity.Concrete.UniformTableSplit.uniform_join embed hinj, ← PMF.monad_bind_eq_bind, liftM_bind]
  simp only [← PMF.monad_map_eq_map, liftM_map, bind_assoc, bind_map_left]
  exact SphincsSecurity.Concrete.RetainedObservation.bind_comm _ _ _
section Assembly
noncomputable local instance instFintypeCoordinate_wotsStructural : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsStructural : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
theorem referenceInputs_canon (adversary : AdversaryP) : canonInputs ⊆ referenceInputs adversary := by
  unfold referenceInputs
  exact CanonGraph.canonInputs_subset_publicUniverse.trans Finset.subset_union_left
theorem tables_bind_spmf {R : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp R) :
    ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun pub => 𝒮[next pt pub]) =
    ((liftM (PMF.uniformOfFintype Secrets) : SPMF _) >>= fun s =>
      (liftM (PMF.uniformOfFintype OtherHalves) : SPMF _) >>= fun o =>
      (liftM (PMF.uniformOfFintype Labels) : SPMF _) >>= fun labels =>
      (liftM (PMF.uniformOfFintype (U → HashOutput)) : SPMF _) >>= fun r =>
        𝒮[next (privateEquiv.symm (s, o)) (programmed U hU s labels r)]) := by
  have h := CanonGraph.tables_bind U hU next
  simp only [evalSPMF_bind, evalSPMF_uniformSample] at h
  exact h
theorem referenceComp_spmf (adversary : AdversaryP) (q : Nat) :
    𝒮[referenceComp adversary q] =
      ((liftM (PMF.uniformOfFintype FullGame.FullTable) : SPMF _) >>= fun pt =>
        (liftM (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)) : SPMF _) >>= fun pub =>
          𝒮[sampleComp adversary q (eagerAnswers (referenceInputs adversary) pt pub)]) := by
  unfold referenceComp
  simp only [evalSPMF_bind, evalSPMF_uniformSample]
  rfl
theorem referenceComp_bound (adversary : AdversaryP) (q : Nat) :
    BoundOn (referenceInputs adversary) 𝒮[referenceComp adversary q] := by
  rw [referenceComp_spmf, tables_bind_spmf _ (referenceInputs_canon adversary)]
  refine boundOn_bind _ _ _ fun s => boundOn_bind _ _ _ fun o => boundOn_bind _ _ _ fun labels => ?_
  rw [uniform_split_bind (strEmbed (referenceInputs adversary) s labels)
    (strEmbed_injective (referenceInputs adversary) s labels)]
  refine boundOn_bind _ _ _ fun rest => ?_
  exact fixed_bound adversary q (referenceInputs adversary) (referenceInputs_canon adversary) s o labels rest
end Assembly
end Structural
theorem liftM_pmf_apply {α : Type} (p : ProbComp α) (x : α) : (liftM p : PMF α) x = Pr[= x | 𝒮[p]] := by
  rw [← PMF.probOutput_eq_apply]
  rfl
theorem probEvent_liftM_pmf {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | 𝒮[p]] := rfl
theorem probEvent_liftM_pmf' {α : Type} (p : ProbComp α) (E : α → Prop) :
    Pr[E | (liftM p : PMF α)] = Pr[E | p] := rfl
theorem mem_support_liftM_pmf {α : Type} (p : ProbComp α) (x : α) (hx : x ∈ support p) :
    x ∈ (liftM p : PMF α).support := by
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply]
  change Pr[= x | p] ≠ 0
  exact (mem_support_iff _ _).mp hx
theorem referenceExperiment_eq (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = liftM (referenceComp adversary q) := rfl
theorem reference_structural_in_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun sample => StructuralHitIn (referenceInputs adversary) sample.answers sample.trace |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  have h := Structural.referenceComp_bound adversary q
  unfold Structural.BoundOn at h
  rw [referenceExperiment_eq, probEvent_liftM_pmf]
  simp only [liftM_pmf_apply]
  exact h
theorem reference_structural_le (adversary : AdversaryP) (q : Nat) (hV : TraceInUniverse adversary q) :
    Pr[fun sample => WotsExtract.StructuralHitSrc sample.answers sample.trace | referenceExperiment adversary q] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑' sample, referenceExperiment adversary q sample * (otherCount sample : ℝ≥0∞) := by
  refine le_trans ?_ (reference_structural_in_le adversary q)
  rw [referenceExperiment_eq, probEvent_liftM_pmf', probEvent_liftM_pmf']
  apply probEvent_mono
  intro sample hs h
  have hsupp : sample ∈ (referenceExperiment adversary q).support := by
    rw [referenceExperiment_eq]
    exact mem_support_liftM_pmf _ sample hs
  obtain ⟨position, input, answer, hmem, hpos, hb, hsrc, hc, hhit⟩ := h
  exact ⟨position, input, answer, hmem, hV sample hsupp (input, answer) hmem, hpos, hb, hsrc, hc, hhit⟩
end SigGolfCandidate.T3.Security.Wots
end
