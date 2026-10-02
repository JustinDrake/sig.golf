import SigGolfCandidate.T3.Secc.WotsStructuralVariant
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservationErasure
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTracePotential
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation

/-!
# Stream S (3): lazily sampled structural rows in R3's world

Generic part of the structural bound (BP-A §1.5 "Structural", record `StructuralOracleObservation` /
`StructuralTraceCache` / `StructuralMatchAccumulation`, adapted to R3's world `RefWorld = coins + hash + ticks`).

Setting: a finite set `Str` of public rows and tables `T ρ` (`ρ : Str → HashOutput`) that answer a row of `Str` by `ρ`
and every other public input independently of `ρ`. A fixed R3 program `C` is run in the world `refImpl (T ρ)` with `ρ`
uniform. Its trace is observed (`refObs`: hash queries with their answers).

* `uniform_run`: sampling `ρ` up front = answering `Str` rows lazily (pinned `UniformTableObservation.run_marginal`).
* `lazy_seen_le`: for an entry predicate `Entry` that only fires on `Str` rows, with a per-row kernel
  `Pr[Entry x · | uniform] ≤ rate · [Charged x]`, `Pr[some trace entry satisfies Entry] ≤ rate · E[#charged entries]`
  (pinned potential `QueryPause.traced_spmf_potential_le`; a cached row repeats its earlier answer, so only fresh rows
  can create a new entry).
* `recorded_traced`: R3's recorded queries with their table answers (`traceOf`) are the observed trace.
-/

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

/-! ## Observed traces of R3 programs -/

/-- R3's observation: a hash query with its answer; coins and ticks are not observed. -/
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

/-- **Recorded = observed**: R3's recorded queries, read with their table answers, are the observed trace. -/
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

/-! ## The lazy table of structural rows -/

section Lazy
variable (Str : Finset HashInput)

/-- R3's world with the rows of `Str` answered by a separate table oracle. -/
abbrev LazySpec := RefWorld + TableSpec Str HashOutput

/-- Route a hash query on a row of `Str` to the table oracle; forward everything else. -/
noncomputable def strTranslate : QueryImpl RefWorld (OracleComp (LazySpec Str))
  | .inl (.inl n) => liftM ((LazySpec Str).query (.inl (.inl (.inl n))))
  | .inl (.inr x) => if h : x ∈ Str then liftM ((LazySpec Str).query (.inr ⟨x, h⟩))
      else liftM ((LazySpec Str).query (.inl (.inl (.inr x))))
  | .inr u => liftM ((LazySpec Str).query (.inl (.inr u)))

/-- The forwarded part of R3's world, answered by a fixed table. -/
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

/-- **Eager = lazy**: sampling the structural rows up front is answering them lazily. -/
theorem uniform_run {α : Type} (C : OracleComp RefWorld α) :
    ((liftM (PMF.uniformOfFintype (Str → HashOutput)) : SPMF (Str → HashOutput)) >>= fun ρ =>
        𝒮[simulateQ (refImpl (T ρ)) C]) =
      Prod.fst <$> lazyRun (lazyAux (T (fun _ => 0))) (simulateQ (strTranslate Str) C) (fun _ => Finset.univ) := by
  rw [uniform_complete Str]
  have h := SphincsSecurity.Concrete.UniformTableObservation.run_marginal (lazyAux (T (fun _ => 0)))
    (simulateQ (strTranslate Str) C) (fun _ : Str => (Finset.univ : Finset HashOutput)) (fun _ => Finset.univ_nonempty)
  simpa only [fixed_run Str T hstr hout] using h

end Lazy

/-! ## Trace consistency of the lazy table -/

section Potential
variable (Str : Finset HashInput) (T0 : Answers)

/-- Observed rows of `Str` are disclosed with their observed answer; unobserved rows are unconstrained. -/
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

/-- R3's world with the `Str` rows sampled lazily (state: allowed answers per row). -/
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

/-! ## The potential argument -/

variable (Hit : HashInput → HashOutput → Prop) (Charged : HashInput → Prop)

/-- Some observed entry is a hit. -/
def Seen (trace : FreeMonoid Entry) : Prop := ∃ e ∈ trace.toList, Hit e.1 e.2

/-- Number of observed entries on charged inputs. -/
noncomputable def chargedCount (trace : FreeMonoid Entry) : Nat :=
  (trace.toList.filter fun e => decide (Charged e.1)).length

/-- Charge of one R3 query: one unit for a charged hash input. -/
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
/-- **One query of the lazy world**: a new hit needs a fresh charged `Str` row (`2^-128` kernel). -/
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

/-- **Structural potential bound**: with uniform `Str` rows, the probability that R3's observed trace has a hit is at
most `rate` times the expected number of charged entries. -/
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
