import SigGolfCandidate.Bridge.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Random-oracle tools for the distribution transfers

* `run'_relabel_on` : the lazy random oracle is invariant under a relabeling that is injective on the queried set
  (MACH-PLAN §1.3; the probe `checks/MachPlanRelabel.lean`).
* `randomOracle_congr` : two computations that agree under **every** fixed answer function have the same output law
  under the lazy random oracle, even on an infinite query domain: every computation over a finite answer type has a
  finite query set (`finite_query_domain`), the relabeling onto that finite set is lazy = eager
  (`evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable`), and eager evaluation is pointwise.
* `foldAll` (five-layer `Final/RO`): run programs in sequence against one oracle and conjoin their outputs.
-/

open OracleSpec OracleComp SigGolfCandidate.Bridge

namespace SigGolfCandidate.T3M.Final

section relabel
variable {ι ι' R : Type} [DecidableEq ι] [DecidableEq ι'] [SampleableType R]

theorem run'_relabel_on (enc : ι' → ι) (S : Set ι') (henc : Set.InjOn enc S) {α : Type}
    (P : OracleComp (ι' →ₒ R) α) (hP : AllQ (· ∈ S) P)
    (cO : QueryCache (ι' →ₒ R)) (cA : QueryCache (ι →ₒ R)) (hc : ∀ x ∈ S, cO x = cA (enc x)) :
    (simulateQ randomOracle P).run' cO = (simulateQ randomOracle (relabel enc P)).run' cA := by
  induction P using OracleComp.inductionOn generalizing cO cA with
  | pure x => rfl
  | query_bind x k ih =>
    rw [allQ_query_bind] at hP
    obtain ⟨hxS, hk⟩ := hP
    rw [relabel_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rw [randomOracle.run_eq, randomOracle.run_eq]
    have hx := hc x hxS
    have hrel : ∀ u, ∀ y ∈ S, (cO.cacheQuery x u) y = (cA.cacheQuery (enc x) u) (enc y) := by
      intro u y hy
      by_cases hyx : y = x
      · subst hyx; simp [QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ hyx,
          QueryCache.cacheQuery_of_ne _ _ (fun h => hyx (henc hy hxS h))]
        exact hc y hy
    revert hx
    cases cO x <;> cases cA (enc x) <;> intro hx <;> simp at hx
    · simp only [bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      have := ih u (hk u) _ _ (hrel u)
      simpa [StateT.run'_eq] using this
    · subst hx
      simp only [pure_bind]
      rename_i u
      have := ih u (hk u) cO cA hc
      simpa [StateT.run'_eq] using this

end relabel

section congr

theorem allQ_mono {ι R α : Type} {P Q : ι → Prop} (h : ∀ x, P x → Q x) :
    ∀ {p : OracleComp (ι →ₒ R) α}, AllQ P p → AllQ Q p := by
  intro p hp
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [allQ_query_bind] at hp ⊢
    exact ⟨h t hp.1, fun u => ih u (hp.2 u)⟩

/-- Every computation over a finite answer type has a finite query set. -/
theorem finite_query_domain {D R α : Type} [DecidableEq D] [Fintype R] (p : OracleComp (D →ₒ R) α) :
    ∃ s : Finset D, AllQ (· ∈ s) p := by
  classical
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨∅, trivial⟩
  | query_bind t k ih =>
    choose sets hsets using ih
    refine ⟨insert t (Finset.univ.biUnion sets), ?_⟩
    rw [allQ_query_bind]
    refine ⟨Finset.mem_insert_self _ _, fun u => ?_⟩
    exact allQ_mono (fun y hy => Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hy⟩))
      (hsets u)

/-- Evaluating a relabeled computation is evaluating it with the relabeled answer function. -/
theorem evalWithAnswerFn_relabel {ι ι' R : Type} (e : ι → ι') (h : QueryImpl (ι' →ₒ R) Id) {α : Type}
    (P : OracleComp (ι →ₒ R) α) :
    evalWithAnswerFn h (relabel e P) = evalWithAnswerFn (fun x => h (e x) : QueryImpl (ι →ₒ R) Id) P := by
  induction P using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind x k ih =>
    rw [relabel_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    have e1 : evalWithAnswerFn h (((ι' →ₒ R).query (e x) : OracleComp (ι' →ₒ R) R)) = h (e x) :=
      evalWithAnswerFn_query h (e x)
    have e2 : evalWithAnswerFn (fun x => h (e x) : QueryImpl (ι →ₒ R) Id)
        (((ι →ₒ R).query x : OracleComp (ι →ₒ R) R)) = h (e x) :=
      evalWithAnswerFn_query _ x
    rw [e1, e2, ih]

/-- **Fixed-oracle extensionality determines the lazy random oracle's output law.** -/
theorem randomOracle_congr {D R α : Type} [DecidableEq D] [Fintype R] [Nonempty R] [SampleableType R]
    (p q : OracleComp (D →ₒ R) α)
    (h : ∀ hash : QueryImpl (D →ₒ R) Id, evalWithAnswerFn hash p = evalWithAnswerFn hash q) :
    𝒮[(simulateQ randomOracle p).run' ∅] = 𝒮[(simulateQ randomOracle q).run' ∅] := by
  classical
  obtain ⟨sp, hp⟩ := finite_query_domain p
  obtain ⟨sq, hq⟩ := finite_query_domain q
  let s := sp ∪ sq
  let enc : D → Option {x : D // x ∈ s} := fun x => if hx : x ∈ s then some ⟨x, hx⟩ else none
  have hi : Set.InjOn enc {x | x ∈ s} := by
    intro x hx y hy he
    change x ∈ s at hx
    change y ∈ s at hy
    simp only [enc, dif_pos hx, dif_pos hy] at he
    exact congrArg Subtype.val (Option.some.inj he)
  have hp' : AllQ (· ∈ {x | x ∈ s}) p :=
    allQ_mono (fun _ hx => Finset.mem_union_left _ hx) hp
  have hq' : AllQ (· ∈ {x | x ∈ s}) q :=
    allQ_mono (fun _ hx => Finset.mem_union_right _ hx) hq
  rw [run'_relabel_on enc _ hi p hp' ∅ ∅ (fun _ _ => rfl), run'_relabel_on enc _ hi q hq' ∅ ∅ (fun _ _ => rfl),
    evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable,
    evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable]
  congr 1
  refine bind_congr fun g => ?_
  rw [evalWithAnswerFn_relabel, evalWithAnswerFn_relabel, h]

theorem probEvent_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y]) (E : α → Prop) :
    Pr[E | X] = Pr[E | Y] := by
  unfold probEvent; rw [h]

theorem probOutput_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y]) (a : α) :
    Pr[= a | X] = Pr[= a | Y] := by
  unfold probOutput; rw [h]

theorem expectedValue_congr_evalSPMF {α : Type} {X Y : ProbComp α} (h : 𝒮[X] = 𝒮[Y])
    (g : α → ENNReal) : OracleComp.EvalDist.expectedValue X g = OracleComp.EvalDist.expectedValue Y g := by
  unfold OracleComp.EvalDist.expectedValue
  simp only [probOutput_congr_evalSPMF h]

end congr

section fold
variable {ι κ : Type} {spec : OracleSpec ι}

/-- Run the programs `P k` for `k ∈ L` in order (against one oracle) and conjoin their outputs. -/
def foldAll (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) : OracleComp spec Bool :=
  L.foldlM (fun b k => (b && ·) <$> P k) b

@[simp] theorem foldAll_nil (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll [] P b = pure b := rfl

theorem foldAll_cons (k : κ) (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll (k :: L) P b = P k >>= fun c => foldAll L P (b && c) := by
  simp [foldAll, List.foldlM_cons]

theorem evalWithAnswerFn_foldAll (h : QueryImpl spec Id) (L : List κ)
    (P : κ → OracleComp spec Bool) (b : Bool) :
    evalWithAnswerFn h (foldAll L P b) = (b && L.all fun k => evalWithAnswerFn h (P k)) := by
  induction L generalizing b with
  | nil => simp [foldAll_nil]
  | cons k L ih =>
    rw [foldAll_cons, evalWithAnswerFn_bind, ih]
    simp [Bool.and_assoc]

end fold

end SigGolfCandidate.T3M.Final
