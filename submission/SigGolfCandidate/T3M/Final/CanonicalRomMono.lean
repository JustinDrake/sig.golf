import SigGolfCandidate.T3M.Final.RO

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec SigGolfCandidate.Bridge

/-- Pointwise event implication also transfers from any partially filled cache. -/
theorem randomOracle_event_mono_cache {D R α β : Type} [DecidableEq D] [Fintype R]
    [Nonempty R] [SampleableType R] (p : OracleComp (D →ₒ R) α)
    (q : OracleComp (D →ₒ R) β) (E : α → Prop) (F : β → Prop)
    (h : ∀ hash : QueryImpl (D →ₒ R) Id,
      E (evalWithAnswerFn hash p) → F (evalWithAnswerFn hash q))
    (cache : QueryCache (D →ₒ R)) :
    Pr[E | (simulateQ randomOracle p).run' cache] ≤
      Pr[F | (simulateQ randomOracle q).run' cache] := by
  classical
  obtain ⟨sp,hp⟩ := finite_query_domain p
  obtain ⟨sq,hq⟩ := finite_query_domain q
  let s := sp ∪ sq
  let enc : D → Option {x : D // x ∈ s} := fun x => if hx : x∈s then some ⟨x,hx⟩ else none
  let small : QueryCache (Option {x : D // x∈s} →ₒ R) := fun x => x.bind (fun y => cache y.1)
  have hi : Set.InjOn enc {x | x∈s} := by
    intro x hx y hy he
    change x∈s at hx
    change y∈s at hy
    simp only [enc,dif_pos hx,dif_pos hy] at he
    exact congrArg Subtype.val (Option.some.inj he)
  have hp' : AllQ (·∈{x | x∈s}) p := allQ_mono (fun _ hx => Finset.mem_union_left _ hx) hp
  have hq' : AllQ (·∈{x | x∈s}) q := allQ_mono (fun _ hx => Finset.mem_union_right _ hx) hq
  have hc : ∀ x∈{x | x∈s},cache x=small (enc x) := by
    intro x hx
    change x∈s at hx
    simp [small,enc,hx]
  rw [run'_relabel_on enc _ hi p hp' cache small hc,
    run'_relabel_on enc _ hi q hq' cache small hc]
  have hpE := probEvent_congr_evalSPMF
    (evalSPMF_simulateQ_randomOracle_run'_eq_tableExtending (relabel enc p) small) E
  have hqF := probEvent_congr_evalSPMF
    (evalSPMF_simulateQ_randomOracle_run'_eq_tableExtending (relabel enc q) small) F
  rw [hpE,hqF]
  rw [probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro g
  gcongr
  simp only [probEvent_pure,evalWithAnswerFn_relabel]
  split_ifs with he hf
  · exact le_rfl
  · exact (hf (h _ he)).elim
  · exact zero_le
  · exact le_rfl

#print axioms randomOracle_event_mono_cache
end SigGolfCandidate.T3M.Final
