import SigGolfCandidate.T3M.Verify.Judg

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
set_option autoImplicit false

theorem eval_mem_support {α : Type} (hash : Hash) (p : OracleComp HashSpec α) :
    evalWithAnswerFn hash p ∈ support p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp only [evalWithAnswerFn_pure,support_pure,Set.mem_singleton_iff]
  | query_bind q next ih =>
    rw [evalWithAnswerFn_bind,mem_support_bind_iff]
    exact ⟨_,mem_support_query q _,ih _⟩

theorem mrealize_mem_support {α : Type} (p : T3.M α) (x : α)
    (h : x ∈ support (mrealize 0 p)) : x ∈ support p := by
  induction p using OracleComp.inductionOn generalizing x with
  | pure a => simpa only [mrealize_pure,support_pure,Set.mem_singleton_iff] using h
  | query_bind q next ih =>
    rw [mrealize_bind,mem_support_bind_iff] at h
    obtain ⟨a,_,ha⟩ := h
    rw [mem_support_bind_iff]
    exact ⟨a,mem_support_query q a,ih a x ha⟩

theorem ccM_some_support {α : Type} (p : T3.M (Option α))
    (R : Option α → OracleComp HashSpec Obs) (hR : R none = pure (false,0))
    (o : Obs) (ho : o ∈ support (ccM p R)) (ht : o.1 = true) :
    ∃ a, some a ∈ support p := by
  rw [ccM,cc,mem_support_bind_iff] at ho
  obtain ⟨v,hv,ho⟩ := ho
  have hmem : v.1 ∈ support (mrealize 0 p) := by
    rw [← fst_countCalls (mrealize 0 p),support_map]
    exact ⟨v,hv,rfl⟩
  have hp := mrealize_mem_support p v.1 hmem
  rcases hval : v.1 with _ | a
  · rw [hval,hR,map_pure] at ho
    simp only [support_pure,Set.mem_singleton_iff] at ho
    rw [ho] at ht
    contradiction
  · exact ⟨a,hval ▸ hp⟩

theorem GoodQ.withSourceProperty {s : MachineState} {N C A : Nat} {Q P : Prop}
    {X : OracleComp HashSpec Obs} (h : GoodQ s N C Q A X)
    (hP : ∀ o ∈ support X, o.1 = true → P) : GoodQ s N C (Q ∧ P) A X := by
  intro fuel hf
  obtain ⟨hx,hr⟩ := h fuel hf
  refine ⟨hx,fun hash => ⟨(hr hash).1,(hr hash).2.1,fun ha => ?_⟩⟩
  obtain ⟨hq,hc⟩ := (hr hash).2.2 ha
  have he := eval_mem_support hash (Riscv.execute fuel image s)
  have ho : obs (evalWithAnswerFn hash (Riscv.execute fuel image s)) ∈ support X := by
    rw [← hx,support_map]
    exact ⟨_,he,rfl⟩
  exact ⟨⟨hq,hP _ ho (by simp only [obs,ha,decide_true])⟩,hc⟩

#print axioms ccM_some_support
#print axioms GoodQ.withSourceProperty
end SigGolfCandidate.T3M.Verify
