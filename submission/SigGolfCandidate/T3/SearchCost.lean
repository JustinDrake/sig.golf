import SigGolfCandidate.T3.Proofs

namespace SigGolfCandidate.T3.SearchCost
open OracleComp OracleSpec Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def cost {α : Type} (answers : Answers) (program : M α) : Nat :=
  (evalWithAnswerFn answers (Cost.countBlocks program)).2
theorem counted_fst {α : Type} (answers : Answers) (program : M α) :
    (evalWithAnswerFn answers (Cost.countBlocks program)).1=evalWithAnswerFn answers program := by
  have h := congrArg (evalWithAnswerFn answers) (fst_countWith weight program)
  simpa only [evalWithAnswerFn_map,countBlocks] using h
@[simp] theorem cost_pure {α : Type} (answers : Answers) (value : α) :
    cost answers (pure value : M α)=0 := rfl
theorem cost_bind {α β : Type} (answers : Answers) (first : M α) (next : α → M β) :
    cost answers (first >>= next)=cost answers first+cost answers (next (evalWithAnswerFn answers first)) := by
  unfold cost
  rw [countBlocks,countWith_bind,evalWithAnswerFn_bind,evalWithAnswerFn_map]
  rw [show (evalWithAnswerFn answers (countWith weight first)).1=evalWithAnswerFn answers first from
    counted_fst answers first]
  rfl
@[simp] theorem cost_query (answers : Answers) (q : Cost.Query) :
    cost answers (T3.Spec.query q)=Cost.weight q := by
  unfold cost countBlocks
  rw [countWith_query,evalWithAnswerFn_map]
theorem eval_mem_support {α : Type} (answers : Answers) (program : M α) :
    evalWithAnswerFn answers program ∈ support program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [evalWithAnswerFn_pure,support_pure,Set.mem_singleton_iff]
  | query_bind q next ih =>
      rw [evalWithAnswerFn_bind,mem_support_bind_iff]
      exact ⟨_,mem_support_query q _,ih _⟩
theorem cost_bound {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (answers : Answers) (h : Cost.Bound P Post k program) :
    cost answers program ≤ k :=
  (h.count_support _ (eval_mem_support answers (Cost.countBlocks program))).2
theorem post_bound {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (answers : Answers) (h : Cost.Bound P Post k program) :
    Post (evalWithAnswerFn answers program) := by
  have hh := (h.count_support _ (eval_mem_support answers (Cost.countBlocks program))).1
  rwa [counted_fst] at hh
end SigGolfCandidate.T3.SearchCost
