import SigGolfCandidate.T3.SearchCost

namespace SigGolfCandidate.T3.FullCacheExpansionCost
open OracleComp OracleSpec Cost Correctness SearchCost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem foldlM_cost_ge {α β : Type} (answers : Answers)
    (f : β → α → M β) (k : Nat)
    (h : ∀ state value, k ≤ cost answers (f state value))
    (values : List α) (init : β) :
    values.length*k ≤ cost answers (values.foldlM f init) := by
  induction values generalizing init with
  | nil => simp only [List.foldlM_nil, cost_pure, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons value values ih =>
      rw [List.foldlM_cons, cost_bind, List.length_cons, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.add_comm] using Nat.add_le_add (h init value)
        (ih (evalWithAnswerFn answers (f init value)))
theorem privatePair_cost (answers : Answers) (tag lay tree position index : Nat) :
    cost answers (privatePair tag lay tree position index) = 1 := by
  simp only [privatePair, privateHash, cost_bind, cost_query, cost_pure, Nat.add_zero]
  rfl
theorem buildFts_cost_ge (answers : Answers) (index coord : Nat) :
    1024 ≤ cost answers (buildFts index coord) := by
  unfold buildFts
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) pair => do
      let (left, right) ← privatePair 8 coord index 0 pair
      let leftLeaf ← ftsLeaf index coord (2*pair) left
      let rightLeaf ← ftsLeaf index coord (2*pair+1) right
      pure (state.1 ++ [leftLeaf,rightLeaf],state.2 ++ [left,right])) 1
    (fun state pair => by
      simp only [cost_bind, privatePair_cost, cost_pure]
      omega) (List.range 1024) ([], [])
  simpa only [List.length_range, Nat.mul_one] using h
theorem forestRows_cost_ge (answers : Answers) (index : Nat) (chosen : List Selection) :
    7168 ≤ cost answers (forestRows index chosen) := by
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map fun s => sel.bucket*128+s
      let opened := selected.map fun s => secrets.getD s 0
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1++opened,state.2.1++inner++outer,state.2.2++[(levels.getD 11 []).getD 0 0]))
    1024
    (fun state coord => by
      rw [cost_bind]
      exact Nat.le_trans (buildFts_cost_ge answers index coord) (Nat.le_add_right _ _))
    (List.range 7) ([],[],[])
  exact h
theorem signPayload_cost_ge (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hs : evalWithAnswerFn answers (signPayload cache message) = some sig) :
    90 ≤ cost answers (signPayload cache message) := by
  rw [signPayload_forestRows] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := forestRows_cost_ge answers (output.toNat%2^31) (selections output)
      omega
end SigGolfCandidate.T3.FullCacheExpansionCost
