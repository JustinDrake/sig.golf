import SigGolfCandidate.Legacy

namespace SigGolfCandidate.T3M.Images
theorem foldl_append_length {α : Type} (chunks : List (List α)) (acc : List α) :
    (chunks.foldl (· ++ ·) acc).length = acc.length + (chunks.map List.length).sum := by
  induction chunks generalizing acc with
  | nil => simp
  | cons head tail ih => simp [List.foldl_cons, ih, Nat.add_assoc]
end SigGolfCandidate.T3M.Images
