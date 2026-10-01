import SigGolfCandidate.AlternativeCodecAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

theorem walkP_zero (lay tree leaf i start count : Nat) (v : Val) :
    walkP lay tree leaf i start count (zeros 32) v = walk lay tree leaf i start count v := rfl

theorem ranges_split (s a b : Nat) :
    List.range' s (a+b) = List.range' s a ++ List.range' (s+a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
    simp only [Nat.succ_add, List.range'_succ, List.cons_append]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 a]

theorem walk_add (lay tree leaf i start a b : Nat) (v : Val) :
    walk lay tree leaf i start (a+b) v = (do
      let mid ← walk lay tree leaf i start a v
      walk lay tree leaf i (start+a) b mid) := by
  unfold walk
  rw [ranges_split, List.foldlM_append]

/-- A disclosed initialPart and the verifier's remaining steps compose exactly. -/
theorem walk_recover (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    (do
      let mid ← walk lay tree leaf i 1 digit v
      walk lay tree leaf i (digit+1) (3-digit) mid) = walk lay tree leaf i 1 3 v := by
  simpa only [Nat.add_comm 1 digit, Nat.add_sub_of_le hd] using
    (walk_add lay tree leaf i 1 digit (3-digit) v).symm

/-- The captured value is precisely a initialPart, including the zero-step case. -/
theorem chainWithCapture_split (lay tree leaf i digit : Nat) (hd : digit ≤ 3) (v : Val) :
    chainWithCapture lay tree leaf i digit v = (do
      let initialPart ← walk lay tree leaf i 1 digit v
      let endpoint ← walk lay tree leaf i (digit+1) (3-digit) initialPart
      pure (endpoint, initialPart)) := by
  unfold chainWithCapture walk
  have hc := fun x l hx a c => SigGolfCandidate.Equiv.capFold_notin
    (fun step v => h16 (chainInput lay tree leaf i step v)) x l hx a c
  cases digit with
  | zero =>
    rw [hc 0 _ (by simp)]
    simp
  | succ k =>
    have hs : List.range' 1 3 =
        List.range' 1 k ++ (1+k) :: List.range' (1+k+1) (2-k) := by
      rw [← List.range'_succ, show 2-k+1 = 3-k by omega, List.range'_append_1]
      congr 1
      omega
    rw [hs, List.foldlM_append, hc (k+1) _ (by simp; omega)]
    simp only [map_bind, bind_map_left, List.foldlM_cons, bind_assoc, pure_bind]
    rw [show List.range' 1 (k+1) = List.range' 1 k ++ [1+k] by
      rw [List.range'_concat]; simp]
    simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_assoc, bind_pure]
    congr 1
    funext w
    congr 1
    funext z
    rw [if_pos (by omega), hc (k+1) _ (by simp),
      show k+1+1 = 1+k+1 by omega, show 3-(k+1) = 2-k by omega]
    simp only [map_eq_bind_pure_comp, Function.comp_def]



end SigGolfCandidate.Base4Candidate.Reference
