import SigGolfCandidate.T3M.Witness.Shaped

namespace SigGolfCandidate.T3M
open OracleComp SigGolfCandidate.T3
set_option maxHeartbeats 1000000

/-- A successful padded byte verifier enforces the digest gate on its actual
queried digest answer. This is separate from the stream-layout predicate Shaped. -/
theorem verifyP_digestGate (answers : Correctness.Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    digestGate (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) = true := by
  rw [verifyP_eq_tail, evalWithAnswerFn_bind] at hv
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · simp [digestP, hdc] at hv
  · simp only [digestP, if_neg hdc, evalWithAnswerFn_map] at hv
    unfold verifyTailP at hv
    by_cases hs : selectionsOk (selections (evalWithAnswerFn answers (digest (wrho w) m (wdc w)))) = true
    · rw [if_neg (by simpa using hs)] at hv
      by_contra hg
      rw [if_pos (by simpa using hg)] at hv
      simp at hv
    · rw [if_pos (by simpa using hs)] at hv
      simp at hv

end SigGolfCandidate.T3M
