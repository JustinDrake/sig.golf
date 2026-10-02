import SigGolfCandidate.Verify.FoldCheckA
import SigGolfCandidate.Verify.FoldCheckB

/-! All Merkle shape blocks. -/

namespace SigGolfCandidate.Verify

theorem layFoldOk_at (lay ci : Nat) (hl : lay < 5) (hci : ci < nCh lay) : layFoldOk lay ci = true := by
  interval_cases lay
  · have : ci < 2 := by simpa [nCh] using hci
    interval_cases ci
    · exact layFoldOk_0_0
    · exact layFoldOk_0_1
  all_goals (have : ci = 0 := by simp [nCh] at hci; omega); subst this
  · exact layFoldOk_1_0
  · exact layFoldOk_2_0
  · exact layFoldOk_3_0
  · exact layFoldOk_4_0

theorem blockCheck_at (lay : Nat) (hl : lay < 5) :
    ∀ ci, ci < nCh lay → ∀ v, v < 2 ^ chBits lay ci → blockCheck lay ci v = true := by
  intro ci hci v hv
  have h := layFoldOk_at lay ci hl hci
  simp only [layFoldOk, foldCheck, List.all_eq_true, List.mem_range'] at h
  exact h v ⟨by omega, by omega⟩

end SigGolfCandidate.Verify
