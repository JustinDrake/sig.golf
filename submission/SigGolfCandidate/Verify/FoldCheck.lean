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

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem topSlotChecks : (List.range 2048).all topSlotCheck = true := by decide +kernel

theorem topSlotCheck_at (E : Nat) (hE : E < 2048) : topSlotCheck E = true :=
  List.all_eq_true.mp topSlotChecks E (List.mem_range.mpr hE)

end SigGolfCandidate.Verify
