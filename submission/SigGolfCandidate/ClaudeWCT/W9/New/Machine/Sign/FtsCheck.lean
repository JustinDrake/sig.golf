import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckA
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckB
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsCheckC

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3M.Verify
theorem okCoord_all {c : Nat} (hc : c < 9) : okCoord c = true := by
  match c, hc with
  | 0, _ => exact okCoord_0
  | 1, _ => exact okCoord_1
  | 2, _ => exact okCoord_2
  | 3, _ => exact okCoord_3
  | 4, _ => exact okCoord_4
  | 5, _ => exact okCoord_5
  | 6, _ => exact okCoord_6
  | 7, _ => exact okCoord_7
  | 8, _ => exact okCoord_8
theorem okCoord_parts {c : Nat} (hc : c < 9) :
    okF c = true ∧ okP c = true ∧ okPre c = true ∧ okChk c = true ∧ okStp c = true ∧ okLc c = true ∧
      okTail c = true := by
  have h := okCoord_all hc
  simp only [okCoord, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
theorem runF_eq {c : Nat} (hc : c < 9) : runF c = some (expF c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.1
theorem runZ_eq {c : Nat} (hc : c < 9) : runZ c = some (expZ c) := by
  have h := (okCoord_parts hc).1
  simp only [okF, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem runP_eq {c p : Nat} (hc : c < 9) (hp : p < 4) : runP c p = some (expP c p) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.1 p (List.mem_range.mpr hp))
theorem runPre_eq {c i : Nat} (hc : c < 9) (hi : i < 7) : runPre c i = some (expPre c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.1 i (List.mem_range.mpr hi))
theorem runChk_eq {c i s v : Nat} (hc : c < 9) (hi : i < 7) (hs : s < 4) (hv : v < 3) :
    runChk c i s v = some (expChk c i s v) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.1 i
    (List.mem_range.mpr hi)) s (List.mem_range.mpr hs)) v (List.mem_range.mpr hv))
theorem runStp_eq {c i s : Nat} (hc : c < 9) (hi : i < 7) (hs1 : 1 ≤ s) (hs : s < 4) :
    runStp c i s = some (expStp c i s) :=
  optBeq_eq (List.all_eq_true.mp (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.1 i (List.mem_range.mpr hi)) s
    (List.mem_range'_1.mpr ⟨hs1, by omega⟩))
theorem runLc_eq {c i : Nat} (hc : c < 9) (hi : i < 7) : runLc c i = some (expLc c i) :=
  optBeq_eq (List.all_eq_true.mp (okCoord_parts hc).2.2.2.2.2.1 i (List.mem_range.mpr hi))
theorem okTail_parts {c : Nat} (hc : c < 9) :
    optBeq (runL c) (expL c) = true ∧ optBeq (runT c true) (expT c true) = true ∧
      optBeq (runT c false) (expT c false) = true ∧ optBeq (runN c) (expN c) = true ∧
      optBeq (runNT c true) (expNT c true) = true ∧ optBeq (runNT c false) (expNT c false) = true ∧
      optBeq (runR0 c) (expR0 c) = true ∧ ((List.range 7).all fun l => optBeq (runPC c l) (expPC c l)) = true := by
  have h := (okCoord_parts hc).2.2.2.2.2.2
  simp only [okTail, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
theorem runL_eq {c : Nat} (hc : c < 9) : runL c = some (expL c) := optBeq_eq (okTail_parts hc).1
theorem runT_eq {c : Nat} (hc : c < 9) (b : Bool) : runT c b = some (expT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.1
  · exact optBeq_eq (okTail_parts hc).2.1
theorem runN_eq {c : Nat} (hc : c < 9) : runN c = some (expN c) := optBeq_eq (okTail_parts hc).2.2.2.1
theorem runNT_eq {c : Nat} (hc : c < 9) (b : Bool) : runNT c b = some (expNT c b) := by
  cases b
  · exact optBeq_eq (okTail_parts hc).2.2.2.2.2.1
  · exact optBeq_eq (okTail_parts hc).2.2.2.2.1
theorem runR0_eq {c : Nat} (hc : c < 9) : runR0 c = some (expR0 c) := optBeq_eq (okTail_parts hc).2.2.2.2.2.2.1
theorem runPC_eq {c l : Nat} (hc : c < 9) (hl : l < 7) : runPC c l = some (expPC c l) :=
  optBeq_eq (List.all_eq_true.mp (okTail_parts hc).2.2.2.2.2.2.2 l (List.mem_range.mpr hl))
theorem okGlobal_parts : optBeq runSK expSK = true ∧ optBeq runFor expFor = true ∧ optBeq runJ expJ = true := by
  have h := okGlobal_ok
  simp only [okGlobal, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
theorem runSK_eq : runSK = some expSK := optBeq_eq okGlobal_parts.1
theorem runFor_eq : runFor = some expFor := optBeq_eq okGlobal_parts.2.1
theorem runJ_eq : runJ = some expJ := optBeq_eq okGlobal_parts.2.2
end ClaudeWCT.W9.Machine.Sign
