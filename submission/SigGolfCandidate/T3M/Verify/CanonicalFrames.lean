import SigGolfCandidate.T3M.Verify.CanonicalBanksCost
import SigGolfCandidate.T3M.Verify.CanonicalForest

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (selections)

theorem banks_end_global (F : FCtx) (hc : ChosenOk (selections F.a)) :
    ∀ n c, c+n≤7 →
    banksEndPtr F c n (segPtr (schedule (selections F.a)) (5*c))=
      segPtr (schedule (selections F.a)) (5*(c+n)) := by
  intro n
  induction n with
  | zero => intro c hn; simp [banksEndPtr]
  | succ n ih =>
    intro c hn
    rw [banksEndPtr,bank_end_schedule_global F hc c (by omega),ih (c+1) (by omega)]
    congr 1 <;> omega

theorem banks_cap_folds (F : FCtx) (hc : ChosenOk (selections F.a))
    (hp : banksEndPtr F 0 7 1088≤10568) : slotBase (selections F.a) 7≤115 := by
  have he := banks_end_global F hc 7 0 (by omega)
  simp only [Nat.mul_zero,segPtr_zero,Nat.zero_add] at he
  change banksEndPtr F 0 7 1088=segPtr (schedule (selections F.a)) (5*7) at he
  have hf := segPtr_end (selections F.a) hc
  rw [show 5*7=35 by decide] at he
  rw [he] at hp
  change segPtr (schedule (selections F.a)) 35=1088+280+80*slotBase (selections F.a) 7 at hf
  omega

theorem normalize_word_header (chosen : List T3.Selection) (w : WBytes) (j : Nat)
    (hj : j<8) : wword (CanonicalAdapter.normalize chosen w) j=wword w j := by
  unfold wword
  rw [show 64*j=8*(8*j) by omega]
  apply CanonicalBytes.extract_patch_frame _ _ (8*j) 8 (by omega)
  intro k hk
  exact CanonicalAdapter.replacement_before_stream _ _ (by omega)

theorem normalize_word_lower (chosen : List T3.Selection) (w : WBytes)
    (hc : ChosenOk chosen) (hf : slotBase chosen 7≤115) (j : Nat) (hj : 11288≤8*j) :
    wword (CanonicalAdapter.normalize chosen w) j=wword w j := by
  by_cases h : j<3155
  · unfold wword
    rw [show 64*j=8*(8*j) by omega]
    apply CanonicalBytes.extract_patch_frame _ _ (8*j) 8 (by omega)
    intro k hk
    exact CanonicalAdapter.replacement_after_stream chosen hc hf (8*j+k) (by omega)
  · rw [wword_zero _ j (by omega),wword_zero _ j (by omega)]

theorem forest_out_normalized (F : FCtx) (hc : ChosenOk (selections F.a))
    (hp : banksEndPtr F 0 7 1088≤10568) {root s} (h : ForestCOut F root s) :
    ForestCOut ⟨F.pk,CanonicalAdapter.normalize (selections F.a) F.w,F.a⟩ root s := by
  have hf := banks_cap_folds F hc hp
  obtain ⟨hglob,hidx,hpc,hroot,hwit⟩ := h
  obtain ⟨hk,hw,hpk,hz,hh,hd⟩ := hglob
  constructor
  · change Glob carryK (CanonicalAdapter.normalize (selections F.a) F.w) F.pk s
    refine ⟨hk,?_,hpk,hz,hh,hd⟩
    intro j hj
    rw [normalize_word_header _ _ j hj]
    exact hw j hj
  · simpa only [FCtx.idx] using hidx
  · exact hpc
  · exact hroot
  · intro j hj ho
    change s.getMem _=wword (CanonicalAdapter.normalize (selections F.a) F.w) j
    rcases ho with ho | ho
    · rw [normalize_word_header _ _ j (by omega)]
      exact hwit j hj (Or.inl ho)
    · rw [normalize_word_lower _ _ hc hf j ho]
      exact hwit j hj (Or.inr ho)

#print axioms forest_out_normalized
end SigGolfCandidate.T3M.CanonicalNative
