import SigGolfCandidate.ClaudeWCT.GuessV2.WCTCoords
import SigGolfCandidate.T3.Gate6.BPORSPrefix

namespace ClaudeWCT.Guess
open SigGolfCandidate.T3 ClaudeWCT.WCT9
open scoped ENNReal
def NearCoveredAt (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) : Prop :=
  ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t'
def NearCoveredBy (X : List HashOutput) (N : HashOutput) : Prop := ∃ k t, NearCoveredAt X N k t
theorem SlotCovered.mono_log {X Y : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 7}
    (h : ∀ x ∈ X, x ∈ Y) (hc : SlotCovered X N k t) : SlotCovered Y N k t := by
  obtain ⟨out, hout, h1, h2, h3⟩ := hc
  exact ⟨out, h out hout, h1, h2, h3⟩
theorem NearCoveredAt.mono_log {X Y : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 7}
    (h : ∀ x ∈ X, x ∈ Y) (hc : NearCoveredAt X N k t) : NearCoveredAt Y N k t :=
  fun k' t' hne => (hc k' t' hne).mono_log h
open Classical in
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  if admissible N = true then ∑ k : Fin 9, ∑ t : Fin 7, (if NearCoveredAt X N k t then 1 else 0) else 0
theorem one_le_nearScore {X : List HashOutput} {N : HashOutput} (hadm : admissible N = true)
    (h : NearCoveredBy X N) : 1 ≤ nearScore X N := by
  classical
  obtain ⟨k, t, hkt⟩ := h
  unfold nearScore
  rw [if_pos hadm]
  calc (1 : ENNReal) = if NearCoveredAt X N k t then 1 else 0 := by rw [if_pos hkt]
    _ ≤ ∑ t' : Fin 7, (if NearCoveredAt X N k t' then 1 else 0) :=
        Finset.single_le_sum (f := fun t' => if NearCoveredAt X N k t' then (1 : ENNReal) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ t)
    _ ≤ _ := Finset.single_le_sum (f := fun k' => ∑ t' : Fin 7, if NearCoveredAt X N k' t' then (1 : ENNReal) else 0)
          (fun _ _ => zero_le) (Finset.mem_univ k)
theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) : nearScore X N ≤ nearScore (X ++ Y) N := by
  classical
  unfold nearScore
  split_ifs with hadm
  · apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro t _
    by_cases h : NearCoveredAt X N k t
    · rw [if_pos h, if_pos (h.mono_log fun x hx => List.mem_append_left _ hx)]
    · rw [if_neg h]
      exact zero_le
  · exact le_rfl
theorem nearScore_le (X : List HashOutput) (N : HashOutput) : nearScore X N ≤ 63 := by
  classical
  unfold nearScore
  split_ifs
  · calc _ ≤ ∑ _k : Fin 9, ∑ _t : Fin 7, (1 : ENNReal) := by
          apply Finset.sum_le_sum; intro k _
          apply Finset.sum_le_sum; intro t _
          split_ifs <;> simp
      _ = 63 := by simp; norm_num
  · exact zero_le
noncomputable def nearPrice (X : List HashOutput) : ENNReal :=
  2 ^ 128 * SigGolfCandidate.T3.BPORS.finiteAverage (fun N : HashOutput => nearScore X N)
theorem average_nearScore (X : List HashOutput) :
    SigGolfCandidate.T3.BPORS.finiteAverage (fun N : HashOutput => nearScore X N) = nearPrice X / 2 ^ 128 := by
  unfold nearPrice
  rw [mul_comm, ENNReal.mul_div_cancel_right (by positivity) (by finiteness)]
theorem nearCoveredBy_of_caseC {X : List HashOutput} {N : HashOutput} {k : Fin 9} {t : Fin 7}
    (h : ∀ k' t', (k', t') ≠ (k, t) → SlotCovered X N k' t') : NearCoveredBy X N :=
  ⟨k, t, h⟩
end ClaudeWCT.Guess
