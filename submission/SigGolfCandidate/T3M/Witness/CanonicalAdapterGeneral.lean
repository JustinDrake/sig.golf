import SigGolfCandidate.T3M.Witness.CanonicalAdapter

/-! Normalization is valid even for selected triples that fail the final
115-fold cap. The machine may query up to 140 folds before rejecting. -/
namespace SigGolfCandidate.T3M.CanonicalAdapter
open SigGolfCandidate.T3 CanonicalBytes

theorem slotBase_bounded (chosen : List Selection) (hc : ChosenOk chosen) :
    ∀ n, n ≤ 7 → slotBase chosen n ≤ 20*n := by
  intro n
  induction n with
  | zero => intro hn; simp [slotBase]
  | succ n ih =>
    intro hn
    have hi := ih (by omega)
    have hp := (CanonicalCost.coord_cap n _ (hc n (by omega))).2.1
    rw [coord_fold_count n _ (hc n (by omega))] at hp
    rw [slotBase_succ]
    omega

theorem slotBase_all (chosen : List Selection) (hc : ChosenOk chosen) :
    slotBase chosen 7 ≤ 140 := slotBase_bounded chosen hc 7 (by decide)

theorem header_bound_general (chosen : List Selection) (hc : ChosenOk chosen)
    (n : Nat) (hn : n<(schedule chosen).length) : segPtr (schedule chosen) n<25240 := by
  have hf := slotBase_all chosen hc
  have hm := segPtr_slope (schedule chosen) 35 (by rw [schedule_length]) n
    (by rw [schedule_length] at hn; omega)
  have he := segPtr_end chosen hc
  unfold streamBase at he
  omega

theorem normalize_streamMatches_general (chosen : List Selection) (w : WBytes)
    (hc : ChosenOk chosen) : StreamMatches chosen (normalize chosen w) := by
  intro n hn
  have hn35 : n<35 := by simpa [schedule_length] using hn
  have ha := schedule_a_le chosen hc hn35
  have hb := byte0_lt ((schedule chosen).getD n default) (by omega)
  unfold normalize
  rw [byte_patch _ _ _ (header_bound_general chosen hc n hn),replacement_header _ n hn]
  simp only [Option.getD_some,UInt8.toNat_ofNat',Nat.mod_eq_of_lt hb]
  exact Segment.matches_byte0 _ ha

theorem fold_digest_normalize_general (chosen : List Selection) (w : WBytes)
    (hc : ChosenOk chosen) (n r off : Nat) (hn : n<(schedule chosen).length)
    (hr : r<((schedule chosen).getD n default).a) (hoff : off+16 ≤ 80) :
    wdig (normalize chosen w) (segPtr (schedule chosen) n+8+80*r+off)=
      wdig w (segPtr (schedule chosen) n+8+80*r+off) := by
  apply digest_patch_frame
  · have hf := slotBase_all chosen hc
    have ht := segPtr_succ (schedule chosen) hn
    have hm := segPtr_slope (schedule chosen) 35 (by rw [schedule_length]) (n+1)
      (by rw [schedule_length] at hn; omega)
    have he := segPtr_end chosen hc
    unfold segNext at ht
    unfold streamBase at he
    omega
  · intro j hj
    exact replacement_inside_segment _ n r off 16 hn hr hoff j hj

#print axioms normalize_streamMatches_general
end SigGolfCandidate.T3M.CanonicalAdapter
