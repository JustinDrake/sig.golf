import SigGolfCandidate.T3M.Verify.FtsRuns

/-! Kernel checks of the FTS code blocks: setup, the 21 leaf codes and dispatches, the 3 merge-tail dispatches, both
segment tables (2 × 256 slots: rejects, pending hashes, parity rejects, the jumps into the ladders), the 126 rungs,
the tails, the 7 coordinate ends and the forest. -/

set_option Elab.async false
set_option maxRecDepth 100000

namespace SigGolfCandidate.T3M.Verify

theorem gateCheckF_ok : gateCheckF = true := by decide +kernel
theorem gateRejectCheckF_ok : gateRejectCheckF = true := by decide +kernel

theorem setupLdCheckF_ok : setupLdCheckF = true := by decide +kernel
theorem setupCheckF_ok : setupCheckF = true := by decide +kernel
theorem leafCheck_all : (List.range 21).all leafCheck = true := by decide +kernel
theorem leafDispCheck_all : (List.range 21).all leafDispCheck = true := by decide +kernel
theorem mDispCheck_all : (List.range 141).all mDispCheck = true := by decide +kernel
theorem slotCheck_N0 : slotCheck 0 0 128 = true := by decide +kernel
theorem slotCheck_N1 : slotCheck 0 128 128 = true := by decide +kernel
theorem slotCheck_L0 : slotCheck 1 0 128 = true := by decide +kernel
theorem slotCheck_L1 : slotCheck 1 128 128 = true := by decide +kernel
theorem entCheck_N : entCheck 0 0 256 = true := by decide +kernel
theorem entCheck_L : entCheck 1 0 256 = true := by decide +kernel
private def rungCases (X a : Nat) : Bool :=
  (List.range 2).all fun tb => (List.range 8).all fun bits =>(List.range 2).all fun t =>
      ((lastCheck1 tb X a bits t) &&
       (List.range (a-1)).all fun i => (List.range 2).all fun t' =>
          (!decide (rungSides bits i t t') || rungCheck1 tb X a bits t i t'))

private theorem rungCases_0_1 : rungCases 0 1 = true := by decide +kernel
private theorem rungCases_0_2 : rungCases 0 2 = true := by decide +kernel
private theorem rungCases_0_3 : rungCases 0 3 = true := by decide +kernel
private theorem rungCases_0_4 : rungCases 0 4 = true := by decide +kernel
private theorem rungCases_0_5 : rungCases 0 5 = true := by decide +kernel
private theorem rungCases_0_6 : rungCases 0 6 = true := by decide +kernel
private theorem rungCases_0_7 : rungCases 0 7 = true := by decide +kernel
private theorem rungCases_0_8 : rungCases 0 8 = true := by decide +kernel
private theorem rungCases_0_9 : rungCases 0 9 = true := by decide +kernel
private theorem rungCases_0_10 : rungCases 0 10 = true := by decide +kernel
private theorem rungCases_0_11 : rungCases 0 11 = true := by decide +kernel
private theorem rungCases_1_1 : rungCases 1 1 = true := by decide +kernel
private theorem rungCases_1_2 : rungCases 1 2 = true := by decide +kernel
private theorem rungCases_1_3 : rungCases 1 3 = true := by decide +kernel
private theorem rungCases_1_4 : rungCases 1 4 = true := by decide +kernel
private theorem rungCases_1_5 : rungCases 1 5 = true := by decide +kernel
private theorem rungCases_1_6 : rungCases 1 6 = true := by decide +kernel
private theorem rungCases_1_7 : rungCases 1 7 = true := by decide +kernel
private theorem rungCases_1_8 : rungCases 1 8 = true := by decide +kernel
private theorem rungCases_1_9 : rungCases 1 9 = true := by decide +kernel
private theorem rungCases_1_10 : rungCases 1 10 = true := by decide +kernel
private theorem rungCases_1_11 : rungCases 1 11 = true := by decide +kernel
private theorem rungCases_2_1 : rungCases 2 1 = true := by decide +kernel
private theorem rungCases_2_2 : rungCases 2 2 = true := by decide +kernel
private theorem rungCases_2_3 : rungCases 2 3 = true := by decide +kernel
private theorem rungCases_2_4 : rungCases 2 4 = true := by decide +kernel
private theorem rungCases_2_5 : rungCases 2 5 = true := by decide +kernel
private theorem rungCases_2_6 : rungCases 2 6 = true := by decide +kernel
private theorem rungCases_2_7 : rungCases 2 7 = true := by decide +kernel
private theorem rungCases_2_8 : rungCases 2 8 = true := by decide +kernel
private theorem rungCases_2_9 : rungCases 2 9 = true := by decide +kernel
private theorem rungCases_2_10 : rungCases 2 10 = true := by decide +kernel
private theorem rungCases_2_11 : rungCases 2 11 = true := by decide +kernel

theorem rungCheck_ok : rungCheck = true := by
  change (List.range 3).all (fun X => (List.range' 1 11).all (rungCases X)) = true
  apply List.all_eq_true.mpr
  intro X hX
  have hX3 : X < 3 := by simpa using hX
  apply List.all_eq_true.mpr
  intro a ha
  have ha1 : 1 ≤ a ∧ a < 12 := by simpa using ha
  obtain ⟨hal,hau⟩ := ha1
  interval_cases X <;> interval_cases a
  · exact rungCases_0_1
  · exact rungCases_0_2
  · exact rungCases_0_3
  · exact rungCases_0_4
  · exact rungCases_0_5
  · exact rungCases_0_6
  · exact rungCases_0_7
  · exact rungCases_0_8
  · exact rungCases_0_9
  · exact rungCases_0_10
  · exact rungCases_0_11
  · exact rungCases_1_1
  · exact rungCases_1_2
  · exact rungCases_1_3
  · exact rungCases_1_4
  · exact rungCases_1_5
  · exact rungCases_1_6
  · exact rungCases_1_7
  · exact rungCases_1_8
  · exact rungCases_1_9
  · exact rungCases_1_10
  · exact rungCases_1_11
  · exact rungCases_2_1
  · exact rungCases_2_2
  · exact rungCases_2_3
  · exact rungCases_2_4
  · exact rungCases_2_5
  · exact rungCases_2_6
  · exact rungCases_2_7
  · exact rungCases_2_8
  · exact rungCases_2_9
  · exact rungCases_2_10
  · exact rungCases_2_11

theorem tailCheck_ok : tailCheck = true := by decide +kernel
theorem coordCheck_all : (List.range 7).all coordCheck1 = true := by decide +kernel
theorem forestCheckF_ok : forestCheckF = true := by decide +kernel

end SigGolfCandidate.T3M.Verify
