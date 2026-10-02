import SigGolfCandidate.T3M.Verify.FtsRuns

/-! Kernel checks of the FTS code blocks: setup, the 21 leaf codes and dispatches, the 3 merge-tail dispatches, both
segment tables (2 × 256 slots: rejects, pending hashes, parity rejects, the jumps into the ladders), the 126 rungs,
the tails, the 7 coordinate ends and the forest. -/

namespace SigGolfCandidate.T3M.Verify

theorem setupCheckF_ok : setupCheckF = true := by decide +kernel
theorem leafCheck_all : (List.range 21).all leafCheck = true := by decide +kernel
theorem leafDispCheck_all : (List.range 21).all leafDispCheck = true := by decide +kernel
theorem mDispCheck_all : (List.range 3).all mDispCheck = true := by decide +kernel
theorem slotCheck_N0 : slotCheck 0 0 128 = true := by decide +kernel
theorem slotCheck_N1 : slotCheck 0 128 128 = true := by decide +kernel
theorem slotCheck_L0 : slotCheck 1 0 128 = true := by decide +kernel
theorem slotCheck_L1 : slotCheck 1 128 128 = true := by decide +kernel
theorem entCheck_N : entCheck 0 0 256 = true := by decide +kernel
theorem entCheck_L : entCheck 1 0 256 = true := by decide +kernel
theorem rungCheck_ok : rungCheck = true := by decide +kernel
theorem tailCheck_ok : tailCheck = true := by decide +kernel
theorem coordCheck_all : (List.range 7).all coordCheck1 = true := by decide +kernel
theorem forestCheckF_ok : forestCheckF = true := by decide +kernel

end SigGolfCandidate.T3M.Verify
