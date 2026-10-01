import SigGolfCandidate.Verify.FoldRuns

/-! Kernel check of the Merkle shape blocks of layers 0 and 1 (one declaration per chunk). -/

namespace SigGolfCandidate.Verify

theorem layFoldOk_0_0 : layFoldOk 0 0 = true := by decide +kernel
theorem layFoldOk_0_1 : layFoldOk 0 1 = true := by decide +kernel
theorem layFoldOk_1_0 : layFoldOk 1 0 = true := by decide +kernel

end SigGolfCandidate.Verify
