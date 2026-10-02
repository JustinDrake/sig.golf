import SigGolfCandidate.T3M.Verify.ChainRuns

/-! Kernel check of the top chain code, quads 0..3. -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem quadCheck_0 : quadCheck 0 0 256 = true := by decide +kernel
theorem quadCheck_1 : quadCheck 1 0 256 = true := by decide +kernel
theorem quadCheck_2 : quadCheck 2 0 256 = true := by decide +kernel
theorem quadCheck_3 : quadCheck 3 0 256 = true := by decide +kernel

end SigGolfCandidate.T3M
