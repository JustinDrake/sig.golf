import SigGolfCandidate.T3M.Verify.ChainCheckQ0

/-! Kernel check of the top chain code, quads 4..7. -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem quadCheck_4 : quadCheck 4 0 256 = true := by decide +kernel
theorem quadCheck_5 : quadCheck 5 0 256 = true := by decide +kernel
theorem quadCheck_6 : quadCheck 6 0 256 = true := by decide +kernel
theorem quadCheck_7 : quadCheck 7 0 256 = true := by decide +kernel

end SigGolfCandidate.T3M
