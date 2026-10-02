import SigGolfCandidate.T3M.Verify.ChainCheckQ1

/-! Kernel check of the top chain code, quads 8..11, the checksum chain and chain 48. -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem quadCheck_8 : quadCheck 8 0 256 = true := by decide +kernel
theorem quadCheck_9 : quadCheck 9 0 256 = true := by decide +kernel
theorem quadCheck_10 : quadCheck 10 0 256 = true := by decide +kernel
theorem quadCheck_11 : quadCheck 11 0 256 = true := by decide +kernel
theorem ckCheck_ok : ckCheck = true := by decide +kernel
theorem q48Check_ok : q48Check = true := by decide +kernel

end SigGolfCandidate.T3M
