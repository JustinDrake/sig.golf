import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_0 : (List.range' 0 1024).all jtOK = true := by decide +kernel
theorem jtOK_4096 : (List.range' 4096 1024).all jtOK = true := by decide +kernel
theorem jtOK_8192 : (List.range' 8192 1024).all jtOK = true := by decide +kernel
theorem jtOK_12288 : (List.range' 12288 1024).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
