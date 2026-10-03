import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_1024 : (List.range' 1024 1024).all jtOK = true := by decide +kernel
theorem jtOK_5120 : (List.range' 5120 1024).all jtOK = true := by decide +kernel
theorem jtOK_9216 : (List.range' 9216 1024).all jtOK = true := by decide +kernel
theorem jtOK_13312 : (List.range' 13312 1024).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
