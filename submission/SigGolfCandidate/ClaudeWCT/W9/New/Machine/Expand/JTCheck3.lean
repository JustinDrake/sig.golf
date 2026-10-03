import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_3072 : (List.range' 3072 1024).all jtOK = true := by decide +kernel
theorem jtOK_7168 : (List.range' 7168 1024).all jtOK = true := by decide +kernel
theorem jtOK_11264 : (List.range' 11264 1024).all jtOK = true := by decide +kernel
theorem jtOK_15360 : (List.range' 15360 656).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
