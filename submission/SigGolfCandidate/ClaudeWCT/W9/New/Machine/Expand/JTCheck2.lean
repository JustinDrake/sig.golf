import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem jtOK_2048 : (List.range' 2048 1024).all jtOK = true := by decide +kernel
theorem jtOK_6144 : (List.range' 6144 1024).all jtOK = true := by decide +kernel
theorem jtOK_10240 : (List.range' 10240 1024).all jtOK = true := by decide +kernel
theorem jtOK_14336 : (List.range' 14336 1024).all jtOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
