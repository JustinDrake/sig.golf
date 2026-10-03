import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_0 : (List.range' 0 64).all routineOK = true := by decide +kernel
theorem routineOK_192 : (List.range' 192 64).all routineOK = true := by decide +kernel
theorem routineOK_384 : (List.range' 384 64).all routineOK = true := by decide +kernel
theorem routineOK_576 : (List.range' 576 64).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
