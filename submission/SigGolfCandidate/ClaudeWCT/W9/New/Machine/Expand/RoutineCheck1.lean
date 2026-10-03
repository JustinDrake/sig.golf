import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_64 : (List.range' 64 64).all routineOK = true := by decide +kernel
theorem routineOK_256 : (List.range' 256 64).all routineOK = true := by decide +kernel
theorem routineOK_448 : (List.range' 448 64).all routineOK = true := by decide +kernel
theorem routineOK_640 : (List.range' 640 64).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
