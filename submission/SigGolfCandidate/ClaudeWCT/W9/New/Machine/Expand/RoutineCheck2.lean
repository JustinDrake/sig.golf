import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem routineOK_128 : (List.range' 128 64).all routineOK = true := by decide +kernel
theorem routineOK_320 : (List.range' 320 64).all routineOK = true := by decide +kernel
theorem routineOK_512 : (List.range' 512 64).all routineOK = true := by decide +kernel
theorem routineOK_704 : (List.range' 704 24).all routineOK = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand
