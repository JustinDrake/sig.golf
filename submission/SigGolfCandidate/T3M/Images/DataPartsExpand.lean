import SigGolfCandidate.T3M.Images.Expand

namespace SigGolfCandidate.T3M.Images
theorem expandPrefixData_length : expandPrefixData.length = 4608 := by
  rw [expandPrefixData, List.length_flatten]
  set_option maxRecDepth 100000 in decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by
  set_option maxRecDepth 100000 in decide +kernel
end SigGolfCandidate.T3M.Images
