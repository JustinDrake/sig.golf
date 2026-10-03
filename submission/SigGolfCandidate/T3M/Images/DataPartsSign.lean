import SigGolfCandidate.T3M.Images.Sign

namespace SigGolfCandidate.T3M.Images
theorem signPrefixData_length : signPrefixData.length = 65536 := by
  rw [signPrefixData, List.length_flatten]
  set_option maxRecDepth 100000 in decide +kernel
theorem signLegacyData_length : signLegacyData.length = 4096 := by
  set_option maxRecDepth 100000 in decide +kernel
end SigGolfCandidate.T3M.Images
