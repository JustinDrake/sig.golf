import SigGolfCandidate.T3M.Images.Verify

namespace SigGolfCandidate.T3M.Images
theorem verifyPrefixData_length : verifyPrefixData.length = 4608 := by
  rw [verifyPrefixData, List.length_flatten]
  set_option maxRecDepth 100000 in decide +kernel
theorem verifyLegacyData_length : verifyLegacyData.length = 67584 := by
  set_option maxRecDepth 100000 in decide +kernel
end SigGolfCandidate.T3M.Images
