import SigGolfCandidate.T3M.Verify.MerkleRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem mkChunk_3 : mkChunkCheck 3 0 0 64 = true := by decide +kernel
theorem mkChunk_2 : mkChunkCheck 2 0 0 64 = true := by decide +kernel
end SigGolfCandidate.T3M
