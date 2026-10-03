import SigGolfCandidate.T3M.Verify.MerkleRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem mkChunk_1a : mkChunkCheck 1 0 0 64 = true := by decide +kernel
theorem mkChunk_1b : mkChunkCheck 1 0 64 64 = true := by decide +kernel
end SigGolfCandidate.T3M
