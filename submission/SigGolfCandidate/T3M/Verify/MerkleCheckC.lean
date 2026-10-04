import SigGolfCandidate.T3M.Verify.MerkleRuns

namespace SigGolfCandidate.T3M
set_option maxRecDepth 100000
theorem mkChunk_00 : mkChunkCheck 0 0 0 64 = true := by decide +kernel
theorem mkChunk_01 : mkChunkCheck 0 1 0 64 = true := by decide +kernel
end SigGolfCandidate.T3M
