import SigGolfCandidate.T3M.Verify.MerkleRuns

/-! Kernel checks of the Merkle shape blocks of layers 3 and 2 (64 blocks each: the table-word entry and the six
levels, ending at the root HASH into the next encoding block). -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem mkChunk_3 : mkChunkCheck 3 0 0 64 = true := by decide +kernel
theorem mkChunk_2 : mkChunkCheck 2 0 0 64 = true := by decide +kernel

end SigGolfCandidate.T3M
