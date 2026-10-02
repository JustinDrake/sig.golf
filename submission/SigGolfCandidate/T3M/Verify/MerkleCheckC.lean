import SigGolfCandidate.T3M.Verify.MerkleRuns

/-! Kernel checks of the Merkle shape blocks of layer 0 (chunk 0: 64 blocks of levels 0..5 ending with the chunk-1
dispatch; chunk 1: 64 blocks of levels 6..11 ending at the root HASH into `0x180`) and of the 64 compare copies. -/

namespace SigGolfCandidate.T3M

set_option maxRecDepth 100000

theorem mkChunk_00 : mkChunkCheck 0 0 0 64 = true := by decide +kernel
theorem mkChunk_01 : mkChunkCheck 0 1 0 64 = true := by decide +kernel
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel

end SigGolfCandidate.T3M
