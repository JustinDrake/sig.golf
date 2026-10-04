import SigGolfCandidate.W9Machine.WctRungSem
import SigGolfCandidate.W9Machine.WctCopySem
import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest M shortHash header)
open OracleComp
theorem wctChainInputP_eq (index coord child t step : Nat) (pad0 pad1 value : Digest) :
    ClaudeWCT.W9.T3M.wctChainInputP index coord child t step pad0 pad1 value =
      blk4 pad0 (header 5 coord index (step + 256 * t) child) pad1 value := by
  unfold ClaudeWCT.W9.T3M.wctChainInputP blk4
  rw [ClaudeWCT.WCT9.chain_header_eq]
theorem wctChainP_zero (index coord child t start : Nat) (pad0 pad1 value : Digest) :
    ClaudeWCT.W9.T3M.wctChainP index coord child t start 0 pad0 pad1 value = pure value := by
  rfl
theorem wctChainP_succ (index coord child t start count : Nat) (pad0 pad1 value : Digest) :
    ClaudeWCT.W9.T3M.wctChainP index coord child t start (count + 1) pad0 pad1 value =
      (shortHash (ClaudeWCT.W9.T3M.wctChainInputP index coord child t start pad0 pad1 value) >>=
        fun v => ClaudeWCT.W9.T3M.wctChainP index coord child t (start + 1) count pad0 pad1 v) := by
  unfold ClaudeWCT.W9.T3M.wctChainP
  rw [List.range'_succ, List.foldlM_cons]
theorem wct_step_register (s : MachineState) (d : Nat) (hd : d < 3)
    (h6 : s.getReg .x6 = 1) (h7 : s.getReg .x7 = 2) :
    (posE d).eval s = BitVec.ofNat 64 d := by
  interval_cases d <;> simp [posE, posReg, RegFile.init, RegFile.get, h6, h7]
end W9Machine
