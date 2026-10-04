import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Machine.WctJudg

namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def FtsGood : Prop :=
  ∀ (pk : Digest) (w : WBytes) (a : HashOutput) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Option Digest → OracleComp HashSpec Obs),
    GatePre pk w a u →
    K none = pure (false, 0) →
    (∀ root t, FtsOut ⟨pk, w, a⟩ root t →
      GoodQFor Frozen.image t N C Q A (K (some root))) →
    GoodQFor Frozen.image u (N + 1982) (C + 1982) Q (A + 1982)
      (ccM (if ClaudeWCT.W9.T3M.gateOk a then ClaudeWCT.W9.T3M.wctP w a
        else pure none) K)
end W9Drv
