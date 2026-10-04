import SigGolfCandidate.W9Machine.WctChainInvDefs
import SigGolfCandidate.W9Machine.WctTraceProgram

set_option autoImplicit false
namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
def sourceEnds (w : WBytes) (k : Fin 9) (rank : Fin 728)
    (answers : List (BitVec 256)) : List Digest :=
  (List.finRange 7).map fun t =>
    let digits := ClaudeWCT.WCT9.codeword rank
    if digits.getD t.val 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t.val)
    else (answers.getD ((digits.take (t.val + 1)).sum - 1) 0).extractLsb' 0 128
def SourceEquivalent : Prop :=
  ∀ (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState), Pre L w index k j rank u →
    (do
      let answers ← traceProgram (originalValue u index k j)
        (expectedQueries (ClaudeWCT.WCT9.codeword rank)) []
      pure (sourceEnds w k rank answers) : M (List Digest)) = program w index k j rank
def EndpointsCorrect : Prop :=
  ∀ (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u s : MachineState) (tr : ChainTrace) (answers : List (BitVec 256)),
    Pre L w index k j rank u → Inv u index k j tr answers s →
    (∀ t, t < 7 → ∀ word, word < 2 →
      tr.read (traceLeafSlot t + 8 * word) =
        expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) →
    ∀ t, t < 7 →
      DigAt s (base k + traceLeafSlot t) ((sourceEnds w k rank answers).getD t 0)
end W9Machine.Chain
