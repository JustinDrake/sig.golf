import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctTraceInvariant

set_option autoImplicit false
namespace W9Machine.Chain
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def originalValue (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128) : ChainWord → Word
  | .original off => u.getMem (BitVec.ofNat 64 (base k + off))
  | .header t d => BitVec.ofNat 64 (V3.chainLow index k.val j.val t d)
  | .route => BitVec.ofNat 64 (index + 2 ^ 32 * j.val)
  | .leafHeader => (SigGolfCandidate.T3.header 6 k.val index 0 j.val).extractLsb' 0 64
  | .answer _ _ => 0
structure Inv (u : MachineState) (index : Nat) (k : Fin 9) (j : Fin 128)
    (tr : ChainTrace) (answers : List (BitVec 256)) (s : MachineState) : Prop where
  keep : ∀ r, r ∉ clobbers → s.getReg r = u.getReg r
  frame : Frame u s (writes k)
  memory : TraceMem (chainValue (originalValue u index k j) answers) (base k) tr s
  count : tr.queries.length = answers.length
  available : tr.Available
  hashLen : s.getReg .x11 = 64
  pointers : 0 < answers.length →
    s.getReg .x10 = BitVec.ofNat 64 (base k + tr.input) ∧
    s.getReg .x12 = BitVec.ofNat 64 (base k + tr.output)
end W9Machine.Chain
