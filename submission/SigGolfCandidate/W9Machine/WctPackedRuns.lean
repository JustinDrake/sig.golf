import SigGolfCandidate.W9Machine.WctLayout
import SigGolfCandidate.T3M.Verify.ChainRuns

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def packedHeader (chain digit : Nat) : E :=
  addC (.reg .x31) (BitVec.ofNat 64 (128 + 4 * chain + 256 * digit))
def packedPos (digit : Nat) : E :=
  if digit = 1 then .reg .x7 else if digit = 2 then .reg .x13 else .c 0
def headRHRel (rb : Reg) (off dst : Word) (p chain digit : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (.reg rb) dst)).set
      .x25 (packedHeader chain digit),
    [(kAt rb off 16, packedHeader chain digit)], [.valid (kAt rb off 16) 8]⟩,
    .c (pcOf (p + 4)), .ecall, 4, 4⟩
def rungRRel (rb : Reg) (digit : Nat) (dst : Option Word) (p : Nat) : Result :=
  let n := if dst.isSome then 2 else 1
  ⟨⟨(match dst with
      | some off => RegFile.init.set .x12 (addC (.reg rb) off)
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 1) (.ld (addC (.reg .x10) 16)) (packedPos digit))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 17⟩ 1]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def copyFHRel (rb : Reg) (off dst : Word) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off,
    [(kAt rb dst 8, lAt rb off 56), (kAt rb dst 0, lAt rb off 48)],
    [.valid (kAt rb dst 8) 8, .valid (kAt rb dst 0) 8,
      .valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]⟩,
    .c (pcOf (p + 4)), .fuel, 4, 4⟩
end W9Machine
