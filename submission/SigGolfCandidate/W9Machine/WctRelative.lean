import SigGolfCandidate.W9Machine.WctRuns

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def headRHRel (rb : Reg) (off dst : Word) (p chain digit : Nat) : Result :=
  ⟨⟨((RegFile.init.set .x10 (addC (.reg rb) off)).set .x12 (addC (.reg rb) dst)).set
      .x25 (hLoad chain digit),
    [(kAt rb off 24, .reg .x4), (kAt rb off 16, hLoad chain digit)],
    [.valid (kAt rb off 24) 8, .valid (kAt rb off 16) 8, .valid (hKey chain digit) 8]⟩,
    .c (pcOf (p + 5)), .ecall, 5, 5⟩
def rungRRel (rb : Reg) (digit : Nat) (dst : Option Word) (p : Nat) : Result :=
  let n := if dst.isSome then 2 else 1
  ⟨⟨(match dst with
      | some off => RegFile.init.set .x12 (addC (.reg rb) off)
      | none => RegFile.init),
    [(⟨some (.reg .x10), 16⟩, .bin (.st .b 4) (.ld (addC (.reg .x10) 16)) (posE digit))],
    [.align8 (.reg .x10), .valid ⟨some (.reg .x10), 20⟩ 1]⟩,
    .c (pcOf (p + n)), .ecall, n, n⟩
def headSample : List (BitVec 32) :=
  [537134355,587466259,0x940e3c83,26556451,4537379,115]
theorem headSample_checked :
    rOK (symRun {} headSample (pcOf 744) 6) (headRHRel .x8 512 560 744 5 0) = true := by
  decide +kernel
def rungSample : List (BitVec 32) := [7670307,0x3d040613,115]
theorem rungSample_checked :
    rOK (symRun {} rungSample (pcOf 752) 3) (rungRRel .x8 2 (some 976) 752) = true := by
  decide +kernel
def copyFHRel (rb : Reg) (off dst : Word) (p : Nat) : Result :=
  ⟨⟨copyRegs rb off,
    [(kAt rb dst 8, lAt rb off 56), (kAt rb dst 0, lAt rb off 48)],
    [.valid (kAt rb dst 8) 8, .valid (kAt rb dst 0) 8,
      .valid (kAt rb off 56) 8, .valid (kAt rb off 48) 8]⟩,
    .c (pcOf (p + 4)), .fuel, 4, 4⟩
def copySample : List (BitVec 32) := [654586243,662976259,0x3c343023,0x3ce43423]
theorem copySample_checked :
    rOK (symRun {} copySample (pcOf 897) 4) (copyFHRel .x8 576 960 897) = true := by
  decide +kernel
end W9Machine
