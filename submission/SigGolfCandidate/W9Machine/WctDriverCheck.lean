import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def dispatchDig (bit : Nat) : E :=
  if bit = 43 ∨ bit % 64 = 0 then
    .ld (.c (BitVec.ofNat 64 (96 + 8 * (bit / 64)))) else .reg .x16
def dispatchChild (bit : Nat) : E :=
  let dig := dispatchDig bit
  let src := if bit % 64 = 0 then dig else mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64)))
  mkBin .and src (.c 127)
def dispatchCost (bit : Nat) (advance : Bool) : Nat :=
  (if advance then 14 else 12) - (if bit % 64 = 0 then 1 else 0) -
    (if bit = 43 ∨ bit % 64 = 0 then 0 else 1)
def coordDispatch (p bit : Nat) (advance : Bool) : Result :=
  let dig := dispatchDig bit
  let child := dispatchChild bit
  let route := mkBin .or (mkBin .sll child (.c 32)) (.reg .x22)
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then addC (.reg .x28) 512 else .reg .x28
  let key := norm (addC hb (-1600))
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64 + 5)))) (.reg .x2)) (.reg .x24)
  let n := dispatchCost bit advance
  let regs := (((RegFile.init.set .x16 dig).set .x3 child).set .x4 route).set .x23 childPc
  let regs := if advance then (regs.set .x8 (addC (.reg .x8) 1024)).set .x28 hb else regs
  let regs := ((regs.set .x27 (.ld (addC hb (-1600)))).set .x14 field).set
    .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], [.valid key 8]⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
def coordRoot (p coord : Nat) : Result :=
  ⟨⟨RegFile.init.set .x12 (.c (BitVec.ofNat 64
      (1792 + if coord = 0 then 0 else 16 * (coord + 1)))), [], []⟩,
    .c (pcOf (p + 1)), .ecall, 1, 1⟩
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords8 : List (BitVec 32) := [0x1585193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x1a85713,0x277733,0x1870733,0x700e7]
theorem dispatch8_checked : rOK (symRun {} dispatchWords8 (pcOf 187) 13)
    (coordDispatch 187 213 true) = true := by
  decide +kernel
theorem dispatch8_linked : sliceChecked 187 dispatchWords8 = true := by
  decide +kernel
def rootWords8 : List (BitVec 32) := [0x79000613,115]
theorem root8_checked : rOK (symRun {} rootWords8 (pcOf 200) 2)
    (coordRoot 200 8) = true := by
  decide +kernel
theorem root8_linked : sliceChecked 200 rootWords8 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords6 : List (BitVec 32) := [0x2a85193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x2f85713,0x277733,0x1870733,0x700e7]
theorem dispatch6_checked : rOK (symRun {} dispatchWords6 (pcOf 157) 13)
    (coordDispatch 157 170 true) = true := by
  decide +kernel
theorem dispatch6_linked : sliceChecked 157 dispatchWords6 = true := by
  decide +kernel
def rootWords6 : List (BitVec 32) := [0x77000613,115]
theorem root6_checked : rOK (symRun {} rootWords6 (pcOf 170) 2)
    (coordRoot 170 6) = true := by
  decide +kernel
theorem root6_linked : sliceChecked 170 rootWords6 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords5 : List (BitVec 32) := [0x1585193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x1a85713,0x277733,0x1870733,0x700e7]
theorem dispatch5_checked : rOK (symRun {} dispatchWords5 (pcOf 142) 13)
    (coordDispatch 142 149 true) = true := by
  decide +kernel
theorem dispatch5_linked : sliceChecked 142 dispatchWords5 = true := by
  decide +kernel
def rootWords5 : List (BitVec 32) := [0x76000613,115]
theorem root5_checked : rOK (symRun {} rootWords5 (pcOf 155) 2)
    (coordRoot 155 5) = true := by
  decide +kernel
theorem root5_linked : sliceChecked 155 rootWords5 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords3 : List (BitVec 32) := [0x2a85193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x2f85713,0x277733,0x1870733,0x700e7]
theorem dispatch3_checked : rOK (symRun {} dispatchWords3 (pcOf 112) 13)
    (coordDispatch 112 106 true) = true := by
  decide +kernel
theorem dispatch3_linked : sliceChecked 112 dispatchWords3 = true := by
  decide +kernel
def rootWords3 : List (BitVec 32) := [0x74000613,115]
theorem root3_checked : rOK (symRun {} rootWords3 (pcOf 125) 2)
    (coordRoot 125 3) = true := by
  decide +kernel
theorem root3_linked : sliceChecked 125 rootWords3 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords2 : List (BitVec 32) := [0x1585193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x1a85713,0x277733,0x1870733,0x700e7]
theorem dispatch2_checked : rOK (symRun {} dispatchWords2 (pcOf 97) 13)
    (coordDispatch 97 85 true) = true := by
  decide +kernel
theorem dispatch2_linked : sliceChecked 97 dispatchWords2 = true := by
  decide +kernel
def rootWords2 : List (BitVec 32) := [0x73000613,115]
theorem root2_checked : rOK (symRun {} rootWords2 (pcOf 110) 2)
    (coordRoot 110 2) = true := by
  decide +kernel
theorem root2_linked : sliceChecked 110 rootWords2 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords7 : List (BitVec 32) := [0x7803803,0x7f87193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x585713,0x277733,0x1870733,0x700e7]
theorem dispatch7_checked : rOK (symRun {} dispatchWords7 (pcOf 172) 13)
    (coordDispatch 172 192 true) = true := by
  decide +kernel
theorem dispatch7_linked : sliceChecked 172 dispatchWords7 = true := by
  decide +kernel
def rootWords7 : List (BitVec 32) := [0x78000613,115]
theorem root7_checked : rOK (symRun {} rootWords7 (pcOf 185) 2)
    (coordRoot 185 7) = true := by
  decide +kernel
theorem root7_linked : sliceChecked 185 rootWords7 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords4 : List (BitVec 32) := [0x7003803,0x7f87193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x585713,0x277733,0x1870733,0x700e7]
theorem dispatch4_checked : rOK (symRun {} dispatchWords4 (pcOf 127) 13)
    (coordDispatch 127 128 true) = true := by
  decide +kernel
theorem dispatch4_linked : sliceChecked 127 dispatchWords4 = true := by
  decide +kernel
def rootWords4 : List (BitVec 32) := [0x75000613,115]
theorem root4_checked : rOK (symRun {} rootWords4 (pcOf 140) 2)
    (coordRoot 140 4) = true := by
  decide +kernel
theorem root4_linked : sliceChecked 140 rootWords4 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords1 : List (BitVec 32) := [0x6803803,0x7f87193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x40040413,0x200e0e13,0x9c0e3d83,0x585713,0x277733,0x1870733,0x700e7]
theorem dispatch1_checked : rOK (symRun {} dispatchWords1 (pcOf 82) 13)
    (coordDispatch 82 64 true) = true := by
  decide +kernel
theorem dispatch1_linked : sliceChecked 82 dispatchWords1 = true := by
  decide +kernel
def rootWords1 : List (BitVec 32) := [0x72000613,115]
theorem root1_checked : rOK (symRun {} rootWords1 (pcOf 95) 2)
    (coordRoot 95 1) = true := by
  decide +kernel
theorem root1_linked : sliceChecked 95 rootWords1 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords0 : List (BitVec 32) := [0x6003803,0x2b85193,0x7f1f193,0x2019213,0x1626233,0x819b93,0x1db8bb3,0x9c0e3d83,0x3085713,0x277733,0x1870733,0x700e7]
theorem dispatch0_checked : rOK (symRun {} dispatchWords0 (pcOf 68) 12)
    (coordDispatch 68 43 false) = true := by
  decide +kernel
theorem dispatch0_linked : sliceChecked 68 dispatchWords0 = true := by
  decide +kernel
def rootWords0 : List (BitVec 32) := [0x70000613,115]
theorem root0_checked : rOK (symRun {} rootWords0 (pcOf 80) 2)
    (coordRoot 80 0) = true := by
  decide +kernel
theorem root0_linked : sliceChecked 80 rootWords0 = true := by
  decide +kernel
end W9Machine
end

section

end
