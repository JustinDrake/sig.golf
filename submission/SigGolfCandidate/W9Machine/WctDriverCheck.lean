import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDispatch (p bit : Nat) (advance : Bool) : Result :=
  let dig : E := .ld (.c (BitVec.ofNat 64 (96 + 8 * (bit / 64))))
  let child := mkBin .and (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64)))) (.c 127)
  let route := mkBin .or (mkBin .sll child (.c 32)) (.reg .x22)
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then addC (.reg .x28) 512 else .reg .x28
  let key := norm (addC hb (-1600))
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64 + 5)))) (.reg .x2)) (.reg .x24)
  let n := if advance then 15 else 13
  let regs := (((RegFile.init.set .x16 dig).set .x3 child).set .x4 route).set .x23 childPc
  let regs := if advance then (regs.set .x8 (addC (.reg .x8) 1024)).set .x28 hb else regs
  let regs := (((regs.set .x27 (.ld (addC hb (-1600)))).set .x11 (.c 64)).set .x14 field).set
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
def dispatchWords8 : List (BitVec 32) := [0x7803803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch8_checked : rOK (symRun {} dispatchWords8 (pcOf 202) 15)
    (coordDispatch 202 213 true) = true := by
  decide +kernel
theorem dispatch8_linked : sliceChecked 202 dispatchWords8 = true := by
  decide +kernel
def rootWords8 : List (BitVec 32) := [0x79000613,115]
theorem root8_checked : rOK (symRun {} rootWords8 (pcOf 217) 2)
    (coordRoot 217 8) = true := by
  decide +kernel
theorem root8_linked : sliceChecked 217 rootWords8 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords6 : List (BitVec 32) := [0x7003803,44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
theorem dispatch6_checked : rOK (symRun {} dispatchWords6 (pcOf 168) 15)
    (coordDispatch 168 170 true) = true := by
  decide +kernel
theorem dispatch6_linked : sliceChecked 168 dispatchWords6 = true := by
  decide +kernel
def rootWords6 : List (BitVec 32) := [0x77000613,115]
theorem root6_checked : rOK (symRun {} rootWords6 (pcOf 183) 2)
    (coordRoot 183 6) = true := by
  decide +kernel
theorem root6_linked : sliceChecked 183 rootWords6 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords5 : List (BitVec 32) := [0x7003803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch5_checked : rOK (symRun {} dispatchWords5 (pcOf 151) 15)
    (coordDispatch 151 149 true) = true := by
  decide +kernel
theorem dispatch5_linked : sliceChecked 151 dispatchWords5 = true := by
  decide +kernel
def rootWords5 : List (BitVec 32) := [0x76000613,115]
theorem root5_checked : rOK (symRun {} rootWords5 (pcOf 166) 2)
    (coordRoot 166 5) = true := by
  decide +kernel
theorem root5_linked : sliceChecked 166 rootWords5 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords3 : List (BitVec 32) := [0x6803803,44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
theorem dispatch3_checked : rOK (symRun {} dispatchWords3 (pcOf 117) 15)
    (coordDispatch 117 106 true) = true := by
  decide +kernel
theorem dispatch3_linked : sliceChecked 117 dispatchWords3 = true := by
  decide +kernel
def rootWords3 : List (BitVec 32) := [0x74000613,115]
theorem root3_checked : rOK (symRun {} rootWords3 (pcOf 132) 2)
    (coordRoot 132 3) = true := by
  decide +kernel
theorem root3_linked : sliceChecked 132 rootWords3 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords2 : List (BitVec 32) := [0x6803803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch2_checked : rOK (symRun {} dispatchWords2 (pcOf 100) 15)
    (coordDispatch 100 85 true) = true := by
  decide +kernel
theorem dispatch2_linked : sliceChecked 100 dispatchWords2 = true := by
  decide +kernel
def rootWords2 : List (BitVec 32) := [0x73000613,115]
theorem root2_checked : rOK (symRun {} rootWords2 (pcOf 115) 2)
    (coordRoot 115 2) = true := by
  decide +kernel
theorem root2_linked : sliceChecked 115 rootWords2 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords7 : List (BitVec 32) := [0x7803803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch7_checked : rOK (symRun {} dispatchWords7 (pcOf 185) 15)
    (coordDispatch 185 192 true) = true := by
  decide +kernel
theorem dispatch7_linked : sliceChecked 185 dispatchWords7 = true := by
  decide +kernel
def rootWords7 : List (BitVec 32) := [0x78000613,115]
theorem root7_checked : rOK (symRun {} rootWords7 (pcOf 200) 2)
    (coordRoot 200 7) = true := by
  decide +kernel
theorem root7_linked : sliceChecked 200 rootWords7 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords4 : List (BitVec 32) := [0x7003803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch4_checked : rOK (symRun {} dispatchWords4 (pcOf 134) 15)
    (coordDispatch 134 128 true) = true := by
  decide +kernel
theorem dispatch4_linked : sliceChecked 134 dispatchWords4 = true := by
  decide +kernel
def rootWords4 : List (BitVec 32) := [0x75000613,115]
theorem root4_checked : rOK (symRun {} rootWords4 (pcOf 149) 2)
    (coordRoot 149 4) = true := by
  decide +kernel
theorem root4_linked : sliceChecked 149 rootWords4 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords1 : List (BitVec 32) := [0x6803803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch1_checked : rOK (symRun {} dispatchWords1 (pcOf 83) 15)
    (coordDispatch 83 64 true) = true := by
  decide +kernel
theorem dispatch1_linked : sliceChecked 83 dispatchWords1 = true := by
  decide +kernel
def rootWords1 : List (BitVec 32) := [0x72000613,115]
theorem root1_checked : rOK (symRun {} rootWords1 (pcOf 98) 2)
    (coordRoot 98 1) = true := by
  decide +kernel
theorem root1_linked : sliceChecked 98 rootWords1 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords0 : List (BitVec 32) := [0x6003803,45633939,0x7f1f193,33657363,23224883,8493971,31165363,0x9c0e3d83,67110291,50878227,2586419,25626419,458983]
theorem dispatch0_checked : rOK (symRun {} dispatchWords0 (pcOf 68) 13)
    (coordDispatch 68 43 false) = true := by
  decide +kernel
theorem dispatch0_linked : sliceChecked 68 dispatchWords0 = true := by
  decide +kernel
def rootWords0 : List (BitVec 32) := [0x70000613,115]
theorem root0_checked : rOK (symRun {} rootWords0 (pcOf 81) 2)
    (coordRoot 81 0) = true := by
  decide +kernel
theorem root0_linked : sliceChecked 81 rootWords0 = true := by
  decide +kernel
end W9Machine
end

section

end
