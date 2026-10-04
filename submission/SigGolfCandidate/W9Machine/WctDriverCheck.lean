import SigGolfCandidate.W9Machine.WctFetch

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDigest (bit : Nat) : E :=
  if bit % 64 = 0 then .ld (.c (BitVec.ofNat 64 (96 + 8 * (bit / 64)))) else .reg .x16
def coordShift (bit : Nat) : E :=
  if bit % 64 = 0 then coordDigest bit else
    mkBin .srl (coordDigest bit) (.c (BitVec.ofNat 64 (bit % 64)))
def coordDispatch (p bit : Nat) (advance : Bool) : Result :=
  let dig := coordDigest bit
  let child := mkBin .and (coordShift bit) (.c 127)
  let route := mkBin .or (mkBin .sll child (.c 32)) (.reg .x22)
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then addC (.reg .x28) 512 else .reg .x28
  let key := norm (addC hb (-1600))
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64 + 5)))) (.reg .x2)) (.reg .x24)
  let n := if advance then 14 else 12
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
def dispatchWords8 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch8_checked : rOK (symRun {} dispatchWords8 (pcOf 194) 14)
    (coordDispatch 194 213 true) = true := by
  decide +kernel
theorem dispatch8_linked : sliceChecked 194 dispatchWords8 = true := by
  decide +kernel
def rootWords8 : List (BitVec 32) := [0x79000613,115]
theorem root8_checked : rOK (symRun {} rootWords8 (pcOf 208) 2)
    (coordRoot 208 8) = true := by
  decide +kernel
theorem root8_linked : sliceChecked 208 rootWords8 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords6 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
theorem dispatch6_checked : rOK (symRun {} dispatchWords6 (pcOf 162) 14)
    (coordDispatch 162 170 true) = true := by
  decide +kernel
theorem dispatch6_linked : sliceChecked 162 dispatchWords6 = true := by
  decide +kernel
def rootWords6 : List (BitVec 32) := [0x77000613,115]
theorem root6_checked : rOK (symRun {} rootWords6 (pcOf 176) 2)
    (coordRoot 176 6) = true := by
  decide +kernel
theorem root6_linked : sliceChecked 176 rootWords6 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords5 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch5_checked : rOK (symRun {} dispatchWords5 (pcOf 146) 14)
    (coordDispatch 146 149 true) = true := by
  decide +kernel
theorem dispatch5_linked : sliceChecked 146 dispatchWords5 = true := by
  decide +kernel
def rootWords5 : List (BitVec 32) := [0x76000613,115]
theorem root5_checked : rOK (symRun {} rootWords5 (pcOf 160) 2)
    (coordRoot 160 5) = true := by
  decide +kernel
theorem root5_linked : sliceChecked 160 rootWords5 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords3 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
theorem dispatch3_checked : rOK (symRun {} dispatchWords3 (pcOf 114) 14)
    (coordDispatch 114 106 true) = true := by
  decide +kernel
theorem dispatch3_linked : sliceChecked 114 dispatchWords3 = true := by
  decide +kernel
def rootWords3 : List (BitVec 32) := [0x74000613,115]
theorem root3_checked : rOK (symRun {} rootWords3 (pcOf 128) 2)
    (coordRoot 128 3) = true := by
  decide +kernel
theorem root3_linked : sliceChecked 128 rootWords3 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords2 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
theorem dispatch2_checked : rOK (symRun {} dispatchWords2 (pcOf 98) 14)
    (coordDispatch 98 85 true) = true := by
  decide +kernel
theorem dispatch2_linked : sliceChecked 98 dispatchWords2 = true := by
  decide +kernel
def rootWords2 : List (BitVec 32) := [0x73000613,115]
theorem root2_checked : rOK (symRun {} rootWords2 (pcOf 112) 2)
    (coordRoot 112 2) = true := by
  decide +kernel
theorem root2_linked : sliceChecked 112 rootWords2 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords7 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch7_checked : rOK (symRun {} dispatchWords7 (pcOf 178) 14)
    (coordDispatch 178 192 true) = true := by
  decide +kernel
theorem dispatch7_linked : sliceChecked 178 dispatchWords7 = true := by
  decide +kernel
def rootWords7 : List (BitVec 32) := [0x78000613,115]
theorem root7_checked : rOK (symRun {} rootWords7 (pcOf 192) 2)
    (coordRoot 192 7) = true := by
  decide +kernel
theorem root7_linked : sliceChecked 192 rootWords7 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords4 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch4_checked : rOK (symRun {} dispatchWords4 (pcOf 130) 14)
    (coordDispatch 130 128 true) = true := by
  decide +kernel
theorem dispatch4_linked : sliceChecked 130 dispatchWords4 = true := by
  decide +kernel
def rootWords4 : List (BitVec 32) := [0x75000613,115]
theorem root4_checked : rOK (symRun {} rootWords4 (pcOf 144) 2)
    (coordRoot 144 4) = true := by
  decide +kernel
theorem root4_linked : sliceChecked 144 rootWords4 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords1 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
theorem dispatch1_checked : rOK (symRun {} dispatchWords1 (pcOf 82) 14)
    (coordDispatch 82 64 true) = true := by
  decide +kernel
theorem dispatch1_linked : sliceChecked 82 dispatchWords1 = true := by
  decide +kernel
def rootWords1 : List (BitVec 32) := [0x72000613,115]
theorem root1_checked : rOK (symRun {} rootWords1 (pcOf 96) 2)
    (coordRoot 96 1) = true := by
  decide +kernel
theorem root1_linked : sliceChecked 96 rootWords1 = true := by
  decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords0 : List (BitVec 32) := [45633939,0x7f1f193,33657363,23224883,8493971,31165363,0x9c0e3d83,67110291,50878227,2586419,25626419,458983]
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
