import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Drv.GateDefs
import SigGolfCandidate.W9Drv.SourceBridge
import SigGolfCandidate.W9Machine.WctChainContract
import SigGolfCandidate.W9Machine.WctJTImageLink
import SigGolfCandidate.W9Drv.Gate

section

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
def coordDispatch (p bit coord : Nat) (advance reload : Bool) : Result :=
  let dig : E := if reload then .ld (.c (BitVec.ofNat 64 (96 + 8 * (bit / 64)))) else .reg .x16
  let child := mkBin .and (if bit % 64 = 0 then dig else
    mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64)))) (.c 127)
  let route := mkBin .or (mkBin .sll child (.c 32)) (.reg .x22)
  let pre := if advance then mkAdd (.reg .x15) (.reg .x6) else .reg .x15
  let packed := mkBin .or (mkBin .sll child (.c 20)) pre
  let childPc := mkAdd (mkBin .sll child (.c 8)) (.reg .x29)
  let hb := if advance then addC (.reg .x28) 512 else .reg .x28
  let key := norm (addC hb (-1600))
  let field := mkAdd (mkBin .and
    (mkBin .srl dig (.c (BitVec.ofNat 64 (bit % 64 + 5)))) (.reg .x2)) (.reg .x24)
  let n := if advance then 18 else 16
  let regs := if reload then RegFile.init.set .x16 dig else RegFile.init
  let regs := (regs.set .x3 child).set .x4 route
  let regs := if advance then regs.set .x15 pre else regs
  let regs := (regs.set .x31 packed).set .x23 childPc
  let regs := if advance then (regs.set .x8 (addC (.reg .x8) 1024)).set .x28 hb else regs
  let regs := (((regs.set .x27 (mkBin .or (.ld (addC hb (-1600))) (.reg .x17))).set
    .x14 field).set .x9 (.c (BitVec.ofNat 64 (0x420 + 32 * coord)))).set
    .x1 (.c (pcOf (p + n)))
  ⟨⟨regs, [], [.valid key 8]⟩, mkBin .and field (.c (~~~1#64)), .jump, n, n⟩
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords8 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x52000493,458983]
theorem dispatch8_checked : rOK (symRun {} dispatchWords8 (pcOf 199) 18) (coordDispatch 199 213 8 true false) = true := by decide +kernel
theorem dispatch8_linked : sliceChecked 199 dispatchWords8 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords6 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,49829651,2586419,25626419,0x4e000493,458983]
theorem dispatch6_checked : rOK (symRun {} dispatchWords6 (pcOf 163) 18) (coordDispatch 163 170 6 true false) = true := by decide +kernel
theorem dispatch6_linked : sliceChecked 163 dispatchWords6 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords5 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x4c000493,458983]
theorem dispatch5_checked : rOK (symRun {} dispatchWords5 (pcOf 145) 18) (coordDispatch 145 149 5 true false) = true := by decide +kernel
theorem dispatch5_linked : sliceChecked 145 dispatchWords5 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords3 : List (BitVec 32) := [44585363,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,49829651,2586419,25626419,0x48000493,458983]
theorem dispatch3_checked : rOK (symRun {} dispatchWords3 (pcOf 109) 18) (coordDispatch 109 106 3 true false) = true := by decide +kernel
theorem dispatch3_linked : sliceChecked 109 dispatchWords3 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords7 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x50000493,458983]
theorem dispatch7_checked : rOK (symRun {} dispatchWords7 (pcOf 181) 18) (coordDispatch 181 192 7 true true) = true := by decide +kernel
theorem dispatch7_linked : sliceChecked 181 dispatchWords7 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords4 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x4a000493,458983]
theorem dispatch4_checked : rOK (symRun {} dispatchWords4 (pcOf 127) 18) (coordDispatch 127 128 4 true true) = true := by decide +kernel
theorem dispatch4_linked : sliceChecked 127 dispatchWords4 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords2 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,27809555,2586419,25626419,0x46000493,458983]
theorem dispatch2_checked : rOK (symRun {} dispatchWords2 (pcOf 91) 18) (coordDispatch 91 85 2 true false) = true := by decide +kernel
theorem dispatch2_linked : sliceChecked 91 dispatchWords2 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords1 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x9c0e3d83,18738611,5789459,2586419,25626419,0x44000493,458983]
theorem dispatch1_checked : rOK (symRun {} dispatchWords1 (pcOf 73) 18) (coordDispatch 73 64 1 true true) = true := by decide +kernel
theorem dispatch1_linked : sliceChecked 73 dispatchWords1 = true := by decide +kernel
end W9Machine
end

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def dispatchWords0 : List (BitVec 32) := [0x6003803,45633939,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x9c0e3d83,18738611,50878227,2586419,25626419,0x42000493,458983]
theorem dispatch0_checked : rOK (symRun {} dispatchWords0 (pcOf 57) 16) (coordDispatch 57 43 0 false true) = true := by decide +kernel
theorem dispatch0_linked : sliceChecked 57 dispatchWords0 = true := by decide +kernel
end W9Machine
end

section

end

section


namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def dispatchCode (k : Fin 9) : List (BitVec 32) :=
  [dispatchWords0, dispatchWords1, dispatchWords2, dispatchWords3, dispatchWords4,
    dispatchWords5, dispatchWords6, dispatchWords7, dispatchWords8].getD k.val []
def dispatchBit (k : Fin 9) : Nat := [43,64,85,106,128,149,170,192,213].getD k.val 0
def dispatchLen (k : Fin 9) : Nat := if k.val = 0 then 16 else 18
def dispatchResult (k : Fin 9) : Result :=
  coordDispatch (dispatchPc k.val) (dispatchBit k) k.val (decide (k.val ≠ 0))
    (decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 4 ∨ k.val = 7))
theorem dispatch_checked (k : Fin 9) :
    rOK (symRun {} (dispatchCode k) (pcOf (dispatchPc k.val)) (dispatchLen k))
      (dispatchResult k) = true := by
  fin_cases k
  · exact dispatch0_checked
  · exact dispatch1_checked
  · exact dispatch2_checked
  · exact dispatch3_checked
  · exact dispatch4_checked
  · exact dispatch5_checked
  · exact dispatch6_checked
  · exact dispatch7_checked
  · exact dispatch8_checked
theorem dispatch_linked (k : Fin 9) :
    sliceChecked (dispatchPc k.val) (dispatchCode k) = true := by
  fin_cases k
  · exact dispatch0_linked
  · exact dispatch1_linked
  · exact dispatch2_linked
  · exact dispatch3_linked
  · exact dispatch4_linked
  · exact dispatch5_linked
  · exact dispatch6_linked
  · exact dispatch7_linked
  · exact dispatch8_linked
theorem dispatch_mem (k : Fin 9) (u : MachineState) (A : Word) :
    ((dispatchResult k).toState u).getMem A = u.getMem A := by
  rfl
theorem dispatch_steps (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    Steps Frozen.image u (dispatchLen k) (dispatchLen k) ((dispatchResult k).toState u) := by
  have hs := symRun_sound (rOK_eq (dispatch_checked k))
    (slice_at _ _ (dispatch_linked k)) u hu.pc
  have hcost : (dispatchResult k).steps = dispatchLen k ∧
      (dispatchResult k).cycles = dispatchLen k := by
    fin_cases k <;> exact ⟨rfl, rfl⟩
  rw [hcost.1, hcost.2] at hs
  apply hs
  change Oblig.all u (dispatchResult k).st.obl
  rw [Oblig.all_iff]
  simp only [dispatchResult, coordDispatch, List.mem_singleton]
  intro o ho
  subst o
  simp only [Oblig.holds, norm_eval, addC_eval]
  fin_cases k <;> simp [addC_eval, E.eval, hu.headerReg, accessValid, rangeValid,
    MEMORY_BYTES]
end W9Drv
end

section



set_option maxRecDepth 10000
namespace W9Drv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
def chainEntryState (a : HashOutput) (k : Fin 9) (u : MachineState) : MachineState :=
  { (dispatchResult k).toState u with
    pc := pcOf (Frozen.layout.chainWord (ClaudeWCT.WCT9.rank a k)) }
theorem dispatch_child (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64)) &&& 127#64 =
      BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  change _ &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.child, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
def dispatchDig (k : Fin 9) : E :=
  if decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 4 ∨ k.val = 7) then
    .ld (.c (BitVec.ofNat 64 (96 + 8*(dispatchBit k/64)))) else .reg .x16
theorem dispatchDig_eval (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchDig k).eval u = a.extractLsb' (64*(dispatchBit k/64)) 64 := by
  have hd := hu.digest (dispatchBit k/64) (by fin_cases k <;> decide)
  fin_cases k <;> first | exact hd | exact hu.cached (by decide)
def dispatchChild (k : Fin 9) : E := mkBin .and
  (if dispatchBit k % 64 = 0 then dispatchDig k else
    mkBin .srl (dispatchDig k) (.c (BitVec.ofNat 64 (dispatchBit k % 64)))) (.c 127)
theorem dispatchChild_eval (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    (dispatchChild k).eval u = BitVec.ofNat 64 (ClaudeWCT.WCT9.child a k).val := by
  have hd := dispatchDig_eval pk w a k pairs u hu
  have hs : (BitVec.ofNat 64 (dispatchBit k % 64)).toNat % 64 = dispatchBit k % 64 := by
    simp only [BitVec.toNat_ofNat]; omega
  unfold dispatchChild
  split
  · rename_i he
    simp only [mkBin_eval, E.eval, BinOp.eval, hd]
    have hc := dispatch_child a k
    simp only [he, BitVec.ushiftRight_zero] at hc
    exact hc
  · simp only [mkBin_eval, E.eval, BinOp.eval, hd, hs]
    exact dispatch_child a k
theorem dispatch_keep (k : Fin 9) (u : MachineState) (r : Reg)
    (hr : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
    ((dispatchResult k).toState u).getReg r = u.getReg r := by
  rw [Result.toState_getReg]
  fin_cases k <;> cases r <;> first | rfl | exact False.elim (hr (by decide))
theorem dispatch_route (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x4 =
      ((dispatchChild k).eval u <<< 32) ||| u.getReg .x22 := by
  fin_cases k <;> rfl
theorem dispatch_childPC (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x23 =
      ((dispatchChild k).eval u <<< 8) + u.getReg .x29 := by
  fin_cases k <;> rfl
theorem dispatch_prefix (k : Fin 9) (u : MachineState) :
    ((dispatchResult k).toState u).getReg .x31 =
      ((dispatchChild k).eval u <<< 20) |||
        (if k.val = 0 then u.getReg .x15 else u.getReg .x15 + u.getReg .x6) := by
  fin_cases k <;> rfl
theorem packedPrefix_eval (i k j : Nat) (hk : k < 9) :
    (BitVec.ofNat 64 j <<< 20) ||| BitVec.ofNat 64 (i*2^27 + 65536*k) =
      BitVec.ofNat 64 (V3.chainPrefix i k j) := by
  have hc : 65536*k < 2^27 := by omega
  have hp : i*2^27 + 65536*k = (i <<< 27) ||| (k <<< 16) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa [Nat.shiftLeft_eq, Nat.mul_comm] using hc)]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hp, BitVec.ofNat_or]
  have hs (x n : Nat) : BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x <<< n) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]
  rw [hs, ← BitVec.ofNat_or, ← BitVec.ofNat_or]
  unfold V3.chainPrefix
  rw [Nat.or_comm]
theorem dispatch_chain_pre (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val pairs u) :
    Chain.Pre Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k) (ClaudeWCT.WCT9.rank a k)
      (chainEntryState a k u) := by
  have hm (A : Word) : (chainEntryState a k u).getMem A = u.getMem A := rfl
  have hr (r : Reg) (h : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hc := dispatchChild_eval pk w a k pairs u hu
  have hi : idxOf a < 2^31 := Nat.mod_lt _ (by decide)
  have hj := (ClaudeWCT.WCT9.child a k).isLt
  refine {
    indexBound := hi
    pc := rfl
    baseReg := ?_
    headerReg := ?_
    prefixReg := ?_
    route := ?_
    hashMode := (hr .x5 (by decide)).trans (hu.glob.1 (.x5, 0) (by simp [baseK]))
    stepOne := (hr .x7 (by decide)).trans hu.stepOne
    stepTwo := (hr .x13 (by decide)).trans hu.stepTwo
    hashLen := (hr .x11 (by decide)).trans hu.hashLen
    childPC := ?_
    returnPC := ?_
    indexReg := (hr .x22 (by decide)).trans hu.index
    nodeHeader := ?_
    forestPointer := ?_
    heaps := ?_
    leafHeader := ?_
    witness := by
      intro off ho h8
      have hw := hu.coords k (Nat.le_refl _) off ho h8
      rw [hm]
      simpa only [OrigW, Chain.base, coordinateBase, V3.regionOffset,
        show 2112 + 1024*k.val + off - 2048 = 64 + 1024*k.val + off by omega] using hw }
  · change ((dispatchResult k).toState u).getReg .x8 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.baseReg, Chain.base, coordinateBase]
  · change ((dispatchResult k).toState u).getReg .x28 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, hu.headerReg, Chain.table, headerTable]
  · change ((dispatchResult k).toState u).getReg .x31 = _
    rw [dispatch_prefix, hc, hu.prefixReg, hu.coordStep]
    have he : (if k.val = 0 then BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1))
        else BitVec.ofNat 64 (idxOf a*2^27+65536*(k.val-1)) + 65536) =
        BitVec.ofNat 64 (idxOf a*2^27+65536*k.val) := by
      fin_cases k <;> simp [← BitVec.ofNat_add, Nat.add_assoc]
    rw [he]
    exact packedPrefix_eval _ _ _ k.isLt
  · change ((dispatchResult k).toState u).getReg .x4 = _
    rw [dispatch_route, hc, hu.index]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : (ClaudeWCT.WCT9.child a k).val < 2^64),
      Nat.mod_eq_of_lt (by omega : (ClaudeWCT.WCT9.child a k).val * 2^32 < 2^64),
      Nat.mod_eq_of_lt (by omega : idxOf a < 2^64)]
    rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega : idxOf a < 2^32)]
    omega
  · change ((dispatchResult k).toState u).getReg .x23 = _
    rw [dispatch_childPC, hc, hu.childBlock]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Frozen.layout, pcOf]
    omega
  · change ((dispatchResult k).toState u).getReg .x1 = _
    fin_cases k <;> rfl
  · change ((dispatchResult k).toState u).getReg .x27 = _
    have hb := hu.bank.node k
    have he : ((dispatchResult k).toState u).getReg .x27 =
        BitVec.ofNat 64 (1+3*256+(4+k.val)*65536) ||| BitVec.ofNat 64 (idxOf a*2^32) := by
      fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
        RegFile.get, RegFile.set, RegFile.init, addC_eval, E.eval, mkBin_eval,
        hu.headerReg, hu.nodeIndex, BinOp.eval] <;>
        norm_num at hb <;> rw [hb]
    rw [he, nodeLow_add]
    rw [BitVec.or_comm, ofNat_or_disjoint _ _ 32
      (by have := k.isLt; omega) (by simp)]
    rw [Nat.add_comm]
  · change ((dispatchResult k).toState u).getReg .x9 = _
    fin_cases k <;> rfl
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hu.heaps h h2 h7)
  · rw [hm, header_lo, if_neg (by decide)]
    rw [hdr0_eq 6 k.val (idxOf a) 0 (by decide) (by have := k.isLt; omega)
      (by omega) (by decide)]
    simpa [Chain.table, headerTable, Nat.mul_comm] using hu.bank.leaf k
end W9Drv
end

section


namespace W9Drv
set_option maxRecDepth 10000
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem aligned_clear_low (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0
    simp
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]
    simp [h]
  · simp [h0, hj]
theorem field_mask (x : BitVec 64) :
    x &&& 65532#64 = ((x >>> 2) &&& 16383#64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp
theorem dispatch_field (a : HashOutput) (k : Fin 9) :
    (a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>> (dispatchBit k % 64 + 5)) &&&
      65532#64 = BitVec.ofNat 64 (4 * ClaudeWCT.WCT9.field a k) := by
  rw [field_mask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change (_ &&& (2 ^ 14 - 1)) * 4 % 2 ^ 64 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  fin_cases k <;> simp [dispatchBit, ClaudeWCT.WCT9.field, ClaudeWCT.WCT9.coordBase,
    BitVec.toNat_ofNat] <;> omega
theorem dispatch_pc (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (roots : List (Digest × Digest)) (u : MachineState) (hu : CoordPre pk w a k.val roots u) :
    ((dispatchResult k).toState u).pc = pcOf (jtStart + ClaudeWCT.WCT9.field a k) := by
  have he : ((dispatchResult k).toState u).pc =
      (mkBin .and (mkAdd (mkBin .and
    (mkBin .srl (dispatchDig k)
      (.c (BitVec.ofNat 64 (dispatchBit k % 64 + 5)))) (.reg .x2)) (.reg .x24))
      (.c (~~~1#64))).eval u := by
    fin_cases k <;> rfl
  rw [he]
  simp only [mkBin_eval, mkAdd_eval, E.eval, BinOp.eval, hu.mask, hu.jt]
  rw [dispatchDig_eval pk w a k roots u hu]
  have hshift : (BitVec.ofNat 64 (dispatchBit k % 64 + 5)).toNat % 64 =
      dispatchBit k % 64 + 5 := by fin_cases k <;> decide
  rw [hshift]
  change (((a.extractLsb' (64 * (dispatchBit k / 64)) 64 >>>
    (dispatchBit k % 64 + 5)) &&& 65532#64) + 878592#64) &&& ~~~1#64 = _
  rw [dispatch_field a k]
  rw [ofNat_add_ofNat, aligned_clear_low _ (by omega)]
  congr 1
  unfold jtStart
  omega
theorem codeAt_single (pc : Nat) (words : List (BitVec 32))
    (hb : pc + words.length < 242393)
    (hc : CodeAt Frozen.image (pcOf pc) words) (i : Nat) (hi : i < words.length) :
    CodeAt Frozen.image (pcOf (pc + i)) [words[i]] := by
  have hp : (pcOf pc).toNat = 4096 + 4 * pc := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  have hpi : (pcOf (pc + i)).toNat = 4096 + 4 * (pc + i) := by
    simp only [pcOf, BitVec.toNat_ofNat]
    omega
  refine ⟨by rw [hpi]; omega, by rw [hpi]; omega, by rw [hpi]; simp; omega, ?_⟩
  have hpre := hc.2.2.2.drop i
  have hs : [words[i]] <+: words.drop i := by
    rw [List.singleton_prefix_iff_head?_eq_some]
    simp [List.head?_drop, hi]
  have ht := hs.trans hpre
  simpa [hp, hpi, List.drop_drop, Nat.add_comm] using ht
def jtChunk (c : Fin 64) : List (BitVec 32) :=
  [jtWords00, jtWords01, jtWords02, jtWords03, jtWords04, jtWords05, jtWords06, jtWords07, jtWords08, jtWords09, jtWords10, jtWords11, jtWords12, jtWords13, jtWords14, jtWords15, jtWords16, jtWords17, jtWords18, jtWords19, jtWords20, jtWords21, jtWords22, jtWords23, jtWords24, jtWords25, jtWords26, jtWords27, jtWords28, jtWords29, jtWords30, jtWords31, jtWords32, jtWords33, jtWords34, jtWords35, jtWords36, jtWords37, jtWords38, jtWords39, jtWords40, jtWords41, jtWords42, jtWords43, jtWords44, jtWords45, jtWords46, jtWords47, jtWords48, jtWords49, jtWords50, jtWords51, jtWords52, jtWords53, jtWords54, jtWords55, jtWords56, jtWords57, jtWords58, jtWords59, jtWords60, jtWords61, jtWords62, jtWords63].getD c.val []
theorem jtChunk_length (c : Fin 64) : (jtChunk c).length = 256 := by
  fin_cases c <;> rfl
theorem jtChunk_checked (c : Fin 64) : jtCheck (256 * c.val) (jtChunk c) = true := by
  fin_cases c
  · exact jtCheck00
  · exact jtCheck01
  · exact jtCheck02
  · exact jtCheck03
  · exact jtCheck04
  · exact jtCheck05
  · exact jtCheck06
  · exact jtCheck07
  · exact jtCheck08
  · exact jtCheck09
  · exact jtCheck10
  · exact jtCheck11
  · exact jtCheck12
  · exact jtCheck13
  · exact jtCheck14
  · exact jtCheck15
  · exact jtCheck16
  · exact jtCheck17
  · exact jtCheck18
  · exact jtCheck19
  · exact jtCheck20
  · exact jtCheck21
  · exact jtCheck22
  · exact jtCheck23
  · exact jtCheck24
  · exact jtCheck25
  · exact jtCheck26
  · exact jtCheck27
  · exact jtCheck28
  · exact jtCheck29
  · exact jtCheck30
  · exact jtCheck31
  · exact jtCheck32
  · exact jtCheck33
  · exact jtCheck34
  · exact jtCheck35
  · exact jtCheck36
  · exact jtCheck37
  · exact jtCheck38
  · exact jtCheck39
  · exact jtCheck40
  · exact jtCheck41
  · exact jtCheck42
  · exact jtCheck43
  · exact jtCheck44
  · exact jtCheck45
  · exact jtCheck46
  · exact jtCheck47
  · exact jtCheck48
  · exact jtCheck49
  · exact jtCheck50
  · exact jtCheck51
  · exact jtCheck52
  · exact jtCheck53
  · exact jtCheck54
  · exact jtCheck55
  · exact jtCheck56
  · exact jtCheck57
  · exact jtCheck58
  · exact jtCheck59
  · exact jtCheck60
  · exact jtCheck61
  · exact jtCheck62
  · exact jtCheck63
theorem jtChunk_linked (c : Fin 64) :
    CodeAt Frozen.image (pcOf (jtStart + 256 * c.val)) (jtChunk c) := by
  fin_cases c
  · exact jt00_at
  · exact jt01_at
  · exact jt02_at
  · exact jt03_at
  · exact jt04_at
  · exact jt05_at
  · exact jt06_at
  · exact jt07_at
  · exact jt08_at
  · exact jt09_at
  · exact jt10_at
  · exact jt11_at
  · exact jt12_at
  · exact jt13_at
  · exact jt14_at
  · exact jt15_at
  · exact jt16_at
  · exact jt17_at
  · exact jt18_at
  · exact jt19_at
  · exact jt20_at
  · exact jt21_at
  · exact jt22_at
  · exact jt23_at
  · exact jt24_at
  · exact jt25_at
  · exact jt26_at
  · exact jt27_at
  · exact jt28_at
  · exact jt29_at
  · exact jt30_at
  · exact jt31_at
  · exact jt32_at
  · exact jt33_at
  · exact jt34_at
  · exact jt35_at
  · exact jt36_at
  · exact jt37_at
  · exact jt38_at
  · exact jt39_at
  · exact jt40_at
  · exact jt41_at
  · exact jt42_at
  · exact jt43_at
  · exact jt44_at
  · exact jt45_at
  · exact jt46_at
  · exact jt47_at
  · exact jt48_at
  · exact jt49_at
  · exact jt50_at
  · exact jt51_at
  · exact jt52_at
  · exact jt53_at
  · exact jt54_at
  · exact jt55_at
  · exact jt56_at
  · exact jt57_at
  · exact jt58_at
  · exact jt59_at
  · exact jt60_at
  · exact jt61_at
  · exact jt62_at
  · exact jt63_at
theorem jt_steps (field : Fin 16384) (u : MachineState)
    (hu : u.pc = pcOf (jtStart + field.val)) :
    Steps Frozen.image u 1 1 {u with pc := pcOf (jtTarget field.val)} := by
  let c : Fin 64 := ⟨field.val / 256, by omega⟩
  let i : Nat := field.val % 256
  have hi : i < (jtChunk c).length := by rw [jtChunk_length]; exact Nat.mod_lt _ (by decide)
  have he : 256 * c.val + i = field.val := by dsimp [c, i]; omega
  have hcode := codeAt_single (jtStart + 256 * c.val) (jtChunk c)
    (by rw [jtChunk_length]; have := c.isLt; unfold jtStart; omega)
    (jtChunk_linked c) i hi
  have hcheck := jtChunk_checked c
  unfold jtCheck at hcheck
  have hmem : ((jtChunk c)[i], i) ∈ (jtChunk c).zipIdx := by
    have hx := List.getElem_mem (l := (jtChunk c).zipIdx) (n := i) (by simpa using hi)
    simpa using hx
  have hrun := List.all_eq_true.mp hcheck _ hmem
  simp only at hrun
  rw [Nat.add_assoc, he] at hrun
  rw [Nat.add_assoc, he] at hcode
  have hs := symRun_sound (rOK_eq hrun) hcode u hu (by trivial)
  convert hs using 1
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> rfl
end W9Drv
end

section


set_option maxHeartbeats 400000
namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open W9Machine
theorem coord_core_good (chains : Chain.AllGood Frozen.layout)
    (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : (Digest × Digest) → OracleComp HashSpec Obs)
    (hu : Chain.Pre Frozen.layout w index k j rank u)
    (hnext : ∀ ends entry, Chain.Post Frozen.layout w index k j u ends entry →
      ∀ pair t, Child.Post Frozen.layout k entry pair t →
        GoodQFor Frozen.image t N C Q A (K (pair.left, pair.right))) :
    GoodQFor Frozen.image u (N + 131) (C + 188) Q (A + 183)
      (ccM (ClaudeWCT.W9.T3M.wctCoordP w index k j rank) K) := by
  rw [wctCoordP_split w index k j rank hu.indexBound, ccM_bind]
  have hcont (ends : List Digest) (entry : MachineState)
      (hp : Chain.Post Frozen.layout w index k j u ends entry) :
      GoodQFor Frozen.layout.image entry (N+42) (C+99) Q (A+99)
        (ccM (coordTail w index k j ends) K) := by
    have hg := ChildProof.child_good j w index k ends entry N C A Q
      (fun pair => K (pair.left, pair.right)) hp.child (hnext ends entry hp)
    rw [← childProgram_canonical w index k j ends hp.length hu.indexBound]
    simp only [ccM_bind, ccM_pure]
    exact hg
  have hc := chains rank w index k j u (N+42) (C+99) (A+99) Q
    (fun ends => ccM (coordTail w index k j ends) K) hu hcont
  simp only [Nat.add_assoc] at hc
  exact hc
#print axioms coord_core_good
end W9Drv
end

section




namespace W9Drv
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open W9Machine
theorem coord_frame (w : WBytes) (a : HashOutput) (k : Fin 9) (u entry t : MachineState)
    (ends : List Digest) (pair : V3.RootPair)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    Frame u t (fun A => (coordinateBase k ≤ A ∧ A < coordinateBase k + 1024) ∨
      (pairAddress k ≤ A ∧ A < pairAddress k + 48)) := by
  intro A hA hn
  rw [ht.frame A hA (by unfold Child.writes; dsimp at hn; omega)]
  exact hp.frame A hA (by unfold Chain.writes Chain.base; dsimp at hn; omega)
theorem coord_next (pk : Digest) (w : WBytes) (a : HashOutput) (k : Fin 9)
    (pairs : List (Digest × Digest)) (u entry t : MachineState) (ends : List Digest)
    (pair : V3.RootPair) (hu : CoordPre pk w a k.val pairs u)
    (hp : Chain.Post Frozen.layout w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (chainEntryState a k u) ends entry)
    (ht : Child.Post Frozen.layout k entry pair t) :
    CoordPre pk w a (k.val+1) (pairs ++ [(pair.left,pair.right)]) t := by
  have hk := k.isLt
  have hc := dispatch_chain_pre pk w a k pairs u hu
  have hf := coord_frame w a k u entry t ends pair hp ht
  have hm (A : Nat) (hA : A < 2^64)
      (hs : A < 1056 ∨ (1360 ≤ A ∧ A < 2112) ∨ 11328 ≤ A) :
      t.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := by
    apply hf A hA
    unfold coordinateBase pairAddress
    omega
  have hr (r : Reg) (h : r ∉ [.x3,.x10,.x11,.x12,.x14,.x25]) :
      t.getReg r = (chainEntryState a k u).getReg r := by
    rw [ht.keep r (by
      simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false] at *
      tauto)]
    exact hp.keep r h
  have hd (r : Reg) (h : r ∉ [.x1,.x3,.x4,.x8,.x9,.x14,.x15,.x16,.x23,.x27,.x28,.x31]) :
      (chainEntryState a k u).getReg r = u.getReg r := dispatch_keep k u r h
  have hg : Glob baseK w pk t := by
    obtain ⟨hreg, hh, hpk, hz, hhalf, hdata⟩ := hu.glob
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp only [baseK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact (hr .x5 (by decide)).trans ((hd .x5 (by decide)).trans (hreg (.x5, 0) (by simp [baseK])))
      · exact (hr .x18 (by decide)).trans ((hd .x18 (by decide)).trans (hreg (.x18, 4095) (by simp [baseK])))
    · intro j hj
      rw [hm _ (by unfold WIT; omega) (by unfold WIT; omega)]
      exact hh j hj
    · exact ⟨(hm 160 (by decide) (by omega)).trans hpk.1,
        (hm 168 (by decide) (by omega)).trans hpk.2⟩
    · intro A hA
      have hb : A < 1056 := by simp [pSlots] at hA; omega
      exact (hm A (by omega) (Or.inl hb)).trans (hz A hA)
    · change (t.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
      rw [hm CTRW (by decide) (Or.inl (by decide))]
      exact hhalf
    · exact hdata.congr (fun A hA hB => hm A (by omega) (Or.inr (Or.inr (by unfold TAB at hA; omega))))
  refine {
    le := by omega
    length := by simp [hu.length]
    pc := ?_
    glob := hg
    digest := fun i hi => (hm _ (by omega) (Or.inl (by omega))).trans (hu.digest i hi)
    bank := ?_
    index := (hr .x22 (by decide)).trans hc.indexReg
    heaps := ?_
    stepOne := (hr .x7 (by decide)).trans hc.stepOne
    stepTwo := (hr .x13 (by decide)).trans hc.stepTwo
    hashLen := ht.hashLen
    coordStep := (hr .x6 (by decide)).trans ((hd .x6 (by decide)).trans hu.coordStep)
    prefixReg := ?_
    nodeIndex := (hr .x17 (by decide)).trans ((hd .x17 (by decide)).trans hu.nodeIndex)
    cached := ?_
    mask := (hr .x2 (by decide)).trans ((hd .x2 (by decide)).trans hu.mask)
    jt := (hr .x24 (by decide)).trans ((hd .x24 (by decide)).trans hu.jt)
    childBlock := (hr .x29 (by decide)).trans ((hd .x29 (by decide)).trans hu.childBlock)
    baseReg := by simpa [Chain.base, coordinateBase] using (hr .x8 (by decide)).trans hc.baseReg
    headerReg := by simpa [Chain.table, headerTable, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using (hr .x28 (by decide)).trans hc.headerReg
    pairs := ?_
    coords := ?_
    layer := ?_ }
  · rw [ht.pc]
    fin_cases k <;> rfl
  · refine ⟨?_, ?_⟩
    · intro l
      exact (hm _ (by have := l.isLt; omega) (Or.inr (Or.inr (by omega)))).trans (hu.bank.node l)
    · intro l
      exact (hm _ (by have := l.isLt; omega) (Or.inr (Or.inr (by omega)))).trans (hu.bank.leaf l)
  · intro h h2 h7
    exact (hr (Child.heapReg h) (by interval_cases h <;> decide)).trans (hc.heaps h h2 h7)
  · rw [hr .x15 (by decide)]
    change ((dispatchResult k).toState u).getReg .x15 = _
    fin_cases k <;> simp [dispatchResult, coordDispatch, Result.toState_getReg,
      RegFile.get, RegFile.set, RegFile.init, mkAdd_eval, E.eval, hu.prefixReg, hu.coordStep,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · intro _
    rw [hr .x16 (by decide)]
    have he : (chainEntryState a k u).getReg .x16 = (dispatchDig k).eval u := by
      fin_cases k <;> rfl
    rw [he, dispatchDig_eval pk w a k pairs u hu]
    fin_cases k <;> rfl
  · intro i hi
    by_cases he : i = k.val
    · subst i
      rw [List.getD_append_right _ _ _ _ (by rw [hu.length]), hu.length, Nat.sub_self]
      exact ⟨ht.left, ht.right⟩
    · rw [List.getD_append _ _ _ _ (by rw [hu.length]; omega)]
      have old := hu.pairs i (by omega)
      refine ⟨ChildProof.DigAt.of_eq old.1 ?_ ?_, ChildProof.DigAt.of_eq old.2 ?_ ?_⟩
      all_goals apply hf _ (by omega); unfold coordinateBase pairAddress; omega
  · intro l hl off hoff halign
    unfold OrigW
    rw [hf _ (by have := l.isLt; unfold coordinateBase; omega) (by
      have := l.isLt
      unfold coordinateBase pairAddress
      omega)]
    exact hu.coords l (by omega) off hoff halign
  · exact hu.layer.frame (fun j hj h => hm _ (by unfold WIT WX at *; omega)
      (by unfold WIT; omega))
theorem coord_good (chains : Chain.AllGood Frozen.layout) (pk : Digest) (w : WBytes) (a : HashOutput)
    (k : Fin 9) (roots : List (Digest × Digest)) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Option (List (Digest × Digest)) → OracleComp HashSpec Obs)
    (hu : CoordPre pk w a k.val roots u) (hnone : K none = pure (false, 0))
    (hnext : ∀ root t, CoordPre pk w a (k.val + 1) (roots ++ [root]) t →
      GoodQFor Frozen.image t N C Q A (K (some (roots ++ [root])))) :
    GoodQFor Frozen.image u (N + (if k.val = 0 then 205 else 207))
      (C + (if k.val = 0 then 205 else 207)) Q (A + (if k.val = 0 then 200 else 202))
      (ccM (ClaudeWCT.W9.T3M.wctStep w a (some roots) k) K) := by
  have ds := dispatch_steps pk w a k roots u hu
  let f : Fin 16384 := ⟨ClaudeWCT.WCT9.field a k, Nat.mod_lt _ (by decide)⟩
  have js := jt_steps f ((dispatchResult k).toState u) (dispatch_pc pk w a k roots u hu)
  by_cases hok : ClaudeWCT.W9.T3M.fieldOk a k = true
  · have hfield : ClaudeWCT.WCT9.field a k < 16016 := by
      exact of_decide_eq_true hok
    have he : jtTarget f.val = chainEntries.getD (ClaudeWCT.WCT9.rank a k).val 0 := by
      simp only [jtTarget, f, if_pos hfield, ClaudeWCT.WCT9.rank]
    rw [he] at js
    change Steps Frozen.image ((dispatchResult k).toState u) 1 1 (chainEntryState a k u) at js
    have core := coord_core_good chains w (idxOf a) k (ClaudeWCT.WCT9.child a k)
      (ClaudeWCT.WCT9.rank a k) (chainEntryState a k u) N C A Q
      (fun root => K (some (roots ++ [root]))) (dispatch_chain_pre pk w a k roots u hu)
      (fun ends entry hp pair t ht => hnext _ _ (coord_next pk w a k roots u entry t ends pair hu hp ht))
    have full := (core.steps js).steps ds
    simp only [ClaudeWCT.W9.T3M.wctStep, hok, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ccM_bind, ccM_pure]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
  · have hfield : ¬ ClaudeWCT.WCT9.field a k < 16016 := by
      intro hh
      exact hok (show decide (ClaudeWCT.WCT9.field a k < 16016) = true from decide_eq_true hh)
    have he : jtTarget f.val = 24 := by simp only [jtTarget, f, if_neg hfield, jtReject]
    rw [he] at js
    let s : MachineState := { (dispatchResult k).toState u with pc := pcOf 24 }
    have rs := block_steps gReject_checked gReject_linked rfl s (by rfl)
    have rf := block_ecall gReject_checked gReject_linked rfl s rfl
    have rr : GoodQFor Frozen.image (gReject.toState s) 1 1 Q 0 (pure (false, 0)) :=
      GoodQFor.reject rf rfl rfl
    have full := ((rr.steps rs).steps js).steps ds
    dsimp only [gReject] at full
    have hfalse : ClaudeWCT.W9.T3M.fieldOk a k = false := Bool.eq_false_iff.mpr hok
    simp only [ClaudeWCT.W9.T3M.wctStep, hfalse, Bool.not_false, ↓reduceIte, ccM_pure, hnone]
    exact full.mono (by unfold dispatchLen; split_ifs <;> omega)
      (by unfold dispatchLen; split_ifs <;> omega)
      (fun hq => ⟨hq, by unfold dispatchLen; split_ifs <;> omega⟩)
end W9Drv
end
