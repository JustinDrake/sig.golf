import SigGolfCandidate.T3M.Verify.Nonbinary.PairTables
import SigGolfCandidate.T3M.Verify.Nonbinary.PairWindow
import SigGolfCandidate.Rv

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def pairInitCode : List (BitVec 32) := [0x00ff89b7, 0x00004c37, 0xfffc0c13]
sym_block pairInitBase := symRun { noAlias := true } pairInitCode 0#64 200
theorem pairInit_run (pc : Word) : symRun { noAlias := true } pairInitCode pc 200 =
    some ⟨pairInitBase.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl

def pairPtr0Code : List (BitVec 32) := [0x01887733, 0x01370733]
sym_block pairPtr0Base := symRun { noAlias := true } pairPtr0Code 0#64 200
theorem pairPtr0_run (pc : Word) : symRun { noAlias := true } pairPtr0Code pc 200 =
    some ⟨pairPtr0Base.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairPtrCode : List (BitVec 32) := [0x018ef733, 0x01370733]
sym_block pairPtrBase := symRun { noAlias := true } pairPtrCode 0#64 200
theorem pairPtr_run (pc : Word) : symRun { noAlias := true } pairPtrCode pc 200 =
    some ⟨pairPtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairPtrHiCode : List (BitVec 32) := [0x0188f733, 0x01370733]
sym_block pairPtrHiBase := symRun { noAlias := true } pairPtrHiCode 0#64 200
theorem pairPtrHi_run (pc : Word) : symRun { noAlias := true } pairPtrHiCode pc 200 =
    some ⟨pairPtrHiBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairTailHiCode : List (BitVec 32) := [0x00ec8cb3, 0x00e8de93]
sym_block pairTailHiBase := symRun { noAlias := true } pairTailHiCode 0#64 200
theorem pairTailHi_run (pc : Word) : symRun { noAlias := true } pairTailHiCode pc 200 =
    some ⟨pairTailHiBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairShift0Code : List (BitVec 32) := [0x00e85e93]
sym_block pairShift0Base := symRun { noAlias := true } pairShift0Code 0#64 200
theorem pairShift0_run (pc : Word) : symRun { noAlias := true } pairShift0Code pc 200 =
    some ⟨pairShift0Base.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl

def pairTailCode : List (BitVec 32) := [0x00ec8cb3, 0x00eede93]
sym_block pairTailBase := symRun { noAlias := true } pairTailCode 0#64 200
theorem pairTail_run (pc : Word) : symRun { noAlias := true } pairTailCode pc 200 =
    some ⟨pairTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def singlePtrCode : List (BitVec 32) := [0x07fef713, 0x01370733]
sym_block singlePtrBase := symRun { noAlias := true } singlePtrCode 0#64 200
theorem singlePtr_run (pc : Word) : symRun { noAlias := true } singlePtrCode pc 200 =
    some ⟨singlePtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def singleTailCode : List (BitVec 32) := [0x00ec8cb3, 0x007ede93]
sym_block singleTailBase := symRun { noAlias := true } singleTailCode 0#64 200
theorem singleTail_run (pc : Word) : symRun { noAlias := true } singleTailCode pc 200 =
    some ⟨singleTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def pairCrossCode : List (BitVec 32) := [0x00189893, 0x01d8e8b3]
sym_block pairCrossBase := symRun { noAlias := true } pairCrossCode 0#64 200
theorem pairCross_run (pc : Word) : symRun { noAlias := true } pairCrossCode pc 200 =
    some ⟨pairCrossBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl

def tailInitCode : List (BitVec 32) := [0x00ffc9b7]
sym_block tailInitBase := symRun { noAlias := true } tailInitCode 0#64 200
theorem tailInit_run (pc : Word) : symRun { noAlias := true } tailInitCode pc 200 =
    some ⟨tailInitBase.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl

theorem pairInit_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairInitCode) (hpc : s.pc = pc) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x19 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x24 = 16383#64 ∧
      RegsExcept s t [.x19,.x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairInit_run pc) hc s hpc (by simp [pairInitBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · rfl
  · intro q hq; cases q <;> simp at hq <;> simp [pairInitBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairInitBase.res,rv_simp]

theorem pairPtr0_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairPtr0Code) (hpc : s.pc = pc) (v : Digest) (q : Nat)
    (hq : q < 8 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x16 = topWindow v q) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA)
    (hm : s.getReg .x24 = 16383#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + pairRank v q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairPtr0_run pc) hc s hpc (by simp [pairPtr0Base.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,pairPtr0Base.res,rv_simp,hw,hb,hm,pairWindow_rank v q hq,ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [pairPtr0Base.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairPtr0Base.res,rv_simp]

theorem pairPtrHi_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairPtrHiCode) (hpc : s.pc = pc) (v : Digest) (q : Nat)
    (hq : q < 8 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x17 = topWindow v q) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA)
    (hm : s.getReg .x24 = 16383#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + pairRank v q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairPtrHi_run pc) hc s hpc (by simp [pairPtrHiBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,pairPtrHiBase.res,rv_simp,hw,hb,hm,pairWindow_rank v q hq,ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [pairPtrHiBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairPtrHiBase.res,rv_simp]

theorem pairTailHi_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairTailHiCode) (hpc : s.pc = pc) (W : Word) (sum value : Nat)
    (hw : s.getReg .x17 = W) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hv : s.getReg .x14 = BitVec.ofNat 64 value) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = W >>> 14 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + value) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairTailHi_run pc) hc s hpc (by simp [pairTailHiBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp [pairTailHiBase.res,rv_simp,hw]
  · simp [pairTailHiBase.res,rv_simp,hs,hv,ofNat_add_ofNat]
  · intro q hq; cases q <;> simp at hq <;> simp [pairTailHiBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairTailHiBase.res,rv_simp]

theorem pairPtr_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairPtrCode) (hpc : s.pc = pc) (v : Digest) (q : Nat)
    (hq : q < 8 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x29 = topWindow v q) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA)
    (hm : s.getReg .x24 = 16383#64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + pairRank v q) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairPtr_run pc) hc s hpc (by simp [pairPtrBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,pairPtrBase.res,rv_simp,hw,hb,hm,pairWindow_rank v q hq,ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [pairPtrBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairPtrBase.res,rv_simp]

theorem pairShift0_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairShift0Code) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x16 = v.extractLsb' 0 64) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x29 = topWindow v 2 ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairShift0_run pc) hc s hpc (by simp [pairShift0Base.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [pairShift0Base.res,rv_simp,hw,topWindow]
  · intro q hq; cases q <;> simp at hq <;> simp [pairShift0Base.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairShift0Base.res,rv_simp]

theorem pairTail_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairTailCode) (hpc : s.pc = pc) (W : Word) (sum value : Nat)
    (hw : s.getReg .x29 = W) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hv : s.getReg .x14 = BitVec.ofNat 64 value) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = W >>> 14 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + value) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairTail_run pc) hc s hpc (by simp [pairTailBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp [pairTailBase.res,rv_simp,hw]
  · simp [pairTailBase.res,rv_simp,hs,hv,ofNat_add_ofNat]
  · intro q hq; cases q <;> simp at hq <;> simp [pairTailBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairTailBase.res,rv_simp]

theorem singleTail_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc singleTailCode) (hpc : s.pc = pc) (W : Word) (sum value : Nat)
    (hw : s.getReg .x29 = W) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hv : s.getReg .x14 = BitVec.ofNat 64 value) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x29 = W >>> 7 ∧ t.getReg .x25 = BitVec.ofNat 64 (sum + value) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (singleTail_run pc) hc s hpc (by simp [singleTailBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp [singleTailBase.res,rv_simp,hw]
  · simp [singleTailBase.res,rv_simp,hs,hv,ofNat_add_ofNat]
  · intro q hq; cases q <;> simp at hq <;> simp [singleTailBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [singleTailBase.res,rv_simp]

theorem singlePtr_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc singlePtrCode) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x29 = topWindow v 8) (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + topRank v 8) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (singlePtr_run pc) hc s hpc (by simp [singlePtrBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,singlePtrBase.res,rv_simp,hw,hb,topWindow_rank v 8 (by decide),ofNat_add_ofNat]
    congr 1; omega
  · intro q hq; cases q <;> simp at hq <;> simp [singlePtrBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [singlePtrBase.res,rv_simp]

theorem pairCross_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc pairCrossCode) (hpc : s.pc = pc) (v : Digest)
    (hw : s.getReg .x29 = v.extractLsb' 0 64 >>> 63) (hh : s.getReg .x17 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pc + 4 + 4 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairCross_run pc) hc s hpc (by simp [pairCrossBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simpa [pairCrossBase.res,rv_simp,hw,hh] using topWindow_cross v
  · intro q hq; cases q <;> simp at hq <;> simp [pairCrossBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [pairCrossBase.res,rv_simp]

theorem tailInit_spec {image : Image} (s : MachineState) (pc : Word)
    (hc : CodeAt image pc tailInitCode) (hpc : s.pc = pc) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg .x19 = BitVec.ofNat 64 TAIL_DATA ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (tailInit_run pc) hc s hpc (by simp [tailInitBase.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro q hq; cases q <;> simp at hq <;> simp [tailInitBase.res,rv_simp] <;> rfl
  · intro A _ _; simp [tailInitBase.res,rv_simp]

/-- The read is stepped directly: byte-table addresses need not be word aligned. -/
theorem pair_lbu_spec {image : Image} (s : MachineState) (pc : Word) (inst : BitVec 32) (rd : Reg)
    (hc : CodeAt image pc [inst]) (hpc : s.pc = pc)
    (hd : decodeInstruction inst = some (.base (.LBU rd .x14 0))) (hrd : rd ≠ .x0)
    (r : Nat) (hr : r < 16384) (ha : s.getReg .x14 = BitVec.ofNat 64 (PAIR_DATA + r))
    (ht : PairTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧ t.getReg rd = BitVec.ofNat 64 (pairLookup r) ∧
      RegsExcept s t [rd] ∧ Frame s t (fun _ => False) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := rfl
  have hlt : PAIR_DATA + r < 2 ^ 64 := by unfold PAIR_DATA; omega
  have hv : accessValid (s.getReg .x14 + signExtend12 0) 1 = true := by
    rw [ha,hz]
    simp only [add_zero,accessValid_iff,MEMORY_BYTES,toNat_ofNat_lt hlt,Nat.mod_one,and_true,true_and]
    unfold PAIR_DATA; omega
  have hs := steps_lbu hc hpc hd hv
  simp only [ha,hz,add_zero,PairTableOK.rank s ht r hr] at hs
  refine ⟨_,hs,?_,?_,?_,?_⟩
  · exact congrArg (fun p => p + 4) hpc
  · exact MachineState.getReg_setReg_eq hrd
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg,MachineState.setPC,MachineState.getMem]

end SigGolfCandidate.T3M.Verify.Nonbinary
