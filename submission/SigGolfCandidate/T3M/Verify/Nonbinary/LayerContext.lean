import SigGolfCandidate.T3M.Verify.Nonbinary.PairAlgebra
import SigGolfCandidate.T3M.Search.TopWindow
import SigGolfCandidate.T3M.Verify.Nonbinary.PairTables
import SigGolfCandidate.Rv
import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.T3M.Search.TopTail
import SigGolfCandidate.T3M.Search.CsBlocks
import SigGolfCandidate.T3M.Verify.LayerSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsDispatchArith
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

section


namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option Elab.async false
def pairRank (v : Digest) (q : Nat) : Nat := v.toNat / 2 ^ (7 * q) % 16384
theorem pairRank_lt (v : Digest) (q : Nat) : pairRank v q < 16384 := by unfold pairRank; omega
theorem pairRank_components (v : Digest) (q : Nat) :
    pairRank v q = topRank v q + 128 * topRank v (q+1) := by
  unfold pairRank topRank
  rw [show 7 * (q + 1) = 7 * q + 7 by omega, Nat.pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul, show 16384 = 128 * 128 by rfl, Nat.mod_mul]
theorem pairWindow_rank (v : Digest) (q : Nat) (hq : q < 8 ∨ (9 ≤ q ∧ q < 16)) :
    topWindow v q &&& 16383#64 = BitVec.ofNat 64 (pairRank v q) := by
  unfold topWindow pairRank
  split_ifs with h
  · simpa using ext_shr_mask v 0 (7 * q) 14 (by omega)
  · have he := ext_shr_mask v 63 (7 * (q - 9)) 14 (by omega)
    rw [show 63 + 7 * (q - 9) = 7 * q by omega] at he
    exact he
theorem pairWindow_shift (v : Digest) (q : Nat) (hq : q < 7 ∨ 9 ≤ q) :
    topWindow v q >>> 14 = topWindow v (q + 2) := by
  unfold topWindow
  by_cases h : q < 7
  · rw [if_pos (by omega),if_pos (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega
  · rw [if_neg (by omega),if_neg (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega
theorem pairLookup_pairRank (v : Digest) (q : Nat) :
    pairLookup (pairRank v q) = pairWeight (topRank v q) (topRank v (q+1)) := by
  rw [pairRank_components,pairLookup_components _ _ (topRank_lt v q)]
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section



namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def pairInitCode : List (BitVec 32) := [0xff89b7,19511,0xfffc0c13]
sym_block pairInitBase := symRun { noAlias := true } pairInitCode 0#64 200
theorem pairInit_run (pc : Word) : symRun { noAlias := true } pairInitCode pc 200 =
    some ⟨pairInitBase.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl
def pairPtr0Code : List (BitVec 32) := [25720627,20383539]
sym_block pairPtr0Base := symRun { noAlias := true } pairPtr0Code 0#64 200
theorem pairPtr0_run (pc : Word) : symRun { noAlias := true } pairPtr0Code pc 200 =
    some ⟨pairPtr0Base.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
def pairPtrCode : List (BitVec 32) := [26146611,20383539]
sym_block pairPtrBase := symRun { noAlias := true } pairPtrCode 0#64 200
theorem pairPtr_run (pc : Word) : symRun { noAlias := true } pairPtrCode pc 200 =
    some ⟨pairPtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
def pairShift0Code : List (BitVec 32) := [0xe85e93]
sym_block pairShift0Base := symRun { noAlias := true } pairShift0Code 0#64 200
theorem pairShift0_run (pc : Word) : symRun { noAlias := true } pairShift0Code pc 200 =
    some ⟨pairShift0Base.res.st, .c (pc + 4), .endOfCode, 1, 1⟩ := by rfl
def pairTailCode : List (BitVec 32) := [0xec8cb3,0xeede93]
sym_block pairTailBase := symRun { noAlias := true } pairTailCode 0#64 200
theorem pairTail_run (pc : Word) : symRun { noAlias := true } pairTailCode pc 200 =
    some ⟨pairTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
def singlePtrCode : List (BitVec 32) := [0x7fef713,20383539]
sym_block singlePtrBase := symRun { noAlias := true } singlePtrCode 0#64 200
theorem singlePtr_run (pc : Word) : symRun { noAlias := true } singlePtrCode pc 200 =
    some ⟨singlePtrBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
def singleTailCode : List (BitVec 32) := [0xec8cb3,8314515]
sym_block singleTailBase := symRun { noAlias := true } singleTailCode 0#64 200
theorem singleTail_run (pc : Word) : symRun { noAlias := true } singleTailCode pc 200 =
    some ⟨singleTailBase.res.st, .c (pc + 4 + 4), .endOfCode, 2, 2⟩ := by rfl
def pairCrossCode : List (BitVec 32) := [1611923,30992563,560787]
sym_block pairCrossBase := symRun { noAlias := true } pairCrossCode 0#64 200
theorem pairCross_run (pc : Word) : symRun { noAlias := true } pairCrossCode pc 200 =
    some ⟨pairCrossBase.res.st, .c (pc + 4 + 4 + 4), .endOfCode, 3, 3⟩ := by rfl
def tailInitCode : List (BitVec 32) := [0xffc9b7]
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
    ∃ t, Steps image s 3 3 t ∧ t.pc = pc + 4 + 4 + 4 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧ t.getReg .x29 = topWindow v 9 ∧
      RegsExcept s t [.x17,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (pairCross_run pc) hc s hpc (by simp [pairCrossBase.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simpa [pairCrossBase.res,rv_simp,hw,hh] using topWindow_cross v
  · simpa [pairCrossBase.res,rv_simp,hw,hh,topWindow] using topWindow_cross v
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
end

section


namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
abbrev packedFoldRegs : List Reg := [.x19,.x24,.x25,.x29,.x14,.x17]
private theorem pairLookup_single (r : Nat) (hr : r < 128) : pairLookup r = rankLookup r := by
  simp only [pairLookup, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr,pairWeight,rankLookup]
  have hz : rankWeight 0 = 0 := rfl
  simp only [show 0 < 125 by decide,and_true,hz,Nat.add_zero]
private theorem pf_96164 : CodeAt Verify.image (pcOf 96164) pairInitCode := by
  have h := codeAt_from 96164 (by decide)
  have hp : pairInitCode <+: codeFrom 96164 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96167 : CodeAt Verify.image (pcOf 96167) pairPtr0Code := by
  have h := codeAt_from 96167 (by decide)
  have hp : pairPtr0Code <+: codeFrom 96167 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96169 : CodeAt Verify.image (pcOf 96169) [0x00074c83] := by
  have h := codeAt_from 96169 (by decide)
  have hp : [0x00074c83] <+: codeFrom 96169 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96170 : CodeAt Verify.image (pcOf 96170) pairShift0Code := by
  have h := codeAt_from 96170 (by decide)
  have hp : pairShift0Code <+: codeFrom 96170 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96171 : CodeAt Verify.image (pcOf 96171) pairPtrCode := by
  have h := codeAt_from 96171 (by decide)
  have hp : pairPtrCode <+: codeFrom 96171 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96173 : CodeAt Verify.image (pcOf 96173) [0x00074703] := by
  have h := codeAt_from 96173 (by decide)
  have hp : [0x00074703] <+: codeFrom 96173 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96174 : CodeAt Verify.image (pcOf 96174) pairTailCode := by
  have h := codeAt_from 96174 (by decide)
  have hp : pairTailCode <+: codeFrom 96174 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96176 : CodeAt Verify.image (pcOf 96176) pairPtrCode := by
  have h := codeAt_from 96176 (by decide)
  have hp : pairPtrCode <+: codeFrom 96176 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96178 : CodeAt Verify.image (pcOf 96178) [0x00074703] := by
  have h := codeAt_from 96178 (by decide)
  have hp : [0x00074703] <+: codeFrom 96178 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96179 : CodeAt Verify.image (pcOf 96179) pairTailCode := by
  have h := codeAt_from 96179 (by decide)
  have hp : pairTailCode <+: codeFrom 96179 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96181 : CodeAt Verify.image (pcOf 96181) pairPtrCode := by
  have h := codeAt_from 96181 (by decide)
  have hp : pairPtrCode <+: codeFrom 96181 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96183 : CodeAt Verify.image (pcOf 96183) [0x00074703] := by
  have h := codeAt_from 96183 (by decide)
  have hp : [0x00074703] <+: codeFrom 96183 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96184 : CodeAt Verify.image (pcOf 96184) pairTailCode := by
  have h := codeAt_from 96184 (by decide)
  have hp : pairTailCode <+: codeFrom 96184 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96186 : CodeAt Verify.image (pcOf 96186) singlePtrCode := by
  have h := codeAt_from 96186 (by decide)
  have hp : singlePtrCode <+: codeFrom 96186 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96188 : CodeAt Verify.image (pcOf 96188) [0x00074703] := by
  have h := codeAt_from 96188 (by decide)
  have hp : [0x00074703] <+: codeFrom 96188 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96189 : CodeAt Verify.image (pcOf 96189) singleTailCode := by
  have h := codeAt_from 96189 (by decide)
  have hp : singleTailCode <+: codeFrom 96189 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96191 : CodeAt Verify.image (pcOf 96191) pairCrossCode := by
  have h := codeAt_from 96191 (by decide)
  have hp : pairCrossCode <+: codeFrom 96191 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96194 : CodeAt Verify.image (pcOf 96194) pairPtrCode := by
  have h := codeAt_from 96194 (by decide)
  have hp : pairPtrCode <+: codeFrom 96194 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96196 : CodeAt Verify.image (pcOf 96196) [0x00074703] := by
  have h := codeAt_from 96196 (by decide)
  have hp : [0x00074703] <+: codeFrom 96196 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96197 : CodeAt Verify.image (pcOf 96197) pairTailCode := by
  have h := codeAt_from 96197 (by decide)
  have hp : pairTailCode <+: codeFrom 96197 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96199 : CodeAt Verify.image (pcOf 96199) pairPtrCode := by
  have h := codeAt_from 96199 (by decide)
  have hp : pairPtrCode <+: codeFrom 96199 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96201 : CodeAt Verify.image (pcOf 96201) [0x00074703] := by
  have h := codeAt_from 96201 (by decide)
  have hp : [0x00074703] <+: codeFrom 96201 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96202 : CodeAt Verify.image (pcOf 96202) pairTailCode := by
  have h := codeAt_from 96202 (by decide)
  have hp : pairTailCode <+: codeFrom 96202 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96204 : CodeAt Verify.image (pcOf 96204) pairPtrCode := by
  have h := codeAt_from 96204 (by decide)
  have hp : pairPtrCode <+: codeFrom 96204 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96206 : CodeAt Verify.image (pcOf 96206) [0x00074703] := by
  have h := codeAt_from 96206 (by decide)
  have hp : [0x00074703] <+: codeFrom 96206 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96207 : CodeAt Verify.image (pcOf 96207) pairTailCode := by
  have h := codeAt_from 96207 (by decide)
  have hp : pairTailCode <+: codeFrom 96207 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96209 : CodeAt Verify.image (pcOf 96209) pairPtrCode := by
  have h := codeAt_from 96209 (by decide)
  have hp : pairPtrCode <+: codeFrom 96209 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96211 : CodeAt Verify.image (pcOf 96211) [0x00074703] := by
  have h := codeAt_from 96211 (by decide)
  have hp : [0x00074703] <+: codeFrom 96211 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem pf_96212 : CodeAt Verify.image (pcOf 96212) pairTailCode := by
  have h := codeAt_from 96212 (by decide)
  have hp : pairTailCode <+: codeFrom 96212 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
theorem pairStep_spec {image : Image} (s : MachineState) (pc : Word) (v : Digest) (q sum : Nat)
    (hc1 : CodeAt image pc pairPtrCode) (hc2 : CodeAt image (pc+4+4) [0x00074703])
    (hc3 : CodeAt image (pc+4+4+4) pairTailCode) (hpc : s.pc = pc)
    (hq : q < 7 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x29 = topWindow v q) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (hm : s.getReg .x24 = 16383#64)
    (ht : PackedTables s) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc+4+4+4+4+4 ∧
      t.getReg .x29 = topWindow v (q+2) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + pairLookup (pairRank v q)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := pairPtr_spec s pc hc1 hpc v q (by omega) hw hb hm
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 hc2 p1 (by rfl) (by decide)
    _ (pairRank_lt v q) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := pairTail_spec s2 _ hc3 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  exact ⟨s3,(e1.trans e2).trans e3,p3,w3.trans (pairWindow_shift v q (by omega)),a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
theorem singleStep_spec (s : MachineState) (v : Digest) (sum : Nat)
    (hpc : s.pc = pcOf 96186) (hw : s.getReg .x29 = topWindow v 8)
    (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (ht : PackedTables s) :
    ∃ t, Steps Verify.image s 5 5 t ∧ t.pc = pcOf 96191 ∧
      t.getReg .x29 = v.extractLsb' 0 64 >>> 63 ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup (topRank v 8)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := singlePtr_spec s _ pf_96186 hpc v hw hb
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 pf_96188 p1 (by rfl) (by decide)
    _ (by have := topRank_lt v 8; omega) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := singleTail_spec s2 _ pf_96189 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  rw [pairLookup_single _ (topRank_lt v 8)] at a3
  refine ⟨s3,(e1.trans e2).trans e3,p3,?_,a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  simpa [topWindow,← BitVec.shiftRight_add] using w3
theorem pairedFold_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96164) (h16 : s.getReg .x16 = v.extractLsb' 0 64)
    (h17 : s.getReg .x17 = v.extractLsb' 64 64) (ht : PackedTables s) :
    ∃ t, Steps Verify.image s 50 50 t ∧ t.pc = pcOf 96214 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x25 = BitVec.ofNat 64 (compressedSum (topRank v)) ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x19 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x24 = 16383#64 ∧
      RegsExcept s t packedFoldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨u0,e0,p0,b0,m0,r0,f0⟩ := pairInit_spec s _ pf_96164 hpc
  obtain ⟨u1,e1,p1,a1,r1,f1⟩ := pairPtr0_spec u0 _ pf_96167 p0 v 0 (by decide)
    (by rw [r0.get (by decide),h16]; simp [topWindow]) b0 m0
  obtain ⟨u2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec u1 _ 0x00074c83 .x25 pf_96169 p1
    (by rfl) (by decide) _ (pairRank_lt v 0) a1 ((ht.frame f0).frame f1).pair
  obtain ⟨t0,e3,p3,w0,r3,f3⟩ := pairShift0_spec u2 _ pf_96170 p2 v
    (by rw [r2.get (by decide),r1.get (by decide),r0.get (by decide),h16])
  have E0 : Steps Verify.image s 7 7 t0 := ((e0.trans e1).trans e2).trans e3
  have R0 : RegsExcept s t0 packedFoldRegs := (((r0.trans r1).trans r2).trans r3).mono (by decide)
  have F0 : Frame s t0 (fun _ => False) := (((f0.trans f1).trans f2).trans f3).mono (by simp)
  have S0 : t0.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0)) := by rw [r3.get (by decide),a2]
  have B0 : t0.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),b0]
  have M0 : t0.getReg .x24 = 16383#64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),m0]
  have H0 : t0.getReg .x17 = v.extractLsb' 64 64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),r0.get (by decide),h17]
  obtain ⟨t1,e1p,p1p,w1,a1,r1p,f1p⟩ := pairStep_spec t0 (pcOf 96171) v 2 _
    pf_96171 pf_96173 pf_96174 p3 (by decide) w0 S0 B0 M0 (ht.frame F0)
  have E1 : Steps Verify.image s 12 12 t1 := E0.trans e1p
  have R1 : RegsExcept s t1 packedFoldRegs := (R0.trans r1p).mono (by decide)
  have F1 : Frame s t1 (fun _ => False) := (F0.trans f1p).mono (by simp)
  have S1 : t1.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) := a1
  have B1 : t1.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r1p.get (by decide),B0]
  have M1 : t1.getReg .x24 = 16383#64 := by rw [r1p.get (by decide),M0]
  have H1 : t1.getReg .x17 = v.extractLsb' 64 64 := by rw [r1p.get (by decide),H0]
  obtain ⟨t2,e2p,p2p,w2,a2,r2p,f2p⟩ := pairStep_spec t1 (pcOf 96176) v 4 _
    pf_96176 pf_96178 pf_96179 p1p (by decide) w1 S1 B1 M1 (ht.frame F1)
  have E2 : Steps Verify.image s 17 17 t2 := E1.trans e2p
  have R2 : RegsExcept s t2 packedFoldRegs := (R1.trans r2p).mono (by decide)
  have F2 : Frame s t2 (fun _ => False) := (F1.trans f2p).mono (by simp)
  have S2 : t2.getReg .x25 = BitVec.ofNat 64 ((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) := a2
  have B2 : t2.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r2p.get (by decide),B1]
  have M2 : t2.getReg .x24 = 16383#64 := by rw [r2p.get (by decide),M1]
  have H2 : t2.getReg .x17 = v.extractLsb' 64 64 := by rw [r2p.get (by decide),H1]
  obtain ⟨t3,e3p,p3p,w3,a3,r3p,f3p⟩ := pairStep_spec t2 (pcOf 96181) v 6 _
    pf_96181 pf_96183 pf_96184 p2p (by decide) w2 S2 B2 M2 (ht.frame F2)
  have E3 : Steps Verify.image s 22 22 t3 := E2.trans e3p
  have R3 : RegsExcept s t3 packedFoldRegs := (R2.trans r3p).mono (by decide)
  have F3 : Frame s t3 (fun _ => False) := (F2.trans f3p).mono (by simp)
  have S3 : t3.getReg .x25 = BitVec.ofNat 64 (((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) := a3
  have B3 : t3.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3p.get (by decide),B2]
  have M3 : t3.getReg .x24 = 16383#64 := by rw [r3p.get (by decide),M2]
  have H3 : t3.getReg .x17 = v.extractLsb' 64 64 := by rw [r3p.get (by decide),H2]
  obtain ⟨us,es,ps,ws,ass,rs,fs⟩ := singleStep_spec t3 v _ p3p w3 S3 B3 (ht.frame F3)
  obtain ⟨t4,ec,pc,wc,wwc,rc,fc⟩ := pairCross_spec us _ pf_96191 ps v ws
    (by rw [rs.get (by decide),H3])
  have E4 : Steps Verify.image s 30 30 t4 := (E3.trans es).trans ec
  have R4 : RegsExcept s t4 packedFoldRegs := ((R3.trans rs).trans rc).mono (by decide)
  have F4 : Frame s t4 (fun _ => False) := ((F3.trans fs).trans fc).mono (by simp)
  have S4 : t4.getReg .x25 = BitVec.ofNat 64 ((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) := by rw [rc.get (by decide),ass]
  have B4 : t4.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [rc.get (by decide),rs.get (by decide),B3]
  have M4 : t4.getReg .x24 = 16383#64 := by rw [rc.get (by decide),rs.get (by decide),M3]
  have H4 : t4.getReg .x17 = v.extractLsb' 63 64 := wc
  obtain ⟨t5,e5p,p5p,w5,a5,r5p,f5p⟩ := pairStep_spec t4 (pcOf 96194) v 9 _
    pf_96194 pf_96196 pf_96197 pc (by decide) wwc S4 B4 M4 (ht.frame F4)
  have E5 : Steps Verify.image s 35 35 t5 := E4.trans e5p
  have R5 : RegsExcept s t5 packedFoldRegs := (R4.trans r5p).mono (by decide)
  have F5 : Frame s t5 (fun _ => False) := (F4.trans f5p).mono (by simp)
  have S5 : t5.getReg .x25 = BitVec.ofNat 64 (((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) := a5
  have B5 : t5.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r5p.get (by decide),B4]
  have M5 : t5.getReg .x24 = 16383#64 := by rw [r5p.get (by decide),M4]
  have H5 : t5.getReg .x17 = v.extractLsb' 63 64 := by rw [r5p.get (by decide),H4]
  obtain ⟨t6,e6p,p6p,w6,a6,r6p,f6p⟩ := pairStep_spec t5 (pcOf 96199) v 11 _
    pf_96199 pf_96201 pf_96202 p5p (by decide) w5 S5 B5 M5 (ht.frame F5)
  have E6 : Steps Verify.image s 40 40 t6 := E5.trans e6p
  have R6 : RegsExcept s t6 packedFoldRegs := (R5.trans r6p).mono (by decide)
  have F6 : Frame s t6 (fun _ => False) := (F5.trans f6p).mono (by simp)
  have S6 : t6.getReg .x25 = BitVec.ofNat 64 ((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) := a6
  have B6 : t6.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r6p.get (by decide),B5]
  have M6 : t6.getReg .x24 = 16383#64 := by rw [r6p.get (by decide),M5]
  have H6 : t6.getReg .x17 = v.extractLsb' 63 64 := by rw [r6p.get (by decide),H5]
  obtain ⟨t7,e7p,p7p,w7,a7,r7p,f7p⟩ := pairStep_spec t6 (pcOf 96204) v 13 _
    pf_96204 pf_96206 pf_96207 p6p (by decide) w6 S6 B6 M6 (ht.frame F6)
  have E7 : Steps Verify.image s 45 45 t7 := E6.trans e7p
  have R7 : RegsExcept s t7 packedFoldRegs := (R6.trans r7p).mono (by decide)
  have F7 : Frame s t7 (fun _ => False) := (F6.trans f7p).mono (by simp)
  have S7 : t7.getReg .x25 = BitVec.ofNat 64 (((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) := a7
  have B7 : t7.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r7p.get (by decide),B6]
  have M7 : t7.getReg .x24 = 16383#64 := by rw [r7p.get (by decide),M6]
  have H7 : t7.getReg .x17 = v.extractLsb' 63 64 := by rw [r7p.get (by decide),H6]
  obtain ⟨t8,e8p,p8p,w8,a8,r8p,f8p⟩ := pairStep_spec t7 (pcOf 96209) v 15 _
    pf_96209 pf_96211 pf_96212 p7p (by decide) w7 S7 B7 M7 (ht.frame F7)
  have E8 : Steps Verify.image s 50 50 t8 := E7.trans e8p
  have R8 : RegsExcept s t8 packedFoldRegs := (R7.trans r8p).mono (by decide)
  have F8 : Frame s t8 (fun _ => False) := (F7.trans f8p).mono (by simp)
  have S8 : t8.getReg .x25 = BitVec.ofNat 64 ((((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) + pairLookup (pairRank v 15)) := a8
  have B8 : t8.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r8p.get (by decide),B7]
  have M8 : t8.getReg .x24 = 16383#64 := by rw [r8p.get (by decide),M7]
  have H8 : t8.getReg .x17 = v.extractLsb' 63 64 := by rw [r8p.get (by decide),H7]
  refine ⟨t8,E8,p8p,w8,?_,H8,B8,M8,R8,F8⟩
  simpa only [pairLookup_pairRank,Nat.reduceAdd,compressedSum] using S8
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section


namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def ptrCode : List (BitVec 32) := [20875059]
sym_block ptrBase := symRun { noAlias := true } ptrCode (pcOf 96215) 200
theorem ptr_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96215) ptrCode) (hpc : s.pc = pcOf 96215)
    (r : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 r)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 TAIL_DATA) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96216 ∧
      t.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound ptrBase hc s hpc (by simp [ptrBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [ptrBase.res, rv_simp, h29, h19, ofNat_add_ofNat, Nat.add_comm]
  · intro q hq; cases q <;> simp at hq <;> simp [ptrBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [ptrBase.res, rv_simp]
theorem tail_lbu {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96216) [0x00074703]) (hpc : s.pc = pcOf 96216)
    (r : Nat) (hr : r < 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r))
    (ht : TailTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96217 ∧
      t.getReg .x14 = BitVec.ofNat 64 (126 - tailSum r) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := rfl
  have hlt : TAIL_DATA + r < 2 ^ 64 := by unfold TAIL_DATA; omega
  have hv : accessValid (s.getReg .x14 + signExtend12 0) 1 = true := by
    rw [h14, hz]
    simp only [add_zero,accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt hlt, Nat.mod_one, and_true, true_and]
    unfold TAIL_DATA; omega
  have hd : decodeInstruction (0x00074703 : BitVec 32) = some (.base (.LBU .x14 .x14 0)) := rfl
  have hs := steps_lbu hc hpc hd hv
  simp only [h14,hz,add_zero,TailTableOK.rank s ht r hr] at hs
  refine ⟨_, hs, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun p => p + 4) hpc
  · rfl
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]
def sumCode : List (BitVec 32) := [0xec8663]
sym_block sumBase := symRun { noAlias := true } sumCode (pcOf 96217) 200
def tailRejectJumpCode : List (BitVec 32) := [50331759]
sym_block tailRejectJumpBase := symRun { noAlias := true } tailRejectJumpCode (pcOf 96218) 200
theorem sum_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96217) sumCode) (hpc : s.pc = pcOf 96217)
    (sum value : Nat) (hsum : sum ≤ 4335) (hvalue : value ≤ 9)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 (126 - value)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if sum + value = 126 then pcOf 96220 else pcOf 96218) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound sumBase hc s hpc (by simp [sumBase.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, sumBase.res, E.eval, CmpOp.eval, BinOp.eval,
      h25, h14, BitVec.toNat_ofNat, Nat.reduceMod, beq_iff_eq]
    have he : (BitVec.ofNat 64 sum = BitVec.ofNat 64 (126-value)) ↔ sum + value = 126 := by
      rw [ofNat_inj (by omega) (by omega)]
      omega
    simp only [he]
  · intro q hq; cases q <;> simp [sumBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [sumBase.res, rv_simp]
theorem tailRejectJump_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96218) tailRejectJumpCode) (hpc : s.pc = pcOf 96218) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRejectJumpBase hc s hpc (by simp [tailRejectJumpBase.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro q hq; cases q <;> simp [tailRejectJumpBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [tailRejectJumpBase.res, rv_simp]
theorem tail_compare_spec {image : Image} (s : MachineState) (v : Digest) (sum : Nat)
    (hptr : CodeAt image (pcOf 96215) ptrCode)
    (hload : CodeAt image (pcOf 96216) [0x00074703])
    (hsumcode : CodeAt image (pcOf 96217) sumCode)
    (hreject : CodeAt image (pcOf 96218) tailRejectJumpCode)
    (hsum : sum ≤ 4335) (hv : v.toNat < 2 ^ 125)
    (hpc : s.pc = pcOf 96215) (h29 : s.getReg .x29 = topWindow v 17)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 TAIL_DATA) (ht : PackedTables s) :
    ∃ t, Steps image s (if sum + tailWeight v = 126 then 3 else 4)
      (if sum + tailWeight v = 126 then 3 else 4) t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf 96220 else pcOf 96230) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  have hr : v.toNat / 2 ^ 119 < 64 := by omega
  rw [topWindow_tail v hv] at h29
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := ptr_spec s hptr hpc _ h29 h19
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := tail_lbu s1 hload p1 _ hr a1 (ht.frame f1).tail
  obtain ⟨s3,e3,p3,r3,f3⟩ := sum_spec s2 hsumcode p2 sum _ hsum (tailSum_le _ hr)
    (by rw [r2.get (by decide), r1.get (by decide), h25]) a2
  rw [tailSum_eq v hv] at p3
  by_cases ha : sum + tailWeight v = 126
  · simp only [if_pos ha] at p3 ⊢
    exact ⟨s3,(e1.trans e2).trans e3,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · simp only [if_neg ha] at p3 ⊢
    obtain ⟨s4,e4,p4,r4,f4⟩ := tailRejectJump_spec s3 hreject p3
    exact ⟨s4,((e1.trans e2).trans e3).trans e4,p4,
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (by simp)⟩
private theorem tail_init_at : CodeAt Verify.image (pcOf 96214) tailInitCode := by
  have h := codeAt_from 96214 (by decide)
  have hp : tailInitCode <+: codeFrom 96214 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem tail_ptr_at : CodeAt Verify.image (pcOf 96215) ptrCode := by
  have h := codeAt_from 96215 (by decide)
  have hp : ptrCode <+: codeFrom 96215 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem tail_load_at : CodeAt Verify.image (pcOf 96216) [0x00074703] := by
  have h := codeAt_from 96216 (by decide)
  have hp : [0x00074703] <+: codeFrom 96216 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem tail_sum_at : CodeAt Verify.image (pcOf 96217) sumCode := by
  have h := codeAt_from 96217 (by decide)
  have hp : sumCode <+: codeFrom 96217 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
private theorem tail_reject_at : CodeAt Verify.image (pcOf 96218) tailRejectJumpCode := by
  have h := codeAt_from 96218 (by decide)
  have hp : tailRejectJumpCode <+: codeFrom 96218 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩
theorem tail_spec (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf 96214)
    (h29 : s.getReg .x29 = topWindow v 17) (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (ht : PackedTables s) :
    ∃ t, Steps Verify.image s (if sum + tailWeight v = 126 then 4 else 5)
      (if sum + tailWeight v = 126 then 4 else 5) t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf 96220 else pcOf 96230) ∧
      RegsExcept s t [.x14,.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,b1,r1,f1⟩ := tailInit_spec s _ tail_init_at hpc
  obtain ⟨s2,e2,p2,r2,f2⟩ := tail_compare_spec s1 v sum tail_ptr_at tail_load_at tail_sum_at tail_reject_at hsum hv p1
    (by rw [r1.get (by decide),h29]) (by rw [r1.get (by decide),h25]) b1 (ht.frame f1)
  refine ⟨s2,?_,p2,(r1.trans r2).mono (by decide),(f1.trans f2).mono (by simp)⟩
  by_cases ha : sum + tailWeight v = 126
  · simpa only [if_pos ha] using e1.trans e2
  · simpa only [if_neg ha] using e1.trans e2
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section


namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def headCode : List (BitVec 32) := [335558659,343947395,64542483,268899939]
sym_block headBase := symRun { noAlias := true } headCode (pcOf 96160) 200
theorem head_at : CodeAt Verify.image (pcOf 96160) headCode := by
  have h := codeAt_from 96160 (by decide)
  have hp : headCode <+: codeFrom 96160 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem head_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) :
    ∃ t, Steps Verify.image s 4 4 t ∧
      t.pc = (if v.toNat < 2 ^ 125 then pcOf 96164 else pcOf 96230) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headBase head_at s hpc (by simp [headBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, headBase.res, E.eval, CmpOp.eval, BinOp.eval,
      show BitVec.ofNat 64 (320 + 8) = 328#64 from rfl, hv.2,
      BitVec.toNat_ofNat, Nat.reduceMod, bne_iff_ne, ne_eq,
      ext64_shr_eq_zero v 61 (by decide), show (64 + 61 : Nat) = 125 from rfl]
    split_ifs <;> first | rfl | omega
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.1
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.2
  · intro r hr; cases r <;> simp at hr <;> simp [headBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [headBase.res, rv_simp]
theorem compressedSum_le (v : Digest) : compressedSum (topRank v) ≤ 4335 := by
  have h0 := pairWeight_le (topRank v 0) (topRank v 1)
  have h1 := pairWeight_le (topRank v 2) (topRank v 3)
  have h2 := pairWeight_le (topRank v 4) (topRank v 5)
  have h3 := pairWeight_le (topRank v 6) (topRank v 7)
  have h4 := rankLookup_le (topRank v 8)
  have h5 := pairWeight_le (topRank v 9) (topRank v 10)
  have h6 := pairWeight_le (topRank v 11) (topRank v 12)
  have h7 := pairWeight_le (topRank v 13) (topRank v 14)
  have h8 := pairWeight_le (topRank v 15) (topRank v 16)
  unfold compressedSum; omega
theorem decode_ok (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hvalid : T3.decode 0 v = some (topDigits v)) :
    ∃ t, Steps Verify.image s 58 58 t ∧ t.pc = pcOf 96220 ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x29 = topWindow v 17 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  have hh : v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 := by
    rw [decode_top_paired] at hvalid
    split_ifs at hvalid with hh
    exact hh
  obtain ⟨t1,e1,p1,a1,b1,r1,f1⟩ := head_spec s v hpc hv
  rw [if_pos hh.1] at p1
  obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
  have hb : compressedSum (topRank v) + tailWeight v = 126 := hh.2
  obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hh.1 p2 w2 a2 ((ht.frame f1).frame f2)
  rw [if_pos hb] at p3 e3
  refine ⟨t3,(e1.trans e2).trans e3,p3,?_,?_,?_,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [r3.get (by decide),r2.get (by decide),a1]
  · rw [r3.get (by decide),h172]
  · rw [r3.get (by decide),w2]
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem decode_reject (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hbad : T3.decode 0 v = none) :
    ∃ k t, Steps Verify.image s k k t ∧ k ≤ 60 ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, b1, r1, f1⟩ := head_spec s v hpc hv
  by_cases hr : v.toNat < 2 ^ 125
  · rw [if_pos hr] at p1
    obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
    have hn : pairedLookupSum v ≠ 126 := by
      intro he
      rw [decode_top_paired,if_pos ⟨hr,he⟩] at hbad
      contradiction
    have hb : compressedSum (topRank v) + tailWeight v ≠ 126 := hn
    obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hr p2 w2 a2 ((ht.frame f1).frame f2)
    rw [if_neg hb] at p3 e3
    exact ⟨59,t3,(e1.trans e2).trans e3,by decide,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [if_neg hr] at p1
    exact ⟨4, t1, e1, by decide, p1, r1.mono (by decide), f1⟩
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xbfda206f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 96230) 20
theorem rejectJump_at : CodeAt Verify.image (pcOf 96230) rejectJumpCode := by
  have h := codeAt_from 96230 (by decide)
  have hp : rejectJumpCode <+: codeFrom 96230 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [1049235,1049875]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 741) 20
theorem rejectExit_at : CodeAt Verify.image (pcOf 741) rejectExitCode := by
  have h := codeAt_from 741 (by decide)
  have hp : rejectExitCode <+: codeFrom 741 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 96230) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 741 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 743) [0x00000073] := by
      have h := codeAt_from 743 (by decide)
      have hp : [0x00000073] <+: codeFrom 743 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def prologueCode : List (BitVec 32) := [18871,0xd9898993,0xd4098b13,134199,0xc00c0c13,714679,0xa81713,25655091,0xf70733,0x9a070067]
sym_block prologueBase := symRun { noAlias := true } prologueCode (pcOf 96220) 200
theorem prologue_at : CodeAt Verify.image (pcOf 96220) prologueCode := by
  have h := codeAt_from 96220 (by decide)
  have hp : prologueCode <+: codeFrom 96220 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def prologueTarget (v : Digest) : Word :=
  (((v.extractLsb' 0 64 <<< (10 : Word)) &&& 130048#64) + pcOf 176744) &&& ~~~1#64
theorem prologue_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96220)
    (h16 : s.getReg .x16 = v.extractLsb' 0 64) (h17 : s.getReg .x17 = v.extractLsb' 63 64) :
    ∃ t, Steps Verify.image s 10 10 t ∧ t.pc = prologueTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x22 = 15064#64 ∧ t.getReg .x19 = 15768#64 ∧ t.getReg .x24 = 130048#64 ∧
      t.getReg .x15 = 712704#64 ∧
      RegsExcept s t [.x3,.x17,.x22,.x19,.x24,.x15,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound prologueBase prologue_at s hpc (by simp [prologueBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prologueBase.res, rv_simp, h16, prologueTarget, pcOf]
    rfl
  · simpa [prologueBase.res, rv_simp] using h16
  · simp [prologueBase.res, rv_simp, h16, h17]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp]
  · simp [prologueBase.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp at hr <;> simp [prologueBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prologueBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
end

section




namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def topPrefixWord (tp : Word) : Word :=
  BitVec.ofNat 64 (128 + 193 * 2 ^ 56) ||| ((tp >>> (32 : Word)) <<< (16 : Word))
def prefixCode : List (BitVec 32) :=
  [0x00ff4e37, 0x800e3e03, 0x02025193, 0x01019193, 0x003e6e33, 0x31c5d06f]
sym_block prefixBase := symRun { noAlias := true } prefixCode (pcOf 724) 200
theorem prefix_at : CodeAt Verify.image (pcOf 724) prefixCode := by
  have h := codeAt_from 724 (by decide)
  have hp : prefixCode <+: codeFrom 724 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
theorem prefix_spec (s : MachineState) (hpc : s.pc = pcOf 724)
    (hmem : s.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ t, Steps Verify.image s 6 6 t ∧ t.pc = pcOf 96160 ∧
      t.getReg .x28 = topPrefixWord (s.getReg .x4) ∧
      RegsExcept s t [.x3,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound prefixBase prefix_at s hpc (by simp [prefixBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [prefixBase.res, rv_simp, pcOf]
  · simp [prefixBase.res, rv_simp, topPrefixWord, hmem]
  · intro r hr; cases r <;> simp at hr <;> simp [prefixBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [prefixBase.res, rv_simp]
theorem topPrefixWord_hdr1 (tree leaf : Nat) (ht : tree < 2 ^ 32) (hl : leaf < 2 ^ 32) :
    topPrefixWord (BitVec.ofNat 64 (hdr1 tree leaf)) =
      BitVec.ofNat 64 (128 + 193 * 2 ^ 56 + leaf * 2 ^ 16) := by
  rw [hdr1_eq tree leaf ht hl]
  unfold topPrefixWord
  change BitVec.ofNat 64 (128 + 193 * 2 ^ 56) |||
    ((BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) >>> (32 : Nat)) <<< (16 : Nat)) = _
  rw [ofNat_shr _ _ (by omega), ofNat_shl]
  rw [show (tree + 2 ^ 32 * leaf) / 2 ^ 32 = leaf by omega]
  rw [show 128 + 193 * 2 ^ 56 = 193 * 2 ^ 56 + 128 by omega,
    ← ofNat_or_add 128 193 56 (by decide), BitVec.or_assoc,
    ofNat_or_disjoint' 128 (leaf * 2 ^ 16) 16 (by decide) (by omega),
    ofNat_or_add _ 193 56 (by omega)]
  congr 1
  omega
end SigGolfCandidate.T3M.Verify.Nonbinary
end
section
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def topEntryRegs : List Reg := [.x1,.x3,.x16,.x17,.x14,.x25,.x29,.x19,.x22,.x24,.x15,.x28]
structure TopEntry (u : MachineState) (v : Digest) (p : Nat) (s : MachineState) : Prop where
  pc : s.pc = pcOf (176744 + 256 * (v.toNat % 128))
  ra : s.getReg .x1 = pcOf (p + 17)
  lo : s.getReg .x16 = v.extractLsb' 0 64
  hi : s.getReg .x17 = (v.extractLsb' 64 64 <<< (1 : Word)) ||| (v.extractLsb' 0 64 >>> (63 : Word))
  tail : s.getReg .x29 = Search.topWindow v 17
  s6 : s.getReg .x22 = 15064#64
  s3 : s.getReg .x19 = 15768#64
  mask : s.getReg .x24 = 130048#64
  table : s.getReg .x15 = 712704#64
  «prefix» : s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4)
  regs : RegsExcept u s topEntryRegs
  frame : Frame u s (fun _ => False)
theorem topCall_jumps (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 17)) (hk : KnownOK (bK 0) u) :
    ∃ s, Steps image u 1 1 s ∧ s.pc = pcOf 724 ∧ s.getReg .x1 = pcOf (trPc 0 c + 17) ∧
      RegsExcept u s [.x1] ∧ Frame u s (fun _ => False) := by
  have hcc := (copy_parts 0 (trPc 0 c) (copyCheck_at 0 c (by decide) hc)).2.2.1 rfl
  obtain ⟨s, hs⟩ := spec_run hcc u hpc (by simp [KnownOK]) (by simp [specTopCall]) (by simp)
  refine ⟨s, hs.steps, hs.pc rfl, ?_, ?_, ?_⟩
  · exact hs.regs (.x1, kw (0x1000 + 4 * (trPc 0 c + 17))) (by simp [specTopCall])
  · intro r hr
    cases r
    case x0 => simp [MachineState.getReg]
    case x1 => simp at hr
    all_goals exact hs.keep _ (by simp [keepTopCall])
  · intro A hA _
    rw [hs.mem]
    rfl
theorem topCall_step (c : Nat) (hc : c < nCopy 0) (u : MachineState)
    (hpc : u.pc = pcOf (trPc 0 c + 17)) (hk : KnownOK (bK 0) u)
    (hmem : u.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56)) :
    ∃ s, Steps image u 7 7 s ∧ s.pc = pcOf 96160 ∧ s.getReg .x1 = pcOf (trPc 0 c + 17) ∧
      s.getReg .x28 = Nonbinary.topPrefixWord (u.getReg .x4) ∧
      RegsExcept u s [.x1,.x3,.x28] ∧ Frame u s (fun _ => False) := by
  obtain ⟨r, er, pr, ra, rr, fr⟩ := topCall_jumps c hc u hpc hk
  have hm : r.getMem (BitVec.ofNat 64 0xff3800) = BitVec.ofNat 64 (128 + 193 * 2 ^ 56) := by
    rw [fr.get (by decide) (by simp), hmem]
  obtain ⟨s, es, ps, hp, rs, fs⟩ := Nonbinary.prefix_spec r pr hm
  refine ⟨s, er.trans es, ps, ?_, ?_, (rr.trans rs).mono (by decide), ?_⟩
  · rw [rs.get (by decide), ra]
  · rw [hp, rr.get (by decide)]
  · exact (fr.trans fs).mono (by simp)
theorem topTransition_reject (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hbad : T3.decode 0 (a.extractLsb' 0 128) = none) :
    ∃ k s, Steps image (writeHash t a) k k s ∧ k ≤ 71 ∧
      fetch image s = some (.base .ECALL) ∧ s.getReg .x5 = 1 ∧ s.getReg .x10 = 1 := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  obtain ⟨s, e, ps, ra, hp, rs, fs⟩ := topCall_step c hc _ hpc hk
    (hglob.2.2.2.2.2.prefix 0 (by decide))
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨k, r, er, hk, pr, rr, fr⟩ := Verify.Nonbinary.decode_reject s _ ps hv hd hbad
  obtain ⟨z, ez, hz, h5, h10⟩ := Verify.Nonbinary.reject_halt r pr
  refine ⟨8 + k + 3, z, (e.trans er).trans ez, by omega, hz, h5, h10⟩
theorem topTransition_ok (w : WBytes) (pk : Digest) (index c : Nat) (hc : c < nCopy 0)
    (t : MachineState) (ht : EncPre w pk index 0 c t) (a : BitVec 256)
    (hgood : T3.decode 0 (a.extractLsb' 0 128) = some (Search.topDigits (a.extractLsb' 0 128))) :
    ∃ s, Steps image (writeHash t a) 76 76 s ∧
      TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have hk : KnownOK (bK 0) (writeHash t a) := fun p hp => by rw [writeHash_getReg]; exact ht.glob.1 p hp
  have hpc : (writeHash t a).pc = pcOf (trPc 0 c + 17) := by
    rw [writeHash_pc, ht.pc]
    change pcOf (trPc 0 c + 16) + 4 = pcOf (trPc 0 c + 17)
    simpa only [Nat.add_assoc] using pcOf_add4 (trPc 0 c + 16)
  have hglob := Glob_writeHash ht.glob a 320 h12 (by decide)
  obtain ⟨s, e, ps, ra, hp, rs, fs⟩ := topCall_step c hc _ hpc hk
    (hglob.2.2.2.2.2.prefix 0 (by decide))
  have hv := (DigAt.writeHash_lo t a 320 h12 (by decide)).frame fs (by decide) (by simp) (by simp)
  have hd := hglob.2.2.2.2.2.packed.frame fs
  obtain ⟨r, er, pr, h16, h17, h29, rr, fr⟩ := Verify.Nonbinary.decode_ok s _ ps hv hd hgood
  obtain ⟨z, ez, pz, lo, hi, s6, s3, mask, tab, rz, fz⟩ := Verify.Nonbinary.prologue_spec r _ pr h16 h17
  refine ⟨z, (e.trans er).trans ez, ⟨?_, ?_, lo, ?_, ?_, s6, s3, mask, tab, ?_, ?_, ?_⟩⟩
  · rw [pz]
    exact Nonbinary.prologue_target _
  · rw [rz.get (by decide), rr.get (by decide), ra]
  · rw [hi]; exact (Search.topWindow_cross _).symm
  · rw [rz.get (by decide), h29]
  · rw [rz.get (by decide), rr.get (by decide), hp]
  · exact ((rs.trans rr).trans rz).mono (by decide)
  · exact ((fs.trans fr).trans fz).mono (by simp)
end SigGolfCandidate.T3M
end

section


namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest route coreDigit)
open Nonbinary (NCtx)
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def nctxOf (w : WBytes) (index : Nat) (v : Digest) (p : Nat) : NCtx :=
  ⟨w, (route index 0).2, (route index 0).1, 15768, coreDigit 0 v, p + 17⟩
theorem nctx_ok (w : WBytes) (index : Nat) (v : Digest) (c : Nat) (hidx : index < 2 ^ 31) :
    (nctxOf w index v (trPc 0 c)).ok := by
  have hp := trPc_lt 0 c
  have ht : (route index 0).2 = 0 := by rw [route_snd]; exact Nat.div_eq_of_lt hidx
  exact ⟨ht, leaf_lt index 0, by norm_num [nctxOf], by norm_num [nctxOf], by norm_num [nctxOf], by dsimp [nctxOf]; omega⟩
theorem nctx_known (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (hidx : index < 2 ^ 31)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    KnownOK (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).known s := by
  have htree : (route index 0).2 = 0 := by
    rw [route_snd]
    exact Nat.div_eq_of_lt hidx
  have hleaf := leaf_lt32 index 0
  have hprefix : s.getReg .x28 = BitVec.ofNat 64
      (nctxOf w index (a.extractLsb' 0 128) (trPc 0 c)).prefix := by
    rw [he.prefix, writeHash_getReg, ht.tp 0 rfl,
      Nonbinary.topPrefixWord_hdr1 _ _ (tree_lt index 0 hidx) hleaf]
    simp only [nctxOf, NCtx.prefix, htree, Nat.zero_mul, Nat.zero_add,
      Nat.mod_eq_of_lt hleaf]
  intro p hp
  simp only [NCtx.known, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact he.s3
  all_goals try exact he.ra
  all_goals try exact hprefix
  all_goals rw [he.regs.get (by simp [topEntryRegs]), writeHash_getReg]
  all_goals try exact ht.tp 0 rfl
  all_goals exact ht.glob.1 _ (by simp [bK, layK, baseK, nctxOf, NCtx.w1, hw])
theorem topEntry_orig (w : WBytes) (pk : Digest) (index c : Nat) (t s : MachineState) (a : BitVec 256)
    (ht : EncPre w pk index 0 c t)
    (he : TopEntry (writeHash t a) (a.extractLsb' 0 128) (trPc 0 c) s) :
    Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) s := by
  have h12 : t.getReg .x12 = 320#64 := ht.glob.1 (_, _) (by simp [bK])
  have ho := Orig_writeHash ht.orig a 320 h12 (by norm_num)
  have hu : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) (writeHash t a) :=
    ho.mono (fun o h => ⟨h, Or.inr (by unfold WIT; omega)⟩)
  exact hu.frame (fun j hj hp => he.frame.get (by unfold WIT WX at *; omega) (by simp))
theorem nctx_orig (w : WBytes) (index : Nat) (v : Digest) (p : Nat) (s : MachineState)
    (ho : Verify.Orig w (fun o => 11288 ≤ o ∧ o < layerEnd 0) s) (hD : DataOK s) :
    (nctxOf w index v p).Orig0 s := by
  refine ⟨fun i hi k hk => ?_, hD⟩
  clear hD
  apply origW_of ho _
  all_goals simp only [NCtx.blk, nctxOf]
  all_goals norm_num [WIT, WX, layerEnd] at *
  all_goals omega
end SigGolfCandidate.T3M
end
