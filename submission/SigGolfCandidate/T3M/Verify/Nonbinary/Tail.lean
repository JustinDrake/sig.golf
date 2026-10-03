import SigGolfCandidate.T3M.Verify.Nonbinary.PairFold
import SigGolfCandidate.T3M.Search.TopTail

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def ptrCode : List (BitVec 32) := [0x013e8733]
sym_block ptrBase := symRun { noAlias := true } ptrCode (pcOf 96214) 200

theorem ptr_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96214) ptrCode) (hpc : s.pc = pcOf 96214)
    (r : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 r)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 TAIL_DATA) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96215 ∧
      t.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r) ∧
      RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound ptrBase hc s hpc (by simp [ptrBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [ptrBase.res, rv_simp, h29, h19, ofNat_add_ofNat, Nat.add_comm]
  · intro q hq; cases q <;> simp at hq <;> simp [ptrBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [ptrBase.res, rv_simp]

theorem tail_lbu {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96215) [0x00074703]) (hpc : s.pc = pcOf 96215)
    (r : Nat) (hr : r < 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 (TAIL_DATA + r))
    (ht : TailTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96216 ∧
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

/-- Complementing the tail table permits a direct comparison and skips two additions on acceptance. -/
def sumCode : List (BitVec 32) := [0x00ec8863]
sym_block sumBase := symRun { noAlias := true } sumCode (pcOf 96216) 200

def tailRejectJumpCode : List (BitVec 32) := [0x0340006f]
sym_block tailRejectJumpBase := symRun { noAlias := true } tailRejectJumpCode (pcOf 96217) 200

theorem sum_spec {image : Image} (s : MachineState)
    (hc : CodeAt image (pcOf 96216) sumCode) (hpc : s.pc = pcOf 96216)
    (sum value : Nat) (hsum : sum ≤ 4335) (hvalue : value ≤ 9)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 (126 - value)) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if sum + value = 126 then pcOf 96220 else pcOf 96217) ∧
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
    (hc : CodeAt image (pcOf 96217) tailRejectJumpCode) (hpc : s.pc = pcOf 96217) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRejectJumpBase hc s hpc (by simp [tailRejectJumpBase.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro q hq; cases q <;> simp [tailRejectJumpBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [tailRejectJumpBase.res, rv_simp]

/-- The tail comparison takes three instructions on acceptance and four on rejection. -/
theorem tail_compare_spec {image : Image} (s : MachineState) (v : Digest) (sum : Nat)
    (hptr : CodeAt image (pcOf 96214) ptrCode)
    (hload : CodeAt image (pcOf 96215) [0x00074703])
    (hsumcode : CodeAt image (pcOf 96216) sumCode)
    (hreject : CodeAt image (pcOf 96217) tailRejectJumpCode)
    (hsum : sum ≤ 4335) (hv : v.toNat < 2 ^ 125)
    (hpc : s.pc = pcOf 96214) (h29 : s.getReg .x29 = topWindow v 17)
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

private theorem tail_init_at : CodeAt Verify.image (pcOf 96213) tailInitCode := by
  have h := codeAt_from 96213 (by decide)
  have hp : tailInitCode <+: codeFrom 96213 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_ptr_at : CodeAt Verify.image (pcOf 96214) ptrCode := by
  have h := codeAt_from 96214 (by decide)
  have hp : ptrCode <+: codeFrom 96214 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_load_at : CodeAt Verify.image (pcOf 96215) [0x00074703] := by
  have h := codeAt_from 96215 (by decide)
  have hp : [0x00074703] <+: codeFrom 96215 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_sum_at : CodeAt Verify.image (pcOf 96216) sumCode := by
  have h := codeAt_from 96216 (by decide)
  have hp : sumCode <+: codeFrom 96216 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem tail_reject_at : CodeAt Verify.image (pcOf 96217) tailRejectJumpCode := by
  have h := codeAt_from 96217 (by decide)
  have hp : tailRejectJumpCode <+: codeFrom 96217 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

/-- The complete tail takes four instructions on acceptance, five on rejection. -/
theorem tail_spec (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf 96213)
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
