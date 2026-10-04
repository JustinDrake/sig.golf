import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def dOff (k : Nat) : Nat := [45,60,77,94,111,128,145,162,179,196].getD k 0
def dLen (k : Nat) : Nat := if k = 0 then 13 else 15
def fslot (k : Nat) : Nat := 0x700 + (if k = 0 then 0 else 16 * (k + 1))
theorem disp_0 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 45))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨0, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 58) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 0) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 0) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨0, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨0, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 0 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 0 43 (by omega)
  have hf4 := field4_bits N 0 43 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 43 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_45 (codeAt_45 hc) s hpc (by
    simp [blk_45.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_45.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_45.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_45.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_45.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_45.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_45.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_45.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_45.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_45.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_45.res, rv_simp]
theorem ret_0 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 58)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 59) ∧
      t.getReg .x12 = BitVec.ofNat 64 1792 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_58 (codeAt_58 hc) s hpc (by simp [blk_58.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_59 hc).fetch _ (by simp [Result.toState_pc, blk_58.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_58.res, E.eval, base]
  · simp [blk_58.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_58.res, rv_simp] <;> rfl
  · intro A; simp [blk_58.res, rv_simp]
theorem disp_1 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 60))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (1 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (1 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨1, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 75) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 1) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 1) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨1, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨1, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 1 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 1 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 0 (by omega)
  have hf4 := field4_bits N 1 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 64 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_60 (codeAt_60 hc) s hpc (by
    simp [blk_60.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_60.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_60.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_60.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_60.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_60.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_60.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_60.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_60.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_60.res, rv_simp]
theorem ret_1 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 75)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 76) ∧
      t.getReg .x12 = BitVec.ofNat 64 1824 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_75 (codeAt_75 hc) s hpc (by simp [blk_75.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_76 hc).fetch _ (by simp [Result.toState_pc, blk_75.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_75.res, E.eval, base]
  · simp [blk_75.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_75.res, rv_simp] <;> rfl
  · intro A; simp [blk_75.res, rv_simp]
theorem disp_2 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 77))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (2 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (2 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨2, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 92) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 2) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 2) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨2, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨2, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 2 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 1 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 21 (by omega)
  have hf4 := field4_bits N 1 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 85 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_77 (codeAt_77 hc) s hpc (by
    simp [blk_77.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_77.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_77.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_77.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_77.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_77.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_77.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_77.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_77.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_77.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_77.res, rv_simp]
theorem ret_2 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 92)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 93) ∧
      t.getReg .x12 = BitVec.ofNat 64 1840 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_92 (codeAt_92 hc) s hpc (by simp [blk_92.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_93 hc).fetch _ (by simp [Result.toState_pc, blk_92.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_92.res, E.eval, base]
  · simp [blk_92.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_92.res, rv_simp] <;> rfl
  · intro A; simp [blk_92.res, rv_simp]
theorem disp_3 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 94))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (3 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (3 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨3, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 109) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 3) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 3) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨3, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨3, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 3 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 1 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 42 (by omega)
  have hf4 := field4_bits N 1 42 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 106 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_94 (codeAt_94 hc) s hpc (by
    simp [blk_94.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_94.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_94.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_94.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_94.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_94.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_94.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_94.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_94.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_94.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_94.res, rv_simp]
theorem ret_3 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 109)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 110) ∧
      t.getReg .x12 = BitVec.ofNat 64 1856 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_109 (codeAt_109 hc) s hpc (by simp [blk_109.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_110 hc).fetch _ (by simp [Result.toState_pc, blk_109.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_109.res, E.eval, base]
  · simp [blk_109.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_109.res, rv_simp] <;> rfl
  · intro A; simp [blk_109.res, rv_simp]
theorem disp_4 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 111))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (4 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (4 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨4, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 126) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 4) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 4) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨4, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨4, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 4 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 0 (by omega)
  have hf4 := field4_bits N 2 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 128 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_111 (codeAt_111 hc) s hpc (by
    simp [blk_111.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_111.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_111.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_111.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_111.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_111.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_111.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_111.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_111.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_111.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_111.res, rv_simp]
theorem ret_4 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 126)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 127) ∧
      t.getReg .x12 = BitVec.ofNat 64 1872 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_126 (codeAt_126 hc) s hpc (by simp [blk_126.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_127 hc).fetch _ (by simp [Result.toState_pc, blk_126.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_126.res, E.eval, base]
  · simp [blk_126.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_126.res, rv_simp] <;> rfl
  · intro A; simp [blk_126.res, rv_simp]
theorem disp_5 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 128))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (5 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (5 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨5, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 143) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 5) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 5) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨5, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨5, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 5 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 21 (by omega)
  have hf4 := field4_bits N 2 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 149 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_128 (codeAt_128 hc) s hpc (by
    simp [blk_128.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_128.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_128.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_128.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_128.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_128.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_128.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_128.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_128.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_128.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_128.res, rv_simp]
theorem ret_5 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 143)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 144) ∧
      t.getReg .x12 = BitVec.ofNat 64 1888 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_143 (codeAt_143 hc) s hpc (by simp [blk_143.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_144 hc).fetch _ (by simp [Result.toState_pc, blk_143.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_143.res, E.eval, base]
  · simp [blk_143.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_143.res, rv_simp] <;> rfl
  · intro A; simp [blk_143.res, rv_simp]
theorem disp_6 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 145))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (6 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (6 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨6, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 160) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 6) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 6) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨6, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨6, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 6 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 42 (by omega)
  have hf4 := field4_bits N 2 42 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 170 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_145 (codeAt_145 hc) s hpc (by
    simp [blk_145.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_145.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_145.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_145.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_145.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_145.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_145.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_145.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_145.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_145.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_145.res, rv_simp]
theorem ret_6 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 160)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 161) ∧
      t.getReg .x12 = BitVec.ofNat 64 1904 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_160 (codeAt_160 hc) s hpc (by simp [blk_160.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_161 hc).fetch _ (by simp [Result.toState_pc, blk_160.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_160.res, E.eval, base]
  · simp [blk_160.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_160.res, rv_simp] <;> rfl
  · intro A; simp [blk_160.res, rv_simp]
theorem disp_7 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 162))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (7 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (7 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨7, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 177) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 7) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 7) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨7, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨7, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 7 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 3 0 (by omega)
  have hf4 := field4_bits N 3 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 192 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_162 (codeAt_162 hc) s hpc (by
    simp [blk_162.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_162.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_162.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_162.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_162.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_162.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_162.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_162.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_162.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_162.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_162.res, rv_simp]
theorem ret_7 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 177)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 178) ∧
      t.getReg .x12 = BitVec.ofNat 64 1920 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_177 (codeAt_177 hc) s hpc (by simp [blk_177.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_178 hc).fetch _ (by simp [Result.toState_pc, blk_177.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_177.res, E.eval, base]
  · simp [blk_177.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_177.res, rv_simp] <;> rfl
  · intro A; simp [blk_177.res, rv_simp]
theorem disp_8 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 179))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17468)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50236) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (8 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (8 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 15 15 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨8, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 194) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 8) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 8) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨8, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17468 + 256 * (WCT9.child N ⟨8, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 8 + 448)) ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x11 → r ≠ .x14 → r ≠ .x16 → r ≠ .x23 → r ≠ .x27 →
        r ≠ .x28 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 3 21 (by omega)
  have hf4 := field4_bits N 3 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 213 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_179 (codeAt_179 hc) s hpc (by
    simp [blk_179.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_179.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_179.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_179.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_179.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_179.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_179.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_179.res, rv_simp, h28, HB0]
    congr 1
  · simp [blk_179.res, rv_simp]
  · intro r h1 h3 h4 h8' h11 h14 h16 h23 h27 h28'
    cases r <;> simp_all [blk_179.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_179.res, rv_simp]
theorem ret_8 {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 194)) :
    ∃ t, Steps im s 1 1 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf (base + 195) ∧
      t.getReg .x12 = BitVec.ofNat 64 1936 ∧ (∀ r, r ≠ .x12 → t.getReg r = s.getReg r) ∧
      (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_194 (codeAt_194 hc) s hpc (by simp [blk_194.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(codeAt_195 hc).fetch _ (by simp [Result.toState_pc, blk_194.res, E.eval, base])]; rfl
  · simp [Result.toState_pc, blk_194.res, E.eval, base]
  · simp [blk_194.res, rv_simp]
  · intro r hr; cases r <;> simp_all [blk_194.res, rv_simp] <;> rfl
  · intro A; simp [blk_194.res, rv_simp]
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
structure DRegs (index : Nat) (s : MachineState) : Prop where
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 index
  x6 : s.getReg .x6 = BitVec.ofNat 64 1
  x7 : s.getReg .x7 = BitVec.ofNat 64 2
  heaps : ∀ h, 1 ≤ h → h ≤ 7 → s.getReg (Merkle.heapReg h) = BitVec.ofNat 64 (index + 2 ^ 32 * h)
  x29 : s.getReg .x29 = BitVec.ofNat 64 17468
  x24 : s.getReg .x24 = BitVec.ofNat 64 50236
  x2 : s.getReg .x2 = BitVec.ofNat 64 65532
theorem heap_or (h index : Nat) (hidx : index < 2 ^ 31) :
    BitVec.ofNat 64 (h * 4294967296) ||| BitVec.ofNat 64 index = BitVec.ofNat 64 (index + 2 ^ 32 * h) := by
  rw [show h * 4294967296 = h * 2 ^ 32 by norm_num, ofNat_or_add index h 32 (by omega)]
  congr 1; ring
theorem drv_entry {im : Image} (hc : NewCodeAt im) (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf base)
    (h5 : s.getReg .x5 = 0) (hN : OutAt s 0x60 N) (hg : N.toNat / 2 ^ 31 % 2 ^ 12 = 0) :
    ∃ t, Steps im s 42 42 t ∧ t.pc = pcOf (base + 45) ∧ DRegs (N.toNat % 2 ^ 31) t ∧
      t.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1)) ∧ Frame s t (fun _ => False) := by
  have hw := hN 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have s1 := symRun_sound blk_0 (codeAt_0 hc) s hpc (by simp [blk_0.res, rv_simp])
  set u1 := blk_0.res.toState s with hu1
  have p1 : u1.pc = pcOf (base + 4) := by simp [hu1, Result.toState_pc, blk_0.res, E.eval, base]
  have s2 := symRun_sound blk_4 (codeAt_4 hc) u1 p1 (by simp [blk_4.res, rv_simp])
  set u2 := blk_4.res.toState u1 with hu2
  have m1 : ∀ A, u1.getMem A = s.getMem A := fun A => by simp [hu1, blk_0.res, rv_simp]
  have r1 : ∀ r, u1.getReg r = s.getReg r := fun r => by cases r <;> simp [hu1, blk_0.res, rv_simp] <;> rfl
  have p2 : u2.pc = pcOf (base + 9) := by simp [hu2, Result.toState_pc, blk_4.res, E.eval, base]
  have x3_2 : u2.getReg .x3 = 0#64 := by
    simp only [hu2, Result.toState_getReg, blk_4.res, rv_simp, m1, hw, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow]
    apply BitVec.eq_of_toNat_eq
    rw [gate_toNat, hg]; rfl
  have s3 := symRun_sound blk_9 (codeAt_9 hc) u2 p2 (by simp [blk_9.res, rv_simp])
  set u3 := blk_9.res.toState u2 with hu3
  have p3 : u3.pc = pcOf (base + 10) := by
    simp [hu3, Result.toState_pc, blk_9.res, E.eval, CmpOp.eval, x3_2, base]
  have r3 : ∀ r, u3.getReg r = u2.getReg r := fun r => by cases r <;> simp [hu3, blk_9.res, rv_simp] <;> rfl
  have m3 : ∀ A, u3.getMem A = u2.getMem A := fun A => by simp [hu3, blk_9.res, rv_simp]
  have x22_3 : u3.getReg .x22 = N.extractLsb' 0 64 := by
    rw [r3]; simp only [hu2, Result.toState_getReg, blk_4.res, rv_simp, m1, hw]
  have s4 := symRun_sound blk_10 (codeAt_10 hc) u3 p3 (by simp [blk_10.res, rv_simp])
  set u4 := blk_10.res.toState u3 with hu4
  have hx : (N.extractLsb' 0 64 <<< 33 >>> 33) = BitVec.ofNat 64 (N.toNat % 2 ^ 31) := index_eq N
  refine ⟨u4, (s1.trans (s2.trans (s3.trans s4))), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hu4, Result.toState_pc, blk_10.res, E.eval, base]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, r3, hu2, blk_4.res, r1, h5]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, x22_3, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow]
    exact hx
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · intro h h1 h7
    have hh : h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Merkle.heapReg, hu4, Result.toState_getReg, blk_10.res, rv_simp, x22_3, BitVec.toNat_ofNat,
        Nat.reduceMod, Nat.reducePow, hx]
      first
        | exact heap_or 1 _ hidx | exact heap_or 2 _ hidx | exact heap_or 3 _ hidx | exact heap_or 4 _ hidx
        | exact heap_or 5 _ hidx | exact heap_or 6 _ hidx | exact heap_or 7 _ hidx
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp, regBase]
  · simp [hu4, blk_10.res, rv_simp, HB0]
  · intro A _ _
    simp only [hu4, Result.toState_getMem, blk_10.res, memEval_nil, m3, hu2, blk_4.res, m1]
end ClaudeWCT.W9.Machine.Expand
end
