import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs

section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open ClaudeWCT.W9.Machine.Expand.Driver
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def dOff (k : Nat) : Nat := [34,50,68,86,104,122,140,158,176,194].getD k 0
def dLen (k : Nat) : Nat := if k = 0 then 16 else 18
def pslot (k : Nat) : Nat := 0x420 + 32 * k
def dWord (k : Nat) : Nat := WCT9.coordBase k / 64
theorem disp_0 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 34))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (0 - 1)))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨0, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 50) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 0) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 0) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨0, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨0, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 0 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 0) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨0, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 0) ∧
      t.getReg .x16 = N.extractLsb' (64 * 0) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 0 43 (by omega)
  have hf4 := field4_bits N 0 43 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 43 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_34 (codeAt_34 hc) s hpc (by
    simp [blk_34.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_34.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_34.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, h15] <;> try rfl
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31n _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_34.res, rv_simp, hw] <;> try rfl
  · simp [blk_34.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_34.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_34.res, rv_simp]
theorem disp_1 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 50))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (1 - 1)))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (1 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (1 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨1, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 68) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 1) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 1) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨1, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨1, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 1 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 1) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨1, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 1) ∧
      t.getReg .x16 = N.extractLsb' (64 * 1) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 1 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 0 (by omega)
  have hf4 := field4_bits N 1 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 64 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_50 (codeAt_50 hc) s hpc (by
    simp [blk_50.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_50.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_50.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_50.res, rv_simp, hw] <;> try rfl
  · simp [blk_50.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_50.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_50.res, rv_simp]
theorem disp_2 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 68))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (2 - 1)))
    (h16 : s.getReg .x16 = N.extractLsb' (64 * 1) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (2 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (2 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨2, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 86) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 2) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 2) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨2, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨2, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 2 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 2) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨2, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 2) ∧
      t.getReg .x16 = N.extractLsb' (64 * 1) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 2) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := h16
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 21 (by omega)
  have hf4 := field4_bits N 1 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 85 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_68 (codeAt_68 hc) s hpc (by
    simp [blk_68.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_68.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_68.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_68.res, rv_simp, hw] <;> try rfl
  · simp [blk_68.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_68.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_68.res, rv_simp]
theorem disp_3 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 86))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (3 - 1)))
    (h16 : s.getReg .x16 = N.extractLsb' (64 * 1) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (3 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (3 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨3, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 104) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 3) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 3) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨3, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨3, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 3 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 3) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨3, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 3) ∧
      t.getReg .x16 = N.extractLsb' (64 * 1) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 3) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := h16
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 1 42 (by omega)
  have hf4 := field4_bits N 1 42 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 106 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_86 (codeAt_86 hc) s hpc (by
    simp [blk_86.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_86.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_86.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_86.res, rv_simp, hw] <;> try rfl
  · simp [blk_86.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_86.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_86.res, rv_simp]
theorem disp_4 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 104))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (4 - 1)))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (4 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (4 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨4, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 122) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 4) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 4) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨4, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨4, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 4 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 4) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨4, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 4) ∧
      t.getReg .x16 = N.extractLsb' (64 * 2) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 4) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 0 (by omega)
  have hf4 := field4_bits N 2 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 128 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_104 (codeAt_104 hc) s hpc (by
    simp [blk_104.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_104.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_104.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_104.res, rv_simp, hw] <;> try rfl
  · simp [blk_104.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_104.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_104.res, rv_simp]
theorem disp_5 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 122))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (5 - 1)))
    (h16 : s.getReg .x16 = N.extractLsb' (64 * 2) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (5 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (5 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨5, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 140) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 5) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 5) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨5, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨5, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 5 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 5) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨5, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 5) ∧
      t.getReg .x16 = N.extractLsb' (64 * 2) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 5) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := h16
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 21 (by omega)
  have hf4 := field4_bits N 2 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 149 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_122 (codeAt_122 hc) s hpc (by
    simp [blk_122.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_122.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_122.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_122.res, rv_simp, hw] <;> try rfl
  · simp [blk_122.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_122.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_122.res, rv_simp]
theorem disp_6 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 140))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (6 - 1)))
    (h16 : s.getReg .x16 = N.extractLsb' (64 * 2) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (6 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (6 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨6, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 158) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 6) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 6) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨6, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨6, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 6 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 6) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨6, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 6) ∧
      t.getReg .x16 = N.extractLsb' (64 * 2) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 6) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := h16
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 2 42 (by omega)
  have hf4 := field4_bits N 2 42 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 170 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_140 (codeAt_140 hc) s hpc (by
    simp [blk_140.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_140.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_140.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_140.res, rv_simp, hw] <;> try rfl
  · simp [blk_140.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_140.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_140.res, rv_simp]
theorem disp_7 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 158))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (7 - 1)))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (7 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (7 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨7, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 176) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 7) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 7) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨7, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨7, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 7 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 7) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨7, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 7) ∧
      t.getReg .x16 = N.extractLsb' (64 * 3) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 7) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := hN 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 3 0 (by omega)
  have hf4 := field4_bits N 3 0 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 192 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_158 (codeAt_158 hc) s hpc (by
    simp [blk_158.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_158.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_158.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_158.res, rv_simp, hw] <;> try rfl
  · simp [blk_158.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_158.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_158.res, rv_simp]
theorem disp_8 {im : Image} (hc : NewCodeAt im) (N : HashOutput) (index : Nat) (hidx : index < 2 ^ 31)
    (s : MachineState) (hpc : s.pc = pcOf (base + 176))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (8 - 1)))
    (h16 : s.getReg .x16 = N.extractLsb' (64 * 3) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (8 - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (8 - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨8, by decide⟩) ∧
      t.getReg .x1 = pcOf (base + 194) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase 8) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * 8) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨8, by decide⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨8, by decide⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * 8 + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * 8) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨8, by decide⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * 8) ∧
      t.getReg .x16 = N.extractLsb' (64 * 3) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot 8) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  have hw := h16
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw
  have hch := child_bits N 3 21 (by omega)
  have hf4 := field4_bits N 3 21 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.ushiftRight_zero] at hch hf4
  have hcl : N.toNat / 2 ^ 213 % 128 < 128 := Nat.mod_lt _ (by decide)
  refine ⟨_, symRun_sound blk_176 (codeAt_176 hc) s hpc (by
    simp [blk_176.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, HB0]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_176.res, E.eval, BinOp.eval, hw, h2, h24, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_pc _ _ hf4 (Nat.mod_lt _ (by decide))]
    rfl
  · simp [blk_176.res, rv_simp, base]
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, h8, regBase] <;> try rfl
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, h28, HB0] <;> try rfl
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, hw, h22, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x4 _ _ _ hch hcl hidx]; rfl
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, hw, h29, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    rw [disp_x23 _ _ hch hcl]; rfl
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, h28, HB0]
    congr 2
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, h15, h6]
    rw [disp_x15]
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, hw, h15, h6, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, BitVec.ushiftRight_zero]
    exact disp_x31s _ _ _ _ _ hch hcl (by norm_num) (by norm_num)
  · simp only [Result.toState_getReg, blk_176.res, rv_simp, hw] <;> try rfl
  · simp [blk_176.res, rv_simp, pslot]
  · intro r h1 h3 h4 h8' h9 h14 h15' h16' h23 h27 h28' h31
    cases r <;> simp_all [blk_176.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_176.res, rv_simp]
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
  x7 : s.getReg .x7 = BitVec.ofNat 64 1
  x6 : s.getReg .x6 = BitVec.ofNat 64 65536
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → s.getReg (Merkle.heapReg h) = BitVec.ofNat 64 h
  x17 : s.getReg .x17 = BitVec.ofNat 64 index <<< 32
  x29 : s.getReg .x29 = BitVec.ofNat 64 17572
  x24 : s.getReg .x24 = BitVec.ofNat 64 50340
  x2 : s.getReg .x2 = BitVec.ofNat 64 65532
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
theorem shl_index (index n : Nat) : BitVec.ofNat 64 index <<< n = BitVec.ofNat 64 (index * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
theorem drv_entry {im : Image} (hc : NewCodeAt im) (N : HashOutput) (s : MachineState) (hpc : s.pc = pcOf base)
    (h5 : s.getReg .x5 = 0) (hN : OutAt s 0x60 N) (hg : N.toNat / 2 ^ 234 % 2 ^ 14 < 5) :
    ∃ t, Steps im s 31 31 t ∧ t.pc = pcOf (base + 34) ∧ DRegs (N.toNat % 2 ^ 31) t ∧
      t.getReg .x8 = BitVec.ofNat 64 (regBase (0 - 1)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (0 - 1)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (N.toNat % 2 ^ 31 * 2 ^ 27 + 65536 * (0 - 1)) ∧
      Frame s t (fun _ => False) := by
  have hw := hN 0 (by decide)
  have hw3 := hN 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw hw3
  have s1 := symRun_sound blk_0 (codeAt_0 hc) s hpc (by simp [blk_0.res, rv_simp])
  set u1 := blk_0.res.toState s with hu1
  have p1 : u1.pc = pcOf (base + 4) := by simp [hu1, Result.toState_pc, blk_0.res, E.eval, base]
  have s2 := symRun_sound blk_4 (codeAt_4 hc) u1 p1 (by simp [blk_4.res, rv_simp])
  set u2 := blk_4.res.toState u1 with hu2
  have m1 : ∀ A, u1.getMem A = s.getMem A := fun A => by simp [hu1, blk_0.res, rv_simp]
  have r1 : ∀ r, u1.getReg r = s.getReg r := fun r => by cases r <;> simp [hu1, blk_0.res, rv_simp] <;> rfl
  have p2 : u2.pc = pcOf (base + 9) := by simp [hu2, Result.toState_pc, blk_4.res, E.eval, base]
  have x3_2 : u2.getReg .x3 = 1#64 := by
    simp only [hu2, Result.toState_getReg, blk_4.res, rv_simp, m1, hw, hw3, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow]
    have hlt : BitVec.ult ((N.extractLsb' 192 64 <<< 8) >>> 50) 5#64 = true := by
      simp only [BitVec.ult, gate_toNat N, show (5#64 : Word).toNat = 5 from rfl, decide_eq_true_eq]; exact hg
    simp [hlt]
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
  refine ⟨u4, (s1.trans (s2.trans (s3.trans s4))), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [hu4, Result.toState_pc, blk_10.res, E.eval, base]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, r3, hu2, blk_4.res, r1, h5]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, x22_3, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow]
    exact hx
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · intro h h1 h7
    have hh : h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 6 ∨ h = 7 := by omega
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp [Merkle.heapReg, hu4, blk_10.res, rv_simp]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, x22_3, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, hx]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp]
  · simp [hu4, blk_10.res, rv_simp, regBase]
  · simp [hu4, blk_10.res, rv_simp, HB0]
  · simp only [hu4, Result.toState_getReg, blk_10.res, rv_simp, x22_3, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, hx]
    rw [shl_index]; simp only [Nat.reducePow, Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
  · intro A _ _
    simp only [hu4, Result.toState_getMem, blk_10.res, memEval_nil, m3, hu2, blk_4.res, m1]
theorem dOff_succ (k : Nat) (hk : k < 9) : dOff (k + 1) = dOff k + dLen k := by
  interval_cases k <;> rfl
theorem disp_spec {im : Image} (hc : NewCodeAt im) (k : Nat) (hk : k < 9) (N : HashOutput) (index : Nat)
    (hidx : index < 2 ^ 31) (s : MachineState) (hpc : s.pc = pcOf (base + dOff k))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 index) (h29 : s.getReg .x29 = BitVec.ofNat 64 17572)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 50340) (h2 : s.getReg .x2 = BitVec.ofNat 64 65532)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 65536)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * (k - 1)))
    (h16 : 0 < k → s.getReg .x16 = N.extractLsb' (64 * dWord (k - 1)) 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 (regBase (k - 1)))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * (k - 1))) (hN : OutAt s 0x60 N) :
    ∃ t, Steps im s (dLen k) (dLen k) t ∧ t.pc = pcOf (jt0 + WCT9.field N ⟨k, hk⟩) ∧
      t.getReg .x1 = pcOf (base + dOff k + dLen k) ∧ t.getReg .x8 = BitVec.ofNat 64 (regBase k) ∧
      t.getReg .x28 = BitVec.ofNat 64 (HB0 + 2048 + 512 * k) ∧
      t.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * (WCT9.child N ⟨k, hk⟩).val) ∧
      t.getReg .x23 = BitVec.ofNat 64 (17572 + 256 * (WCT9.child N ⟨k, hk⟩).val) ∧
      t.getReg .x27 = s.getMem (BitVec.ofNat 64 (HB0 + 512 * k + 448)) ||| s.getReg .x17 ∧
      t.getReg .x15 = BitVec.ofNat 64 (index * 2 ^ 27 + 65536 * k) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((WCT9.child N ⟨k, hk⟩).val * 2 ^ 20 + index * 2 ^ 27 + 65536 * k) ∧
      t.getReg .x16 = N.extractLsb' (64 * dWord k) 64 ∧
      t.getReg .x9 = BitVec.ofNat 64 (pslot k) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x23 →
        r ≠ .x27 → r ≠ .x28 → r ≠ .x31 → t.getReg r = s.getReg r) ∧ Frame s t (fun _ => False) := by
  interval_cases k
  · exact disp_0 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 h8 h28 hN
  · exact disp_1 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 h8 h28 hN
  · exact disp_2 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 (h16 (by decide)) h8 h28 hN
  · exact disp_3 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 (h16 (by decide)) h8 h28 hN
  · exact disp_4 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 h8 h28 hN
  · exact disp_5 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 (h16 (by decide)) h8 h28 hN
  · exact disp_6 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 (h16 (by decide)) h8 h28 hN
  · exact disp_7 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 h8 h28 hN
  · exact disp_8 hc N index hidx s hpc h22 h29 h24 h2 h6 h15 (h16 (by decide)) h8 h28 hN
theorem forest_blk {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 194)) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf (base + 203) ∧ fetch im t = some (.base .ECALL) ∧
      t.getMem (BitVec.ofNat 64 0x400) = 0 ∧ t.getMem (BitVec.ofNat 64 0x408) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x410) = BitVec.ofNat 64 3841 ∧ t.getMem (BitVec.ofNat 64 0x418) = s.getReg .x22 ∧
      t.getReg .x10 = BitVec.ofNat 64 0x400 ∧ t.getReg .x11 = BitVec.ofNat 64 320 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x100 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      Frame s t (fun A => 0x400 ≤ A ∧ A < 0x420) := by
  have hs := symRun_sound blk_194 (codeAt_194 hc) s hpc (by simp [blk_194.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, blk_194.res, E.eval, base]
  · rw [(codeAt_203 hc).fetch _ (by simp [Result.toState_pc, blk_194.res, E.eval, base])]; rfl
  · simp only [Result.toState_getMem, blk_194.res]; t3n []
  · simp only [Result.toState_getMem, blk_194.res]; t3n []
  · simp only [Result.toState_getMem, blk_194.res]; t3n []
  · simp only [Result.toState_getMem, blk_194.res]; t3n []
  · simp [blk_194.res, rv_simp]
  · simp [blk_194.res, rv_simp]
  · simp [blk_194.res, rv_simp]
  · intro r h3 h10 h11 h12; cases r <;> simp_all [blk_194.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [not_and, not_lt] at hn
    simp only [Result.toState_getMem, blk_194.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem end_blk {im : Image} (hc : NewCodeAt im) (s : MachineState) (hpc : s.pc = pcOf (base + 204)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 39142 ∧ (∀ r, t.getReg r = s.getReg r) ∧ (∀ A, t.getMem A = s.getMem A) := by
  have hs := symRun_sound blk_204 (codeAt_204 hc) s hpc (by simp [blk_204.res, rv_simp])
  refine ⟨_, hs, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, blk_204.res, E.eval, base]
  · intro r; cases r <;> simp [blk_204.res, rv_simp] <;> rfl
  · intro A; simp [blk_204.res, rv_simp]
end ClaudeWCT.W9.Machine.Expand
end
