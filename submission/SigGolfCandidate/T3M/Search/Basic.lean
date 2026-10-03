import SigGolfCandidate.T3M.Mem

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev NODE : Nat := 0x20200
abbrev NOUT : Nat := 0x20240
abbrev ENC : Nat := 0x20260
abbrev EOUT : Nat := 0x202A0
abbrev DIGITS : Nat := 0x20420
abbrev SEL : Nat := 0x204A0
@[simp] theorem pcOf_and_max (k : Nat) : pcOf k &&& 18446744073709551614#64 = pcOf k :=
  pcOf_and_not1 k
theorem pcOf_inj {a b : Nat} (ha : 0x1000 + 4 * a < 2 ^ 64) (hb : 0x1000 + 4 * b < 2 ^ 64)
    (h : pcOf a = pcOf b) : a = b := by
  have := (ofNat_inj ha hb).mp h
  omega
theorem extractByte_replaceByte_same (w : Word) (k : Nat) (hk : k < 8) (b : BitVec 8) :
    extractByte (replaceByte w k b) k = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  have h1 : k * 8 + i < 64 := by omega
  simp only [h1, decide_true, Bool.true_and, show ¬ (k * 8 + i < k * 8) by omega, decide_false,
    Bool.not_false, Bool.true_and, Nat.add_sub_cancel_left]
  have h2 : (255 : Nat).testBit i = true := by
    have : (255 : Nat) = 2 ^ 8 - 1 := rfl
    rw [this, Nat.testBit_two_pow_sub_one]; simp; omega
  simp [BitVec.getLsbD_ofNat, h2, hi, show i < 64 by omega]
theorem extractByte_replaceByte_diff (w : Word) (j k : Nat) (hj : j < 8) (_hk : k < 8) (hne : j ≠ k)
    (b : BitVec 8) : extractByte (replaceByte w k b) j = extractByte w j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, replaceByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  have h1 : j * 8 + i < 64 := by omega
  by_cases hlt : j * 8 + i < k * 8
  · simp [h1, hlt]
  · have h3 : ¬ (j * 8 + i - k * 8 < 8) := by
      rcases Nat.lt_or_gt_of_ne hne with h | h <;> omega
    have h2 : (255 : Nat).testBit (j * 8 + i - k * 8) = false := by
      have : (255 : Nat) = 2 ^ 8 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; simpa using h3
    simp [h1, hlt, BitVec.getLsbD_ofNat, h2, BitVec.getLsbD_of_ge b _ (by omega : 8 ≤ j * 8 + i - k * 8)]
theorem getByte_setByte (s : MachineState) (a a' : Nat) (ha : a < 2 ^ 64) (ha' : a' < 2 ^ 64) (b : BitVec 8) :
    (s.setByte (BitVec.ofNat 64 a) b).getByte (BitVec.ofNat 64 a') =
      if a' = a then b else s.getByte (BitVec.ofNat 64 a') := by
  rw [getByte_eq_word _ a' ha']
  unfold MachineState.setByte
  have hal : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega)]; omega
  have hbo : byteOffset (BitVec.ofNat 64 a) = a % 8 := by rw [byteOffset_eq, toNat_ofNat_lt ha]
  simp only [hal, hbo]
  rw [getMem_setMem_ofNat _ _ _ _ (by omega) (by omega)]
  by_cases hw : a' / 8 * 8 = a / 8 * 8
  · rw [if_pos hw]
    by_cases he : a' = a
    · subst he; rw [if_pos rfl, extractByte_replaceByte_same _ _ (Nat.mod_lt _ (by decide))]
    · rw [if_neg he, extractByte_replaceByte_diff _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
        (by omega), getByte_eq_word _ a' ha', hw]
  · rw [if_neg hw, if_neg (by omega), getByte_eq_word _ a' ha']
@[simp] theorem getByte_setPC (s : MachineState) (pc a : Word) : (s.setPC pc).getByte a = s.getByte a := rfl
@[simp] theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getByte a = s.getByte a := by
  cases r <;> rfl
@[simp] theorem getReg_setByte (s : MachineState) (a : Word) (v : BitVec 8) (r : Reg) :
    (s.setByte a v).getReg r = s.getReg r := by
  simp [MachineState.setByte]
@[simp] theorem getReg_setPC' (s : MachineState) (pc : Word) (r : Reg) : (s.setPC pc).getReg r = s.getReg r := by
  cases r <;> rfl
@[simp] theorem getMem_setPC' (s : MachineState) (pc a : Word) : (s.setPC pc).getMem a = s.getMem a := rfl
theorem getMem_setByte (s : MachineState) (a A : Nat) (ha : a < 2 ^ 64) (hA : A < 2 ^ 64) (b : BitVec 8)
    (hne : A ≠ a / 8 * 8) : (s.setByte (BitVec.ofNat 64 a) b).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  unfold MachineState.setByte
  have hal : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega)]; omega
  simp only [hal]
  rw [getMem_setMem_ofNat _ _ _ _ (by omega) hA, if_neg hne]
theorem steps_sb {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32}
    (hc : CodeAt image pc [w]) (hpc : s.pc = pc) {rs1 rs2 : Reg} {off : BitVec 12}
    (hdec : decodeInstruction w = some (.base (.SB rs1 rs2 off)))
    (hv : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    Steps image s 1 1 ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC
      (s.pc + 4)) := by
  have hf : fetch image s = some (.base (.SB rs1 rs2 off)) := (hc.fetch s hpc).trans hdec
  have hcl : classify (.base (.SB rs1 rs2 off)) = some (.store .b rs1 rs2 (signExtend12 off)) := rfl
  have hs : ordinaryStep s (.base (.SB rs1 rs2 off)) =
      some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, StoreKind.width, hv, if_true, StoreKind.write]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl
end SigGolfCandidate.T3M.Search
