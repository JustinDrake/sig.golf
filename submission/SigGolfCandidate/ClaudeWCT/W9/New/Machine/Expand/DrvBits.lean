import SigGolfCandidate.T3M.Expand.LayersBlocks
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.SearchCode
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.T3M.Search.DigestSearch
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev FLEAF : Nat := 0x202C0
abbrev FOREST : Nat := 0x20320
abbrev FOUT : Nat := 0x203A0
theorem shl_shr_33 (w : BitVec 64) : w <<< 33 >>> 33 = BitVec.ofNat 64 (w.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 64 = 2 ^ 31 * 2 ^ 33 by norm_num, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by positivity)]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 31 by positivity)
  omega
section blocks
variable (s : MachineState)
theorem s0_spec (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 30 30 t ∧ t.pc = pcOf 30 ∧ t.getReg .x5 = 0 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x40) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x48) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x50) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x58) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound eblk_0 codeAt_0 s hpc (by simp [eblk_0.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_0.res, E.eval]
  · simp [eblk_0.res, rv_simp]
  · simp [eblk_0.res, rv_simp]
  iterate 8
    · simp only [Result.toState_getMem, eblk_0.res, DIG]
      t3n []
  · ex_regs eblk_0.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, eblk_0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem s49_spec (hpc : s.pc = pcOf 49) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 65 ∧
      t.getReg .x9 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 0x810) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x810)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x2 = BitVec.ofNat 64 0x22000 ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 0xC40 ∧ t.getReg .x8 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x2, .x8, .x9, .x18, .x22, .x28] ∧ Frame s t (fun A => A = IDXV ∨ A = 0x810) := by
  refine ⟨_, symRun_sound eblk_49 codeAt_49 s hpc (by simp [eblk_49.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_49.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49.res, rv_simp, NBUF]
    t3n []
    rw [shl_shr_33]
    norm_num
  · simp only [Result.toState_getMem, eblk_49.res, NBUF, IDXV]
    t3n []
    rw [shl_shr_33]
    norm_num
  · simp only [Result.toState_getMem, eblk_49.res]
    t3n [h19]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · simp [eblk_49.res, rv_simp]
  · ex_regs eblk_49.res
  · intro A hA hn
    simp only [IDXV] at hn
    simp only [Result.toState_getMem, eblk_49.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem s215_spec (hpc : s.pc = pcOf 215) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = s.getReg .x18 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_215 codeAt_215 s hpc (by simp [eblk_215.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_215.res, E.eval]
  · simp [eblk_215.res, rv_simp]
  · ex_regs eblk_215.res
  · intro A _ _; simp [eblk_215.res, rv_simp]
theorem s216_spec (hpc : s.pc = pcOf 216) (j : Nat) (hj : j ≤ 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 115 ≤ j then pcOf 228 else pcOf 218) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_216 codeAt_216 s hpc (by simp [eblk_216.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_216.res, E.eval, CmpOp.eval, rebase, rv_simp, h13]
    rw [ex_slt j 115 (by omega) (by omega)]
    by_cases h : 115 ≤ j
    · simp [h, show ¬ j < 115 by omega]
    · simp [h, show j < 115 by omega]
  · ex_regs eblk_216.res
  · intro A _ _; simp [eblk_216.res, rv_simp]
theorem slot_addr (j : Nat) :
    BitVec.ofNat 64 j <<< ((4#64 : BitVec 64).toNat % 64) + 29024#64 = BitVec.ofNat 64 (0x7160 + 16 * j) := by
  rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem s218_spec (hpc : s.pc = pcOf 218) (j : Nat) (hj : j < 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 6 6 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = 0 then pcOf 224 else pcOf 354) ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7160 + 16 * j) ∧
      RegsExcept s t [.x6, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_218 codeAt_218 s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_218.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h13, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    rw [slot_addr]
    exact ex_valid _ (by omega) (by omega)
  · simp only [Result.toState_pc, eblk_218.res, E.eval, CmpOp.eval, rebase, rv_simp, h13]
    rw [slot_addr]
    by_cases h : s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = 0
    · simp [h]
    · simp [h]
  · simp only [Result.toState_getReg, eblk_218.res, rv_simp, h13]
    t3n []
    congr 1; omega
  · ex_regs eblk_218.res
  · intro A _ _; simp [eblk_218.res, rv_simp]
theorem s224_spec (hpc : s.pc = pcOf 224) (j : Nat) (hj : j < 115)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (0x7160 + 16 * j)) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = 0 then pcOf 226 else pcOf 354) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_224 codeAt_224 s hpc ?_, ?_, ?_, ?_⟩
  · simp only [eblk_224.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h28, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    exact ex_valid _ (by omega) (by omega)
  · simp only [Result.toState_pc, eblk_224.res, E.eval, CmpOp.eval, rebase, rv_simp, h28, ofNat_add_ofNat]
    by_cases h : s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = 0
    · simp [h]
    · simp [h]
  · ex_regs eblk_224.res
  · intro A _ _; simp [eblk_224.res, rv_simp]
theorem s226_spec (hpc : s.pc = pcOf 226) (j : Nat) (hj : j < 115) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_226 codeAt_226 s hpc (by simp [eblk_226.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_226.res, E.eval]
  · simp only [Result.toState_getReg, eblk_226.res, rv_simp, h13, ofNat_add_ofNat]
  · ex_regs eblk_226.res
  · intro A _ _; simp [eblk_226.res, rv_simp]
theorem s228_spec (hpc : s.pc = pcOf 228) (index : Nat) (hi : index < 2 ^ 31)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 240 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 16)) = BitVec.ofNat 64 2817 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 24)) = BitVec.ofNat 64 index ∧
      t.getReg .x10 = BitVec.ofNat 64 FOREST ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 FOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = FOREST + 16 ∨ A = FOREST + 24) := by
  refine ⟨_, symRun_sound eblk_228 codeAt_228 s hpc (by simp [eblk_228.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_228.res, E.eval]
  · simp only [Result.toState_getMem, eblk_228.res, FOREST]
    t3n []
  · simp only [Result.toState_getMem, eblk_228.res, FOREST]
    t3n [h9]
  · simp [eblk_228.res, rv_simp]
  · simp [eblk_228.res, rv_simp]
  · simp [eblk_228.res, rv_simp]
  · ex_regs eblk_228.res
  · intro A hA hn
    simp only [FOREST] at hn
    simp only [Result.toState_getMem, eblk_228.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_240 (hpc : s.pc = pcOf 240) : fetch image s = some (.base .ECALL) :=
  (codeAt_240.fetch s hpc).trans rfl
theorem s241_spec (hpc : s.pc = pcOf 241) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf 249 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_241 codeAt_241 s hpc (by simp [eblk_241.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_241.res, E.eval]
  · simp only [Result.toState_getMem, eblk_241.res, ENC, FOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_241.res, ENC, FOUT]
    t3n []
  · ex_regs eblk_241.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_241.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
end blocks
end SigGolfCandidate.T3M.Expand
end

section




namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Expand.SearchCode
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
theorem extractLsb'_256_toNat (a : BitVec 256) (w : Nat) :
    (a.extractLsb' (64 * w) 64).toNat = a.toNat / 2 ^ (64 * w) % 2 ^ 64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem mod_div_mod (X k m : Nat) (h : k + m ≤ 64) : X % 2 ^ 64 / 2 ^ k % 2 ^ m = X / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have : i + k < 64 := by omega
    simp [this]
  · simp [hi]
theorem field_toNat (a : BitVec 256) (w sh : Nat) (h : sh + 21 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh >>> 7) &&& 16383#64).toNat = a.toNat / 2 ^ (64 * w + sh + 7) % 2 ^ 14 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (16383#64).toNat = 2 ^ 14 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add, mod_div_mod _ _ _ (by omega),
    Nat.div_div_eq_div_mul, ← Nat.pow_add]
  ring_nf
theorem field_toNat0 (a : BitVec 256) (w : Nat) :
    ((a.extractLsb' (64 * w) 64 >>> 7) &&& 16383#64).toNat = a.toNat / 2 ^ (64 * w + 7) % 2 ^ 14 := by
  have := field_toNat a w 0 (by omega)
  simpa using this
theorem gate_toNat (a : BitVec 256) :
    ((a.extractLsb' 192 64 <<< 8) >>> 50).toNat = a.toNat / 2 ^ 234 % 2 ^ 14 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have h1 : a.toNat / 2 ^ 192 % 2 ^ 64 * 2 ^ 8 % 2 ^ 64 / 2 ^ 50 = a.toNat / 2 ^ 192 % 2 ^ 64 / 2 ^ 42 % 2 ^ 14 := by
    have := Nat.mod_lt (a.toNat / 2 ^ 192) (show 0 < 2 ^ 64 by positivity)
    omega
  rw [h1, show (2 : Nat) ^ 64 = 2 ^ 42 * 2 ^ 22 by norm_num, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 14 ≤ 22)), Nat.div_div_eq_div_mul, ← pow_add]
theorem beq_sltu5 {α : Type} (g : Word) (n : Nat) (hg : g.toNat = n) (A B : α) :
    (if ((if BitVec.ult g 5#64 = true then (1 : Word) else 0) == 0#64) = true then A else B) =
      (if n < 5 then B else A) := by
  by_cases hn : n < 5
  · have : BitVec.ult g 5#64 = true := by simp [BitVec.ult, hg, hn]
    simp [this, hn]
  · have : BitVec.ult g 5#64 = false := by simp [BitVec.ult, hg]; omega
    simp [this, hn]
theorem index_eq (a : BitVec 256) :
    a.extractLsb' 0 64 <<< 33 >>> 33 = BitVec.ofNat 64 (a.toNat % 2 ^ 31) := by
  rw [SigGolfCandidate.T3M.Expand.shl_shr_33]
  congr 1
  rw [show (0 : Nat) = 64 * 0 from rfl, extractLsb'_256_toNat]
  rw [show 64 * 0 = 0 from rfl, pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
def fieldN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14
theorem admissible_eq (a : BitVec 256) :
    WCT9.admissible a = (decide (a.toNat / 2 ^ 234 % 2 ^ 14 < 5) &&
      (List.range 9).all fun c => decide (fieldN a c < 16016)) := rfl
def SearchAt (im : Image) (b : Nat) : Prop := CodeAt im (pcOf b) SearchCode.code
theorem ult_ofNat (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
section blocks
variable {im : Image} {b : Nat}
theorem sr0_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf b) (i : Nat) (hi : i ≤ 2 ^ 21)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i < 2 ^ 21 then pcOf (b + 4) else pcOf (b + 3)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_0 b) (codeAt_0 h) s hpc (by simp [blk_0.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, rebase, blk_0.res, E.eval, CmpOp.eval, h19]
    rw [show (2097152#64 : Word) = BitVec.ofNat 64 2097152 from rfl, ult_ofNat _ _ (by omega) (by omega)]
    by_cases hlt : i < 2 ^ 21
    · simp [hlt]
    · simp only [show ¬ i < 2097152 by omega, hlt, decide_false, ite_false]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_0.res, rv_simp]
theorem sr3_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (b + 138) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_3 b) (codeAt_3 h) s hpc (by simp [blk_3.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, rebase, blk_3.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_3.res, rv_simp]
theorem sr138_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 138)) :
    ∃ t, Steps im s 2 2 t ∧ FailedAt (b + 138) t ∧ fetch im t = some (.base .ECALL) := by
  have hs := symRun_sound (run'_138 b) (codeAt_138 h) s hpc (by simp [blk_138.res, rv_simp])
  refine ⟨_, hs, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp [Result.toState_pc, rebase, blk_138.res, E.eval]
  · simp [blk_138.res, rv_simp]
  · simp [blk_138.res, rv_simp]
  · rw [(codeAt_140 h).fetch _ (by simp [Result.toState_pc, rebase, blk_138.res, E.eval])]; rfl
theorem sr4_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 4)) (i : Nat)
    (hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf (b + 16) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run'_4 b) (codeAt_4 h) s hpc
    (by simp [blk_4.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, rebase, blk_4.res, E.eval]
  · simp only [Result.toState_getMem, blk_4.res]
    t3n [DIG]
    rfl
  · simp only [Result.toState_getMem, blk_4.res]
    t3n [h19, DIG]
    rw [hdr1_eq 0 i (by decide) (by omega)]
    congr 1
    omega
  · simp [blk_4.res, rv_simp]
  · simp [blk_4.res, rv_simp]
  · simp [blk_4.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_4.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_4.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]
theorem bgeu_16016 {α : Type} (v : Word) (n : Nat) (hv : v.toNat = n) (A B : α) :
    (if (!v.ult 16016#64) = true then A else B) = (if n < 16016 then B else A) := by
  simp only [BitVec.ult, hv, show (16016#64 : Word).toNat = 16016 from rfl]
  by_cases hn : n < 16016 <;> simp [hn]
theorem srF0_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 25)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 0 < 16016 then pcOf (b + 37) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_25 b) (codeAt_25 h) s hpc (by simp [blk_25.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 0 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_25.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 0 43 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 0) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_25.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_25.res, rv_simp]
theorem srF1_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 37)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = (if fieldN a 1 < 16016 then pcOf (b + 48) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_37 b) (codeAt_37 h) s hpc (by simp [blk_37.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 1 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_37.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat0 a 1
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 1) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_37.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_37.res, rv_simp]
theorem srF2_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 48)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 2 < 16016 then pcOf (b + 60) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_48 b) (codeAt_48 h) s hpc (by simp [blk_48.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 1 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_48.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 1 21 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 2) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_48.res, rv_simp]
theorem srF3_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 60)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 3 < 16016 then pcOf (b + 72) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_60 b) (codeAt_60 h) s hpc (by simp [blk_60.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 1 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_60.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 1 42 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 3) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_60.res, rv_simp]
theorem srF4_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 72)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = (if fieldN a 4 < 16016 then pcOf (b + 83) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_72 b) (codeAt_72 h) s hpc (by simp [blk_72.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 2 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_72.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat0 a 2
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 4) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_72.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_72.res, rv_simp]
theorem srF5_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 83)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 5 < 16016 then pcOf (b + 95) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_83 b) (codeAt_83 h) s hpc (by simp [blk_83.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 2 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_83.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 2 21 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 5) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_83.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_83.res, rv_simp]
theorem srF6_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 95)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 6 < 16016 then pcOf (b + 107) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_95 b) (codeAt_95 h) s hpc (by simp [blk_95.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 2 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_95.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 2 42 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 6) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_95.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_95.res, rv_simp]
theorem srF7_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 107)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = (if fieldN a 7 < 16016 then pcOf (b + 118) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_107 b) (codeAt_107 h) s hpc (by simp [blk_107.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_107.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat0 a 3
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 7) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_107.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_107.res, rv_simp]
theorem srF8_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 118)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = (if fieldN a 8 < 16016 then pcOf (b + 130) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run'_118 b) (codeAt_118 h) s hpc (by simp [blk_118.res, rv_simp]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw
    simp only [Result.toState_pc, rebase, blk_118.res, E.eval, CmpOp.eval, BinOp.eval, hw]
    have hv := field_toNat a 3 21 (by omega)
    simp only [Nat.reduceMul, Nat.reduceAdd] at hv
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    rw [bgeu_16016 _ (fieldN a 8) (by rw [hv]; rfl)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_118.res, rv_simp]
theorem bne_zero {α : Type} (v : Word) (n : Nat) (hv : v.toNat = n) (A B : α) :
    (if (v != 0#64) = true then A else B) = (if n = 0 then B else A) := by
  by_cases hn : n = 0
  · have : v = 0#64 := BitVec.eq_of_toNat_eq (by rw [hv, hn]; rfl)
    simp [this, hn]
  · have : v ≠ 0#64 := fun he => hn (by rw [← hv, he]; rfl)
    simp [this, hn]
theorem sr17_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 17)) (a : BitVec 256)
    (hN : OutAt s NBUF a) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = (if a.toNat / 2 ^ 234 % 2 ^ 14 < 5 then pcOf (b + 25) else pcOf (b + 136)) ∧
      t.getReg .x22 = a.extractLsb' 0 64 ∧ RegsExcept s t [.x6, .x7, .x22, .x28] ∧ Frame s t (fun _ => False) := by
  have hw := hN 0 (by decide)
  have hw3 := hN 3 (by decide)
  simp only [NBUF, Nat.reduceMul, Nat.reduceAdd] at hw hw3
  refine ⟨_, symRun_sound (run'_17 b) (codeAt_17 h) s hpc (by simp [blk_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, rebase, blk_17.res, E.eval, CmpOp.eval, BinOp.eval, hw, hw3]
    have hv := gate_toNat a
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at hv ⊢
    rw [beq_sltu5 _ _ hv]
  · simp [blk_17.res, rv_simp, hw]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_17.res, rv_simp]
theorem sr130_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 130)) (a : BitVec 256)
    (h22 : s.getReg .x22 = a.extractLsb' 0 64) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf (b + 141) ∧ t.getReg .x22 = BitVec.ofNat 64 (a.toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (a.toNat % 2 ^ 31) ∧ RegsExcept s t [.x22, .x28] ∧
      Frame s t (fun A => A = IDXV) := by
  refine ⟨_, symRun_sound (run'_130 b) (codeAt_130 h) s hpc
    (by simp [blk_130.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, rebase, blk_130.res, E.eval]
  · simp only [Result.toState_getReg, blk_130.res, rv_simp, h22, BitVec.toNat_ofNat, Nat.reduceMod]
    exact index_eq a
  · simp only [Result.toState_getMem, blk_130.res, rv_simp, h22, BitVec.toNat_ofNat, Nat.reduceMod, IDXV]
    simp only [ite_true]
    exact index_eq a
  · intro r hr; simp at hr; cases r <;> simp_all [blk_130.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_130.res]
    t3n []
    simp only [IDXV] at hn
    rw [if_neg (by omega)]
theorem sr136_spec (h : SearchAt im b) (s : MachineState) (hpc : s.pc = pcOf (b + 136)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf b ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  have s1 := symRun_sound (run'_136 b) (codeAt_136 h) s hpc (by simp [blk_136.res, rv_simp])
  set u := Result.toState _ s with hu
  have hpu : u.pc = pcOf (b + 137) := by simp [hu, Result.toState_pc, rebase, blk_136.res, E.eval]
  have s2 := jal_137 h u hpu
  refine ⟨_, s1.trans s2, rfl, ?_, ?_, ?_⟩
  · rw [MachineState.getReg_setPC]
    simp only [hu, Result.toState_getReg, blk_136.res, rv_simp, h19]
    t3n []
  · intro r hr
    rw [MachineState.getReg_setPC]
    simp at hr; cases r <;> simp_all [hu, blk_136.res, rv_simp] <;> rfl
  · intro A _ _
    simp [hu, blk_136.res, rv_simp]
def fs (c : Nat) : Nat := [25,37,48,60,72,83,95,107,118,130].getD c 0
theorem fld_spec (h : SearchAt im b) (c : Nat) (hc : c < 9) (s : MachineState) (hpc : s.pc = pcOf (b + fs c))
    (a : BitVec 256) (hN : OutAt s NBUF a) :
    ∃ t, Steps im s (fs (c + 1) - fs c) (fs (c + 1) - fs c) t ∧
      t.pc = (if fieldN a c < 16016 then pcOf (b + fs (c + 1)) else pcOf (b + 136)) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  interval_cases c
  · exact srF0_spec h s hpc a hN
  · exact srF1_spec h s hpc a hN
  · exact srF2_spec h s hpc a hN
  · exact srF3_spec h s hpc a hN
  · exact srF4_spec h s hpc a hN
  · exact srF5_spec h s hpc a hN
  · exact srF6_spec h s hpc a hN
  · exact srF7_spec h s hpc a hN
  · exact srF8_spec h s hpc a hN
theorem fs_mono (c : Nat) (hc : c < 9) : fs c < fs (c + 1) ∧ fs (c + 1) ≤ 130 ∧ 25 ≤ fs c := by
  interval_cases c <;> decide
theorem fields_spec (h : SearchAt im b) (a : BitVec 256) :
    ∀ d c, c + d = 9 → ∀ s : MachineState, s.pc = pcOf (b + fs c) → OutAt s NBUF a →
      ∃ t k, Steps im s k k t ∧ k ≤ 130 - fs c ∧
        t.pc = (if ∀ c', c ≤ c' → c' < 9 → fieldN a c' < 16016 then pcOf (b + 130) else pcOf (b + 136)) ∧
        RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  intro d
  induction d with
  | zero =>
    intro c hc s hpc _
    have hc9 : c = 9 := by omega
    subst hc9
    refine ⟨s, 0, Steps.refl s, by omega, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    rw [if_pos (fun c' h1 h2 => by omega)]
    exact hpc
  | succ d ih =>
    intro c hc s hpc hN
    have hc9 : c < 9 := by omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := fld_spec h c hc9 s hpc a hN
    have hm := fs_mono c hc9
    by_cases hf : fieldN a c < 16016
    · rw [if_pos hf] at p1
      have hN1 : OutAt t1 NBUF a := fun j hj => by rw [f1.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
      obtain ⟨t2, k2, s2, hk2, p2, r2, f2⟩ := ih (c + 1) (by omega) t1 p1 hN1
      refine ⟨t2, _, s1.trans s2, by omega, ?_, (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun _ _ h => by
        rcases h with h | h <;> exact h)⟩
      rw [p2]
      by_cases hall : ∀ c', c + 1 ≤ c' → c' < 9 → fieldN a c' < 16016
      · rw [if_pos hall, if_pos (fun c' h1 h2 => by
          rcases Nat.lt_or_ge c' (c + 1) with h3 | h3
          · rw [show c' = c by omega]; exact hf
          · exact hall c' h3 h2)]
      · rw [if_neg hall, if_neg (fun hh => hall (fun c' h1 h2 => hh c' (by omega) h2))]
    · rw [if_neg hf] at p1
      refine ⟨t1, _, s1, by omega, ?_, r1, f1⟩
      rw [p1, if_neg (fun hh => hf (hh c (le_refl _) hc9))]
theorem admissible_iff (a : BitVec 256) :
    WCT9.admissible a = true ↔ a.toNat / 2 ^ 234 % 2 ^ 14 < 5 ∧ ∀ c', 0 ≤ c' → c' < 9 → fieldN a c' < 16016 := by
  rw [admissible_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun c _ hc => h2 c hc⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun c hc => h2 c (Nat.zero_le _) hc⟩
end blocks
abbrev srchRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x22, .x24, .x25, .x28]
def SrchW (A : Nat) : Prop := A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV
structure SrchPre (b : Nat) (s : MachineState) (rho : Digest) (m : Message) : Prop where
  pc : s.pc = pcOf b
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def SrchPost (b : Nat) (s0 : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt (b + 138) t
  | some (c, N), t => t.pc = pcOf (b + 141) ∧ t.getReg .x5 = 0 ∧ WCT9.admissible N = true ∧ OutAt t NBUF N ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧
      t.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31) ∧ RegsExcept s0 t srchRegs ∧ Frame s0 t SrchW ∧
      c.toNat < 2 ^ 21 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
structure SrchInv (b : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf b
  hi : i ≤ 2 ^ 21
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t srchRegs
  frame : Frame s0 t SrchW
theorem digest_eq (rho : Digest) (m : Message) (c : BitVec 32) :
    SigGolfCandidate.T3.digest rho m c = SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m c) := rfl
section loop
variable {im : Image} {b : Nat} {sk : BitVec 256}
theorem search_loop (h : SearchAt im b) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : SrchPre b s0 rho m) :
    ∀ F i t, i + F = 2 ^ 21 → SrchInv b s0 i t →
      TBSim im sk t (F * 150 + 6) (WCT9.digestSearch rho m i F) (SrchPost b s0) := by
  intro F
  induction F with
  | zero =>
    intro i t hF hI
    obtain ⟨t1, s1, p1, _, _⟩ := sr0_spec h t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, s2, p2, _, _⟩ := sr3_spec h t1 p1
    obtain ⟨t3, s3, hf3, _⟩ := sr138_spec h t2 p2
    exact (TBSim.steps (s1.trans (s2.trans s3)) (TBSim.pure (Q := SrchPost b s0) (a := none) hf3)).mono
      (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t hF hI
    have hi : i < 2 ^ 21 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := sr0_spec h t hI.pc i hI.hi hI.x19
    rw [if_pos hi] at p1
    obtain ⟨u, s2, p2, h16, h24, h10, h11, h12, r2, f2⟩ :=
      sr4_spec h t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u srchRegs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have u19 : u.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), r1.get (by decide), hI.x19]
    have fu : Frame s0 u SrchW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with h | h
      · exact h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have mem : ∀ A, A < 2 ^ 64 → ¬ SrchW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ SrchW A := by
      intro A hA; simp only [SrchW, DIG, NBUF, IDXV] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput, digestInput_length]) h10 (by decide) (by decide)
        h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput, hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : WCT9.digestSearch rho m i (F + 1) =
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if WCT9.admissible output then pure (some (BitVec.ofNat 32 i, output))
          else WCT9.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    have hfe : fetch im u = some (.base .ECALL) := ((codeAt_16 h).fetch u p2).trans rfl
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind hfe h5 hv hq
      (W := 127 + (F * 150 + 6)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput]; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf (b + 17) := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : OutAt (writeHash u a) NBUF a := NAt.writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    have rw' : RegsExcept u (writeHash u a) [] := fun r _ => getReg_writeHash u a r
    obtain ⟨t2, s3, p3, x22_2, r3, f3⟩ := sr17_spec h (writeHash u a) pw a hN
    have hN2 : OutAt t2 NBUF a := fun j hj => by
      rw [f3.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
    have fA : Frame s0 (writeHash u a) SrchW := (fu.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl h)))
    have rA : RegsExcept s0 (writeHash u a) srchRegs := (ru.trans rw').mono (by decide)
    have g19 : (writeHash u a).getReg .x19 = BitVec.ofNat 64 i := by rw [getReg_writeHash, u19]
    by_cases hg : a.toNat / 2 ^ 234 % 2 ^ 14 < 5
    · rw [if_pos hg] at p3
      obtain ⟨t4, k4, s4, hk4, p4, r4, f4⟩ := fields_spec h a 9 0 rfl t2 p3 hN2
      have hN4 : OutAt t4 NBUF a := fun j hj => by
        rw [f4.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN2 j hj
      have r24 : RegsExcept s0 t4 srchRegs := ((rA.trans r3).trans r4).mono (by decide)
      have f24 : Frame s0 t4 SrchW := ((fA.trans f3).trans f4).mono (fun A _ h => by
        rcases h with (h | h) | h
        · exact h
        · exact h.elim
        · exact h.elim)
      have x19_4 : t4.getReg .x19 = BitVec.ofNat 64 i := by
        rw [r4.get (by decide), r3.get (by decide), g19]
      by_cases hall : ∀ c', 0 ≤ c' → c' < 9 → fieldN a c' < 16016
      · have hadm : WCT9.admissible a = true := (admissible_iff a).mpr ⟨hg, hall⟩
        rw [if_pos hall] at p4
        simp only [hadm, ↓reduceIte]
        obtain ⟨t5, s5, p5, x22_5, idx5, r5, f5⟩ := sr130_spec h t4 p4 a
          (by rw [r4.get (by decide)]; exact x22_2)
        refine (TBSim.steps (s3.trans (s4.trans s5)) (TBSim.pure ?_)).mono (by simp [fs] at hk4; omega)
          (fun _ _ h => h)
        refine ⟨p5, by rw [r5.get (by decide), r24.get (by decide), hpre.x5], hadm, ?_, idx5, x22_5,
          (r24.trans r5).mono (by decide), (f24.trans f5).mono (fun A _ h => by
            rcases h with h | h
            · exact h
            · exact Or.inr (Or.inr (Or.inr h))), by rw [hc]; exact hi,
          by rw [hc, r5.get (by decide), x19_4]⟩
        intro j hj; rw [f5.get (by simp only [NBUF]; omega) (by simp only [NBUF, IDXV]; omega)]; exact hN4 j hj
      · have hadm : WCT9.admissible a = false := by
          have := (admissible_iff a).not.mpr (fun hh => hall hh.2); simpa using this
        rw [if_neg hall] at p4
        simp only [hadm, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨t5, s5, p5, x19_5, r5, f5⟩ := sr136_spec h t4 p4 i x19_4
        have hI' : SrchInv b s0 (i + 1) t5 :=
          ⟨p5, by omega, x19_5, (r24.trans r5).mono (by decide),
            (f24.trans f5).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩
        refine (TBSim.steps (s3.trans (s4.trans s5)) (ih (i + 1) t5 (by omega) hI')).mono
          (by simp [fs] at hk4; omega) (fun _ _ h => h)
    · rw [if_neg hg] at p3
      have hadm : WCT9.admissible a = false := by
        have := (admissible_iff a).not.mpr (fun hh => hg hh.1); simpa using this
      simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      have x19_2 : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r3.get (by decide), g19]
      obtain ⟨t5, s5, p5, x19_5, r5, f5⟩ := sr136_spec h t2 p3 i x19_2
      have hI' : SrchInv b s0 (i + 1) t5 :=
        ⟨p5, by omega, x19_5, ((rA.trans r3).trans r5).mono (by decide),
          ((fA.trans f3).trans f5).mono (fun A _ h => by rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim)⟩
      refine (TBSim.steps (s3.trans s5) (ih (i + 1) t5 (by omega) hI')).mono (by omega) (fun _ _ h => h)
theorem search_tbsim (h : SearchAt im b) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : SrchPre b s0 rho m) :
    TBSim im sk s0 (2 ^ 21 * 150 + 6) (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) (SrchPost b s0) :=
  search_loop h hpre (2 ^ 21) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩
end loop
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
def base : Nat := 3164
def seg_0 : List (BitVec 32) := [16777327]
def seg_1 : List (BitVec 32) := [1049235,1049875,115]
def seg_4 : List (BitVec 32) := [0x6003b03,0x7803183,8491411,52547987,5353875]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [35330835,35347219,1049363,2098067,1049747,33854611,23389363,2098835,33986195,23520947,3148179,34183571,23718323,4196883,34216467,23751219,5245587,34249363,23784115,6294803,34413843,23948595,7343891,34545427,24080179,5175,0x84040413,0xffee37,0x600e0e13,65847,0xffc10113,20151,0x4c0e8e93,52279,0x4c0c0c13]
def seg_45 : List (BitVec 32) := [0x6003803,45633939,0x7f1f193,33657363,23224883,8493971,31165363,0x9c0e3d83,67110291,50878227,2586419,25626419,458983]
def seg_58 : List (BitVec 32) := [0x70000613]
def seg_59 : List (BitVec 32) := [115]
def seg_60 : List (BitVec 32) := [0x6803803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
def seg_75 : List (BitVec 32) := [0x72000613]
def seg_76 : List (BitVec 32) := [115]
def seg_77 : List (BitVec 32) := [0x6803803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
def seg_92 : List (BitVec 32) := [0x73000613]
def seg_93 : List (BitVec 32) := [115]
def seg_94 : List (BitVec 32) := [0x6803803,44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
def seg_109 : List (BitVec 32) := [0x74000613]
def seg_110 : List (BitVec 32) := [115]
def seg_111 : List (BitVec 32) := [0x7003803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
def seg_126 : List (BitVec 32) := [0x75000613]
def seg_127 : List (BitVec 32) := [115]
def seg_128 : List (BitVec 32) := [0x7003803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
def seg_143 : List (BitVec 32) := [0x76000613]
def seg_144 : List (BitVec 32) := [115]
def seg_145 : List (BitVec 32) := [0x7003803,44585363,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,49829651,2586419,25626419,458983]
def seg_160 : List (BitVec 32) := [0x77000613]
def seg_161 : List (BitVec 32) := [115]
def seg_162 : List (BitVec 32) := [0x7803803,545171,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,5789459,2586419,25626419,458983]
def seg_177 : List (BitVec 32) := [0x78000613]
def seg_178 : List (BitVec 32) := [115]
def seg_179 : List (BitVec 32) := [0x7803803,22565267,0x7f1f193,33657363,23224883,8493971,31165363,0x40040413,537792019,0x9c0e3d83,67110291,27809555,2586419,25626419,458983]
def seg_194 : List (BitVec 32) := [0x79000613]
def seg_195 : List (BitVec 32) := [115]
def seg_196 : List (BitVec 32) := [4535,0xf0118193,0x70303823,0x71603c23,0x7a003023,0x7a003423,0x7a003823,0x7a003c23,0x70000513,0xc000593,268437011]
def seg_207 : List (BitVec 32) := [115]
def seg_208 : List (BitVec 32) := [6455,0xfff90913,659,0x4092306f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (45, seg_45), (58, seg_58), (59, seg_59), (60, seg_60), (75, seg_75), (76, seg_76), (77, seg_77), (92, seg_92), (93, seg_93), (94, seg_94), (109, seg_109), (110, seg_110), (111, seg_111), (126, seg_126), (127, seg_127), (128, seg_128), (143, seg_143), (144, seg_144), (145, seg_145), (160, seg_160), (161, seg_161), (162, seg_162), (177, seg_177), (178, seg_178), (179, seg_179), (194, seg_194), (195, seg_195), (196, seg_196), (207, seg_207), (208, seg_208)]
def code : List (BitVec 32) := layoutCode layout
theorem layout_ok : layoutOk 0 layout = true := by decide +kernel
theorem window : windowOK base code = true := by decide +kernel
theorem codeAt_region {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf base) code :=
  codeAt_of_window hc (by decide) window
theorem codeAt_0 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 0)) seg_0 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 0) (by kernel_rfl)
theorem codeAt_1 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 1)) seg_1 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 1) (by kernel_rfl)
theorem codeAt_4 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 4)) seg_4 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 2) (by kernel_rfl)
theorem codeAt_9 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 9)) seg_9 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 3) (by kernel_rfl)
theorem codeAt_10 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 10)) seg_10 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 4) (by kernel_rfl)
theorem codeAt_45 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 45)) seg_45 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 5) (by kernel_rfl)
theorem codeAt_58 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 58)) seg_58 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 6) (by kernel_rfl)
theorem codeAt_59 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 59)) seg_59 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 7) (by kernel_rfl)
theorem codeAt_60 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 60)) seg_60 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 8) (by kernel_rfl)
theorem codeAt_75 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 75)) seg_75 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 9) (by kernel_rfl)
theorem codeAt_76 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 76)) seg_76 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 10) (by kernel_rfl)
theorem codeAt_77 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 77)) seg_77 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 11) (by kernel_rfl)
theorem codeAt_92 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 92)) seg_92 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 12) (by kernel_rfl)
theorem codeAt_93 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 93)) seg_93 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 13) (by kernel_rfl)
theorem codeAt_94 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 94)) seg_94 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 14) (by kernel_rfl)
theorem codeAt_109 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 109)) seg_109 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 15) (by kernel_rfl)
theorem codeAt_110 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 110)) seg_110 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 16) (by kernel_rfl)
theorem codeAt_111 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 111)) seg_111 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 17) (by kernel_rfl)
theorem codeAt_126 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 126)) seg_126 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 18) (by kernel_rfl)
theorem codeAt_127 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 127)) seg_127 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 19) (by kernel_rfl)
theorem codeAt_128 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 128)) seg_128 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 20) (by kernel_rfl)
theorem codeAt_143 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 143)) seg_143 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 21) (by kernel_rfl)
theorem codeAt_144 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 144)) seg_144 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 22) (by kernel_rfl)
theorem codeAt_145 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 145)) seg_145 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 23) (by kernel_rfl)
theorem codeAt_160 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 160)) seg_160 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 24) (by kernel_rfl)
theorem codeAt_161 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 161)) seg_161 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 25) (by kernel_rfl)
theorem codeAt_162 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 162)) seg_162 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 26) (by kernel_rfl)
theorem codeAt_177 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 177)) seg_177 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 27) (by kernel_rfl)
theorem codeAt_178 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 178)) seg_178 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 28) (by kernel_rfl)
theorem codeAt_179 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 179)) seg_179 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 29) (by kernel_rfl)
theorem codeAt_194 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 194)) seg_194 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 30) (by kernel_rfl)
theorem codeAt_195 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 195)) seg_195 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 31) (by kernel_rfl)
theorem codeAt_196 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 196)) seg_196 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 32) (by kernel_rfl)
theorem codeAt_207 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 207)) seg_207 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 33) (by kernel_rfl)
theorem codeAt_208 {im : Image} (hc : NewCodeAt im) : CodeAt im (pcOf (base + 208)) seg_208 :=
  codeAt_sublayout (codeAt_region hc) layout_ok (i := 34) (by kernel_rfl)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf (base + 0)) 200
sym_block blk_1 := symRun { noAlias := true } seg_1 (pcOf (base + 1)) 200
sym_block blk_4 := symRun { noAlias := true } seg_4 (pcOf (base + 4)) 200
sym_block blk_9 := symRun { noAlias := true } seg_9 (pcOf (base + 9)) 200
sym_block blk_10 := symRun { noAlias := true } seg_10 (pcOf (base + 10)) 200
sym_block blk_45 := symRun { noAlias := true } seg_45 (pcOf (base + 45)) 200
sym_block blk_58 := symRun { noAlias := true } seg_58 (pcOf (base + 58)) 200
sym_block blk_60 := symRun { noAlias := true } seg_60 (pcOf (base + 60)) 200
sym_block blk_75 := symRun { noAlias := true } seg_75 (pcOf (base + 75)) 200
sym_block blk_77 := symRun { noAlias := true } seg_77 (pcOf (base + 77)) 200
sym_block blk_92 := symRun { noAlias := true } seg_92 (pcOf (base + 92)) 200
sym_block blk_94 := symRun { noAlias := true } seg_94 (pcOf (base + 94)) 200
sym_block blk_109 := symRun { noAlias := true } seg_109 (pcOf (base + 109)) 200
sym_block blk_111 := symRun { noAlias := true } seg_111 (pcOf (base + 111)) 200
sym_block blk_126 := symRun { noAlias := true } seg_126 (pcOf (base + 126)) 200
sym_block blk_128 := symRun { noAlias := true } seg_128 (pcOf (base + 128)) 200
sym_block blk_143 := symRun { noAlias := true } seg_143 (pcOf (base + 143)) 200
sym_block blk_145 := symRun { noAlias := true } seg_145 (pcOf (base + 145)) 200
sym_block blk_160 := symRun { noAlias := true } seg_160 (pcOf (base + 160)) 200
sym_block blk_162 := symRun { noAlias := true } seg_162 (pcOf (base + 162)) 200
sym_block blk_177 := symRun { noAlias := true } seg_177 (pcOf (base + 177)) 200
sym_block blk_179 := symRun { noAlias := true } seg_179 (pcOf (base + 179)) 200
sym_block blk_194 := symRun { noAlias := true } seg_194 (pcOf (base + 194)) 200
sym_block blk_196 := symRun { noAlias := true } seg_196 (pcOf (base + 196)) 200
sym_block blk_208 := symRun { noAlias := true } seg_208 (pcOf (base + 208)) 200
end ClaudeWCT.W9.Machine.Expand.Driver
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
theorem child_bits (a : BitVec 256) (w sh : Nat) (h : sh + 7 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh) &&& 127#64).toNat = a.toNat / 2 ^ (64 * w + sh) % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (127#64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    mod_div_mod _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
theorem field4_bits (a : BitVec 256) (w sh : Nat) (h : sh + 21 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> (sh + 5)) &&& 65532#64).toNat =
      4 * (a.toNat / 2 ^ (64 * w + sh + 7) % 2 ^ 14) := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat, Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (65532#64 : Word).toNat = 65532 from rfl]
  have hm : (65532 : Nat).testBit i = (decide (2 ≤ i) && decide (i < 16)) := by
    rcases Nat.lt_or_ge i 16 with h16 | h16
    · interval_cases i <;> decide
    · have : (65532 : Nat).testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide)
        (Nat.pow_le_pow_right (by decide) h16))
      rw [this]; simp; omega
  rw [hm, Nat.mul_comm 4, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mul_two_pow]
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rcases Nat.lt_or_ge i 2 with h2 | h2
  · simp [show ¬ 2 ≤ i by omega]
  · rcases Nat.lt_or_ge i 16 with h16 | h16
    · simp only [show 2 ≤ i from h2, show i < 16 from h16, decide_true, Bool.and_true, Bool.true_and,
        show i - 2 < 14 by omega, show i + (sh + 5) < 64 by omega]
      rw [show i + (sh + 5) + 64 * w = i - 2 + (64 * w + sh + 7) by omega]
    · simp [show ¬ i < 16 by omega, show ¬ i - 2 < 14 by omega]
theorem not1_eq : (18446744073709551614#64 : Word) = ~~~1#64 := by decide
theorem disp_pc (v : Word) (f : Nat) (hv : v.toNat = 4 * f) (hf : f < 2 ^ 14) :
    v + 50368#64 &&& 18446744073709551614#64 = pcOf (11568 + f) := by
  have : v + 50368#64 = pcOf (11568 + f) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, hv, pcOf, BitVec.toNat_ofNat]
    omega
  rw [this, not1_eq, pcOf_and_not1]
theorem disp_x4 (c : Word) (n index : Nat) (hc : c.toNat = n) (_hn : n < 128) (hidx : index < 2 ^ 31) :
    c <<< 32 ||| BitVec.ofNat 64 index = BitVec.ofNat 64 (index + 2 ^ 32 * n) := by
  have e : c <<< 32 = BitVec.ofNat 64 (n * 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, hc, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [e, ofNat_or_add index n 32 (by omega)]
  congr 1; ring
theorem disp_x23 (c : Word) (n : Nat) (hc : c.toNat = n) (hn : n < 128) :
    c <<< 8 + 17600#64 = BitVec.ofNat 64 (17600 + 256 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, hc, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega
end ClaudeWCT.W9.Machine.Expand
end
