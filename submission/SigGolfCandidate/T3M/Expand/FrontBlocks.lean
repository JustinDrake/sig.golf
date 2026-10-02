import SigGolfCandidate.T3M.Expand.LayersBlocks

/-!
# `expand`: block specifications of `start`, `ds_done`, `zt_loop`, `zt_done` (stream E)

* `start` (0..29): rho (signature bytes 0..16 at `0x7000`) to the witness (`0x800`) and the digest block (`DIG`), the
  message (`0x40`) to `DIG + 32`, `I = 0`;
* `ds_done` (49..64): the index `N mod 2^31` to `s1` and `IDXV`, the digest counter to the witness (`0x810`), the
  stack pointer, `used = 0`, the stream pointer `0xC40`, `coord = 0`;
* `zt_loop` (215..227): the canonical tail (proof slots `used .. 123` zero);
* `zt_done` (228..248): the forest pk HASH (`FOREST`, 128 bytes, into `FOUT`), copied to `ENC`.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)

set_option autoImplicit false
set_option maxRecDepth 8192

/-- The FTS leaf block `0^16 | T9 | secret | 0^16`. -/
abbrev FLEAF : Nat := 0x202C0
/-- The forest block `root0 | T11 | root1 .. root6`. -/
abbrev FOREST : Nat := 0x20320
/-- The forest pk output. -/
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

/-- `start`: rho to the witness and the digest block, the message to the digest block, `I = 0`. -/
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

/-- `ds_done`: the index `N mod 2^31` (from `NBUF`) to `s1` and `IDXV`, the counter to the witness header (`0x810`),
`sp = 0x22000`, `s2 = 0`, `s6 = 0xC40`, `s0 = 0`. -/
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

/-- `fts_done`: `a3 = used`. -/
theorem s215_spec (hpc : s.pc = pcOf 215) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = s.getReg .x18 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_215 codeAt_215 s hpc (by simp [eblk_215.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_215.res, E.eval]
  · simp [eblk_215.res, rv_simp]
  · ex_regs eblk_215.res
  · intro A _ _; simp [eblk_215.res, rv_simp]

/-- `zt_loop`: done at slot 121. -/
theorem s216_spec (hpc : s.pc = pcOf 216) (j : Nat) (hj : j ≤ 121) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 121 ≤ j then pcOf 228 else pcOf 218) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_216 codeAt_216 s hpc (by simp [eblk_216.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_216.res, E.eval, CmpOp.eval, rebase, rv_simp, h13]
    rw [ex_slt j 121 (by omega) (by omega)]
    by_cases h : 121 ≤ j
    · simp [h, show ¬ j < 121 by omega]
    · simp [h, show j < 121 by omega]
  · ex_regs eblk_216.res
  · intro A _ _; simp [eblk_216.res, rv_simp]

theorem slot_addr (j : Nat) :
    BitVec.ofNat 64 j <<< ((4#64 : BitVec 64).toNat % 64) + 29024#64 = BitVec.ofNat 64 (0x7160 + 16 * j) := by
  rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- `zt_loop`, low doubleword of slot `j`. -/
theorem s218_spec (hpc : s.pc = pcOf 218) (j : Nat) (hj : j < 121) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
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

/-- `zt_loop`, high doubleword of slot `j`. -/
theorem s224_spec (hpc : s.pc = pcOf 224) (j : Nat) (hj : j < 121)
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

/-- `zt_loop`: next slot. -/
theorem s226_spec (hpc : s.pc = pcOf 226) (j : Nat) (hj : j < 121) (h13 : s.getReg .x13 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 216 ∧ t.getReg .x13 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_226 codeAt_226 s hpc (by simp [eblk_226.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_226.res, E.eval]
  · simp only [Result.toState_getReg, eblk_226.res, rv_simp, h13, ofNat_add_ofNat]
  · ex_regs eblk_226.res
  · intro A _ _; simp [eblk_226.res, rv_simp]

/-- `zt_done`: the forest header (`T11`, index), the HASH arguments `FOREST`, 128, `FOUT`. -/
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

/-- `zt_done`, after the HASH: the forest pk (`FOUT`) to `ENC`. -/
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
