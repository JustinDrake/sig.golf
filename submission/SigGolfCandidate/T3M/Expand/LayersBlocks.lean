import SigGolfCandidate.T3M.Expand.Layer

/-!
# `expand`: block specifications of the layer driver (stream E)

`layer_3` .. `layer_0` (words 249 .. 341): the layer's constants (`s0` lay, `a5` H, `s10` N, `s11` N4, `a7` target),
leaf and tree from the index at `IDXV`, `jal counter_search`; the counter into the witness header, the layer's
signature piece `a6`, the witness chain / Merkle blocks `s7` / `s8`, `jal recover_layer`. `compare` (342 .. 350) and
`accept` (351 .. 353).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)

set_option autoImplicit false
set_option maxRecDepth 8192

/-- The hypertree index `N mod 2^31` (written by `ds_done`). -/
abbrev IDXV : Nat := 0x20550

theorem shr_and_mask (a k m : Nat) (ha : a < 2 ^ 64) (hm : m ≤ 64) :
    BitVec.ofNat 64 a >>> k &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a / 2 ^ k % 2 ^ m) := by
  rw [ofNat_shr _ _ ha, ofNat_and_mask _ _ hm]

theorem replaceWord32_lo (x c : Nat) (hc : c < 2 ^ 32) :
    replaceWord32 (BitVec.ofNat 64 x) 0 ((BitVec.ofNat 64 c).truncate 32) =
      BitVec.ofNat 64 (2 ^ 32 * (x / 2 ^ 32) + c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, Nat.zero_mul, BitVec.shiftLeft_zero, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, hi,
    decide_true, Bool.true_and, Nat.testBit_two_pow_mul_add _ hc]
  by_cases h : i < 32
  · have : (0xFFFFFFFF : Nat).testBit i = true := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp [h]
    simp [this, h]
  · have h1 : (0xFFFFFFFF : Nat).testBit i = false := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
    have h3 : c.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h3, h]
    rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, Nat.testBit_div_two_pow, show i - 32 + 32 = i by omega]

theorem replaceWord32_hi (x c : Nat) (hx : x < 2 ^ 32) :
    replaceWord32 (BitVec.ofNat 64 x) 1 ((BitVec.ofNat 64 c).truncate 32) =
      BitVec.ofNat 64 (2 ^ 32 * c + x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, Nat.one_mul, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, hi,
    decide_true, Bool.true_and, Nat.testBit_two_pow_mul_add _ hx, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 32
  · simp [h]
  · have hx' : x.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h1 : (0xFFFFFFFF : Nat).testBit (i - 32) = true := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
    simp [h, hx', h1, show i - 32 < 64 by omega, show i - 32 < 32 by omega]

section blocks
variable (s : MachineState)

/-- `layer_3`: the layer constants, leaf `index / 2^0 mod 2^6`, tree `index >> 6`, `jal counter_search`. -/
theorem l249_spec (hpc : s.pc = pcOf 249) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 262 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 195 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 0 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 6) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_249 codeAt_249 s hpc (by simp [eblk_249.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_249.res, E.eval]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp [eblk_249.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_249.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_249.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_249.res
  · intro A _ _; simp [eblk_249.res, rv_simp]

/-- `layer_2`: the layer constants, leaf `index / 2^6 mod 2^6`, tree `index >> 12`, `jal counter_search`. -/
theorem l272_spec (hpc : s.pc = pcOf 272) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 285 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 195 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 6 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 12) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_272 codeAt_272 s hpc (by simp [eblk_272.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_272.res, E.eval]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp [eblk_272.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_272.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_272.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_272.res
  · intro A _ _; simp [eblk_272.res, rv_simp]

/-- `layer_1`: the layer constants, leaf `index / 2^12 mod 2^7`, tree `index >> 19`, `jal counter_search`. -/
theorem l295_spec (hpc : s.pc = pcOf 295) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 308 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 195 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 12 % 2 ^ 7) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_295 codeAt_295 s hpc (by simp [eblk_295.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_295.res, E.eval]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [show (127#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_295.res
  · intro A _ _; simp [eblk_295.res, rv_simp]

/-- `layer_0`: the layer constants, leaf `index / 2^19 mod 2^12`, tree `index >> 31`, `jal counter_search`. -/
theorem l318_spec (hpc : s.pc = pcOf 318) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 332 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 12 ∧
      t.getReg .x26 = BitVec.ofNat 64 58 ∧ t.getReg .x27 = BitVec.ofNat 64 49 ∧
      t.getReg .x17 = BitVec.ofNat 64 126 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 2 ^ 12) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 31) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_318 codeAt_318 s hpc (by simp [eblk_318.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_318.res, E.eval]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [show (4095#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 12 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_318.res
  · intro A _ _; simp [eblk_318.res, rv_simp]

/-- After `counter_search`: the counter into the witness header (dword `0x820`, half 0), `a6 = 0x8350`,
`s7 = 0x6a58`, `s8 = 0x5f98`, `jal recover_layer`. -/
theorem l262_spec (hpc : s.pc = pcOf 262) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 0x820) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x820)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x8350 ∧ t.getReg .x23 = BitVec.ofNat 64 0x6a58 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x5f98 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x820) := by
  refine ⟨_, symRun_sound eblk_262 codeAt_262 s hpc (by simp [eblk_262.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_262.res, E.eval]
  · simp [eblk_262.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_262.res]
    t3n [h19]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · ex_regs eblk_262.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_262.res]
    t3n []
    rw [if_neg (by omega)]

/-- After `counter_search`: the counter into the witness header (dword `0x818`, half 1), `a6 = 0x8040`,
`s7 = 0x5e18`, `s8 = 0x5358`, `jal recover_layer`. -/
theorem l285_spec (hpc : s.pc = pcOf 285) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 295 ∧
      t.getMem (BitVec.ofNat 64 0x818) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x818)) 1 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x8040 ∧ t.getReg .x23 = BitVec.ofNat 64 0x5e18 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x5358 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x818) := by
  refine ⟨_, symRun_sound eblk_285 codeAt_285 s hpc (by simp [eblk_285.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_285.res, E.eval]
  · simp [eblk_285.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_285.res]
    t3n [h19]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · ex_regs eblk_285.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_285.res]
    t3n []
    rw [if_neg (by omega)]

/-- After `counter_search`: the counter into the witness header (dword `0x818`, half 0), `a6 = 0x7d20`,
`s7 = 0x51d8`, `s8 = 0x4718`, `jal recover_layer`. -/
theorem l308_spec (hpc : s.pc = pcOf 308) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 318 ∧
      t.getMem (BitVec.ofNat 64 0x818) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x818)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7d20 ∧ t.getReg .x23 = BitVec.ofNat 64 0x51d8 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x4718 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x818) := by
  refine ⟨_, symRun_sound eblk_308 codeAt_308 s hpc (by simp [eblk_308.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_308.res, E.eval]
  · simp [eblk_308.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_308.res]
    t3n [h19]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · ex_regs eblk_308.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_308.res]
    t3n []
    rw [if_neg (by omega)]

/-- After `counter_search`: the counter into the witness header (dword `0x810`, half 1), `a6 = 0x78c0`,
`s7 = 0x4558`, `s8 = 0x36d8`, `jal recover_layer`. -/
theorem l332_spec (hpc : s.pc = pcOf 332) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 342 ∧
      t.getMem (BitVec.ofNat 64 0x810) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x810)) 1 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x78c0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x4558 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x36d8 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x810) := by
  refine ⟨_, symRun_sound eblk_332 codeAt_332 s hpc (by simp [eblk_332.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_332.res, E.eval]
  · simp [eblk_332.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_332.res]
    t3n [h19]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · ex_regs eblk_332.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_332.res]
    t3n []
    rw [if_neg (by omega)]


/-- `compare`, first doubleword: the root (`ENC`) against the public key (`0xA0`). -/
theorem c342_spec (hpc : s.pc = pcOf 342) :
    ∃ t, Steps image s 6 6 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 0xA0) then pcOf 348 else pcOf 354) ∧
      t.getReg .x28 = BitVec.ofNat 64 ENC ∧ t.getReg .x29 = BitVec.ofNat 64 0xA0 ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_342 codeAt_342 s hpc (by simp [eblk_342.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_342.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC]
    split_ifs with h1 h2 h2 <;> simp_all
  · simp [eblk_342.res, rv_simp]
  · simp [eblk_342.res, rv_simp]
  · ex_regs eblk_342.res
  · intro A _ _; simp [eblk_342.res, rv_simp]

/-- `compare`, second doubleword. -/
theorem c348_spec (hpc : s.pc = pcOf 348) (h28 : s.getReg .x28 = BitVec.ofNat 64 ENC)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 0xA0) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 0xA8) then pcOf 351 else pcOf 354) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_348 codeAt_348 s hpc
    (by simp [eblk_348.res, rv_simp, accessValid_iff, MEMORY_BYTES, h28, h29, ENC]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_348.res, E.eval, CmpOp.eval, rebase, rv_simp, ENC, h28, h29]
    split_ifs with h1 h2 h2 <;> simp_all
  · ex_regs eblk_348.res
  · intro A _ _; simp [eblk_348.res, rv_simp]

/-- `accept`: `t0 = 1`, `a0 = 0`, at the `HALT` `ECALL`. -/
theorem c351_spec (hpc : s.pc = pcOf 351) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 353 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 0 ∧ fetch image t = some (.base .ECALL) ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_351 codeAt_351 s hpc (by simp [eblk_351.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_351.res, E.eval]
  · simp [eblk_351.res, rv_simp]
  · simp [eblk_351.res, rv_simp]
  · rw [codeAt_353.fetch _ (by simp [Result.toState_pc, eblk_351.res, E.eval])]; rfl
  · ex_regs eblk_351.res
  · intro A _ _; simp [eblk_351.res, rv_simp]

end blocks

/-! ## The layer table -/

/-- Entry word of the driver block of layer `lay`. -/
def lE (lay : Layer) : Nat := ![318, 295, 272, 249] lay
/-- Steps of the entry block. -/
def lK (lay : Layer) : Nat := ![14, 13, 13, 13] lay
/-- Return word after `counter_search`. -/
def lR1 (lay : Layer) : Nat := ![332, 308, 285, 262] lay
/-- Return word after `recover_layer` (the next layer's entry, or `compare`). -/
def lR2 (lay : Layer) : Nat := ![342, 318, 295, 272] lay
/-- The witness header doubleword and half of the layer's counter. -/
def lD (lay : Layer) : Nat := ![0x810, 0x818, 0x818, 0x820] lay
def lk (lay : Layer) : Nat := ![1, 0, 1, 0] lay
/-- The layer's signature piece, witness chain block of chain 0, witness Merkle block of level 0. -/
def lP (lay : Layer) : Nat := ![0x78c0, 0x7d20, 0x8040, 0x8350] lay
def lWC (lay : Layer) : Nat := ![0x4558, 0x51D8, 0x5E18, 0x6A58] lay
def lWM (lay : Layer) : Nat := ![0x36D8, 0x4718, 0x5358, 0x5F98] lay

theorem route_fst (index : Nat) (lay : Layer) :
    (route index lay).1 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay) % 2 ^ height lay := rfl

theorem route_snd (index : Nat) (lay : Layer) :
    (route index lay).2 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay + height lay) := rfl

/-- **The entry block of layer `lay`**, uniformly. -/
theorem lentry_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lE lay)) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps image s (lK lay) (lK lay) t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf (lR1 lay) ∧
      t.getReg .x8 = BitVec.ofNat 64 lay.val ∧ t.getReg .x15 = BitVec.ofNat 64 (height lay) ∧
      t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) ∧ t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) ∧
      t.getReg .x17 = BitVec.ofNat 64 (target lay) ∧
      t.getReg .x18 = BitVec.ofNat 64 (route index lay).1 ∧ t.getReg .x9 = BitVec.ofNat 64 (route index lay).2 ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  rw [route_fst, route_snd]
  fin_cases lay
  · exact l318_spec s hpc index hi hidx
  · exact l295_spec s hpc index hi hidx
  · exact l272_spec s hpc index hi hidx
  · exact l249_spec s hpc index hi hidx

/-- **The block after `counter_search` of layer `lay`**, uniformly. -/
theorem lpost_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lR1 lay)) (c : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf (lR2 lay) ∧
      t.getMem (BitVec.ofNat 64 (lD lay)) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 (lP lay) ∧ t.getReg .x23 = BitVec.ofNat 64 (lWC lay) ∧
      t.getReg .x24 = BitVec.ofNat 64 (lWM lay) ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = lD lay) := by
  fin_cases lay
  · exact l332_spec s hpc c h19
  · exact l308_spec s hpc c h19
  · exact l285_spec s hpc c h19
  · exact l262_spec s hpc c h19

end SigGolfCandidate.T3M.Expand
