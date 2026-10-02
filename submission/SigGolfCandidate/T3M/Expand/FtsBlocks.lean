import SigGolfCandidate.T3M.Expand.RcBlocks

/-!
# `expand`: block specifications of the FTS coordinate loop (stream E)

`fts_coord` .. `fts_root0` (words 65 .. 214; `s0` coordinate, `s1` index, `s2` the next proof slot, `s3` the
inner counter, `s6` / `s7` / `s8` the open stream segment): the coordinate test, the secret copies to the witness
leaf blocks (`0x860 + 48 (3 s0 + j)`), the call of `recover_child` at level 7 on the bucket (`SEL + 24 s0` row
entry 0 `>> 7`), the four outer folds (slot `s2` to `NODE` and the fold block `s7` at `L` / `R` by the bucket bit,
the node header, the node HASH arguments), the segment close and the root store (`FOREST + slotOff s0`).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (NODE NOUT SEL)

set_option autoImplicit false
set_option maxRecDepth 8192

theorem secB (c j k : Nat) :
    (BitVec.ofNat 64 c <<< ((1#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 c + BitVec.ofNat 64 j) <<<
        ((5#64 : BitVec 64).toNat % 64) +
      (BitVec.ofNat 64 c <<< ((1#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 c + BitVec.ofNat 64 j) <<<
        ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 k = BitVec.ofNat 64 (48 * (3 * c + j) + k) := by
  rw [show ((1#64 : BitVec 64).toNat % 64) = 1 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
    show ((5#64 : BitVec 64).toNat % 64) = 5 from rfl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_shl,
    ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]
  congr 1; ring

section blocks
variable (s : MachineState)

/-- `fts_coord`: after seven coordinates to `fts_done`. -/
theorem f65_spec (hpc : s.pc = pcOf 65) (c : Nat) (hc : c ≤ 7) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 7 ≤ c then pcOf 215 else pcOf 67) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_65 codeAt_65 s hpc (by simp [eblk_65.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_65.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h8,
      BitVec.ofNat_eq_ofNat]
    rw [ex_slt c 7 (by omega) (by omega)]
    by_cases h : 7 ≤ c
    · simp [h, show ¬ c < 7 by omega]
    · simp [h, show c < 7 by omega]
  · ex_regs eblk_65.res
  · intro A _ _; simp [eblk_65.res, rv_simp]

/-- `s3 = 0`. -/
theorem f67_spec (hpc : s.pc = pcOf 67) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 68 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_67 codeAt_67 s hpc (by simp [eblk_67.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_67.res, E.eval]
  · simp [eblk_67.res, rv_simp]
  · ex_regs eblk_67.res
  · intro A _ _; simp [eblk_67.res, rv_simp]

/-- `fts_sec`: after three secrets to `fts_sec_done`. -/
theorem f68_spec (hpc : s.pc = pcOf 68) (j : Nat) (hj : j ≤ 3) (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 3 ≤ j then pcOf 89 else pcOf 70) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_68 codeAt_68 s hpc (by simp [eblk_68.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_68.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h19,
      BitVec.ofNat_eq_ofNat]
    rw [ex_slt j 3 (by omega) (by omega)]
    by_cases h : 3 ≤ j
    · simp [h, show ¬ j < 3 by omega]
    · simp [h, show j < 3 by omega]
  · ex_regs eblk_68.res
  · intro A _ _; simp [eblk_68.res, rv_simp]

/-- Secret `3 s0 + s3` (at `0x7010 + 16 (3 s0 + s3)`) to its witness leaf block (`0x860 + 48 (3 s0 + s3)`). -/
theorem f70_spec (hpc : s.pc = pcOf 70) (c j : Nat) (hc : c < 7) (hj : j < 3)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 19 19 t ∧ t.pc = pcOf 68 ∧
      t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j))) =
        s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j))) ∧
      t.getMem (BitVec.ofNat 64 (0x860 + 48 * (3 * c + j) + 8)) =
        s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j) + 8)) ∧
      t.getReg .x19 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x6, .x7, .x13, .x14, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = 0x860 + 48 * (3 * c + j) ∨ A = 0x860 + 48 * (3 * c + j) + 8) := by
  refine ⟨_, symRun_sound eblk_70 codeAt_70 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_70.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h8, h19, secA,
      secB]
    exact ⟨ex_valid _ (by omega) (by omega), ex_valid _ (by omega) (by omega), ex_valid _ (by omega) (by omega),
      ex_valid _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_70.res, E.eval]
  iterate 2
    · simp only [Result.toState_getMem, eblk_70.res, rv_simp, h8, h19, secA, secB]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; omega) | rfl)
  · simp only [Result.toState_getReg, eblk_70.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_70.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_70.res, rv_simp, h8, h19, secA, secB]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fts_sec_done`: `recover_child` at level 7 on the bucket (row `SEL + 24 s0`, entry 0 `>> 7`), `ra = 99`. -/
theorem f89_spec (hpc : s.pc = pcOf 89) (c g : Nat) (hc : c < 7) (hg : g < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c)
    (hrow : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 0)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 824 ∧ t.getReg .x1 = pcOf 99 ∧
      t.getReg .x10 = BitVec.ofNat 64 7 ∧ t.getReg .x11 = BitVec.ofNat 64 (g / 2 ^ 7) ∧
      RegsExcept s t [.x1, .x10, .x11, .x14, .x28] ∧ Frame s t (fun _ => False) := by
  have ha : BitVec.ofNat 64 c <<< ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 c <<<
      ((3#64 : BitVec 64).toNat % 64) + 132256#64 = BitVec.ofNat 64 (SEL + 24 * c + 8 * 0) := by
    rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, show ((3#64 : BitVec 64).toNat % 64) = 3 from rfl,
      ofNat_shl, ofNat_shl, ofNat_add_ofNat, show (132256#64 : BitVec 64) = BitVec.ofNat 64 132256 from rfl,
      ofNat_add_ofNat]
    congr 1; simp only [SEL]; omega
  refine ⟨_, symRun_sound eblk_89 codeAt_89 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_89.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h8]
    rw [ha]; exact ex_valid _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)
  · simp [Result.toState_pc, eblk_89.res, E.eval]
  · simp [eblk_89.res, rv_simp]
  · simp [eblk_89.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_89.res, rv_simp, h8]
    rw [ha, hrow, show ((7#64 : BitVec 64).toNat % 64) = 7 from rfl, ofNat_shr _ _ hg]
  · ex_regs eblk_89.res
  · intro A _ _; simp [eblk_89.res, rv_simp]

/-- `s3 = 0`. -/
theorem f99_spec (hpc : s.pc = pcOf 99) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 100 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_99 codeAt_99 s hpc (by simp [eblk_99.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_99.res, E.eval]
  · simp [eblk_99.res, rv_simp]
  · ex_regs eblk_99.res
  · intro A _ _; simp [eblk_99.res, rv_simp]

/-- `fts_outer`: after four outer folds to `fts_outer_done`. -/
theorem f100_spec (hpc : s.pc = pcOf 100) (j : Nat) (hj : j ≤ 4) (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 4 ≤ j then pcOf 193 else pcOf 102) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_100 codeAt_100 s hpc (by simp [eblk_100.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_100.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h19,
      BitVec.ofNat_eq_ofNat]
    rw [ex_slt j 4 (by omega) (by omega)]
    by_cases h : 4 ≤ j
    · simp [h, show ¬ j < 4 by omega]
    · simp [h, show j < 4 by omega]
  · ex_regs eblk_100.res
  · intro A _ _; simp [eblk_100.res, rv_simp]

/-- Out of proof slots (`s2 ≥ 115`) fails. -/
theorem f102_spec (hpc : s.pc = pcOf 102) (used : Nat) (hu : used < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 used) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 115 ≤ used then pcOf 354 else pcOf 104) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_102 codeAt_102 s hpc (by simp [eblk_102.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_102.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h18,
      BitVec.ofNat_eq_ofNat]
    rw [ex_slt used 115 hu (by omega)]
    by_cases h : 115 ≤ used
    · simp [h, show ¬ used < 115 by omega]
    · simp [h, show used < 115 by omega]
  · ex_regs eblk_102.res
  · intro A _ _; simp [eblk_102.res, rv_simp]

/-- An outer fold: slot address `a3 = 0x7160 + 16 s2`, `s2 += 1`, `a4` the bucket, then by bit `s3` of the bucket. -/
theorem f104_spec (hpc : s.pc = pcOf 104) (c g used j : Nat) (hc : c < 7) (hg : g < 2 ^ 64) (hu : used < 115)
    (hj : j < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h18 : s.getReg .x18 = BitVec.ofNat 64 used)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j)
    (hrow : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 0)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = (if g / 2 ^ 7 / 2 ^ j % 2 = 0 then pcOf 144 else pcOf 120) ∧
      t.getReg .x13 = BitVec.ofNat 64 (0x7160 + 16 * used) ∧ t.getReg .x18 = BitVec.ofNat 64 (used + 1) ∧
      t.getReg .x14 = BitVec.ofNat 64 (g / 2 ^ 7) ∧
      RegsExcept s t [.x13, .x14, .x18, .x28] ∧ Frame s t (fun _ => False) := by
  have ha : BitVec.ofNat 64 c <<< ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 c <<<
      ((3#64 : BitVec 64).toNat % 64) + 132256#64 = BitVec.ofNat 64 (SEL + 24 * c + 8 * 0) := by
    rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, show ((3#64 : BitVec 64).toNat % 64) = 3 from rfl,
      ofNat_shl, ofNat_shl, ofNat_add_ofNat, show (132256#64 : BitVec 64) = BitVec.ofNat 64 132256 from rfl,
      ofNat_add_ofNat]
    congr 1; simp only [SEL]; omega
  refine ⟨_, symRun_sound eblk_104 codeAt_104 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_104.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h8]
    rw [ha]; exact ex_valid _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)
  · simp only [Result.toState_pc, eblk_104.res, E.eval, CmpOp.eval, BinOp.eval, h8, h19]
    have hlt : g / 2 ^ 7 < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hg
    rw [ha, hrow, show ((7#64 : BitVec 64).toNat % 64) = 7 from rfl, ofNat_shr _ _ hg, ofNat_shr', ofNat_and1,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 64 by omega)]
    by_cases h : g / 2 ^ 7 / 2 ^ j % 2 = 0
    · rw [if_pos h, h]; rfl
    · rw [if_neg h, show g / 2 ^ 7 / 2 ^ j % 2 = 1 by omega]; rfl
  · simp only [Result.toState_getReg, eblk_104.res, rv_simp, h18]
    rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl,
      show (29024#64 : BitVec 64) = BitVec.ofNat 64 29024 from rfl, ofNat_add_ofNat]
    congr 1; ring
  · simp only [Result.toState_getReg, eblk_104.res, rv_simp, h18, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, eblk_104.res, rv_simp, h8]
    rw [ha, hrow, show ((7#64 : BitVec 64).toNat % 64) = 7 from rfl, ofNat_shr _ _ hg]
  · ex_regs eblk_104.res
  · intro A _ _; simp [eblk_104.res, rv_simp]

theorem foldA (ptr cnt : Nat) : BitVec.ofNat 64 cnt <<< ((6#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 cnt <<<
    ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 ptr = BitVec.ofNat 64 (ptr + 80 * cnt) := by
  rw [show ((6#64 : BitVec 64).toNat % 64) = 6 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
    ofNat_shl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]; congr 1; ring

/-- `fts_outer` with bucket bit 1: the slot (at `P`) to `NODE` and to fold block `s7` at `L`, the node `NOUT` to
`NODE + 48`, `s7 += 1`. -/
theorem f120_spec (hpc : s.pc = pcOf 120) (P ptr cnt : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P)
    (hP' : P + 16 ≤ 0x7000 + 5680) (hp8 : ptr % 8 = 0) (hptr : 0xC40 ≤ ptr) (hcnt : cnt < 2 ^ 20)
    (hfit : ptr + 80 * cnt + 24 ≤ 0x3418) (h13 : s.getReg .x13 = BitVec.ofNat 64 P)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr) (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 24 24 t ∧ t.pc = pcOf 167 ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 8)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 16)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (cnt + 1) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨ A = ptr + 80 * cnt + 8 ∨
        A = ptr + 80 * cnt + 16) := by
  refine ⟨_, symRun_sound eblk_120 codeAt_120 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_120.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h13, h22, h23, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat, foldA]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [rv_simp, accessValid_iff, MEMORY_BYTES]; decide)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_120.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_120.res, rv_simp, h13, h22, h23, ofNat_add_ofNat, foldA, NODE, NOUT]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; omega) | rfl)
  · simp only [Result.toState_getReg, eblk_120.res, rv_simp, h23, ofNat_add_ofNat]
  · ex_regs eblk_120.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_120.res, rv_simp, h13, h22, h23, ofNat_add_ofNat, foldA]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- `fts_outer_r` (bucket bit 0): the node `NOUT` to `NODE`, the slot (at `P`) to `NODE + 48` and to fold block
`s7` at `R`, `s7 += 1`. -/
theorem f144_spec (hpc : s.pc = pcOf 144) (P ptr cnt : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P)
    (hP' : P + 16 ≤ 0x7000 + 5680) (hp8 : ptr % 8 = 0) (hptr : 0xC40 ≤ ptr) (hcnt : cnt < 2 ^ 20)
    (hfit : ptr + 80 * cnt + 72 ≤ 0x3418) (h13 : s.getReg .x13 = BitVec.ofNat 64 P)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr) (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 23 23 t ∧ t.pc = pcOf 167 ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 56)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 64)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (cnt + 1) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨ A = ptr + 80 * cnt + 56 ∨
        A = ptr + 80 * cnt + 64) := by
  refine ⟨_, symRun_sound eblk_144 codeAt_144 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_144.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h13, h22, h23, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat, foldA]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [rv_simp, accessValid_iff, MEMORY_BYTES]; decide)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_144.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_144.res, rv_simp, h13, h22, h23, ofNat_add_ofNat, foldA, NODE, NOUT]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; omega) | rfl)
  · simp only [Result.toState_getReg, eblk_144.res, rv_simp, h23, ofNat_add_ofNat]
  · ex_regs eblk_144.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_144.res, rv_simp, h13, h22, h23, ofNat_add_ofNat, foldA]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- `fts_outer_t`: the node header `T10(coord)`, `index | heap << 32` (`heap = 2^(2 - j) + bucket >> (j + 1)`),
the HASH arguments `NODE`, 64, `NOUT`. -/
theorem f167_spec (hpc : s.pc = pcOf 167) (c index j b : Nat) (hc : c < 7) (hi : index < 2 ^ 32) (hj : j < 4)
    (hb : b < 16) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h9 : s.getReg .x9 = BitVec.ofNat 64 index)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (h14 : s.getReg .x14 = BitVec.ofNat 64 b) :
    ∃ t, Steps image s 23 23 t ∧ t.pc = pcOf 190 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (2561 + 65536 * c + 2^32 * index) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (2 ^ (3 - j) + b / 2 ^ (j + 1)) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  refine ⟨_, symRun_sound eblk_167 codeAt_167 s hpc (by simp [eblk_167.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [Result.toState_pc, eblk_167.res, E.eval]
  · simp only [Result.toState_getMem, eblk_167.res, rv_simp, h8, h9, h19, h14, NODE]
    t3n []
    rw [ofNat_or_disjoint' 2561 (c * 65536) 16 (by norm_num) (by omega),
      ofNat_or_disjoint' (2561 + c * 65536) (index * 4294967296) 32 (by omega) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_167.res, rv_simp, h8, h9, h19, h14, NODE]
    t3n []
    rw [show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, ofNat_sub_ofNat 3 j (by omega) (by omega),
      toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (show 3 - j < 64 by omega), Nat.one_mul,
      Nat.mod_eq_of_lt (show j + 1 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show j + 1 < 64 by omega),
      ofNat_shr _ _ (by omega), ofNat_add_ofNat]
  · simp [eblk_167.res, rv_simp]
  · simp [eblk_167.res, rv_simp]
  · simp [eblk_167.res, rv_simp]
  · ex_regs eblk_167.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_167.res, rv_simp]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_190 (hpc : s.pc = pcOf 190) : fetch image s = some (.base .ECALL) :=
  (codeAt_190.fetch s hpc).trans rfl

/-- `s3 += 1`, back to `fts_outer`. -/
theorem f191_spec (hpc : s.pc = pcOf 191) (j : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 100 ∧ t.getReg .x19 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_191 codeAt_191 s hpc (by simp [eblk_191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_191.res, E.eval]
  · simp only [Result.toState_getReg, eblk_191.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_191.res
  · intro A _ _; simp [eblk_191.res, rv_simp]

/-- `fts_outer_done`: close the open segment (header byte `s7 | s8 << 5` at `s6`, `s6 += 8 + 80 s7`), the forest
slot offset `16 s0`, then by `s0 = 0`. -/
theorem f193_spec (hpc : s.pc = pcOf 193) (c ptr cnt par : Nat) (hc : c < 7) (hp8 : ptr % 8 = 0)
    (hp : ptr + 8 ≤ 2 ^ 24) (hcnt : cnt < 16) (hpar : par < 2) (hfit : ptr + 8 + 80 * cnt < 2 ^ 24)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt) (h24 : s.getReg .x24 = BitVec.ofNat 64 par) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = (if c = 0 then pcOf 204 else pcOf 203) ∧
      t.getMem (BitVec.ofNat 64 ptr) =
        replaceByte (s.getMem (BitVec.ofNat 64 ptr)) 0 ((BitVec.ofNat 64 (32 * par + cnt)).truncate 8) ∧
      t.getReg .x22 = BitVec.ofNat 64 (ptr + 80 * cnt + 8) ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * c) ∧
      RegsExcept s t [.x22, .x28, .x30] ∧ Frame s t (fun A => A = ptr) := by
  refine ⟨_, symRun_sound eblk_193 codeAt_193 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_193.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, BitVec.ofNat_eq_ofNat]
    rw [show (0#64 : BitVec 64) = 0 from rfl]; simp only [add_zero]
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  · simp only [Result.toState_pc, eblk_193.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h8,
      BitVec.ofNat_eq_ofNat]
    by_cases h : c = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 c == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq]; intro he; exact h ((ofNat_inj (by omega) (by omega)).mp he)
      rw [this, if_neg h]; rfl
  · simp only [Result.toState_getMem, eblk_193.res, rv_simp, h22, h23, h24]
    t3n []
    rw [ofNat_or_disjoint cnt (par * 32) 5 (by omega) (by omega), show par * 32 + cnt = 32 * par + cnt by ring]
  · simp only [Result.toState_getReg, eblk_193.res, rv_simp, h22, h23]
    t3n []
    congr 1; omega
  · simp only [Result.toState_getReg, eblk_193.res, rv_simp, h8]
    rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]; congr 1; ring
  · ex_regs eblk_193.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_193.res, rv_simp, h22]
    t3n []
    rw [if_neg (by omega)]

/-- Forest slot offset `+ 16` for coordinates `≠ 0`. -/
theorem f203_spec (hpc : s.pc = pcOf 203) (k : Nat) (h28 : s.getReg .x28 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 204 ∧ t.getReg .x28 = BitVec.ofNat 64 (k + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_203 codeAt_203 s hpc (by simp [eblk_203.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_203.res, E.eval]
  · simp only [Result.toState_getReg, eblk_203.res, rv_simp, h28, ofNat_add_ofNat]
  · ex_regs eblk_203.res
  · intro A _ _; simp [eblk_203.res, rv_simp]

/-- `fts_root0`: the coordinate root (`NOUT`) to `FOREST + off`, `s0 += 1`, back to `fts_coord`. -/
theorem f204_spec (hpc : s.pc = pcOf 204) (c off : Nat) (hc : c < 7) (hoff : off + 16 ≤ 128) (hoff8 : off % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 off) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 65 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + off)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (FOREST + off + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getReg .x8 = BitVec.ofNat 64 (c + 1) ∧
      RegsExcept s t [.x6, .x7, .x8, .x28, .x29] ∧ Frame s t (fun A => A = FOREST + off ∨ A = FOREST + off + 8) := by
  refine ⟨_, symRun_sound eblk_204 codeAt_204 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_204.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h28, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [rv_simp, accessValid_iff, MEMORY_BYTES]; decide)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_204.res, E.eval]
  iterate 2
    · simp only [Result.toState_getMem, eblk_204.res, rv_simp, h28, ofNat_add_ofNat, FOREST, NOUT]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; omega) | rfl)
  · simp only [Result.toState_getReg, eblk_204.res, rv_simp, h8, ofNat_add_ofNat]
  · ex_regs eblk_204.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_204.res, rv_simp, h28, ofNat_add_ofNat]
    t3n []
    simp only [FOREST] at hn
    rw [if_neg (by omega), if_neg (by omega)]

end blocks

end SigGolfCandidate.T3M.Expand
