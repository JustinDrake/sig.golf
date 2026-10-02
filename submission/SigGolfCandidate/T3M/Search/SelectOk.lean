import SigGolfCandidate.T3M.Search.Blocks
import SigGolfCandidate.T3M.Search.Arith

/-!
# `select_ok` (stream E; shared by sign at base 543 and expand at base 354)

`select_ok` (kernel offsets 3..102): for each coordinate `c < 7` extract the 25-bit window of `N` at
bit `31 + 25c` (two doublewords at `NBUF`), split it into bucket and three leaves, sort the leaves
(three compare-exchanges), reject a repeated leaf, accumulate `4 + bitlen (a ⊕ b) + bitlen (b ⊕ c)`
onto `21`, store the row `128 bucket + leaf` (three doublewords at `SEL + 24c`); finally accept iff the
total is `< 116`. Result in `a3` (`x13`), return through `ra`.
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section blocks
variable {image : Image} {b : Nat}

/-- Entry: `s5 = 21`, `s4 = 0`, `s9 = SEL`. -/
theorem so3_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 7) ∧ t.getReg .x21 = BitVec.ofNat 64 21 ∧
      t.getReg .x20 = BitVec.ofNat 64 0 ∧ t.getReg .x25 = BitVec.ofNat 64 SEL ∧
      RegsExcept s t [.x20, .x21, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_3 hK.2) (codeAt_k_3 hK) s hpc (by simp [st_3, blk354_3.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_3, blk354_3.res, E.eval]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_3, blk354_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_3, blk354_3.res, rv_simp]

/-- Loop head: `s4 < 7` continues with the coordinate, else the final check. -/
theorem so7_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 7)) (c : Nat)
    (hc : c ≤ 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c < 7 then pcOf (b + 9) else pcOf (b + 97)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_7 hK.2) (codeAt_k_7 hK) s hpc (by simp [st_7, blk354_7.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_7, rebase, blk354_7.res, E.eval, CmpOp.eval, h20]
    rw [ofNat_slt c 7 (by omega) (by omega)]
    by_cases h : c < 7 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_7, blk354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_7, blk354_7.res, rv_simp]

/-- The window of coordinate `c` into `t3`. -/
theorem so9_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 9))
    (c : Nat) (hc : c < 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 22 22 t ∧ t.pc = pcOf (b + 31) ∧
      t.getReg .x28 = BitVec.ofNat 64 (selWin N c) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_9 hK.2) (codeAt_k_9 hK) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · interval_cases c <;> simp [st_9, blk354_9.res, rv_simp, h20, accessValid_iff, MEMORY_BYTES]
  · simp [pcE_9, blk354_9.res, E.eval]
  · simp only [Result.toState_getReg, st_9, blk354_9.res]
    interval_cases c <;> simpa [rv_simp, h20] using window_mem s N hN _ hc
  · intro r hr; simp at hr; cases r <;> simp_all [st_9, blk354_9.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_9, blk354_9.res, rv_simp]

/-- Fields of the window `u`: bucket row base `t1 = 128 (u mod 16)`, leaves `s6, s7, s8`; first
compare-exchange test `s7 ≥ s6`. -/
theorem so31_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if u / 16 % 128 ≤ u / 2 ^ 11 % 128 then pcOf (b + 43) else pcOf (b + 40)) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 (u / 16 % 128) ∧
      t.getReg .x23 = BitVec.ofNat 64 (u / 2 ^ 11 % 128) ∧
      t.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  have hu' : u < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_31 hK.2) (codeAt_k_31 hK) s hpc (by simp [st_31, blk354_31.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_31, rebase, blk354_31.res, E.eval, CmpOp.eval, h28, BinOp.eval,
      ofNat_shr _ _ hu', ofNat_and127]
    rw [ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : u / 16 % 128 ≤ u / 2 ^ 11 % 128 <;> simp [h]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · intro r hr; simp at hr; cases r <;> simp_all [st_31, blk354_31.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_31, blk354_31.res, rv_simp]


/-- Exchange `s6`, `s7`. -/
theorem so40_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 40)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 43) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_40 hK.2) (codeAt_k_40 hK) s hpc (by simp [st_40, blk354_40.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_40, blk354_40.res, E.eval]
  · simp [st_40, blk354_40.res, rv_simp]
  · simp [st_40, blk354_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_40, blk354_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_40, blk354_40.res, rv_simp]

/-- `bge s8, s7`. -/
theorem so43_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 43)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x24 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 47) else pcOf (b + 44)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_43 hK.2) (codeAt_k_43 hK) s hpc (by simp [st_43, blk354_43.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_43, rebase, blk354_43.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_43, blk354_43.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_43, blk354_43.res, rv_simp]

/-- Exchange `s7`, `s8`. -/
theorem so44_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 44)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 47) ∧ t.getReg .x23 = s.getReg .x24 ∧
      t.getReg .x24 = s.getReg .x23 ∧ RegsExcept s t [.x7, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_44 hK.2) (codeAt_k_44 hK) s hpc (by simp [st_44, blk354_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, blk354_44.res, E.eval]
  · simp [st_44, blk354_44.res, rv_simp]
  · simp [st_44, blk354_44.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk354_44.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_44, blk354_44.res, rv_simp]

/-- `bge s7, s6`. -/
theorem so47_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 47)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x23 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x22 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 51) else pcOf (b + 48)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_47 hK.2) (codeAt_k_47 hK) s hpc (by simp [st_47, blk354_47.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_47, rebase, blk354_47.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_47, blk354_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_47, blk354_47.res, rv_simp]

/-- Exchange `s6`, `s7`. -/
theorem so48_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 48)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 51) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_48 hK.2) (codeAt_k_48 hK) s hpc (by simp [st_48, blk354_48.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_48, blk354_48.res, E.eval]
  · simp [st_48, blk354_48.res, rv_simp]
  · simp [st_48, blk354_48.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_48, blk354_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_48, blk354_48.res, rv_simp]

/-- `beq s6, s7 → sel_fail`. -/
theorem so51_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 51)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x22 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 52)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_51 hK.2) (codeAt_k_51 hK) s hpc (by simp [st_51, blk354_51.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_51, rebase, blk354_51.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_51, blk354_51.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_51, blk354_51.res, rv_simp]

/-- `beq s7, s8 → sel_fail`. -/
theorem so52_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 52)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x23 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x24 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 53)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_52 hK.2) (codeAt_k_52 hK) s hpc (by simp [st_52, blk354_52.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_52, rebase, blk354_52.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_52, blk354_52.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_52, blk354_52.res, rv_simp]

/-- The row cost `4 + bitlen (a ⊕ y) + bitlen (y ⊕ z)` onto `s5`, the row `R + a, R + y, R + z` at
`s9`, next row, next coordinate. -/
theorem so53_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 53))
    (a y z R S P c : Nat) (ha : a < 256) (hy : y < 256) (hz : z < 256)
    (hP : P + 24 ≤ 2 ^ 24) (hP8 : P % 8 = 0)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 a) (h23 : s.getReg .x23 = BitVec.ofNat 64 y)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 z) (h6 : s.getReg .x6 = BitVec.ofNat 64 R)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 S) (h25 : s.getReg .x25 = BitVec.ofNat 64 P)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 44 44 t ∧ t.pc = pcOf (b + 7) ∧
      t.getReg .x21 = BitVec.ofNat 64 (S + ((a ^^^ y).log2 + 1) + ((y ^^^ z).log2 + 1) + 4) ∧
      t.getMem (BitVec.ofNat 64 P) = BitVec.ofNat 64 (R + a) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = BitVec.ofNat 64 (R + y) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = BitVec.ofNat 64 (R + z) ∧
      t.getReg .x25 = BitVec.ofNat 64 (P + 24) ∧ t.getReg .x20 = BitVec.ofNat 64 (c + 1) ∧
      RegsExcept s t [.x7, .x20, .x21, .x25, .x28, .x29] ∧
      Frame s t (fun A => A = P ∨ A = P + 8 ∨ A = P + 16) := by
  have hay : a ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) ha hy
  have hyz : y ^^^ z < 256 := Nat.xor_lt_two_pow (n := 8) hy hz
  refine ⟨_, symRun_sound (run_53 hK.2) (codeAt_k_53 hK) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st_53, blk354_53.res, rv_simp, h25, accessValid_iff, MEMORY_BYTES]; omega
  · simp [pcE_53, blk354_53.res, E.eval]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    simp only [rv_simp, h22, h23, h24, h21, ofNat_xor a y (by omega) (by omega),
      ofNat_xor y z (by omega) (by omega)]
    rw [bitlen_word _ hay, bitlen_word _ hyz]
    t3n []
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h22, h6]
    all_goals (split_ifs <;> first | omega | rfl)
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h23, h6]
    split_ifs <;> first | omega | rfl
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h24, h6]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h25]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_53, blk354_53.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `sel_check`: accept iff `s5 < 116`. -/
theorem so97_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 97)) (S : Nat)
    (hS : S < 2 ^ 63) (h21 : s.getReg .x21 = BitVec.ofNat 64 S) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 116 ≤ S then pcOf (b + 101) else pcOf (b + 99)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_97 hK.2) (codeAt_k_97 hK) s hpc (by simp [st_97, blk354_97.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_97, rebase, blk354_97.res, E.eval, CmpOp.eval, h21]
    rw [ofNat_slt _ _ hS (by omega)]
    by_cases h : 116 ≤ S
    · simp [h, show ¬ S < 116 by omega]
    · simp [h, show S < 116 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_97, blk354_97.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_97, blk354_97.res, rv_simp]

/-- Accept: `a3 = 1`, return. -/
theorem so99_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 99)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_99 hK.2) (codeAt_k_99 hK) s hpc (by simp [st_99, blk354_99.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_99, blk354_99.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_99, blk354_99.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_99, blk354_99.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_99, blk354_99.res, rv_simp]

/-- Reject: `a3 = 0`, return. -/
theorem so101_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 101)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_101 hK.2) (codeAt_k_101 hK) s hpc (by simp [st_101, blk354_101.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_101, blk354_101.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_101, blk354_101.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_101, blk354_101.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_101, blk354_101.res, rv_simp]

end blocks


/-! ## The sorting network -/

section sort
variable {image : Image} {b : Nat}

/-- A taken-or-skipped compare-exchange: the pair `(rlo, rhi)` becomes `(min, max)`. -/
theorem exch {rlo rhi : Reg} {o nxt : Nat}
    (hsw : ∀ s : MachineState, s.pc = pcOf (b + o) → ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = s.getReg rhi ∧ t.getReg rhi = s.getReg rlo ∧ RegsExcept s t [.x7, rlo, rhi] ∧
      Frame s t (fun _ => False))
    (s : MachineState) (x y : Nat)
    (hpc : s.pc = if x ≤ y then pcOf (b + nxt) else pcOf (b + o))
    (hlo : s.getReg rlo = BitVec.ofNat 64 x) (hhi : s.getReg rhi = BitVec.ofNat 64 y) :
    ∃ k t, Steps image s k k t ∧ k ≤ 3 ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = BitVec.ofNat 64 (min x y) ∧ t.getReg rhi = BitVec.ofNat 64 (max x y) ∧
      RegsExcept s t [.x7, rlo, rhi] ∧ Frame s t (fun _ => False) := by
  by_cases h : x ≤ y
  · rw [if_pos h] at hpc
    refine ⟨0, s, Steps.refl s, by omega, hpc, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [hlo, Nat.min_eq_left h]
    · rw [hhi, Nat.max_eq_right h]
  · rw [if_neg h] at hpc
    obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := hsw s hpc
    refine ⟨3, t, h1, le_refl _, h2, ?_, ?_, h5, h6⟩
    · rw [h3, hhi, Nat.min_eq_right (by omega)]
    · rw [h4, hlo, Nat.max_eq_left (by omega)]

/-- From the window `u` in `t3` (offset 31) to offset 51: bucket base in `t1`, the sorted leaves in
`s6 ≤ s7 ≤ s8` (`sort3`), at most 20 cycles. -/
theorem sort_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ k t, Steps image s k k t ∧ k ≤ 20 ∧ t.pc = pcOf (b + 51) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 0 0) ∧
      t.getReg .x23 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 1 0) ∧
      t.getReg .x24 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 2 0) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, h6, h22, h23, h24, r1, f1⟩ := so31_spec hK s hpc u hu h28
  obtain ⟨k2, t2, s2, k2le, p2, a22, a23, r2, f2⟩ :=
    exch (so40_spec hK) t1 _ _ p1 h22 h23
  have b24 : t2.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) := by
    rw [r2.get (by decide), h24]
  obtain ⟨t3, s3, p3, r3, f3⟩ := so43_spec hK t2 p2 _ _ (by omega) (by omega) b24 a23
  obtain ⟨k4, t4, s4, k4le, p4, a23', a24, r4, f4⟩ :=
    exch (so44_spec hK) t3 (max (u / 16 % 128) (u / 2 ^ 11 % 128))
      (u / 2 ^ 18 % 128) p3 (by rw [r3.get (by decide), a23]) (by rw [r3.get (by decide), b24])
  have b22 : t4.getReg .x22 = BitVec.ofNat 64 (min (u / 16 % 128) (u / 2 ^ 11 % 128)) := by
    rw [r4.get (by decide), r3.get (by decide), a22]
  obtain ⟨t5, s5, p5, r5, f5⟩ := so47_spec hK t4 p4 _ _ (by omega) (by omega) a23' b22
  obtain ⟨k6, t6, s6, k6le, p6, a22', a23'', r6, f6⟩ :=
    exch (so48_spec hK) t5 _ _ p5
      (by rw [r5.get (by decide), b22]) (by rw [r5.get (by decide), a23'])
  refine ⟨9 + k2 + 1 + k4 + 1 + k6, t6, ?_, by omega, p6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
    exact this
  · rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide),
      r2.get (by decide), h6]
  · rw [a22']; rfl
  · rw [a23'']; rfl
  · rw [r6.get (by decide), r5.get (by decide), a24]; rfl
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide))
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)

end sort

/-! ## The coordinate loop -/

/-- Row `c` of the selection table: three doublewords `128 bucket + leaf` at `SEL + 24 c`. -/
def RowAt (t : MachineState) (N : BitVec 256) (c : Nat) : Prop :=
  ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
    BitVec.ofNat 64 (selBucket N c * 128 + (selRow N c).getD j 0)

/-- The selection table (21 doublewords at `SEL`): the only memory `select_ok` writes. -/
def SelW (A : Nat) : Prop := SEL ≤ A ∧ A < SEL + 168

/-- The registers `select_ok` may change. -/
abbrev selRegs : List Reg := [.x6, .x7, .x13, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29]

theorem NAt.frame {s t : MachineState} {N : BitVec 256} (h : NAt s N) (hf : Frame s t SelW) : NAt t N := by
  intro j hj
  rw [hf.get (by simp only [NBUF]; omega) (by simp only [SelW, SEL, NBUF]; omega)]
  exact h j hj

section loop
variable {image : Image} {b : Nat}

/-- The loop invariant at `sel_loop` after `c` coordinates. -/
structure SelInv (b : Nat) (s0 : MachineState) (N : BitVec 256) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 7)
  x20 : t.getReg .x20 = BitVec.ofNat 64 c
  x21 : t.getReg .x21 = BitVec.ofNat 64 (21 + selCost N c)
  x25 : t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c)
  ok : ∀ c' < c, rowOk (selRow N c') = true
  rows : ∀ c' < c, RowAt t N c'
  regs : RegsExcept s0 t selRegs
  frame : Frame s0 t SelW

/-- Close a frame-weakening goal `∀ A, (W ∨ False ∨ …) → SelW A`. -/
macro "sel_frame" : tactic =>
  `(tactic| (intro A _ hA; (try simp only [or_false, false_or, or_self] at hA); first | exact hA | (simp only [SelW, SEL] at *; omega)))

theorem regs_mono {s t : MachineState} {l : List Reg} (h : RegsExcept s t l)
    (hl : l.all (fun r => decide (r ∈ selRegs)) = true) : RegsExcept s t selRegs :=
  h.mono (fun r hr => by simpa using List.all_eq_true.1 hl r hr)

/-- One coordinate: a repeated leaf exits to `sel_fail`, else the row is stored and the invariant
advances; at most 90 cycles. -/
theorem sel_body (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) {c : Nat}
    (hc : c < 7) {t : MachineState} (hI : SelInv b s0 N c t) :
    ∃ k u, Steps image t k k u ∧ k ≤ 90 ∧
      (if rowOk (selRow N c) then SelInv b s0 N (c + 1) u
       else u.pc = pcOf (b + 101) ∧ RegsExcept s0 u selRegs ∧ Frame s0 u SelW) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := so7_spec hK t hI.pc c (by omega) hI.x20
  rw [if_pos hc] at p1
  have hN1 : NAt t1 N := (hN.frame hI.frame).frame (f1.mono (by simp))
  obtain ⟨t2, s2, p2, h28, r2, f2⟩ := so9_spec hK t1 p1 c hc (by rw [r1.get (by decide), hI.x20]) N hN1
  obtain ⟨k3, t3, s3, k3le, p3, h6, h22, h23, h24, r3, f3⟩ := sort_spec hK t2 p2 _ (selWin_lt N c) h28
  have hrow : ∀ j, (selRow N c).getD j 0 < 128 := selRow_lt N c
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 ((selRow N c).getD 0 0) := h22
  have g23 : t3.getReg .x23 = BitVec.ofNat 64 ((selRow N c).getD 1 0) := h23
  have g24 : t3.getReg .x24 = BitVec.ofNat 64 ((selRow N c).getD 2 0) := h24
  obtain ⟨t4, s4, p4, r4, f4⟩ := so51_spec hK t3 p3 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) (by have := hrow 0; omega)
    (by have := hrow 1; omega) g22 g23
  have regs4 : RegsExcept s0 t4 selRegs :=
    regs_mono ((((hI.regs.trans r1).trans r2).trans r3).trans r4) (by decide)
  have frame4 : Frame s0 t4 SelW := ((((hI.frame.trans f1).trans f2).trans f3).trans f4).mono
    (by sel_frame)
  by_cases e1 : (selRow N c).getD 0 0 = (selRow N c).getD 1 0
  · rw [if_pos e1] at p4
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e1]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    refine ⟨2 + 22 + k3 + 1, t4, ((s1.trans s2).trans s3).trans s4, by omega, ?_⟩
    rw [hok]; exact ⟨p4, regs4, frame4⟩
  rw [if_neg e1] at p4
  obtain ⟨t5, s5, p5, r5, f5⟩ := so52_spec hK t4 p4 ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (by have := hrow 1; omega)
    (by have := hrow 2; omega) (by rw [r4.get (by decide), g23]) (by rw [r4.get (by decide), g24])
  by_cases e2 : (selRow N c).getD 1 0 = (selRow N c).getD 2 0
  · rw [if_pos e2] at p5
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e2]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    refine ⟨2 + 22 + k3 + 1 + 1, t5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, ?_⟩
    rw [hok]
    exact ⟨p5, regs_mono (regs4.trans r5) (by decide),
      (frame4.trans f5).mono (by sel_frame)⟩
  rw [if_neg e2] at p5
  have hok : rowOk (selRow N c) = true := by
    rw [rowOk]; simp only [ne_eq, e1, e2, not_false_eq_true, decide_true, Bool.and_self]
  have hcost := selCost_le N c
  obtain ⟨t6, s6, p6, h21', m0, m8, m16, h25', h20', r6, f6⟩ :=
    so53_spec hK t5 p5 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (selBucket N c * 128) (21 + selCost N c) (SEL + 24 * c) c (by have := hrow 0; omega) (by have := hrow 1; omega) (by have := hrow 2; omega)
      (by simp only [SEL]; omega) (by simp only [SEL]; omega)
      (by rw [r5.get (by decide), r4.get (by decide), g22])
      (by rw [r5.get (by decide), r4.get (by decide), g23])
      (by rw [r5.get (by decide), r4.get (by decide), g24])
      (by rw [r5.get (by decide), r4.get (by decide), h6]; rfl)
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x21])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x25])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x20])
  refine ⟨2 + 22 + k3 + 1 + 1 + 44, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6,
    by omega, ?_⟩
  rw [if_pos hok]
  have fr0 := (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6)
  have fr : Frame t t6 SelW := fr0.mono (by sel_frame)
  refine ⟨p6, h20', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h21', selCost_succ]; unfold rowCost; congr 1; omega
  · rw [h25']; congr 1
  · intro c' hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · exact hI.ok c' h
    · exact hok
  · intro c' hc' j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · rw [fr0.get (by simp only [SEL]; omega) (by simp only [SEL, or_false, false_or]; omega)]
      exact hI.rows c' h j hj
    · interval_cases j
      · simpa [selBucket, Nat.add_comm] using m0
      · simpa [selBucket, Nat.add_comm] using m8
      · simpa [selBucket, Nat.add_comm] using m16
  · exact regs_mono (regs4.trans (r5.trans r6)) (by decide)
  · exact (hI.frame.trans fr).mono (by intro A _ hA; rcases hA with hA | hA <;> exact hA)

/-- The coordinate loop from coordinate `c` (`c + n = 7`): an early `sel_fail` exit (some row
repeats a leaf), or the invariant after all seven coordinates; at most `90 n` cycles. -/
theorem sel_loop (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) :
    ∀ n c t, c + n = 7 → SelInv b s0 N c t →
      ∃ k u, Steps image t k k u ∧ k ≤ 90 * n ∧
        ((u.pc = pcOf (b + 101) ∧ (List.range 7).all (fun c => rowOk (selRow N c)) = false ∧
          RegsExcept s0 u selRegs ∧ Frame s0 u SelW) ∨ SelInv b s0 N 7 u) := by
  intro n
  induction n with
  | zero => intro c t hc hI; exact ⟨0, t, Steps.refl t, le_refl _, Or.inr (by simpa using hc ▸ hI)⟩
  | succ n ih =>
    intro c t hc hI
    obtain ⟨k1, t1, s1, k1le, h1⟩ := sel_body hK hN (by omega) hI
    by_cases hok : rowOk (selRow N c) = true
    · rw [if_pos hok] at h1
      obtain ⟨k2, t2, s2, k2le, h2⟩ := ih (c + 1) t1 (by omega) h1
      exact ⟨k1 + k2, t2, s1.trans s2, by rw [Nat.mul_succ]; omega, h2⟩
    · rw [if_neg hok] at h1
      refine ⟨k1, t1, s1, by rw [Nat.mul_succ]; omega, Or.inl ⟨h1.1, ?_, h1.2⟩⟩
      rw [List.all_eq_false]
      exact ⟨c, List.mem_range.2 (by omega), hok⟩

/-- **`select_ok`** (kernel at base `b`, entry `b + 3`, return address `ret` in `ra`, `N` at `NBUF`):
returns to `ret` within 640 cycles with `a3 = 1` iff `admissible (selections N)`; on acceptance the
selection table at `SEL` holds row `c` = `128 bucket + leaf` (sorted leaves) for every coordinate.
Writes only the table; changes only `selRegs`. -/
theorem selectOk_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 640 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.admissible (T3.selections N) then 1 else 0) ∧
      (T3.admissible (T3.selections N) = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨t0, s0', p0, h21, h20, h25, r0, f0⟩ := so3_spec hK s hpc
  have hI : SelInv b s N 0 t0 :=
    ⟨p0, h20, by simpa [selCost_zero] using h21, by simpa using h25, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), regs_mono r0 (by decide), f0.mono (by intro _ _ h; exact h.elim)⟩
  obtain ⟨k1, t1, s1, k1le, h⟩ := sel_loop hK hN 7 0 t0 rfl hI
  have hx1 : ∀ u, RegsExcept s u selRegs → u.getReg .x1 = pcOf ret := fun u hu => by
    rw [hu.get (by decide), h1]
  rcases h with ⟨p1, hall, r1, f1⟩ | hI7
  · obtain ⟨t2, s2, p2, h13, r2, f2⟩ := so101_spec hK t1 p1 ret (hx1 t1 r1)
    have hadm : T3.admissible (T3.selections N) = false := by
      rw [admissible_selections, hall, Bool.false_and]
    refine ⟨4 + k1 + 2, t2, (s0'.trans s1).trans s2, by omega, p2, by rw [h13, hadm]; rfl,
      fun h => by rw [hadm] at h; exact absurd h (by decide), regs_mono (r1.trans r2) (by decide),
      f1.trans f2 |>.mono (by intro A _ hA; rcases hA with hA | hA; exact hA; exact hA.elim)⟩
  · have hS := selCost_le N 7
    obtain ⟨t2, s2, p2, r2, f2⟩ := so7_spec hK t1 hI7.pc 7 (le_refl _) hI7.x20
    rw [if_neg (by omega)] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := so97_spec hK t2 p2 (21 + selCost N 7) (by omega)
      (by rw [r2.get (by decide), hI7.x21])
    have hall : (List.range 7).all (fun c => rowOk (selRow N c)) = true :=
      List.all_eq_true.2 (fun c hc => hI7.ok c (List.mem_range.1 hc))
    have rr : RegsExcept s t3 selRegs := regs_mono ((hI7.regs.trans r2).trans r3) (by decide)
    have ff : Frame t1 t3 (fun _ => False) := (f2.trans f3).mono (by intro A _ hA; simpa using hA)
    by_cases hc : 116 ≤ 21 + selCost N 7
    · rw [if_pos hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so101_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = false := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun h => by rw [hadm] at h; exact absurd h (by decide),
        regs_mono (rr.trans r4) (by decide), ?_⟩
      exact ((hI7.frame.trans ff).trans f4).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)
    · rw [if_neg hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so99_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = true := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      have fr : Frame t1 t4 (fun _ => False) := (ff.trans f4).mono (by intro A _ hA; simpa using hA)
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun _ c hc j hj => ?_, regs_mono (rr.trans r4) (by decide),
        (hI7.frame.trans fr).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)⟩
      rw [fr.get (by simp only [SEL]; omega) (by simp)]
      exact hI7.rows c hc j hj

end loop

end SigGolfCandidate.T3M.Search
