import SigGolfCandidate.T3M.Search.Blocks
import SigGolfCandidate.T3M.Search.Arith
import SigGolfCandidate.T3M.Search.CounterSearch

section


namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
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
section sort
variable {image : Image} {b : Nat}
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
def RowAt (t : MachineState) (N : BitVec 256) (c : Nat) : Prop :=
  ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
    BitVec.ofNat 64 (selBucket N c * 128 + (selRow N c).getD j 0)
def SelW (A : Nat) : Prop := SEL ≤ A ∧ A < SEL + 168
abbrev selRegs : List Reg := [.x6, .x7, .x13, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29]
theorem NAt.frame {s t : MachineState} {N : BitVec 256} (h : NAt s N) (hf : Frame s t SelW) : NAt t N := by
  intro j hj
  rw [hf.get (by simp only [NBUF]; omega) (by simp only [SelW, SEL, NBUF]; omega)]
  exact h j hj
section loop
variable {image : Image} {b : Nat}
structure SelInv (b : Nat) (s0 : MachineState) (N : BitVec 256) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 7)
  x20 : t.getReg .x20 = BitVec.ofNat 64 c
  x21 : t.getReg .x21 = BitVec.ofNat 64 (21 + selCost N c)
  x25 : t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c)
  ok : ∀ c' < c, rowOk (selRow N c') = true
  rows : ∀ c' < c, RowAt t N c'
  regs : RegsExcept s0 t selRegs
  frame : Frame s0 t SelW
macro "sel_frame" : tactic =>
  `(tactic| (intro A _ hA; (try simp only [or_false, false_or, or_self] at hA); first | exact hA | (simp only [SelW, SEL] at *; omega)))
theorem regs_mono {s t : MachineState} {l : List Reg} (h : RegsExcept s t l)
    (hl : l.all (fun r => decide (r ∈ selRegs)) = true) : RegsExcept s t selRegs :=
  h.mono (fun r hr => by simpa using List.all_eq_true.1 hl r hr)
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
end

section

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gate_word (N : BitVec 256) :
    N.extractLsb' 192 64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, show (7 : Nat) = 2 ^ 3 - 1 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 3
  · simp [h, hi, show 14 + i < 64 by omega, BitVec.testBit_toNat,
      show 192 + (14 + i) = i + 206 by omega]
  · simp [h]
theorem gate_head_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if N.toNat / 2 ^ 206 % 8 = 0 then pcOf (gatePc b + 5) else pcOf (b + 101)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gate hK.2) (codeAt_gateHead hG) s hpc
    (by simp [gateSt, blkGateE.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    have hh : s.getMem 131448#64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
      simpa only [NBUF] using hw ▸ gate_word N
    simp only [Result.toState_pc, gateEnd, rebase, blkGateE.res, E.eval, BinOp.eval, CmpOp.eval]
    change (if (s.getMem 131448#64 >>> 14 &&& 7#64 != 0#64) = true then pcOf (b + 101) else pcOf (gatePc b + 5)) = _
    rw [hh]
    have he : (BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) = 0#64) ↔ N.toNat / 2 ^ 206 % 8 = 0 :=
      ofNat_inj (by have := Nat.mod_lt (N.toNat / 2 ^ 206) (show 0 < 8 by decide); omega) (by decide)
    simp only [bne_iff_ne, ne_eq, he, ite_not]
  · intro r hr; simp at hr; cases r <;> simp_all [gateSt, blkGateE.res, rv_simp] <;> rfl
  · intro A _ _; simp [gateSt, blkGateE.res, rv_simp]
theorem gate_jump_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 3) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gateJump hK.2) (codeAt_gateJump hG) s hpc
    (by simp [blkGateJE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [E.eval]
  · intro r hr; cases r <;> simp [blkGateJE.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGateJE.res, rv_simp]
theorem gatedSelect_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 646 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.digestAdmissible N then 1 else 0) ∧
      (T3.digestAdmissible N = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨u, hs, hp, hr, hf⟩ := gate_head_spec hK hG s hpc N hN
  have hN' : NAt u N := by intro j hj; rw [hf.get (by simp only [NBUF]; omega) (by simp)]; exact hN j hj
  have hu1 : u.getReg .x1 = pcOf ret := by rw [hr.get (by decide), h1]
  by_cases hg : N.toNat / 2 ^ 206 % 8 = 0
  · rw [if_pos hg] at hp
    obtain ⟨v, hs', hp', hr', hf'⟩ := gate_jump_spec hK hG u hp
    have hN'' : NAt v N := by intro j hj; rw [hf'.get (by simp only [NBUF]; omega) (by simp)]; exact hN' j hj
    have hv1 : v.getReg .x1 = pcOf ret := by rw [hr'.get (by decide), hu1]
    obtain ⟨k, t, st, hk, pt, ht13, htrows, rt, ft⟩ := selectOk_spec hK v hp' ret hv1 N hN''
    have hgB : T3.digestGate N = true := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = true; exact decide_eq_true hg
    have he : T3.digestAdmissible N = T3.admissible (T3.selections N) := by simp only [T3.digestAdmissible, hgB, Bool.and_true]
    refine ⟨5 + 1 + k, t, (hs.trans hs').trans st, by omega, pt, by simpa [he] using ht13,
      by simpa [he] using htrows, ?_, ?_⟩
    · exact regs_mono ((hr.trans hr').trans rt) (by decide)
    · exact ((hf.trans hf').trans ft).mono (by intro A _ h; simpa using h)
  · rw [if_neg hg] at hp
    obtain ⟨t, st, pt, ht13, rt, ft⟩ := so101_spec hK u hp ret hu1
    have hgB : T3.digestGate N = false := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = false; exact decide_eq_false hg
    have he : T3.digestAdmissible N = false := by simp only [T3.digestAdmissible, hgB, Bool.and_false]
    refine ⟨7, t, hs.trans st, by decide, pt, by simpa [he] using ht13,
      by simp [he], ?_, ?_⟩
    · exact regs_mono (hr.trans rt) (by decide)
    · exact (hf.trans ft).mono (by intro A _ h; simpa using h)
end SigGolfCandidate.T3M.Search
end

section


namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) : (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    T3.pad64 (T3.digestInput rho m c) = T3.digestInput rho m c := by
  unfold T3.pad64
  rw [digestInput_length]
  simp
theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 12 0 0 0),
        BitVec.ofNat 64 (hdr1 0 c.toNat), m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput]
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_bytesLE32]
  rfl
theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]
theorem TBSim.publicHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
section blocks
variable {image : Image} {d b : Nat}
theorem ds0_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 0)) (i : Nat)
    (hi : i ≤ 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 20 then pcOf (b + 0) else pcOf (d + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds0 hD.2) (codeAt_ds_0 hD) s hpc (by simp [stds_0, blkds30_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_0, rebase, blkds30_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 20
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 1048576#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_0, blkds30_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_0, blkds30_0.res, rv_simp]
theorem ds2_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 2)) (i : Nat)
    (hi : i < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (d + 14) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run_ds2 hD.2) (codeAt_ds_2 hD) s hpc
    (by simp [stds_2, blkds30_2.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcEds_2, E.eval]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [DIG]
    rfl
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [h19, DIG]
    rw [hdr1_eq 0 i (by decide) (by omega)]
    congr 1
    omega
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_2, blkds30_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]
theorem ds14_fetch (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 14)) :
    fetch image s = some (.base .ECALL) :=
  ((codeAt_ds_14 hD).fetch s hpc).trans rfl
theorem ds15_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 15)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (gatePc b) ∧ t.getReg .x1 = pcOf (d + 16) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds15 hD.2) (codeAt_ds_15 hD) s hpc
    (by simp [stds_15, blkds30_15.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_15, E.eval]
  · simp [stds_15, blkds30_15.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_15, blkds30_15.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [stds_15, blkds30_15.res, rv_simp]
theorem ds16_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 16)) (ok : Bool)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if ok then pcOf (d + 19) else pcOf (d + 17)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds16 hD.2) (codeAt_ds_16 hD) s hpc
    (by simp [stds_16, blkds30_16.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_16, rebase, blkds30_16.res, E.eval, CmpOp.eval, h13]
    cases ok <;> simp
  · intro r hr; simp at hr; cases r <;> simp_all [stds_16, blkds30_16.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_16, blkds30_16.res, rv_simp]
theorem ds17_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 17)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (d + 0) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds17 hD.2) (codeAt_ds_17 hD) s hpc
    (by simp [stds_17, blkds30_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_17, E.eval]
  · simp only [Result.toState_getReg, stds_17, blkds30_17.res]
    t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_17, blkds30_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_17, blkds30_17.res, rv_simp]
end blocks
abbrev dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (d : Nat) (s : MachineState) (rho : Digest) (m : T3.Message) : Prop where
  pc : s.pc = pcOf d
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((T3.selections N).getD c ⟨0, []⟩).bucket * 128 + ((T3.selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def DsPost (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (c, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW ∧
      c.toNat < 2 ^ 20 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
def DsPostS (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCostS : Nat := T3.attemptLimit * 700 + 100
theorem selEntry_eq (N : HashOutput) (c j : Nat) (hc : c < 7) :
    selEntry N c j = selBucket N c * 128 + (selRow N c).getD j 0 := by
  simp [selEntry, selections_eq, List.getD_eq_getElem?_getD, hc]
theorem NAt.writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    NAt (writeHash t a) a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
structure DsInv (d : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (d + 0)
  hi : i ≤ 2 ^ 20
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t dsRegs
  frame : Frame s0 t DsW
theorem ds_loop (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    ∀ F i t, i + F = 2 ^ 20 → DsInv d s0 i t →
      TBSim image sk t (F * 672 + 670) (T3.digestSearch rho m i F) (DsPost b d s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, _⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := DsPost b d s0) (a := none) ⟨p2, h5, h10⟩)
    exact this.mono (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 20 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨u, s2, p2, h16, h24, h10, h11, h12, r2, f2⟩ :=
      ds2_spec hD t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u dsRegs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have u19 : u.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), r1.get (by decide), hI.x19]
    have fu : Frame s0 u DsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with h | h
      · exact h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have mem : ∀ A, A < 2 ^ 64 → ¬ DsW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ DsW A := by
      intro A hA; simp only [DsW, DIG, NBUF, SEL] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (T3.pad64 (T3.digestInput rho m (BitVec.ofNat 32 i))) := by
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
    have prog : T3.digestSearch rho m i (F + 1) =
        (T3.publicHash (T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if T3.digestAdmissible output then pure (some (BitVec.ofNat 32 i, output))
          else T3.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind (ds14_fetch hD u p2) h5 hv hq
      (W := 650 + (F * 672 + 670)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput]; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf (d + 15) := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : NAt (writeHash u a) a := NAt.writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    obtain ⟨t15, s15, p15, h1, r15, f15⟩ := ds15_spec hD (writeHash u a) pw
    obtain ⟨k, t16, s16, hk, p16, h13, hrows, r16, f16⟩ := gatedSelect_spec hK hD.1.2 t15 p15 (d + 16) h1 a
      (NAt.frame hN (f15.mono (fun _ _ h => h.elim)))
    obtain ⟨t17, s17, p17, r17, f17⟩ := ds16_spec hD t16 p16 _ h13
    have r17' : RegsExcept s0 t17 dsRegs :=
      ((((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans r15).trans
        r16).trans r17).mono (by decide)
    have x19' : t17.getReg .x19 = BitVec.ofNat 64 i := by
      rw [r17.get (by decide), r16.get (by decide), r15.get (by decide), getReg_writeHash, u19]
    have f17' : Frame s0 t17 DsW := ((((fu.trans fw).trans f15).trans f16).trans f17).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with (h | h) | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hN17 : NAt t17 a :=
      NAt.frame (NAt.frame (NAt.frame hN (f15.mono (fun _ _ h => h.elim))) f16) (f17.mono (fun _ _ h => h.elim))
    by_cases hadm : T3.digestAdmissible a = true
    · simp only [hadm, ↓reduceIte] at p17 ⊢
      refine (TBSim.steps (s15.trans (s16.trans s17)) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
      refine ⟨p17, by rw [r17'.get (by decide), hpre.x5], (by have hh := hadm; simp only [T3.digestAdmissible, Bool.and_eq_true] at hh; exact hh.1), hN17, ?_, r17', f17', by rw [hc]; exact hi,
        by rw [hc, x19']⟩
      intro c hc7 j hj
      rw [f17.get (by simp only [SEL]; omega) (fun h => h), hrows hadm c hc7 j hj, selEntry_eq a c j hc7]
    · have hadm' : T3.digestAdmissible a = false := by simpa using hadm
      simp only [hadm', Bool.false_eq_true, ↓reduceIte] at p17 ⊢
      obtain ⟨t18, s18, p18, h19, r18, f18⟩ := ds17_spec hD t17 p17 i x19'
      have hI' : DsInv d s0 (i + 1) t18 :=
        ⟨p18, by omega, h19, (r17'.trans r18).mono (by decide),
          (f17'.trans f18).mono (fun A _ h => by simp only [or_false] at h; exact h)⟩
      refine (TBSim.steps (s15.trans (s16.trans (s17.trans s18))) (ih (i + 1) t18 (by omega) hI')).mono
        (by omega) (fun _ _ h => h)
theorem digestSearch_tbsim (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    TBSim image sk s0 (2 ^ 20 * 672 + 670) (T3.digestSearch rho m 0 T3.attemptLimit) (DsPost b d s0) :=
  ds_loop hD hK hpre (2 ^ 20) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩
theorem digestSearch_spec (hD : DsAt image d b) (hK : KernAt image b) (s : MachineState) (rho : Digest)
    (m : T3.Message) (h : DsPre d s rho m) :
    TBSim image sk s dsCostS (T3.digestSearch rho m 0 T3.attemptLimit) (DsPostS b d s) := by
  refine (digestSearch_tbsim (sk := sk) hD hK h).mono (by unfold dsCostS T3.attemptLimit; omega)
    (fun r t ht => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1⟩
end loop
end SigGolfCandidate.T3M.Search
end
