import SigGolfCandidate.T3M.Keygen.Chain

/-!
# Block specifications of the shared `build_levels` subroutine (offsets 113..159 from the base)

Registers: `x15` height `H`, `x21` header word 0 (`1 | tag << 8 | lay << 16`), `x9` tree, `x2` heap
arena (node `k` at `arena + 16 k`), `x20` level size `lo`, `x24` node index `k`, `x1` return address.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- `lo := 2^(H-1)`. -/
theorem sub113_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 113)) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_113 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_113 h) s hpc (by simp [st_113, blk117_113.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_113, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_113, blk117_113.res, rv_simp, h15]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)]
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk117_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk117_113.res, rv_simp]

/-- `lv_level`: `lo = 0` ends the levels. -/
theorem sub116_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]

theorem sub117_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]

/-- `lv_node`: `k ≥ 2 lo` ends the level. -/
theorem sub118_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]

/-- The node block `node 2k | T(word0, tree | k << 32) | 0 | node 2k+1` and the HASH arguments. -/
theorem sub120_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (hk' : k < 2 ^ 32) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (hdr1 tree k) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have hrun := run_120 h.2
  have hobl : Oblig.all s st_120.obl := by
    simp only [st_120, blk117_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_120 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_120, Result.toState_pc, E.eval]
  · simp [st_120, blk117_120.res, rv_simp]
  · simp [st_120, blk117_120.res, rv_simp]
  · simp [st_120, blk117_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n []
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h9, h24]
    rw [BitVec.or_comm, ofNat_or_disjoint tree (k * 4294967296) 32 htree (by omega),
      hdr1_eq tree k htree hk']
    congr 1; ring
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120, blk117_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120, blk117_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem fetch_sub146 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_146 h).fetch s hpc).trans rfl

/-- Node `k := NOUT` (16 bytes), `k := k + 1`, back to `lv_node`. -/
theorem sub147_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 147)) (arena k : Nat) (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (hdis : NOUT + 16 ≤ arena + 16 * k ∨ arena + 16 * k + 16 ≤ NOUT)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x24, .x28, .x29] ∧
      Frame s t (fun X => X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  have hrun := run_147 h.2
  have hobl : Oblig.all s st_147.obl := by
    simp only [st_147, blk117_147.res]
    t3n [h2, h24]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_147 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_147, Result.toState_pc, E.eval]
  · t3n [st_147, blk117_147.res, h24]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_147, blk117_147.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `lv_next_level`: `lo := lo / 2`. -/
theorem sub157_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 157)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_157 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_157 h) s hpc (by simp [st_157, blk117_157.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_157, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_157, blk117_157.res, rv_simp, h20]
    rw [ofNat_shr _ _ hlo]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_157, blk117_157.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_157, blk117_157.res, rv_simp]

/-- `lv_done`: return. -/
theorem sub159_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2
  refine ⟨_, symRun_sound hrun (codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]

end SigGolfCandidate.T3M.Keygen
