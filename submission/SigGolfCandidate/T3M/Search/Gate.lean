import SigGolfCandidate.T3M.Search.SelectOk

/-! The ten-bit digest gate (`srli 54; sltiu 135; beqz`) followed by the shared selection kernel. -/
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false

theorem gate_field (N : BitVec 256) : (N.extractLsb' 192 64 >>> 54).toNat = N.toNat / 2 ^ 246 := by
  have h1 : N.toNat / 2 ^ 192 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by
    calc N.toNat < 2 ^ 256 := N.isLt
      _ = 2 ^ 192 * 2 ^ 64 := by norm_num)
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h1, Nat.div_div_eq_div_mul]
  all_goals norm_num

/-- `srli 54; sltiu 135` on digest word 3 is Core's ten-bit gate. -/
theorem gate_ult (N : BitVec 256) :
    BitVec.ult (N.extractLsb' 192 64 >>> 54) (BitVec.ofNat 64 135) = decide (N.toNat / 2 ^ 246 < 135) := by
  simp only [BitVec.ult, gate_field, BitVec.toNat_ofNat]
  all_goals norm_num

theorem gate_head_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if N.toNat / 2 ^ 246 < 135 then pcOf (gatePc b + 5) else pcOf (b + 101)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gate hK.2) (codeAt_gateHead hG) s hpc
    (by simp [gateSt, blkGateE.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    have hh : s.getMem 131448#64 = N.extractLsb' 192 64 := by simpa only [NBUF] using hw
    simp only [Result.toState_pc, gateEnd, rebase, blkGateE.res, E.eval, BinOp.eval, CmpOp.eval]
    change (if ((if BitVec.ult (s.getMem 131448#64 >>> 54) (BitVec.ofNat 64 135) then (1 : BitVec 64) else 0)
      == BitVec.ofNat 64 0) = true then pcOf (b + 101) else pcOf (gatePc b + 5)) = _
    rw [hh, gate_ult]
    generalize N.toNat / 2 ^ 246 = v
    by_cases hv : v < 135
    · have h' : ¬ 135 ≤ v := by omega
      simp [hv, h']
    · have h' : 135 ≤ v := by omega
      simp [hv, h']
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

/-- The gate wrapper returns exactly Core's complete digest predicate. -/
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
  by_cases hg : N.toNat / 2 ^ 246 < 135
  · rw [if_pos hg] at hp
    obtain ⟨v, hs', hp', hr', hf'⟩ := gate_jump_spec hK hG u hp
    have hN'' : NAt v N := by intro j hj; rw [hf'.get (by simp only [NBUF]; omega) (by simp)]; exact hN' j hj
    have hv1 : v.getReg .x1 = pcOf ret := by rw [hr'.get (by decide), hu1]
    obtain ⟨k, t, st, hk, pt, ht13, htrows, rt, ft⟩ := selectOk_spec hK v hp' ret hv1 N hN''
    have hgB : T3.digestGate N = true := by change decide (N.toNat / 2 ^ 246 < 135) = true; exact decide_eq_true hg
    have he : T3.digestAdmissible N = T3.admissible (T3.selections N) := by simp only [T3.digestAdmissible, hgB, Bool.and_true]
    refine ⟨5 + 1 + k, t, (hs.trans hs').trans st, by omega, pt, by simpa [he] using ht13,
      by simpa [he] using htrows, ?_, ?_⟩
    · exact regs_mono ((hr.trans hr').trans rt) (by decide)
    · exact ((hf.trans hf').trans ft).mono (by intro A _ h; simpa using h)
  · rw [if_neg hg] at hp
    obtain ⟨t, st, pt, ht13, rt, ft⟩ := so101_spec hK u hp ret hu1
    have hgB : T3.digestGate N = false := by change decide (N.toNat / 2 ^ 246 < 135) = false; exact decide_eq_false hg
    have he : T3.digestAdmissible N = false := by simp only [T3.digestAdmissible, hgB, Bool.and_false]
    refine ⟨7, t, hs.trans st, by decide, pt, by simpa [he] using ht13,
      by simp [he], ?_, ?_⟩
    · exact regs_mono (hr.trans rt) (by decide)
    · exact (hf.trans ft).mono (by intro A _ h; simpa using h)

end SigGolfCandidate.T3M.Search
