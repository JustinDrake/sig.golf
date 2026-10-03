import SigGolfCandidate.T3M.Keygen.Chain

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sub27_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 27)) (lay tree leaf : Nat) (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (hleaf : leaf < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x3 = s.getReg .x1 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = BitVec.ofNat 64 (hdr1 tree leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = BitVec.ofNat 64 (hdr1 tree leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = BitVec.ofNat 64 (513 + 65536 * lay) ∧
      RegsExcept s t [.x3, .x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hrun := run_27 h.2.1
  have hw1 : BitVec.ofNat 64 tree ||| BitVec.ofNat 64 (leaf * 4294967296) = BitVec.ofNat 64 (hdr1 tree leaf) := by
    rw [BitVec.or_comm, ofNat_or_disjoint tree (leaf * 4294967296) 32 htree (by omega),
      hdr1_eq tree leaf htree hleaf]
    congr 1; ring
  refine ⟨_, symRun_sound hrun (codeAt_sub_27 h) s hpc (by simp [st_27, blk117_27.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_27, Result.toState_pc, E.eval]
  · simp [st_27, blk117_27.res, rv_simp]
  · simp [st_27, blk117_27.res, rv_simp]
  · simp only [Result.toState_getMem, st_27, blk117_27.res, CHAIN, LEAFPK]
    t3n [h9, h18]
    exact hw1
  · simp only [Result.toState_getMem, st_27, blk117_27.res, CHAIN, LEAFPK]
    t3n [h9, h18]
    exact hw1
  · simp only [Result.toState_getMem, st_27, blk117_27.res, CHAIN, LEAFPK]
    t3n [h8]
    rw [ofNat_or_disjoint 513 (lay * 65536) 16 (by omega) (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_27, blk117_27.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN, LEAFPK] at hn
    simp only [Result.toState_getMem, st_27, blk117_27.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem sub41_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 41)) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if i < n then pcOf (b + 42) else pcOf (b + 95)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_41 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_41 h) s hpc (by simp [st_41, blk117_41.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_41, rebase, blk117_41.res, E.eval, CmpOp.eval, h19, h26,
      ofNat_slt i n hi hn]
    by_cases hin : i < n <;> simp [hin]
  · intro r hr; cases r <;> simp_all [st_41, blk117_41.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_41, blk117_41.res, rv_simp]
theorem sub42_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 42)) (i : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf (b + 44) else pcOf (b + 60)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_42 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_42 h) s hpc (by simp [st_42, blk117_42.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_42, rebase, blk117_42.res, rv_simp, h19, ofNat_and1]
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2 <;> simp [h2]
  · intro r hr; simp at hr; cases r <;> simp_all [st_42, blk117_42.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_42, blk117_42.res, rv_simp]
theorem sub44_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 44)) (lay tree leaf i : Nat) (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = pcOf (b + 59) ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 SEEDS ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 0 lay tree (i / 2)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 tree leaf) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  have hrun := run_44 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_44 h) s hpc (by simp [st_44, blk117_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, Result.toState_pc, E.eval]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp [st_44, blk117_44.res, rv_simp]
  · simp only [Result.toState_getMem, st_44, blk117_44.res, PRIV]
    t3n [h8, h19]
    rw [ofNat_shr i 1 (by omega), ofNat_shl, Nat.pow_one,
      ofNat_or_disjoint' (lay * 65536) (i / 2 * 2 ^ 32) 32 (by omega) (by omega),
      ofNat_or_disjoint 1 _ 16 (by omega) (by omega), hdr0_eq 0 lay tree (i / 2) (by omega) hlay htree
        (by omega)]
    congr 1; omega
  · simp only [Result.toState_getMem, st_44, blk117_44.res, PRIV]
    t3n [h9, h18]
    rw [BitVec.or_comm, ofNat_or_disjoint tree (leaf * 4294967296) 32 htree (by omega),
      hdr1_eq tree leaf htree hleaf]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk117_44.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, st_44, blk117_44.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_sub59 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 59)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_59 h).fetch s hpc).trans rfl
set_option maxRecDepth 100000 in
theorem sub60_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 60)) (i digp : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 digp) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (b + 72) ∧ t.getReg .x28 = BitVec.ofNat 64 (digp + i) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2))) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (SEEDS + 16 * (i % 2) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hrun := run_60 h.2.1
  have hm : i % 2 < 2 := Nat.mod_lt _ (by decide)
  have hobl : Oblig.all s st_60.obl := by
    simp only [st_60, blk117_60.res]
    t3n [h19, ofNat_and1]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_60 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_60, Result.toState_pc, E.eval]
  · t3n [st_60, blk117_60.res, h19, h22]
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · simp only [Result.toState_getMem, st_60, blk117_60.res, CHAIN, SEEDS]
    t3n [h19, ofNat_and1]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_60, blk117_60.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, st_60, blk117_60.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub72_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 72)) (a : Nat) (ha : a + 1 ≤ 2 ^ 24) (d : Nat) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 a) (hbyte : s.getByte (BitVec.ofNat 64 a) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 73) ∧ t.getReg .x17 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hoff : s.getReg .x28 + signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 a := by
    rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have st := steps_lbu (rd := .x17) (rs := .x28) (off := 0) (codeAt_sub_72 h) hpc rfl
    (by rw [hoff, accessValid_iff, toNat_ofNat_lt (by omega)]; simp [MEMORY_BYTES]; omega)
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = pcOf (b + 73)
    rw [hpc, pcOf_add4]
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide), hoff, hbyte]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A _ _; simp
theorem sub73_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 73)) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf (b + 75) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_73 h.2.1
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt (show lay < 2 ^ 64 by omega)] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound hrun (codeAt_sub_73 h) s hpc (by simp [st_73, blk117_73.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, pcE_73, rebase, blk117_73.res, E.eval, CmpOp.eval, h8, hz]
  · simp [st_73, blk117_73.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_73, blk117_73.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_73, blk117_73.res, rv_simp]
theorem sub75_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 75)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1000) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_75 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_75 h) s hpc (by simp [st_75, blk117_75.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcE_75, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [st_75, blk117_75.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_75, blk117_75.res, rv_simp]
theorem maxLow_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1000)) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf (b + 1002) else pcOf (b + 76)) ∧
      t.getReg .x21 = BitVec.ofNat 64 3 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxLow h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_maxLow h) s hpc (by simp [maxLowState, max117Low.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, maxLowPC, rebase, max117Low.res, E.eval, CmpOp.eval, h19, h27,
      ofNat_slt i n4 hi hn]
    by_cases hin : i < n4 <;> simp [hin]
  · simp [maxLowState, max117Low.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxLowState, max117Low.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxLowState, max117Low.res, rv_simp]
theorem maxHigh_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1002)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 76) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_maxHigh h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_maxHigh h) s hpc (by simp [maxHighState, max117High.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [maxHighPC, Result.toState_pc, E.eval]
  · simp [maxHighState, max117High.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [maxHighState, max117High.res, rv_simp] <;> rfl
  · intro A _ _; simp [maxHighState, max117High.res, rv_simp]
theorem sub76_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 76)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 77) else pcOf (b + 78)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_76 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_76 h) s hpc (by simp [st_76, blk117_76.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_76, rebase, blk117_76.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_76, blk117_76.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_76, blk117_76.res, rv_simp]
theorem sub77_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 77)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 78) ∧ t.getReg .x21 = s.getReg .x17 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hrun := run_77 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_77 h) s hpc (by simp [st_77, blk117_77.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_77, Result.toState_pc, E.eval]
  · simp [st_77, blk117_77.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_77, blk117_77.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_77, blk117_77.res, rv_simp]
theorem sub78_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 78)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf b ∧ t.getReg .x1 = pcOf (b + 79) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  have hrun := run_78 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_78 h) s hpc (by simp [st_78, blk117_78.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_78, Result.toState_pc, E.eval]
  · simp [st_78, blk117_78.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [st_78, blk117_78.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [st_78, blk117_78.res, rv_simp]
theorem sub79_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 79)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 92) else pcOf (b + 80)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_79 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_79 h) s hpc (by simp [st_79, blk117_79.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_79, rebase, blk117_79.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_79, blk117_79.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_79, blk117_79.res, rv_simp]
theorem sub80_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 80)) (i : Nat) (hi : i < 2 ^ 32) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 0 then pcOf (b + 83) else pcOf (b + 82)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_80 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_80 h) s hpc (by simp [st_80, blk117_80.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_80, rebase, blk117_80.res, E.eval, CmpOp.eval, h19]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · have : BitVec.ofNat 64 i ≠ 0#64 := fun he => hi0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
      simp [hi0, this]
  · t3n [st_80, blk117_80.res, h19]; congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_80, blk117_80.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_80, blk117_80.res, rv_simp]
theorem sub82_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 82)) (o : Nat) (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 83) ∧ t.getReg .x28 = BitVec.ofNat 64 (o + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_82 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_82 h) s hpc (by simp [st_82, blk117_82.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_82, Result.toState_pc, E.eval]
  · t3n [st_82, blk117_82.res, h28]
  · intro r hr; simp at hr; cases r <;> simp_all [st_82, blk117_82.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_82, blk117_82.res, rv_simp]
theorem sub83_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 83)) (o : Nat) (ho : o % 8 = 0) (ho' : LEAFPK + o + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 92) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + o + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + o ∨ A = LEAFPK + o + 8) := by
  have hrun := run_83 h.2.1
  have hobl : Oblig.all s st_83.obl := by
    simp only [st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho'
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_83 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_83, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    simp only [LEAFPK] at ho' ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_83, blk117_83.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [LEAFPK] at hn ho'
    simp only [Result.toState_getMem, st_83, blk117_83.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub92_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 92)) (i v : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 v) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 41) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x23 = BitVec.ofNat 64 (v + 16) ∧ RegsExcept s t [.x19, .x23] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_92 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_92 h) s hpc (by simp [st_92, blk117_92.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_92, Result.toState_pc, E.eval]
  · t3n [st_92, blk117_92.res, h19]
  · t3n [st_92, blk117_92.res, h23]
  · intro r hr; simp at hr; cases r <;> simp_all [st_92, blk117_92.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_92, blk117_92.res, rv_simp]
theorem sub95_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 95)) (so : Bool) (h31 : s.getReg .x31 = BitVec.ofNat 64 (if so then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if so then pcOf (b + 112) else pcOf (b + 96)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_95 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_95 h) s hpc (by simp [st_95, blk117_95.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_95, rebase, blk117_95.res, E.eval, CmpOp.eval, h31]
    cases so <;> simp
  · intro r hr; cases r <;> simp_all [st_95, blk117_95.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_95, blk117_95.res, rv_simp]
theorem sub96_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 96)) (n : Nat) (hn : n = 54 ∨ n = 43)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf (b + 105) ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧
      t.getReg .x12 = BitVec.ofNat 64 LOUT ∧ RegsExcept s t [.x6, .x10, .x11, .x12] ∧
      Frame s t (fun _ => False) := by
  have hrun := run_96 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_96 h) s hpc (by simp [st_96, blk117_96.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_96, Result.toState_pc, E.eval]
  · simp [st_96, blk117_96.res, rv_simp]
  · simp only [Result.toState_getReg, st_96, blk117_96.res, rv_simp, h26]
    rcases hn with rfl | rfl <;> decide
  · simp [st_96, blk117_96.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_96, blk117_96.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_96, blk117_96.res, rv_simp]
theorem fetch_sub105 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 105)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_105 h).fetch s hpc).trans rfl
theorem sub106_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 106)) (dest : Nat) (hd : dest % 8 = 0) (hd' : dest + 16 ≤ 2 ^ 24)
    (hdl : dest + 16 ≤ LOUT ∨ LOUT + 16 ≤ dest) (h25 : s.getReg .x25 = BitVec.ofNat 64 dest) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 112) ∧
      t.getMem (BitVec.ofNat 64 dest) = s.getMem (BitVec.ofNat 64 LOUT) ∧
      t.getMem (BitVec.ofNat 64 (dest + 8)) = s.getMem (BitVec.ofNat 64 (LOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29] ∧ Frame s t (fun A => A = dest ∨ A = dest + 8) := by
  have hrun := run_106 h.2.1
  have hobl : Oblig.all s st_106.obl := by
    simp only [st_106, blk117_106.res]
    t3n [h25]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_106 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_106, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
  · intro r hr; simp at hr; cases r <;> simp_all [st_106, blk117_106.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_106, blk117_106.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega)]
theorem sub112_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 112)) (k : Nat) (h3 : s.getReg .x3 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_112 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_112 h) s hpc (by simp [st_112, blk117_112.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_112, blk117_112.res, rv_simp, h3, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_112, blk117_112.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_112, blk117_112.res, rv_simp]
end SigGolfCandidate.T3M.Keygen
