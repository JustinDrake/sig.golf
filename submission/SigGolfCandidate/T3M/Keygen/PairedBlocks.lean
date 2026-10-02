import SigGolfCandidate.T3M.Keygen.MainBlocks

/-! Exact blocks for the full cached tree and paired masks. -/
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

theorem blk277_spec (s : MachineState) (hpc : s.pc = pcOf 277) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 289 ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      t.getReg .x20 = BitVec.ofNat 64 4096 ∧ t.getReg .x22 = 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 REGION ∧
      t.getMem (BitVec.ofNat 64 0xA0) = s.getMem (BitVec.ofNat 64 (TOP+16)) ∧
      t.getMem (BitVec.ofNat 64 0xA8) = s.getMem (BitVec.ofNat 64 (TOP+24)) ∧
      RegsExcept s t [.x2,.x6,.x7,.x20,.x22,.x24,.x30] ∧
      Frame s t (fun A => A=0xA0 ∨ A=0xA8) := by
  refine ⟨_,symRun_sound blk_277 codeAt_277 s hpc (by simp [blk_277.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_277.res,E.eval]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp]
  · simp [blk_277.res,rv_simp,REGION]
  · simp [blk_277.res,rv_simp,TOP]
  · simp [blk_277.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_277.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem,blk_277.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]

theorem blk289_spec (s : MachineState) (hpc : s.pc = pcOf 289) (lo : Nat)
    (hlo : lo ≤ 4096) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 295 ∧ t.getReg .x23 = 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 (lo/2) ∧
      t.getReg .x21 = BitVec.ofNat 64 (TOP+16*lo) ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧
      RegsExcept s t [.x2,.x21,.x23,.x26] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_289 codeAt_289 s hpc (by simp [blk_289.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_289.res,E.eval]
  · simp [blk_289.res,rv_simp]
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_289.res]; t3n [h20]
    congr 1; unfold TOP; omega
  · simp [blk_289.res,rv_simp,TOP]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_289.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_289.res,rv_simp]

theorem blk295_spec (s : MachineState) (hpc : s.pc = pcOf 295) (level i : Nat)
    (hlev : level < 2^32) (hi : i < 2^32)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 309 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = BitVec.ofNat 64 (hdr0 13 0 0 level) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      RegsExcept s t [.x6,.x7,.x10,.x11,.x12,.x28] ∧
      Frame s t (fun A => A=PRIV+16 ∨ A=PRIV+24) := by
  refine ⟨_,symRun_sound blk_295 codeAt_295 s hpc (by simp [blk_295.res,rv_simp]),
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [blk_295.res,E.eval]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp]
  · simp [blk_295.res,rv_simp,MOUT]
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h22]
    rw [ofNat_or_disjoint' 3329 (level*4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 level (by norm_num) (by norm_num) (by norm_num) hlev]
    congr 1; ring
  · simp only [Result.toState_getMem,blk_295.res,PRIV]
    t3n [h23]
    rw [hdr1_eq 0 i (by norm_num) hi]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_295.res,rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem,blk_295.res]
    t3n []
    rw [if_neg (by omega),if_neg (by omega)]

theorem fetch_309 (s : MachineState) (hpc : s.pc = pcOf 309) :
    fetch image s = some (.base .ECALL) := (codeAt_309.fetch s hpc).trans rfl

theorem blk330_spec (s : MachineState) (hpc : s.pc = pcOf 330) (lo level : Nat)
    (hlo : lo ≤ 4096) (hl : level < 12)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 level) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if level+1<12 then pcOf 289 else pcOf 334) ∧
      t.getReg .x20 = BitVec.ofNat 64 (lo/2) ∧ t.getReg .x22 = BitVec.ofNat 64 (level+1) ∧
      RegsExcept s t [.x6,.x20,.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound blk_330 codeAt_330 s hpc (by simp [blk_330.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_330.res,E.eval,CmpOp.eval,h22]
    have hx : (BitVec.ofNat 64 level+1#64).toNat=level+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,BinOp.eval,hx]
    rfl
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h20]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · simp only [Result.toState_getReg,blk_330.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_330.res,rv_simp] <;> rfl
  · intro A _ _; simp [blk_330.res,rv_simp]

theorem blk310_spec (s : MachineState) (hpc : s.pc = pcOf 310)
    (nodep endp i cap : Nat)
    (hn0 : TOP ≤ nodep) (hn : nodep+32 ≤ 0x70000) (hn8 : nodep%8=0)
    (he0 : REGION ≤ endp) (he : endp+32 ≤ 0xA0000) (he8 : endp%8=0)
    (hi : i < 4096) (hc : cap ≤ 4096)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 nodep)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 endp)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 i)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 cap)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 MOUT) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = (if i+1<cap then pcOf 295 else pcOf 330) ∧
      (∀ j : Fin 4, t.getMem (BitVec.ofNat 64 (endp+8*j.val)) =
        s.getMem (BitVec.ofNat 64 (nodep+8*j.val)) ^^^
          s.getMem (BitVec.ofNat 64 (MOUT+8*j.val))) ∧
      t.getReg .x21 = BitVec.ofNat 64 (nodep+32) ∧
      t.getReg .x24 = BitVec.ofNat 64 (endp+32) ∧
      t.getReg .x23 = BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x6,.x7,.x21,.x23,.x24] ∧
      Frame s t (fun A => A=endp ∨ A=endp+8 ∨ A=endp+16 ∨ A=endp+24) := by
  have hobl : Oblig.all s blk_310.res.st.obl := by
    simp only [blk_310.res]
    t3n [h21,h24,h12]
    simp only [TOP,REGION,MOUT] at *
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    norm_num [Nat.add_mod,hn8,he8] <;> omega
  refine ⟨_,symRun_sound blk_310 codeAt_310 s hpc hobl,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,blk_310.res,E.eval,CmpOp.eval,BinOp.eval,h23,h26]
    have hx : (BitVec.ofNat 64 i+1#64).toNat=i+1 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]; omega
    simp only [BitVec.ult,decide_eq_true_eq,hx,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show cap<2^64 by omega)]
  · intro j
    fin_cases j <;> simp only [Fin.val_mk,Nat.reduceMul,Nat.add_zero,
      Result.toState_getMem,blk_310.res,MOUT] <;>
      t3n [h21,h24,h12] <;>
      (simp only [TOP,REGION,MOUT] at *; split_ifs <;> first | rfl | omega)
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h21]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h24]
  · simp only [Result.toState_getReg,blk_310.res]; t3n [h23]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_310.res,rv_simp] <;> rfl
  · intro A hA hnot
    simp only [Result.toState_getMem,blk_310.res]
    t3n [h24]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

end SigGolfCandidate.T3M.Keygen
