import SigGolfCandidate.T3M.FullCache.MacSetup

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def laneEnd (j : Fin 4) : Nat := if j.val < 3 then 80+42*j.val else 205

theorem mac_pass_at (sg : Bool) (j : Fin 4) :
    CodeAt (macImage sg) (pcOf (macBase sg+38+42*j.val)) MacPass.macPassCode := by
  fin_cases j
  · have h := macAt_38 sg
    rw [macSeg_38_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_80 sg
    rw [macSeg_80_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_122 sg
    rw [macSeg_122_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  · have h := macAt_164 sg
    rw [macSeg_164_pass] at h
    convert h using 1 <;> congr 1 <;> simp only [Fin.val_zero, Fin.val_one] <;> omega

/-- Store one lane and advance the private key-word pointer. -/
theorem mac_store (sg : Bool) (j : Fin 4) (s : MachineState)
    (hpc : s.pc = pcOf (macBase sg+78+42*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg)) :
    ∃ t, Steps (macImage sg) s (if j.val < 3 then 2 else 1) (if j.val < 3 then 2 else 1) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = s.getReg .x14 ∧
      t.getReg .x22 = (if j.val < 3 then s.getReg .x22+16 else s.getReg .x22) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  cases sg
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkK_78 (macAt_78 false) s hpc
        (by simp only [macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_120 (macAt_120 false) s hpc
        (by simp only [macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_162 (macAt_162 false) s hpc
        (by simp only [macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkK_204 (macAt_204 false) s hpc
        (by simp only [macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkK_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkK_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkK_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkK_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
  · fin_cases j
    · refine ⟨_, symRun_sound macBlkS_78 (macAt_78 true) s hpc
        (by simp only [macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_78.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_78.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_78.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_78.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_78.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_120 (macAt_120 true) s hpc
        (by simp only [macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_120.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_120.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_120.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_120.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_120.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_162 (macAt_162 true) s hpc
        (by simp only [macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_162.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_162.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_162.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_162.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_162.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]
    · refine ⟨_, symRun_sound macBlkS_204 (macAt_204 true) s hpc
        (by simp only [macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
      · simp [macBlkS_204.res, macBase, laneEnd, rv_simp]
      · simp only [Result.toState_getMem, macBlkS_204.res]; t3n [h25, macOut, Bool.false_eq_true]
      · simp [macBlkS_204.res, rv_simp]
      · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_204.res, rv_simp] <;> rfl
      · intro A hA hn
        simp only [macOut, Bool.false_eq_true, if_false, if_true, Fin.val_zero, Fin.val_one, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at hn
        simp only [Result.toState_getMem, macBlkS_204.res]
        t3n [h25, macOut, Bool.false_eq_true]
        rw [if_neg (by omega)]

end SigGolfCandidate.T3M.FullCache

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SphincsSecurity (polyMac chunks32)
set_option maxRecDepth 20000

theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]

def laneWord (s : MachineState) (j : Fin 4) (region : List UInt8) : Word :=
  BitVec.ofNat 64 (polyMac ((s.getMem (BitVec.ofNat 64 (KEYS+16*j.val))).toNat % 2^61) (chunks32 region)) +
    s.getMem (BitVec.ofNat 64 (KEYS+16*j.val+8))

def laneRegs : List Reg := [.x13,.x14,.x15,.x16,.x17,.x22,.x23,.x24]

theorem one_lane (sg : Bool) (j : Fin 4) (s : MachineState) (region : List UInt8)
    (hpc : s.pc = pcOf (macBase sg+38+42*j.val))
    (h18 : s.getReg .x18 = BitVec.ofNat 64 (2^61-1))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 REGIONEND)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 (KEYS+16*j.val))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 (macOut sg))
    (hlen : region.length = 131040)
    (hreg : wordsToNat (s.readWords (BitVec.ofNat 64 REGION) 16380) = T3.readLE region) :
    ∃ t, Steps (macImage sg) s (425894+(if j.val<3 then 2 else 1))
        (622454+(if j.val<3 then 2 else 1)) t ∧
      t.pc = pcOf (macBase sg+laneEnd j) ∧
      t.getMem (BitVec.ofNat 64 (macOut sg+8*j.val)) = laneWord s j region ∧
      t.getReg .x22 = (if j.val<3 then BitVec.ofNat 64 (KEYS+16*(j.val+1)) else s.getReg .x22) ∧
      RegsExcept s t laneRegs ∧ Frame s t (fun A => A = macOut sg+8*j.val) := by
  have hj := j.isLt
  obtain ⟨u,hu,upc,u14,ur,um⟩ := MacPass.mac_pass_region (mac_pass_at sg j) s hpc
    (KEYS+16*j.val) region h22 (by simp [KEYS]; omega) (by simp [KEYS]; omega)
    h18 h19 hlen hreg
  have upc' : u.pc = pcOf (macBase sg+78+42*j.val) := by
    rw [upc]; unfold pcOf
    change BitVec.ofNat 64 (4096+4*(macBase sg+38+42*j.val)) + BitVec.ofNat 64 160 = _
    rw [ofNat_add_ofNat]; exact congrArg (BitVec.ofNat 64) (by omega)
  have ur25 : u.getReg .x25 = BitVec.ofNat 64 (macOut sg) := by
    rw [ur .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),h25]
  obtain ⟨t,ht,tpc,tm,t22,tr,tf⟩ := mac_store sg j u upc' ur25
  refine ⟨t,hu.trans ht,tpc,?_,?_,?_,?_⟩
  · rw [tm,u14]; rfl
  · rw [t22,ur .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    split_ifs
    · rw [h22]
      change BitVec.ofNat 64 (KEYS+16*j.val) + BitVec.ofNat 64 16 = _
      rw [ofNat_add_ofNat]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rfl
  · intro r hr
    have hr' : r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x24 := by simpa [laneRegs] using hr
    rw [tr.get (by simpa using hr'.2.2.2.2.2.1)]
    exact ur r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2.1 hr'.2.2.2.2.2.2.1 hr'.2.2.2.2.2.2.2
  · intro A hA hn; rw [tf.get hA hn,um]

end SigGolfCandidate.T3M.FullCache
