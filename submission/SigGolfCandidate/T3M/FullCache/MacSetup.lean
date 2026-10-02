import SigGolfCandidate.T3M.FullCache.MacBlocks

namespace SigGolfCandidate.T3M.FullCache
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- Copy the private seed and form the first private MAC-key query. -/
theorem mac_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg)) :
    ∃ t, Steps (macImage sg) s 23 23 t ∧ t.pc = pcOf (macBase sg + 23) ∧
      t.getReg .x28 = BitVec.ofNat 64 PRIV ∧ t.getReg .x10 = BitVec.ofNat 64 PRIV ∧
      t.getReg .x11 = 64 ∧ t.getReg .x12 = BitVec.ofNat 64 KEYS ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem 0x80 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+8)) = s.getMem 0x88 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+16)) = 3585 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+32)) = s.getMem 0x90 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+40)) = s.getMem 0x98 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+48)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (PRIV+56)) = 0 ∧
      RegsExcept s t [.x6,.x10,.x11,.x12,.x28,.x29] ∧
      Frame s t (fun A => PRIV ≤ A ∧ A < PRIV+64) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_0 (macAt_0 false) s hpc (by simp [macBlkK_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_0.res]
      t3n []
      repeat rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_0 (macAt_0 true) s hpc (by simp [macBlkS_0.res, rv_simp]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_0.res, macBase, PRIV, KEYS, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_0.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_0.res]
      t3n []
      repeat rw [if_neg (by omega)]

/-- Form the second private key query while retaining the first answer. -/
theorem mac_next (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+24))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 PRIV) :
    ∃ t, Steps (macImage sg) s 5 5 t ∧ t.pc = pcOf (macBase sg+29) ∧
      t.getReg .x12 = BitVec.ofNat 64 (KEYS+32) ∧
      t.getMem (BitVec.ofNat 64 (PRIV+24)) = BitVec.ofNat 64 (2^32) ∧
      RegsExcept s t [.x6,.x12] ∧ Frame s t (fun A => A = PRIV+24) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_24 (macAt_24 false) s hpc
      (by simp only [macBlkK_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkK_24.res, macBase, rv_simp]
    · simp [macBlkK_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkK_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkK_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]
  · refine ⟨_, symRun_sound macBlkS_24 (macAt_24 true) s hpc
      (by simp only [macBlkS_24.res]; t3n [h28, PRIV]; norm_num), ?_, ?_, ?_, ?_, ?_⟩
    · simp [macBlkS_24.res, macBase, rv_simp]
    · simp [macBlkS_24.res, KEYS, rv_simp]
    · simp only [Result.toState_getMem, macBlkS_24.res]; t3n [h28, PRIV]
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_24.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [PRIV] at hn
      simp only [Result.toState_getMem, macBlkS_24.res]
      t3n [h28, PRIV]
      rw [if_neg (by omega)]

/-- Initialize the four pure polynomial passes. -/
theorem mac_lanes_init (sg : Bool) (s : MachineState) (hpc : s.pc = pcOf (macBase sg+30)) :
    ∃ t, Steps (macImage sg) s 8 8 t ∧ t.pc = pcOf (macBase sg+38) ∧
      t.getReg .x18 = BitVec.ofNat 64 (2^61-1) ∧
      t.getReg .x19 = BitVec.ofNat 64 REGIONEND ∧
      t.getReg .x22 = BitVec.ofNat 64 KEYS ∧ t.getReg .x25 = BitVec.ofNat 64 (macOut sg) ∧
      RegsExcept s t [.x18,.x19,.x22,.x25] ∧ Frame s t (fun _ => False) := by
  cases sg
  · refine ⟨_, symRun_sound macBlkK_30 (macAt_30 false) s hpc
      (by simp [macBlkK_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkK_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkK_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkK_30.res, rv_simp]
  · refine ⟨_, symRun_sound macBlkS_30 (macAt_30 true) s hpc
      (by simp [macBlkS_30.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp [macBlkS_30.res, macBase, macOut, KEYS, REGIONEND, rv_simp])
      | skip
    · intro r hr; simp at hr; cases r <;> simp_all [macBlkS_30.res, rv_simp] <;> rfl
    · intro A _ _; simp [macBlkS_30.res, rv_simp]

end SigGolfCandidate.T3M.FullCache
