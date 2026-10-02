import SigGolfCandidate.T3M.Sign.Basic

/-!
# Sign: block specifications of the front (words 0..152)

`start` saves the old tag and jumps to the shared two-key polynomial MAC routine.
Words47..62 compare its four words with the saved tag;63..121 build the nonce input;
122queries the nonce, and123..152 copy rho and the message into the digest-search buffer.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)

/-- Save the four tag words, then enter the shared polynomial MAC routine. -/
theorem blk0_spec (s : MachineState) (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 17 17 t ∧ t.pc = pcOf 1227 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 TAG) = s.getMem (BitVec.ofNat 64 CACHE) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 8)) = s.getMem (BitVec.ofNat 64 (CACHE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 16)) = s.getMem (BitVec.ofNat 64 (CACHE + 16)) ∧
      t.getMem (BitVec.ofNat 64 (TAG + 24)) = s.getMem (BitVec.ofNat 64 (CACHE + 24)) ∧
      RegsExcept s t [.x5, .x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => (TAG ≤ A ∧ A < TAG + 32) ∨ (MACBLK ≤ A ∧ A < MACBLK + 64)) := by
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc (by simp [blk_0.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_0.res, E.eval]
  · simp [blk_0.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_0.res, TAG, CACHE, MACBLK, SK]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [TAG, MACBLK] at hn
    simp only [Result.toState_getMem, blk_0.res]
    t3n []
    repeat rw [if_neg (by omega)]

/-- Return from the shared MAC to the existing four-word comparison chain. -/
theorem blk1432_spec (s : MachineState) (hpc : s.pc = pcOf 1432) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 47 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1432 codeAt_1432 s hpc (by simp [blk_1432.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [blk_1432.res, E.eval]
  · intro r hr; cases r <;> simp [blk_1432.res, rv_simp] <;> rfl
  · intro A hA hn; simp [blk_1432.res, rv_simp]

theorem fetch_46 (s : MachineState) (hpc : s.pc = pcOf 46) : fetch image s = some (.base .ECALL) :=
  (codeAt_46.fetch s hpc).trans rfl

theorem blk47_spec (s : MachineState) (hpc : s.pc = pcOf 47) :
    ∃ t, Steps image s 7 7 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 MACOUT) = s.getMem (BitVec.ofNat 64 TAG) then pcOf 54
        else pcOf 543) ∧
      t.getReg .x28 = BitVec.ofNat 64 MACOUT ∧ t.getReg .x29 = BitVec.ofNat 64 TAG ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_47 codeAt_47 s hpc (by simp [blk_47.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_47.res, E.eval, CmpOp.eval, MACOUT, TAG]
    t3n []
    split_ifs <;> simp_all
  · simp [blk_47.res, rv_simp]
  · simp [blk_47.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_47.res, rv_simp]

/-- Compare doubleword `k` (`k = 1, 2, 3`, blocks 54, 57, 60) with `t3 = MACOUT`, `t4 = TAG`. -/
theorem cmp_next_spec {a k : Nat} {seg : List (BitVec 32)} {r : Result}
    (hc : CodeAt image (pcOf a) seg) (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r)
    (s : MachineState) (hpc : s.pc = pcOf a)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG)
    (hobl : r.obligs s)
    (hpcE : (r.toState s).pc = if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (TAG + 8 * k)) then pcOf (a + 3) else pcOf 543)
    (hregs : RegsExcept s (r.toState s) [.x6, .x7]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps image s r.steps r.cycles t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * k)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * k))
        then pcOf (a + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, hregs, hfr⟩

theorem blk54_spec (s : MachineState) (hpc : s.pc = pcOf 54)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 1)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 1))
        then pcOf (54 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_54 blk_54 s hpc h28 h29 (by simp only [blk_54.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_54.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_54.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_54.res, rv_simp])

theorem blk57_spec (s : MachineState) (hpc : s.pc = pcOf 57)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 2)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 2))
        then pcOf (57 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_57 blk_57 s hpc h28 h29 (by simp only [blk_57.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_57.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_57.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_57.res, rv_simp])

theorem blk60_spec (s : MachineState) (hpc : s.pc = pcOf 60)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 MACOUT) (h29 : s.getReg .x29 = BitVec.ofNat 64 TAG) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if s.getMem (BitVec.ofNat 64 (MACOUT + 8 * 3)) = s.getMem (BitVec.ofNat 64 (TAG + 8 * 3))
        then pcOf (60 + 3) else pcOf 543) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) :=
  cmp_next_spec codeAt_60 blk_60 s hpc h28 h29 (by simp only [blk_60.res]; t3n [h28, h29, MACOUT, TAG] <;> norm_num)
    (by simp only [Result.toState_pc, blk_60.res, E.eval, CmpOp.eval, MACOUT, TAG]; t3n [h28, h29]
        split_ifs <;> simp_all)
    (by intro r hr; simp at hr; cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_60.res, rv_simp])

/-- 63..121: the private prefix at `PRIV`, the nonce block at `NONCE`, the nonce HASH arguments. -/
theorem blk63_spec (s : MachineState) (hpc : s.pc = pcOf 63) :
    ∃ t, Steps image s 59 59 t ∧ t.pc = pcOf 122 ∧
      t.getReg .x10 = BitVec.ofNat 64 NONCE ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 RHOOUT ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 NONCE) = s.getMem (BitVec.ofNat 64 SK) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 8)) = s.getMem (BitVec.ofNat 64 (SK + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 16)) = BitVec.ofNat 64 1793 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 32)) = s.getMem (BitVec.ofNat 64 (SK + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 40)) = s.getMem (BitVec.ofNat 64 (SK + 24)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (NONCE + 56)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 64)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 72)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 80)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NONCE + 88)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨
        A = PRIV + 56 ∨ (NONCE ≤ A ∧ A < NONCE + 96)) := by
  refine ⟨_, symRun_sound blk_63 codeAt_63 s hpc (by simp [blk_63.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_63.res, E.eval]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  · simp [blk_63.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_63.res, PRIV, NONCE, SK, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_63.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV, NONCE] at hn
    simp only [Result.toState_getMem, blk_63.res]
    t3n []
    repeat rw [if_neg (by omega)]

theorem fetch_122 (s : MachineState) (hpc : s.pc = pcOf 122) : fetch image s = some (.base .ECALL) :=
  (codeAt_122.fetch s hpc).trans rfl

/-- 123..152: `rho` to `SIG` and `DIG`, `m` to `DIG + 32`, `I := 0`. -/
theorem blk123_spec (s : MachineState) (hpc : s.pc = pcOf 123) :
    ∃ t, Steps image s 30 30 t ∧ t.pc = pcOf 153 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 SIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (SIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 RHOOUT) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 (RHOOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 MSG) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 (MSG + 8)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 (MSG + 16)) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 (MSG + 24)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = SIG ∨ A = SIG + 8 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound blk_123 codeAt_123 s hpc (by simp [blk_123.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_123.res, E.eval]
  · simp [blk_123.res, rv_simp]
  all_goals first
    | (simp only [Result.toState_getMem, blk_123.res, SIG, DIG, RHOOUT, MSG]; t3n [])
    | skip
  · intro r hr; simp at hr; cases r <;> simp_all [blk_123.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [SIG, DIG] at hn
    simp only [Result.toState_getMem, blk_123.res]
    t3n []
    repeat rw [if_neg (by omega)]

end SigGolfCandidate.T3M.Sign
