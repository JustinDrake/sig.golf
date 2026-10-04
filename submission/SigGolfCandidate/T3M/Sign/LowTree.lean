import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Sign.TopBlocks
import SigGolfCandidate.T3M.Sign.Frontier
import SigGolfCandidate.T3M.Sign.BaseInv
import SigGolfCandidate.T3M.Sign.TopLeaf
import SigGolfCandidate.T3M.Keygen.Tree
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
theorem blk357_spec (s : MachineState) (hpc : s.pc = pcOf 357) (idx : Nat)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 369 ∧
      t.getReg .x10 = BitVec.ofNat 64 FOREST ∧ t.getReg .x11 = BitVec.ofNat 64 128 ∧
      t.getReg .x12 = BitVec.ofNat 64 FOUT ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 16)) = BitVec.ofNat 64 2817 ∧
      t.getMem (BitVec.ofNat 64 (FOREST + 24)) = BitVec.ofNat 64 idx ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧
      Frame s t (fun A => A = FOREST + 16 ∨ A = FOREST + 24) := by
  refine ⟨_, symRun_sound blk_357 codeAt_357 s hpc (by simp [blk_357.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_357.res, E.eval]
  · simp [blk_357.res, rv_simp]
  · simp [blk_357.res, rv_simp]
  · simp [blk_357.res, rv_simp]
  · simp only [Result.toState_getMem, blk_357.res, FOREST]; t3n []
  · simp only [Result.toState_getMem, blk_357.res, FOREST]; t3n [h9]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_357.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [FOREST] at hn
    simp only [Result.toState_getMem, blk_357.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_369 (s : MachineState) (hpc : s.pc = pcOf 369) : fetch image s = some (.base .ECALL) :=
  (codeAt_369.fetch s hpc).trans rfl
theorem blk370_spec (s : MachineState) (hpc : s.pc = pcOf 370) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 396 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      t.getReg .x2 = BitVec.ofNat 64 LOW ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4832) ∧ t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 64) ∧
      RegsExcept s t [.x1, .x2, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x26, .x27, .x28, .x29, .x30,
        .x31] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 0 &&& 63#64) = BitVec.ofNat 64 (x % 64) := by
    intro x hx
    rw [ofNat_shr x 0 hx, pow_zero, Nat.div_one]
    exact ofNat_and_mask x 6 (by norm_num)
  refine ⟨_, symRun_sound blk_370 codeAt_370 s hpc (by simp [blk_370.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_370.res, E.eval]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp only [Result.toState_getMem, blk_370.res, ENC, FOUT]; t3n []
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp [blk_370.res, rv_simp]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_370.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 6 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_370.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_370.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem blkBT_spec {a : Nat} {seg : List (BitVec 32)} {r : Result} (hc : CodeAt image (pcOf a) seg)
    (hrun : symRun { noAlias := true } seg (pcOf a) 100 = some r) (s : MachineState) (hpc : s.pc = pcOf a)
    (hobl : r.obligs s) (hpcE : (r.toState s).pc = pcOf 1173) (h1 : (r.toState s).getReg .x1 = pcOf (a + 1))
    (hregs : RegsExcept s (r.toState s) [.x1]) (hfr : Frame s (r.toState s) (fun _ => False)) :
    ∃ t, Steps image s r.steps r.cycles t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf (a + 1) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  ⟨_, symRun_sound hrun hc s hpc hobl, hpcE, h1, hregs, hfr⟩
theorem blk396_spec (s : MachineState) (hpc : s.pc = pcOf 396) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 397 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_396 blk_396 s hpc (by simp [blk_396.res, rv_simp]) (by simp [blk_396.res, E.eval])
    (by simp [blk_396.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_396.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_396.res, rv_simp])
theorem blk411_spec (s : MachineState) (hpc : s.pc = pcOf 411) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 412 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_411 blk_411 s hpc (by simp [blk_411.res, rv_simp]) (by simp [blk_411.res, E.eval])
    (by simp [blk_411.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_411.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_411.res, rv_simp])
theorem blk426_spec (s : MachineState) (hpc : s.pc = pcOf 426) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1173 ∧ t.getReg .x1 = pcOf 427 ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) :=
  blkBT_spec codeAt_426 blk_426 s hpc (by simp [blk_426.res, rv_simp]) (by simp [blk_426.res, E.eval])
    (by simp [blk_426.res, rv_simp]) (by intro r hr; simp at hr; cases r <;> simp_all [blk_426.res, rv_simp] <;> rfl)
    (by intro A _ _; simp [blk_426.res, rv_simp])
theorem blk397_spec (s : MachineState) (hpc : s.pc = pcOf 397) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 411 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4048) ∧ t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 64 % 64) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 64 % 64) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 4096) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 6 &&& 63#64) = BitVec.ofNat 64 (x / 64 % 64) := by
    intro x hx
    rw [ofNat_shr x 6 hx]
    exact ofNat_and_mask (x / 2 ^ 6) 6 (by norm_num)
  refine ⟨_, symRun_sound blk_397 codeAt_397 s hpc (by simp [blk_397.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_397.res, E.eval]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp [blk_397.res, rv_simp]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_397.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 12 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_397.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_397.res, rv_simp]
theorem blk412_spec (s : MachineState) (hpc : s.pc = pcOf 412) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 426 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 3248) ∧ t.getReg .x17 = BitVec.ofNat 64 196 ∧
      t.getReg .x18 = BitVec.ofNat 64 (idx / 4096 % 128) ∧ t.getReg .x14 = BitVec.ofNat 64 (idx / 4096 % 128) ∧
      t.getReg .x9 = BitVec.ofNat 64 (idx / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x18, .x28] ∧
      Frame s t (fun _ => False) := by
  have hand : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x >>> 12 &&& 127#64) = BitVec.ofNat 64 (x / 4096 % 128) := by
    intro x hx
    rw [ofNat_shr x 12 hx]
    exact ofNat_and_mask (x / 2 ^ 12) 7 (by norm_num)
  refine ⟨_, symRun_sound blk_412 codeAt_412 s hpc (by simp [blk_412.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_412.res, E.eval]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp [blk_412.res, rv_simp]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, hand idx (by omega)]
  · simp only [Result.toState_getReg, blk_412.res]; t3n []
    rw [show (132432#64 : Word) = BitVec.ofNat 64 IDXV from rfl, hm, ofNat_shr idx 19 (by omega)]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [blk_412.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_412.res, rv_simp]
theorem blk1173_spec (s : MachineState) (hpc : s.pc = pcOf 1173) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x4 = s.getReg .x1 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x4, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1173 codeAt_1173 s hpc (by simp [blk_1173.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1173.res, E.eval]
  · simp [blk_1173.res, rv_simp]
  · simp [blk_1173.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1173.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1173.res, rv_simp]
theorem blk1175_spec (s : MachineState) (hpc : s.pc = pcOf 1175) (l h : Nat) (hl : l < 2 ^ 63) (hh : h ≤ 12)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if l < 2 ^ h then pcOf 1178 else pcOf 1193) ∧
      t.getReg .x6 = BitVec.ofNat 64 (2 ^ h) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1175 codeAt_1175 s hpc (by simp [blk_1175.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1175.res, E.eval, CmpOp.eval, BinOp.eval, h13, h15, e,
      ofNat_slt l (2 ^ h) hl (by omega)]
    by_cases hc : l < 2 ^ h <;> simp [hc]
  · simp only [Result.toState_getReg, blk_1175.res, rv_simp, BinOp.eval, h15, e]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1175.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1175.res, rv_simp]
theorem blk1178_spec (s : MachineState) (hpc : s.pc = pcOf 1178) (l sel : Nat) (hl : l < 2 ^ 64)
    (hsel : sel < 2 ^ 64) (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if l = sel then pcOf 1184 else pcOf 1187) ∧
      t.getReg .x18 = BitVec.ofNat 64 l ∧ t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧ RegsExcept s t [.x18, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1178 codeAt_1178 s hpc (by simp [blk_1178.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1178.res, E.eval, CmpOp.eval, h13, h14]
    by_cases hc : l = sel
    · subst hc; simp
    · rw [if_neg hc]
      have : BitVec.ofNat 64 l ≠ BitVec.ofNat 64 sel := fun he => hc ((ofNat_inj hl hsel).mp he)
      simp [this]
  · simp only [Result.toState_getReg, blk_1178.res]; t3n [h13]
  · simp [blk_1178.res, rv_simp]
  · simp [blk_1178.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1178.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1178.res, rv_simp]
theorem blk1184_spec (s : MachineState) (hpc : s.pc = pcOf 1184) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1187 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = s.getReg .x16 ∧ RegsExcept s t [.x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1184 codeAt_1184 s hpc (by simp [blk_1184.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1184.res, E.eval]
  · simp [blk_1184.res, rv_simp]
  · simp [blk_1184.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1184.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1184.res, rv_simp]
theorem blk1187_spec (s : MachineState) (hpc : s.pc = pcOf 1187) (l h ar : Nat) (hl : l < 2 ^ h)
    (hh : h ≤ 12) (har : ar + 16 * 8192 < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h6 : s.getReg .x6 = BitVec.ofNat 64 (2 ^ h))
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (1013 + 27) ∧ t.getReg .x1 = pcOf 1191 ∧
      t.getReg .x25 = BitVec.ofNat 64 (ar + 16 * (2 ^ h + l)) ∧
      RegsExcept s t [.x1, .x7, .x25] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  refine ⟨_, symRun_sound blk_1187 codeAt_1187 s hpc (by simp [blk_1187.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1187.res, E.eval]
  · simp [blk_1187.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1187.res]; t3n [h13, h6, h2]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1187.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1187.res, rv_simp]
theorem blk1191_spec (s : MachineState) (hpc : s.pc = pcOf 1191) (l : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1191 codeAt_1191 s hpc (by simp [blk_1191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_1191.res, E.eval]
  · simp only [Result.toState_getReg, blk_1191.res]; t3n [h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1191.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1191.res, rv_simp]
theorem blk1193_spec (s : MachineState) (hpc : s.pc = pcOf 1193) (lay : Nat) (hlay : lay < 256)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (1013 + 113) ∧ t.getReg .x1 = pcOf 1196 ∧
      t.getReg .x21 = BitVec.ofNat 64 (769 + 65536 * lay) ∧
      RegsExcept s t [.x1, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1193 codeAt_1193 s hpc (by simp [blk_1193.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1193.res, E.eval]
  · simp [blk_1193.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1193.res]
    t3n [h8]
    rw [show (769#64 : Word) = BitVec.ofNat 64 769 from rfl,
      ofNat_or_disjoint 769 (lay * 65536) 16 (by norm_num) (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1193.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1193.res, rv_simp]
theorem blk1196_spec (s : MachineState) (hpc : s.pc = pcOf 1196) (h sel sb n : Nat) (hh : h ≤ 12)
    (hsel : sel < 4096) (hsb : sb + 16 * n < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 sel)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 sb) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      t.getReg .x19 = BitVec.ofNat 64 (2 ^ h + sel) ∧ t.getReg .x24 = BitVec.ofNat 64 (sb + 16 * n) ∧
      RegsExcept s t [.x6, .x7, .x13, .x19, .x24] ∧ Frame s t (fun _ => False) := by
  have hp : 2 ^ h ≤ 4096 := by
    calc 2 ^ h ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hh
      _ = 4096 := by norm_num
  have e : (1#64 : Word) <<< ((BitVec.ofNat 64 h).toNat % 64) = BitVec.ofNat 64 (2 ^ h) := by
    rw [toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega), show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_shl, Nat.one_mul]
  refine ⟨_, symRun_sound blk_1196 codeAt_1196 s hpc (by simp [blk_1196.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1196.res, E.eval]
  · simp [blk_1196.res, rv_simp]
  · simp only [Result.toState_getReg, blk_1196.res, rv_simp, BinOp.eval, h15, h14, e, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, blk_1196.res]; t3n [h16, h26]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1196.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1196.res, rv_simp]
theorem blk1202_spec (s : MachineState) (hpc : s.pc = pcOf 1202) (l h : Nat) (hl : l < 2 ^ 63) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if l < h then pcOf 1203 else pcOf 1214) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1202 codeAt_1202 s hpc (by simp [blk_1202.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1202.res, E.eval, CmpOp.eval, h13, h15, ofNat_slt l h hl hh]
    by_cases hc : l < h <;> simp [hc]
  · intro r hr; cases r <;> simp_all [blk_1202.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1202.res, rv_simp]
theorem blk1203_spec (s : MachineState) (hpc : s.pc = pcOf 1203) (l hi ar ep : Nat) (hl : l < 64)
    (hhi : hi < 8192) (har : ar + 16 * 8192 ≤ 2 ^ 24) (har8 : ar % 8 = 0) (hep : ep + 16 ≤ 2 ^ 24)
    (hep8 : ep % 8 = 0)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h19 : s.getReg .x19 = BitVec.ofNat 64 hi)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h24 : s.getReg .x24 = BitVec.ofNat 64 ep) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 1202 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      t.getReg .x24 = BitVec.ofNat 64 (ep + 16) ∧
      t.getMem (BitVec.ofNat 64 ep) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (ep + 8)) = s.getMem (BitVec.ofNat 64 (ar + 16 * (hi / 2 ^ l ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x13, .x24, .x28] ∧ Frame s t (fun A => A = ep ∨ A = ep + 8) := by
  have hd : hi / 2 ^ l < 8192 := lt_of_le_of_lt (Nat.div_le_self _ _) hhi
  have hx : hi / 2 ^ l ^^^ 1 < 8192 := Nat.xor_lt_two_pow (n := 13) hd (by norm_num)
  have e1 : BitVec.ofNat 64 hi >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64 =
      BitVec.ofNat 64 (hi / 2 ^ l ^^^ 1) := by
    rw [toNat_mod64 l hl, ofNat_shr hi l (by omega), ofNat_xor1 _ (by omega)]
  have hobl : Oblig.all s blk_1203.res.st.obl := by
    simp only [blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    omega
  refine ⟨_, symRun_sound blk_1203 codeAt_1203 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1203.res, E.eval]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h13]
  · simp only [Result.toState_getReg, blk_1203.res]; t3n [h24]
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · simp only [Result.toState_getMem, blk_1203.res]
    simp only [rv_simp, h13, h19, h2, h24, e1]
    t3n []
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1203.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_1203.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]
theorem blk1214_spec (s : MachineState) (hpc : s.pc = pcOf 1214) (ar : Nat) (har : ar + 64 ≤ 2 ^ 24)
    (har8 : ar % 8 = 0) (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = pcOf 10947 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getReg .x30 = BitVec.ofNat 64 ENC ∧
      RegsExcept s t [.x6, .x7, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  have hobl : Oblig.all s blk_1214.res.st.obl := by
    simp only [blk_1214.res]
    t3n [h2]
    omega
  refine ⟨_, symRun_sound blk_1214 codeAt_1214 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1214.res, rv_simp]
  · simp only [Result.toState_getMem, blk_1214.res, ENC]; t3n [h2]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · simp only [Result.toState_getMem, blk_1214.res, ENC]; t3n [h2]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · simp [Result.toState_getReg, blk_1214.res, rv_simp, ENC]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1214.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_1214.res]
    t3n [h2]
    rw [if_neg (by omega), if_neg (by omega)]
theorem blk2074_spec (s : MachineState) (hpc : s.pc = pcOf 10947) (ar ret : Nat) (har : ar + 64 ≤ 2 ^ 24)
    (har8 : ar % 8 = 0) (hsep : ENC + 64 ≤ ar) (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 ENC) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun A => A = ENC + 48 ∨ A = ENC + 56) := by
  simp only [ENC] at hsep
  have hobl : Oblig.all s blk_2074.res.st.obl := by
    simp only [blk_2074.res]
    t3n [h2, h30, ENC, h4]
    exact ⟨⟨by norm_num, trivial⟩, ⟨by norm_num, trivial⟩, ⟨by omega, by omega⟩, by omega, by omega⟩
  refine ⟨_, symRun_sound blk_2074 codeAt_2074 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_2074.res, rv_simp, h4, pcOf_and_max]
  · simp only [Result.toState_getMem, blk_2074.res, ENC]; t3n [h2, h30, ENC]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · simp only [Result.toState_getMem, blk_2074.res, ENC]; t3n [h2, h30, ENC]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · intro r hr; simp at hr; cases r <;> simp_all [blk_2074.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_2074.res]
    t3n [h2, h30, ENC]
    rw [if_neg (by omega), if_neg (by omega)]
theorem blk1214_full (s : MachineState) (hpc : s.pc = pcOf 1214) (ar ret : Nat) (har : ar + 64 ≤ 2 ^ 24)
    (har8 : ar % 8 = 0) (hsep : ENC + 64 ≤ ar) (h2 : s.getReg .x2 = BitVec.ofNat 64 ar)
    (h4 : s.getReg .x4 = pcOf ret) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 40)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (ar + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (ar + 56)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨t1, st1, p1, m0, m8, x30, r1, f1⟩ := blk1214_spec s hpc ar har har8 h2
  obtain ⟨t2, st2, p2, m48, m56, r2, f2⟩ := blk2074_spec t1 p1 ar ret har har8 hsep
    (by rw [r1.get (by decide), h2]) (by rw [r1.get (by decide), h4]) x30
  refine ⟨t2, st1.trans st2, p2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), m0]
  · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), m8]
  · rw [m48, f1.get (by omega) (by simp only [ENC] at hsep ⊢; omega)]
  · rw [m56, f1.get (by omega) (by simp only [ENC] at hsep ⊢; omega)]
  · exact (r1.trans r2).mono (by decide)
  · exact (f1.trans f2).mono (fun A _ h => by rcases h with (h | h) | (h | h) <;> simp [h])
end SigGolfCandidate.T3M.Sign
end
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest buildLeaf buildLevels buildTree height chainCount width)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION
  LeafArgs LeafPre LeafW leafRegs LevArgs LevPre HeapAt LevW levRegs n4 buildLeaf_tsim buildLevels_tsim)
def btLeaf (lay : Layer) (tree sel : Nat) (ds : List Nat) (sb l : Nat) : LeafArgs :=
  ⟨lay, tree, l, if l = sel then ds else [], false, if l = sel then DIGITS else ZDIG,
    if l = sel then sb else DUMMY, LOW + 16 * (2 ^ height lay + l), 1191⟩
theorem btLeaf_costs (lay : Layer) (hlay : lay ≠ 0) (tree sel : Nat) (ds : List Nat) (sb l : Nat) :
    (btLeaf lay tree sel ds sb l).leafK = (if lay = 1 then 13800 else 14101) ∧
    (btLeaf lay tree sel ds sb l).leafC = (if lay = 1 then 16148 else 16449) ∧
    (btLeaf lay tree sel ds sb l).leafN = 324 ∧ (btLeaf lay tree sel ds sb l).leafB = 334 := by
  have e : (btLeaf lay tree sel ds sb l).leafK = (btLeaf lay 0 0 [] 0 1).leafK ∧
      (btLeaf lay tree sel ds sb l).leafC = (btLeaf lay 0 0 [] 0 1).leafC ∧
      (btLeaf lay tree sel ds sb l).leafN = (btLeaf lay 0 0 [] 0 1).leafN ∧
      (btLeaf lay tree sel ds sb l).leafB = (btLeaf lay 0 0 [] 0 1).leafB := ⟨rfl, rfl, rfl, rfl⟩
  rw [e.1, e.2.1, e.2.2.1, e.2.2.2]
  fin_cases lay
  · exact absurd rfl hlay
  all_goals decide
theorem chainCount_low {lay : Layer} (h : lay ≠ 0) : chainCount lay = 43 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals rfl
theorem n4_low {lay : Layer} (h : lay ≠ 0) : n4 lay = 0 := by simp [n4, h]
theorem height_low {lay : Layer} (h : lay ≠ 0) : height lay = 6 ∨ height lay = 7 := by
  fin_cases lay
  · exact absurd rfl h
  all_goals simp [height]
structure BtPre (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel : Nat) (ds : List Nat)
    (sb : Nat) (s : MachineState) : Prop where
  x2 : s.getReg .x2 = BitVec.ofNat 64 LOW
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x14 : s.getReg .x14 = BitVec.ofNat 64 sel
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 sb
  x26 : s.getReg .x26 = BitVec.ofNat 64 43
  x27 : s.getReg .x27 = BitVec.ofNat 64 0
  x31 : s.getReg .x31 = BitVec.ofNat 64 0
  base : BaseL sk cache s
  hlay : lay ≠ 0
  htree : tree < 2 ^ 32
  hroute : ∀ l < 2 ^ height lay, tree * 2 ^ height lay + l < 2 ^ 31
  hsel : sel < 2 ^ height lay
  hdb : ∀ i < 43, ds.getD i 0 ≤ 7
  digits : ∀ i < 43, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)
  hsb : SIG ≤ sb ∧ sb + 16 * (43 + height lay) ≤ SIG + 5616
  hsb8 : sb % 8 = 0
def BtW (sb H : Nat) (X : Nat) : Prop :=
  X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
    (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * 44) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
    (DUMMY ≤ X ∧ X < DUMMY + 16 * 43) ∨ (sb ≤ X ∧ X < sb + 16 * 43) ∨
    (LOW + 16 * 2 ^ H ≤ X ∧ X < LOW + 16 * 2 ^ (H + 1))
def btRegs : List Reg := leafRegs ++ [.x6, .x13, .x18, .x22, .x23, .x25]
structure BtInv (s1 : MachineState) (sb sel H l : Nat) (st : List Digest × List Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf 1175
  x13 : t.getReg .x13 = BitVec.ofNat 64 l
  regs : RegsExcept s1 t btRegs
  frame : Frame s1 t (BtW sb H)
  len : st.1.length = l
  roots : DigsAt t (LOW + 16 * 2 ^ H) st.1
  vals : sel < l → st.2.length = 43 ∧ DigsAt t sb st.2
theorem extractByte_zero' (k : Nat) : extractByte (0 : Word) k = 0 := by
  simp [extractByte]
def btBody (lay : Layer) (tree sel : Nat) (ds : List Nat) (state : List Digest × List Digest) (leaf : Nat) :
    T3.M (List Digest × List Digest) := do
  let (root, values) ← buildLeaf lay tree leaf (if leaf = sel then ds else [])
  pure (state.1 ++ [root], if leaf = sel then values else state.2)
theorem buildTree_eq (lay : Layer) (tree sel : Nat) (ds : List Nat) : buildTree lay tree sel ds = (do
    let state ← (List.range (2 ^ height lay)).foldlM (btBody lay tree sel ds) ([], [])
    let levels ← buildLevels 3 lay.val tree (height lay) state.1
    pure (levels, state.2)) := rfl
section loop
variable {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat} {sb : Nat}
  {s1 : MachineState} (hs : BtPre sk cache lay tree sel ds sb s1)
include hs
theorem bt_leafPre {l : Nat} (hl : l < 2 ^ height lay) {t : MachineState}
    (hr : RegsExcept s1 t (btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25])) (hf : Frame s1 t (BtW sb (height lay)))
    (h1 : t.getReg .x1 = pcOf 1191) (h18 : t.getReg .x18 = BitVec.ofNat 64 l)
    (h22 : t.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG))
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 (LOW + 16 * (2 ^ height lay + l))) :
    LeafPreS sk t (btLeaf lay tree sel ds sb l) := by
  have hlay := hs.hlay
  have hn : (btLeaf lay tree sel ds sb l).n = 43 := chainCount_low hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs ++ [.x1, .x4, .x6, .x7, .x18, .x22, .x23, .x25] → t.getReg r = s1.getReg r :=
    fun r hr' => hr.get hr'
  have m : ∀ X, X < 2 ^ 64 → ¬ BtW sb (height lay) X → t.getMem (BitVec.ofNat 64 X) = s1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn' => hf.get hX hn'
  have hz : ∀ X, X < 2 ^ 64 → NeverWL X → t.getMem (BitVec.ofNat 64 X) = 0 := fun X hX hnw =>
    (m X hX (by unfold NeverWL at hnw; unfold BtW; rcases hH with h | h <;> rw [h] <;> sgo)).trans
      (hs.base.zero X hX hnw)
  refine
    { x1 := h1
      x5 := by rw [g _ (by decide), hs.base.x5]
      x8 := by rw [g _ (by decide), hs.x8]; rfl
      x9 := by rw [g _ (by decide), hs.x9]; rfl
      x18 := h18
      x22 := h22
      x23 := h23
      x25 := h25
      x26 := by rw [g _ (by decide), hs.x26, hn]
      x27 := by rw [g _ (by decide), hs.x27]; show _ = BitVec.ofNat 64 (n4 lay); rw [n4_low hlay]
      x31 := by rw [g _ (by decide), hs.x31]; rfl
      htree := hs.htree
      hleaf := by show l < 2 ^ 32; omega
      hroute := hs.hroute l hl
      hleafHeight := hl
      hsteps := fun i _ => by change T3.maxDigit lay i ≤ 8; simp [T3.maxDigit, hlay]
      p0 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p0]
      p8 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p8]
      p32 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p32]
      p40 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p40]
      p48 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p48]
      p56 := by rw [m _ (by decide) (by unfold BtW; sgo), hs.base.p56]
      z0 := hz _ (by decide) (by unfold NeverWL; simp)
      z8 := hz _ (by decide) (by unfold NeverWL; simp)
      z32 := hz _ (by decide) (by unfold NeverWL; simp)
      z40 := hz _ (by decide) (by unfold NeverWL; simp)
      ztail := fun h => by rw [hn] at h; exact absurd h (by norm_num)
      hdig := fun i hi => by
        rw [hn] at hi
        show t.getByte (BitVec.ofNat 64 ((if l = sel then DIGITS else ZDIG) + i)) =
          BitVec.ofNat 8 ((if l = sel then ds else []).getD i 0)
        by_cases hls : l = sel
        · simp only [hls, if_true]
          rw [hf.getByte (by sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> sgo)]
          exact hs.digits i hi
        · simp only [hls, if_false, List.getD_nil]
          rw [hf.getByte (by sgo) (by unfold BtW; rcases hH with h | h <;> rw [h] <;> sgo),
            getByte_eq_word s1 _ (by sgo), hs.base.zero _ (by sgo) (by unfold NeverWL; sgo), extractByte_zero']
          rfl
      hdigb := fun i hi => by
        rw [hn] at hi
        show (if l = sel then ds else []).getD i 0 < 256 ∧
          (false = false → (if l = sel then ds else []).getD i 0 ≤ T3.maxDigit lay i)
        have hw : T3.maxDigit lay i = 7 := by simp [T3.maxDigit, hlay]
        rw [hw]
        by_cases hls : l = sel
        · simp only [hls, if_true]; have := hs.hdb i hi; omega
        · simp [hls]
      hdigp := by show (if l = sel then DIGITS else ZDIG) + (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
                  rw [hn]; split_ifs <;> sgo
      hdigW := fun i hi => by
        rw [hn] at hi
        show ¬ LeafW (btLeaf lay tree sel ds sb l) (((if l = sel then DIGITS else ZDIG) + i) / 8 * 8)
        unfold LeafW
        show ¬ (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ (LEAFPK ≤ _ ∧ _ < LEAFPK + 16 * ((btLeaf lay tree sel ds sb l).n + 1)) ∨ _ ∨
          ((if l = sel then sb else DUMMY) ≤ _ ∧ _ < (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ _ ∧ _ < LOW + 16 * (2 ^ height lay + l) + 16))
        rw [hn]
        split_ifs <;> sgo
      hv8 := by show (if l = sel then sb else DUMMY) % 8 = 0; split_ifs; exact hs.hsb8; decide
      hv := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ 2 ^ 24
        rw [hn]; split_ifs <;> sgo
      hvs := by
        show (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ PRIV ∨
          LEAFPK + 960 ≤ (if l = sel then sb else DUMMY)
        rw [hn]; split_ifs
        · left; sgo
        · right; decide
      hd8 := fun _ => by show (LOW + 16 * (2 ^ height lay + l)) % 8 = 0; sgo
      hd := by show LOW + 16 * (2 ^ height lay + l) + 16 ≤ 2 ^ 24; sgo
      hds := Or.inr (Or.inl (by show LEAFPK + 960 ≤ LOW + 16 * (2 ^ height lay + l); sgo))
      hdv := by
        show LOW + 16 * (2 ^ height lay + l) + 16 ≤ (if l = sel then sb else DUMMY) ∨
          (if l = sel then sb else DUMMY) + 16 * (btLeaf lay tree sel ds sb l).n ≤ LOW + 16 * (2 ^ height lay + l)
        rw [hn]; right; split_ifs <;> sgo }
theorem bt_body {l : Nat} (hl : l < 2 ^ height lay) {st : List Digest × List Digest} {t : MachineState}
    (ht : BtInv s1 sb sel (height lay) l st t) :
    TSim image sk t ((if lay = 1 then 13815 else 14116) + (if l = sel then 3 else 0))
      ((if lay = 1 then 16163 else 16464) + (if l = sel then 3 else 0)) 324 334
      (btBody lay tree sel ds st l) (BtInv s1 sb sel (height lay) (l + 1)) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsb := hs.hsb
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1x6, t1r, t1f⟩ := blk1175_spec t ht.pc l (height lay) (by omega)
    (by rcases hH with h | h <;> omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_pos hl] at t1pc
  obtain ⟨t2, st2, t2pc, t2x18, t2x22, t2x23, t2r, t2f⟩ := blk1178_spec t1 t1pc l sel (by omega)
    (by have := hs.hsel; omega) (by rw [t1r.get (by simp)]; exact ht.x13)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x14])
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x22, t3x23, t3r, t3f⟩ : ∃ t3 k3, Steps image t2 k3 k3 t3 ∧
      k3 = (if l = sel then 3 else 0) ∧ t3.pc = pcOf 1187 ∧
      t3.getReg .x22 = BitVec.ofNat 64 (if l = sel then DIGITS else ZDIG) ∧
      t3.getReg .x23 = BitVec.ofNat 64 (if l = sel then sb else DUMMY) ∧
      RegsExcept t2 t3 [.x22, .x23] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hls : l = sel
    · rw [if_pos hls] at t2pc
      obtain ⟨u, stu, upc, u22, u23, ur, uf⟩ := blk1184_spec t2 t2pc
      refine ⟨u, 3, stu, by simp [hls], upc, by simp [hls, u22], ?_, ur, uf⟩
      rw [u23, t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x16]; simp [hls]
    · rw [if_neg hls] at t2pc
      exact ⟨t2, 0, Steps.refl _, by simp [hls], t2pc, by simp [hls, t2x22], by simp [hls, t2x23],
        RegsExcept.refl _ _, Frame.refl _ _⟩
  obtain ⟨t4, st4, t4pc, t4x1, t4x25, t4r, t4f⟩ := blk1187_spec t3 t3pc l (height lay) LOW hl
    (by rcases hH with h | h <;> omega) (by sgo)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp)]; exact ht.x13)
    (by rw [t3r.get (by simp), t2r.get (by simp)]; exact t1x6)
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by decide), hs.x2])
  have r14 : RegsExcept t t4 ([.x6] ++ [.x18, .x22, .x23] ++ [.x22, .x23] ++ [.x1, .x7, .x25]) :=
    ((t1r.trans t2r).trans t3r).trans t4r
  have f14 : Frame t t4 (fun _ => False) :=
    (((t1f.trans t2f).trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  have hpre : LeafPreS sk t4 (btLeaf lay tree sel ds sb l) :=
    bt_leafPre hs hl ((ht.regs.trans r14).mono (by decide)) ((ht.frame.trans f14).mono
      (fun X _ h => by rcases h with h | h; exact h; exact h.elim)) t4x1
      (by rw [t4r.get (by simp), t3r.get (by simp)]; exact t2x18)
      (by rw [t4r.get (by simp)]; exact t3x22) (by rw [t4r.get (by simp)]; exact t3x23) t4x25
  have hleaf := buildLeaf_tsimS subAt_sign sk hpre t4pc
  obtain ⟨cK, cC, cN, cB⟩ := btLeaf_costs lay hlay tree sel ds sb l
  rw [cK, cC, cN, cB] at hleaf
  unfold btBody
  refine (TSim.steps (st1.trans (st2.trans (st3.trans st4))) (TSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0)
    hleaf (fun r u hu => ?_))).of_eq rfl (by rw [hk3]; split_ifs <;> omega)
      (by rw [hk3]; split_ifs <;> omega) rfl rfl
  obtain ⟨upc, uroot, uvals, ulen, -, ur, uf⟩ := hu
  obtain ⟨root, values⟩ := r
  obtain ⟨t5, st5, t5pc, t5x13, t5r, t5f⟩ := blk1191_spec u upc l
    (by rw [ur.get (by decide), r14.get (by simp)]; exact ht.x13)
  have hLW : ∀ X, LeafW (btLeaf lay tree sel ds sb l) X → BtW sb (height lay) X := by
    intro X h
    unfold LeafW at h
    rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
    change X = PRIV + 16 ∨ X = PRIV + 24 ∨ (SEEDS ≤ X ∧ X < SEEDS + 32) ∨ X = CHAIN + 16 ∨ X = CHAIN + 24 ∨
      (CHAIN + 48 ≤ X ∧ X < CHAIN + 80) ∨ (LEAFPK ≤ X ∧ X < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ X ∧ X < LOUT + 32) ∨
      ((if l = sel then sb else DUMMY) ≤ X ∧ X < (if l = sel then sb else DUMMY) + 16 * 43) ∨
      (LOW + 16 * (2 ^ height lay + l) ≤ X ∧ X < LOW + 16 * (2 ^ height lay + l) + 16) at h
    unfold BtW
    rw [show 2 ^ (height lay + 1) = 2 * 2 ^ height lay by rw [pow_succ]; ring]
    split_ifs at h <;> sgo
  have fU : Frame t t5 (BtW sb (height lay)) := ((f14.trans uf).trans t5f).mono (fun X _ h => by
    rcases h with (h | h) | h
    · exact h.elim
    · exact hLW X h
    · exact h.elim)
  refine TSim.pure_steps st5 ⟨t5pc, t5x13, ?_, ?_, by simp [ht.len], ?_, ?_⟩
  · exact (((ht.regs.trans r14).trans ur).trans t5r).mono (by decide)
  · exact (ht.frame.trans fU).mono (fun X _ h => by rcases h with h | h <;> exact h)
  ·
    have hd : DigAt u (LOW + 16 * 2 ^ height lay + 16 * st.1.length) root := by
      rw [ht.len, show LOW + 16 * 2 ^ height lay + 16 * l = LOW + 16 * (2 ^ height lay + l) by ring]
      exact uroot rfl
    have hold : DigsAt u (LOW + 16 * 2 ^ height lay) st.1 := by
      refine ht.roots.frame ((f14.trans uf).mono (fun X _ h => h)) (by rw [ht.len]; sgo) ?_
      intro B h1 h2 h
      rw [ht.len] at h2
      rcases h with h | h
      · exact h
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 48 ≤ B ∧ B < CHAIN + 80) ∨ (LEAFPK ≤ B ∧ B < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        split_ifs at h <;> sgo
    exact (hold.snoc hd).frame t5f (by simp only [List.length_append, List.length_singleton, ht.len]; sgo)
      (fun _ _ _ h => h)
  ·
    intro hsl
    by_cases hls : l = sel
    · subst hls
      simp only [if_true]
      refine ⟨by rw [ulen]; exact chainCount_low hlay, ?_⟩
      have := uvals
      simp only [btLeaf, if_true] at this
      exact this.frame t5f (by rw [ulen, show (btLeaf lay tree l ds sb l).n = 43 from chainCount_low hlay]; sgo)
        (fun _ _ _ h => h)
    · simp only [hls, if_false]
      obtain ⟨hl2, hv⟩ := ht.vals (by omega)
      refine ⟨hl2, hv.frame ((f14.trans uf).trans t5f) (by rw [hl2]; sgo) (fun B h1 h2 h => ?_)⟩
      rw [hl2] at h2
      rcases h with (h | h) | h
      · exact h
      · unfold LeafW at h
        rw [show (btLeaf lay tree sel ds sb l).n = 43 from chainCount_low hlay] at h
        change B = PRIV + 16 ∨ B = PRIV + 24 ∨ (SEEDS ≤ B ∧ B < SEEDS + 32) ∨ B = CHAIN + 16 ∨ B = CHAIN + 24 ∨
          (CHAIN + 48 ≤ B ∧ B < CHAIN + 80) ∨ (LEAFPK ≤ B ∧ B < LEAFPK + 16 * (43 + 1)) ∨ (LOUT ≤ B ∧ B < LOUT + 32) ∨
          ((if l = sel then sb else DUMMY) ≤ B ∧ B < (if l = sel then sb else DUMMY) + 16 * 43) ∨
          (LOW + 16 * (2 ^ height lay + l) ≤ B ∧ B < LOW + 16 * (2 ^ height lay + l) + 16) at h
        rw [if_neg hls] at h
        sgo
      · exact h
end loop
theorem bt_path_loop (t0 : MachineState) (H hi : Nat) (hH : H ≤ 7) (hhi : hi < 2 ^ (H + 1)) :
    ∀ (n j : Nat), j + n = H → ∀ (t : MachineState) (ep : Nat), t.pc = pcOf 1202 →
      t.getReg .x13 = BitVec.ofNat 64 j → t.getReg .x15 = BitVec.ofNat 64 H →
      t.getReg .x19 = BitVec.ofNat 64 hi → t.getReg .x2 = BitVec.ofNat 64 LOW →
      t.getReg .x24 = BitVec.ofNat 64 ep → ep % 8 = 0 → ep + 16 * n ≤ LOW →
      (∀ A, LOW ≤ A → A < LOW + 4096 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      ∃ u k, Steps image t k k u ∧ k ≤ 12 * n + 1 ∧ u.pc = pcOf 1214 ∧
        (∀ i < n, DigAt u (ep + 16 * i) (memDig t0 (LOW + 16 * (hi / 2 ^ (j + i) ^^^ 1)))) ∧
        RegsExcept t u [.x6, .x7, .x13, .x24, .x28] ∧ Frame t u (fun A => ep ≤ A ∧ A < ep + 16 * n)
  | 0, j, hjn, t, ep, hpc, h13, h15, _, _, _, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_neg (by omega)] at upc
    exact ⟨u, 1, st, by omega, upc, fun i hi => absurd hi (by omega), ur.mono (by simp),
      uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, j, hjn, t, ep, hpc, h13, h15, h19, h2, h24, hep8, hepl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk1202_spec t hpc j H (by omega) (by omega) h13 h15
    rw [if_pos (by omega)] at t1pc
    have hhi' : hi < 8192 := lt_of_lt_of_le hhi (by
      calc 2 ^ (H + 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 8192 := by norm_num)
    obtain ⟨t2, st2, t2pc, t2x13, t2x24, m0, m8, t2r, t2f⟩ := blk1203_spec t1 t1pc j hi LOW ep (by omega)
      hhi' (by sgo) (by sgo) (by sgo) hep8 (by rw [t1r.get (by simp)]; exact h13)
      (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h2)
      (by rw [t1r.get (by simp)]; exact h24)
    have hx : hi / 2 ^ j ^^^ 1 < 8192 :=
      Nat.xor_lt_two_pow (n := 13) (lt_of_le_of_lt (Nat.div_le_self _ _) hhi') (by norm_num)
    have hx' : hi / 2 ^ j ^^^ 1 < 256 := by
      have h1 : hi / 2 ^ j < 2 ^ 8 := lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le hhi
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact Nat.xor_lt_two_pow h1 (by norm_num)
    have f12 : Frame t t2 (fun A => A = ep ∨ A = ep + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, uem, ur, uf⟩ := bt_path_loop t0 H hi hH hhi n (j + 1) (by omega) t2 (ep + 16) t2pc
      t2x13 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h15)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h19) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2)
      t2x24 (by omega) (by omega) (fun A h1 h2' => (f12.get (by sgo) (by sgo)).trans (hheap A h1 h2'))
    refine ⟨u, 1 + (11 + k), st1.trans (st2.trans st), by omega, upc, fun i hi' => ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rcases i with _ | i
    · simp only [Nat.mul_zero, Nat.add_zero]
      refine ⟨?_, ?_⟩
      · rw [uf.get (by sgo) (by omega), m0, t1f.get (by sgo) (fun h => h), hheap _ (by sgo) (by sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).1
      · rw [uf.get (by sgo) (by omega), m8, t1f.get (by sgo) (fun h => h), hheap _ (by sgo) (by sgo)]
        exact (memDig_digAt t0 (LOW + 16 * (hi / 2 ^ j ^^^ 1))).2
    · have := uem i (by omega)
      rw [show ep + 16 + 16 * i = ep + 16 * (i + 1) by ring, show j + 1 + i = j + (i + 1) by ring] at this
      exact this
def btLev (lay : Layer) (tree : Nat) : LevArgs := ⟨3, lay.val, tree, height lay, LOW, 1196⟩
def btAllRegs : List Reg :=
  [.x4, .x13] ++ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
    [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]
def BtAllW (lay : Layer) (tree sb : Nat) (A : Nat) : Prop :=
  BtW sb (height lay) A ∨ LevW (btLev lay tree) A ∨ (sb + 16 * 43 ≤ A ∧ A < sb + 16 * (43 + height lay)) ∨
    A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56
structure BtPost (sk : SecretKey) (cache : Bytes 131072) (lay : Layer) (tree sel sb ret : Nat) (s : MachineState)
    (r : List (List Digest) × List Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf ret
  vlen : r.2.length = 43
  vals : DigsAt u sb r.2
  path : DigsAt u (sb + 16 * 43) ((List.range (height lay)).map fun j => (r.1.getD j []).getD (sel / 2 ^ j ^^^ 1) 0)
  root : DigAt u ENC ((r.1.getD (height lay - 1) []).getD 0 0)
  rootR : DigAt u (ENC + 48) ((r.1.getD (height lay - 1) []).getD 1 0)
  base : BaseL sk cache u
  regs : RegsExcept s u btAllRegs
  frame : Frame s u (BtAllW lay tree sb)
def btCost : Nat := 2127776
theorem sumTo_le_mul (f : Nat → Nat) (b : Nat) : ∀ n, (∀ j < n, f j ≤ b) → sumTo f n ≤ n * b
  | 0, _ => by simp [sumTo]
  | n + 1, h => by
    have := sumTo_le_mul f b n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; rw [Nat.succ_mul]; omega
theorem sumTo_le_sumTo (f g : Nat → Nat) : ∀ n, (∀ j < n, f j ≤ g j) → sumTo f n ≤ sumTo g n
  | 0, _ => le_rfl
  | n + 1, h => by
    have := sumTo_le_sumTo f g n (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [sumTo]; omega
theorem heapH_sib {H sel i : Nat} (hi : i < H) :
    (2 ^ H + sel) / 2 ^ i ^^^ 1 = 2 ^ (H - i) + (sel / 2 ^ i ^^^ 1) := by
  have h2 : 2 ^ H = 2 ^ (H - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i), Nat.add_comm,
    two_pow_add_xor_one (by omega)]
theorem btLev_costs (lay : Layer) (hlay : lay ≠ 0) (tree : Nat) :
    (btLev lay tree).levK ≤ (btLev lay tree).levC ∧ (btLev lay tree).levC ≤ 5889 := by
  rcases height_low hlay with h | h <;> simp only [LevArgs.levK, LevArgs.levC, btLev, h] <;> decide
theorem bt_tail {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s s1 t : MachineState} (hs : BtPre sk cache lay tree sel ds sb s1)
    (h4 : s1.getReg .x4 = pcOf ret) (hr0 : RegsExcept s s1 [.x4, .x13]) (hf0 : Frame s s1 (fun _ => False))
    {st : List Digest × List Digest} (ht : BtInv s1 sb sel (height lay) (2 ^ height lay) st t) :
    TBSim image sk t 19000 (do
      let levels ← buildLevels 3 lay.val tree (height lay) st.1
      pure (levels, st.2)) (BtPost sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hH7 : height lay ≤ 7 := by rcases hH with h | h <;> omega
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  have hsb8 := hs.hsb8
  have g : ∀ r, r ∉ btRegs → t.getReg r = s1.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, -, t1r, t1f⟩ := blk1175_spec t ht.pc (2 ^ height lay) (height lay) (by omega)
    (by omega) ht.x13 (by rw [g _ (by decide), hs.x15])
  rw [if_neg (lt_irrefl _)] at t1pc
  obtain ⟨t2, st2, t2pc, t2x1, t2x21, t2r, t2f⟩ := blk1193_spec t1 t1pc lay.val (by have := lay.isLt; omega)
    (by rw [t1r.get (by simp), g _ (by decide), hs.x8])
  have g2 : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] → t2.getReg r = s1.getReg r := fun r hr =>
    ((ht.regs.trans t1r).trans t2r).get hr
  have f2 : Frame s1 t2 (BtW sb (height lay)) := (ht.frame.trans (t1f.trans t2f)).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact h.elim
    · exact h.elim)
  have hlp : LevPre t2 (btLev lay tree) st.1 :=
    { x1 := t2x1
      x2 := by rw [g2 _ (by decide), hs.x2]; rfl
      x5 := by rw [g2 _ (by decide), hs.base.x5]
      x9 := by rw [g2 _ (by decide), hs.x9]; rfl
      x15 := by rw [g2 _ (by decide), hs.x15]; rfl
      x21 := by
        rw [t2x21]
        show BitVec.ofNat 64 (769 + 65536 * lay.val) = BitVec.ofNat 64 (hdr0 3 lay.val tree 0)
        congr 1
        unfold hdr0
        rw [Nat.div_eq_of_lt hs.htree]
        have := lay.isLt
        omega
      tag3 := Or.inl rfl
      htree := hs.htree
      hh1 := by show 1 ≤ height lay; omega
      hh := by show height lay ≤ 12; omega
      ha8 := by show LOW % 8 = 0; decide
      ha := by
        show LOW + 16 * 2 ^ (height lay + 1) ≤ 2 ^ 24
        rcases hH with h | h <;> rw [h] <;> norm_num
      has := Or.inl (by show NOUT + 32 ≤ LOW; decide)
      z32 := by
        rw [f2.get (by sgo) (by unfold BtW; sgo)]
        exact hs.base.zero _ (by sgo) (by unfold NeverWL; simp)
      z40 := by
        rw [f2.get (by sgo) (by unfold BtW; sgo)]
        exact hs.base.zero _ (by sgo) (by unfold NeverWL; simp)
      hlen := ht.len
      hleaves := by
        show DigsAt t2 (LOW + 16 * 2 ^ height lay) st.1
        exact ht.roots.frame (t1f.trans t2f) (by rw [ht.len]; sgo) (fun _ _ _ h => by
          rcases h with h | h <;> exact h) }
  have hlev := buildLevels_tsim subAt_sign sk hlp t2pc
  obtain ⟨hlk, hlc⟩ := btLev_costs lay hlay tree
  refine TBSim.mono (TBSim.steps (st1.trans st2) (TBSim.bind (W₂ := 110) (TSim.toTBSim hlev hlk)
    (fun levels u hu => ?_))) (by omega) (fun _ _ h => h)
  obtain ⟨upc, uheap, ur, uf⟩ := hu
  have gu : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs → u.getReg r = s1.getReg r := fun r hr =>
    (((ht.regs.trans t1r).trans t2r).trans ur).get hr
  obtain ⟨v, stv, vpc, vx13, vx19, vx24, vr, vf⟩ := blk1196_spec u upc (height lay) sel sb 43 (by omega)
    (by omega) (by sgo) (by rw [gu _ (by decide), hs.x15]) (by rw [gu _ (by decide), hs.x14])
    (by rw [gu _ (by decide), hs.x16]) (by rw [gu _ (by decide), hs.x26])
  have gv : ∀ r, r ∉ btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] →
      v.getReg r = s1.getReg r := fun r hr => ((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).get hr
  obtain ⟨w, k, stw, hk, wpc, wem, wr, wf⟩ := bt_path_loop u (height lay) (2 ^ height lay + sel) hH7
    (by rw [pow_succ]; omega) (height lay) 0 (by omega) v (sb + 16 * 43) vpc vx13
    (by rw [gv _ (by decide), hs.x15]) vx19 (by rw [gv _ (by decide), hs.x2]) vx24 (by omega) (by sgo)
    (fun A h1 h2 => vf.get (by sgo) (fun h => h))
  obtain ⟨x, stx, xpc, xm0, xm8, xm48, xm56, xr, xf⟩ := blk1214_full w wpc LOW ret (by decide) (by decide)
    (by decide) (by rw [wr.get (by simp), gv _ (by decide), hs.x2])
    (by rw [wr.get (by simp), gv _ (by decide), h4])
  refine TBSim.mono (TBSim.pure_steps (stv.trans (stw.trans stx)) ?_) (by omega) (fun _ _ h => h)
  have fux : Frame u x (fun A => (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨
      A = ENC + 56) :=
    ((vf.trans wf).trans xf).mono (fun A _ h => by
      rcases h with (h | h) | h
      · exact h.elim
      · exact Or.inl h
      · exact Or.inr h)
  have f1x : Frame s1 x (BtAllW lay tree sb) := (f2.trans (uf.trans fux)).mono (fun A _ h => by
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr h)))
  have hW : ∀ A, A < 2 ^ 64 → BaseAL A → ¬ BtAllW lay tree sb A := by
    intro A _ hb hw
    unfold BaseAL NeverWL Search.TOP_DATA at hb
    unfold BtAllW BtW LevW at hw
    simp only [btLev] at hw
    rcases hH with h | h <;> rw [h] at hw <;> sgo
  have r1x : RegsExcept s1 x (btRegs ++ [.x6] ++ [.x1, .x21] ++ levRegs ++ [.x6, .x7, .x13, .x19, .x24] ++
      [.x6, .x7, .x13, .x24, .x28] ++ [.x6, .x7, .x30]) :=
    (((((ht.regs.trans t1r).trans t2r).trans ur).trans vr).trans wr).trans xr
  obtain ⟨-, hlv⟩ := uheap
  refine ⟨xpc, (ht.vals hsel).1, ?_, ?_, ?_, ?_, hs.base.frame f1x r1x (by decide) hW, ?_, ?_⟩
  ·
    obtain ⟨hl2, hv⟩ := ht.vals hsel
    have ftx : Frame t x (fun A => LevW (btLev lay tree) A ∨
        (sb + 16 * 43 ≤ A ∧ A < sb + 16 * 43 + 16 * height lay) ∨ A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨
      A = ENC + 56) :=
      ((t1f.trans t2f).trans (uf.trans fux)).mono (fun A _ h => by
        rcases h with (h | h) | h
        · exact h.elim
        · exact h.elim
        · exact h)
    refine hv.frame ftx (by rw [hl2]; sgo) (fun B h1 h2 h => ?_)
    rw [hl2] at h2
    unfold LevW at h
    simp only [btLev] at h
    sgo
  ·
    intro i hi
    rw [List.length_map, List.length_range] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    have he := wem i hi
    rw [Nat.zero_add, heapH_sib hi] at he
    obtain ⟨hlen, hd⟩ := hlv i (by show i ≤ height lay; omega)
    have hq : sel / 2 ^ i < 2 ^ (height lay - i) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos i), ← pow_add, Nat.sub_add_cancel hi.le]; exact hsel
    have h2i : 2 ^ 1 ≤ 2 ^ (height lay - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hkq : sel / 2 ^ i ^^^ 1 < 2 ^ (height lay - i) := Nat.xor_lt_two_pow hq (by omega)
    have hdi := hd _ (by rw [hlen]; exact hkq)
    simp only [btLev] at hdi
    rw [show LOW + 16 * (2 ^ (height lay - i) + (sel / 2 ^ i ^^^ 1)) =
      LOW + 16 * 2 ^ (height lay - i) + 16 * (sel / 2 ^ i ^^^ 1) by ring, memDig_eq hdi] at he
    exact he.frame xf (by sgo) (by sgo) (by sgo)
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by simp only [btLev]; omega)
    have h1 : height lay - (height lay - 1) = 1 := by omega
    have hd0 := hd 0 (by rw [hl0]; simp [btLev, h1])
    simp only [btLev, h1, pow_one, Nat.mul_zero, Nat.add_zero] at hd0
    refine ⟨?_, ?_⟩
    · rw [xm0, wf.get (by sgo) (by sgo), vf.get (by sgo) (fun h => h)]; exact hd0.1
    · rw [xm8, wf.get (by sgo) (by sgo), vf.get (by sgo) (fun h => h)]; exact hd0.2
  ·
    obtain ⟨hl0, hd⟩ := hlv (height lay - 1) (by simp only [btLev]; omega)
    have h1 : height lay - (height lay - 1) = 1 := by omega
    have hd1 := hd 1 (by rw [hl0]; simp [btLev, h1])
    simp only [btLev, h1, pow_one, Nat.mul_one] at hd1
    refine ⟨?_, ?_⟩
    · rw [xm48, wf.get (by sgo) (by sgo), vf.get (by sgo) (fun h => h)]; exact hd1.1
    · rw [xm56, wf.get (by sgo) (by sgo), vf.get (by sgo) (fun h => h)]; exact hd1.2
  · exact (hr0.trans r1x).mono (by decide)
  · exact (hf0.trans f1x).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
theorem buildTree_tbsim {sk : SecretKey} {cache : Bytes 131072} {lay : Layer} {tree sel : Nat} {ds : List Nat}
    {sb ret : Nat} {s : MachineState} (hs : BtPre sk cache lay tree sel ds sb s) (hpc : s.pc = pcOf 1173)
    (h1 : s.getReg .x1 = pcOf ret) :
    TBSim image sk s btCost (buildTree lay tree sel ds) (BtPost sk cache lay tree sel sb ret s) := by
  have hlay := hs.hlay
  have hH := height_low hlay
  have hHp : 2 ^ height lay ≤ 128 := by rcases hH with h | h <;> rw [h] <;> norm_num
  have hsel := hs.hsel
  have hsb := hs.hsb
  obtain ⟨s1, st1, s1pc, s1x4, s1x13, s1r, s1f⟩ := blk1173_spec s hpc
  have g1 : ∀ r, r ∉ [.x4, .x13] → s1.getReg r = s.getReg r := fun r hr => s1r.get hr
  have hs1 : BtPre sk cache lay tree sel ds sb s1 :=
    { x2 := by rw [g1 _ (by decide), hs.x2]
      x8 := by rw [g1 _ (by decide), hs.x8]
      x9 := by rw [g1 _ (by decide), hs.x9]
      x14 := by rw [g1 _ (by decide), hs.x14]
      x15 := by rw [g1 _ (by decide), hs.x15]
      x16 := by rw [g1 _ (by decide), hs.x16]
      x26 := by rw [g1 _ (by decide), hs.x26]
      x27 := by rw [g1 _ (by decide), hs.x27]
      x31 := by rw [g1 _ (by decide), hs.x31]
      base := hs.base.frame s1f s1r (by decide) (fun _ _ _ h => h)
      hlay := hlay
      htree := hs.htree
      hsel := hsel
      hroute := hs.hroute
      hdb := hs.hdb
      digits := fun i hi => by rw [s1f.getByte (by sgo) (fun h => h)]; exact hs.digits i hi
      hsb := hsb
      hsb8 := hs.hsb8 }
  have h0 : BtInv s1 sb sel (height lay) 0 ([], []) s1 :=
    ⟨s1pc, s1x13, RegsExcept.refl _ _, Frame.refl _ _, rfl, DigsAt.nil _ _, fun h => absurd h (by omega)⟩
  have hloop := TSim.foldlM_range (image := image) (sk := sk) (2 ^ height lay) (btBody lay tree sel ds) ([], [])
    (BtInv s1 sb sel (height lay)) (fun l => (if lay = 1 then 13815 else 14116) + (if l = sel then 3 else 0))
    (fun l => (if lay = 1 then 16163 else 16464) + (if l = sel then 3 else 0)) (fun _ => 324) (fun _ => 334)
    (fun l hl st t ht => bt_body hs1 hl ht) h0
  have hkc : sumTo (fun l => (if lay = 1 then 13815 else 14116) + (if l = sel then 3 else 0)) (2 ^ height lay) ≤
      sumTo (fun l => (if lay = 1 then 16163 else 16464) + (if l = sel then 3 else 0)) (2 ^ height lay) :=
    sumTo_le_sumTo _ _ _ (fun j _ => by split_ifs <;> omega)
  have hcb : sumTo (fun l => (if lay = 1 then 16163 else 16464) + (if l = sel then 3 else 0)) (2 ^ height lay) ≤ 128 * 16467 :=
    le_trans (sumTo_le_mul _ 16467 _ (fun j _ => by split_ifs <;> omega)) (Nat.mul_le_mul_right _ hHp)
  rw [buildTree_eq]
  exact TBSim.mono (TBSim.steps st1 (TBSim.bind (W₂ := 19000) (TSim.toTBSim hloop hkc)
    (fun st t ht => bt_tail hs1 (by rw [s1x4, h1]) s1r s1f ht))) (by unfold btCost; omega) (fun _ _ h => h)
end SigGolfCandidate.T3M.Sign
end
