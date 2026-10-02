import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Sign.TopBlocks

/-!
# Sign: block specifications of the forest and layers 3..1 (words 357..426, `build_tree` 1173..1220)

`fts_done` (357): the forest header `T11(index)` and the HASH arguments; 369: its `ECALL`; 370: the forest
pk to `ENC`, `ARENA = LOW`, `SIGONLY = 0`, `N = 43`, `N4 = 0` and the layer-3 registers, `counter_search`;
396/411/426: `build_tree`; 397/412: the layer-2 / layer-1 registers, `counter_search`. `build_tree`:
the leaf loop (1173..1192), `build_levels` (1193..1195), the path (1196..1213), the root to `ENC` (1214..1220).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)

/-- `fts_done` (357..368): the forest header `T11(0, index)` at `FOREST+16`, HASH `(FOREST, 128, FOUT)`. -/
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

/-- 370..395: the forest pk to `ENC`, the lower-layer registers, layer 3 (`H = 6`, values to `SIG + 4944`,
target 194, leaf `index mod 64`, tree `index / 64`), `counter_search` (return to 396). -/
theorem blk370_spec (s : MachineState) (hpc : s.pc = pcOf 370) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 396 ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 FOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (FOUT + 8)) ∧
      t.getReg .x2 = BitVec.ofNat 64 LOW ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4944) ∧ t.getReg .x17 = BitVec.ofNat 64 194 ∧
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

/-- The `build_tree` call of a layer (396, 411, 426): `jal ra, build_tree`. -/
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

/-- 397..410: layer 2 (`H = 6`, values to `SIG + 4160`, target 194, leaf `index / 64 mod 64`, tree
`index / 4096`), `counter_search` (return to 411). -/
theorem blk397_spec (s : MachineState) (hpc : s.pc = pcOf 397) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 411 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 4160) ∧ t.getReg .x17 = BitVec.ofNat 64 194 ∧
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

/-- 412..425: layer 1 (`H = 7`, values to `SIG + 3360`, target 194, leaf `index / 4096 mod 128`, tree
`index / 2^19`), `counter_search` (return to 426). -/
theorem blk412_spec (s : MachineState) (hpc : s.pc = pcOf 412) (idx : Nat) (hidx : idx < 2 ^ 31)
    (hm : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 idx) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 646 ∧ t.getReg .x1 = pcOf 426 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x16 = BitVec.ofNat 64 (SIG + 3360) ∧ t.getReg .x17 = BitVec.ofNat 64 194 ∧
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

/-! ## `build_tree` (1173..1220) -/

/-- `build_tree` (1173..1174): `LINK2 = ra`, `L3 = 0`. -/
theorem blk1173_spec (s : MachineState) (hpc : s.pc = pcOf 1173) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x4 = s.getReg .x1 ∧
      t.getReg .x13 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x4, .x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1173 codeAt_1173 s hpc (by simp [blk_1173.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1173.res, E.eval]
  · simp [blk_1173.res, rv_simp]
  · simp [blk_1173.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1173.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1173.res, rv_simp]

/-- `bt_leaf` (1175..1177): `L3 ≥ 2^H` ends the leaves; `t1 = 2^H`. -/
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

/-- 1178..1183: `LEAF = L3`, `DIGP = ZDIG`, `VALP = DUMMY`; the selected leaf goes on to 1184. -/
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

/-- 1184..1186: the selected leaf: `DIGP = DIGITS`, `VALP = SIGB`. -/
theorem blk1184_spec (s : MachineState) (hpc : s.pc = pcOf 1184) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1187 ∧ t.getReg .x22 = BitVec.ofNat 64 DIGITS ∧
      t.getReg .x23 = s.getReg .x16 ∧ RegsExcept s t [.x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1184 codeAt_1184 s hpc (by simp [blk_1184.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_1184.res, E.eval]
  · simp [blk_1184.res, rv_simp]
  · simp [blk_1184.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1184.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1184.res, rv_simp]

/-- `bt_sel_done` (1187..1190): `DEST = ARENA + 16 (2^H + L3)`, `jal build_leaf` (return to 1191). -/
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

/-- 1191..1192: `L3 += 1`, back to `bt_leaf`. -/
theorem blk1191_spec (s : MachineState) (hpc : s.pc = pcOf 1191) (l : Nat)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1175 ∧ t.getReg .x13 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1191 codeAt_1191 s hpc (by simp [blk_1191.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_1191.res, E.eval]
  · simp only [Result.toState_getReg, blk_1191.res]; t3n [h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1191.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1191.res, rv_simp]

/-- `bt_leaves_done` (1193..1195): `E = hdr0 3 lay`, `jal build_levels` (return to 1196). -/
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

/-- 1196..1201: `L3 = 0`, `I = 2^H + SELD`, `ENDP = SIGB + 16 N`. -/
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

/-- `bt_path` (1202): `L3 ≥ H` ends the path. -/
theorem blk1202_spec (s : MachineState) (hpc : s.pc = pcOf 1202) (l h : Nat) (hl : l < 2 ^ 63) (hh : h < 2 ^ 63)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 l) (h15 : s.getReg .x15 = BitVec.ofNat 64 h) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if l < h then pcOf 1203 else pcOf 1214) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_1202 codeAt_1202 s hpc (by simp [blk_1202.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1202.res, E.eval, CmpOp.eval, h13, h15, ofNat_slt l h hl hh]
    by_cases hc : l < h <;> simp [hc]
  · intro r hr; cases r <;> simp_all [blk_1202.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_1202.res, rv_simp]

/-- 1203..1213: the path node `((2^H + SELD) >> L3) ^ 1` to `[ENDP]`, `ENDP += 16`, `L3 += 1`. -/
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

/-- `bt_path_done` (1214..1220): the root (heap node 1) to `ENC`, return through `LINK2`. -/
theorem blk1214_spec (s : MachineState) (hpc : s.pc = pcOf 1214) (ar ret : Nat) (har : ar + 32 ≤ 2 ^ 24)
    (har8 : ar % 8 = 0) (h2 : s.getReg .x2 = BitVec.ofNat 64 ar) (h4 : s.getReg .x4 = pcOf ret) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 (ar + 16)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (ar + 24)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  have hobl : Oblig.all s blk_1214.res.st.obl := by
    simp only [blk_1214.res]
    t3n [h2]
    omega
  refine ⟨_, symRun_sound blk_1214 codeAt_1214 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_1214.res, rv_simp, h4, pcOf_and_max]
  · simp only [Result.toState_getMem, blk_1214.res, ENC]; t3n [h2]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · simp only [Result.toState_getMem, blk_1214.res, ENC]; t3n [h2]
    repeat (first | rw [if_neg (by omega)] | rw [if_pos (by omega)])
  · intro r hr; simp at hr; cases r <;> simp_all [blk_1214.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, blk_1214.res]
    t3n [h2]
    rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.T3M.Sign
