import SigGolfCandidate.T3M.Keygen.Chain

/-!
# Block specifications of the keygen main program (words 0..116)

`start` (0): `t0 = 0`, the private prefix `S0 | . | S1 | 0^16` at `PRIV`, the leaf registers
(`LAY = TREE = 0`, `N = 58`, `N4 = 49`, `SIGONLY = 0`, `DIGP = ZDIG`, `ARENA = TOP`, `LEAF = 0`);
`kg_leaf` (26..36): `build_leaf` for leaf `LEAF` into `TOP + 16 (4096 + LEAF)`; 36: `build_levels`
(tag 3, height 12); 39: `pk := node 1`; `kg_level`/`kg_mask` (48..84): the masked nodes of levels
2..11 to the region at `0x9020`; 84: the MAC block at `0x8FE0` and the MAC `ECALL` (113); 114: `HALT`.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- The mask output. -/
abbrev MOUT : Nat := 0x20060
/-- All-zero digits (never written). -/
abbrev ZDIG : Nat := 0x20460
/-- The value sink of the keygen leaves. -/
abbrev DUMMY : Nat := 0x20A00
/-- The top tree in heap layout (node `k` at `TOP + 16 k`). -/
abbrev TOP : Nat := 0x50000
/-- The MAC block `S0 | T14 | S1 | 0^16`, right before the region. -/
abbrev MACBLK : Nat := 0x8FE0
/-- The masked region (`cache + 32`). -/
abbrev REGION : Nat := 0x9020

/-- `omega` after unfolding every scratch and buffer address. -/
macro "kg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION] at *); omega))

/-- `start`: the private prefix at `PRIV` and the leaf registers. -/
theorem blk0_spec (s : MachineState) (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 26 ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧ t.getReg .x5 = 0 ∧ t.getReg .x8 = BitVec.ofNat 64 0 ∧
      t.getReg .x9 = BitVec.ofNat 64 0 ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧ t.getReg .x26 = BitVec.ofNat 64 58 ∧
      t.getReg .x27 = BitVec.ofNat 64 49 ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem (BitVec.ofNat 64 0x80) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 8)) = s.getMem (BitVec.ofNat 64 0x88) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 32)) = s.getMem (BitVec.ofNat 64 0x90) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 40)) = s.getMem (BitVec.ofNat 64 0x98) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0 ∧
      RegsExcept s t [.x2, .x5, .x6, .x7, .x8, .x9, .x18, .x22, .x26, .x27, .x29, .x30, .x31] ∧
      Frame s t (fun A => A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨
        A = PRIV + 56) := by
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc (by simp [blk_0.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_0.res, E.eval]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, blk_0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- `kg_leaf`: `LEAF ≥ 4096` ends the leaves. -/
theorem blk26_spec (s : MachineState) (hpc : s.pc = pcOf 26) (leaf : Nat) (hl : leaf < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if leaf < 4096 then pcOf 28 else pcOf 36) ∧
      t.getReg .x6 = BitVec.ofNat 64 4096 ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_26 codeAt_26 s hpc (by simp [blk_26.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_26.res, E.eval, CmpOp.eval, h18,
      ofNat_slt leaf 4096 hl (by norm_num)]
    by_cases h : leaf < 4096 <;> simp [h]
  · simp [blk_26.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_26.res, rv_simp]

/-- The `build_leaf` call: `VALP = DUMMY`, `DEST = TOP + 16 (4096 + LEAF)`, return to 34. -/
theorem blk28_spec (s : MachineState) (hpc : s.pc = pcOf 28) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h6 : s.getReg .x6 = BitVec.ofNat 64 4096)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 TOP) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (117 + 27) ∧ t.getReg .x1 = pcOf 34 ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧
      t.getReg .x25 = BitVec.ofNat 64 (TOP + 16 * (4096 + leaf)) ∧
      RegsExcept s t [.x1, .x7, .x23, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_28 codeAt_28 s hpc (by simp [blk_28.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [blk_28.res, E.eval]
  · simp [blk_28.res, rv_simp]
  · simp [blk_28.res, rv_simp]
  · simp only [Result.toState_getReg, blk_28.res]
    t3n [h18, h6, h2]
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_28.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_28.res, rv_simp]

/-- `LEAF += 1`, back to `kg_leaf`. -/
theorem blk34_spec (s : MachineState) (hpc : s.pc = pcOf 34) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 26 ∧ t.getReg .x18 = BitVec.ofNat 64 (leaf + 1) ∧
      RegsExcept s t [.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_34 codeAt_34 s hpc (by simp [blk_34.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_34.res, E.eval]
  · t3n [blk_34.res, h18]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_34.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_34.res, rv_simp]

/-- The `build_levels` call: `H = 12`, `E = 0x301` (tag 3), return to 39. -/
theorem blk36_spec (s : MachineState) (hpc : s.pc = pcOf 36) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (117 + 113) ∧ t.getReg .x1 = pcOf 39 ∧
      t.getReg .x15 = BitVec.ofNat 64 12 ∧ t.getReg .x21 = BitVec.ofNat 64 769 ∧
      RegsExcept s t [.x1, .x15, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_36 codeAt_36 s hpc (by simp [blk_36.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [blk_36.res, E.eval]
  · simp [blk_36.res, rv_simp]
  · simp [blk_36.res, rv_simp]
  · simp [blk_36.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_36.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_36.res, rv_simp]

/-- `pk := node 1`; `ENDP = REGION`, `STEP = 1024`, `L3 = 2`. -/
theorem blk39_spec (s : MachineState) (hpc : s.pc = pcOf 39)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 TOP) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf 48 ∧
      t.getMem (BitVec.ofNat 64 0xA0) = s.getMem (BitVec.ofNat 64 (TOP + 16)) ∧
      t.getMem (BitVec.ofNat 64 0xA8) = s.getMem (BitVec.ofNat 64 (TOP + 24)) ∧
      t.getReg .x24 = BitVec.ofNat 64 REGION ∧ t.getReg .x20 = BitVec.ofNat 64 1024 ∧
      t.getReg .x13 = BitVec.ofNat 64 2 ∧
      RegsExcept s t [.x6, .x7, .x13, .x20, .x24, .x30] ∧
      Frame s t (fun A => A = 0xA0 ∨ A = 0xA8) := by
  have hobl : Oblig.all s blk_39.res.st.obl := by
    simp only [blk_39.res]
    t3n [h2, TOP]
    norm_num
  refine ⟨_, symRun_sound blk_39 codeAt_39 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_39.res, E.eval]
  · simp only [Result.toState_getMem, blk_39.res]; t3n [h2]
  · simp only [Result.toState_getMem, blk_39.res]; t3n [h2]
  · simp [blk_39.res, rv_simp]
  · simp [blk_39.res, rv_simp]
  · simp [blk_39.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_39.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_39.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `kg_level`: `STEP = 1` ends the masks. -/
theorem blk48_spec (s : MachineState) (hpc : s.pc = pcOf 48) (lo : Nat) (hlo : lo < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lo = 1 then pcOf 84 else pcOf 50) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_48 codeAt_48 s hpc (by simp [blk_48.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_48.res, E.eval, CmpOp.eval, h20]
    by_cases h : lo = 1
    · subst h; simp
    · have : BitVec.ofNat 64 lo ≠ 1#64 := fun he => h (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h, this]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_48.res, rv_simp]

/-- `I := 0`. -/
theorem blk50_spec (s : MachineState) (hpc : s.pc = pcOf 50) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 51 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_50 codeAt_50 s hpc (by simp [blk_50.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_50.res, E.eval]
  · simp [blk_50.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_50.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_50.res, rv_simp]

/-- `kg_mask`: `I ≥ STEP` ends the level. -/
theorem blk51_spec (s : MachineState) (hpc : s.pc = pcOf 51) (i lo : Nat) (hi : i < 2 ^ 63)
    (hlo : lo < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if i < lo then pcOf 52 else pcOf 81) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_51 codeAt_51 s hpc (by simp [blk_51.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_51.res, E.eval, CmpOp.eval, h19, h20, ofNat_slt i lo hi hlo]
    by_cases h : i < lo <;> simp [h]
  · intro r hr; cases r <;> simp_all [blk_51.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_51.res, rv_simp]

/-- The mask header `T13(level, i)` at `PRIV+16` and the HASH arguments `(PRIV, 64, MOUT)`. -/
theorem blk52_spec (s : MachineState) (hpc : s.pc = pcOf 52) (level i : Nat) (hlev : level < 2 ^ 32)
    (hi : i < 2 ^ 32) (h13 : s.getReg .x13 = BitVec.ofNat 64 level)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 MOUT ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (hdr0 13 0 0 level) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  refine ⟨_, symRun_sound blk_52 codeAt_52 s hpc (by simp [blk_52.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [blk_52.res, E.eval]
  · simp [blk_52.res, rv_simp]
  · simp [blk_52.res, rv_simp]
  · simp [blk_52.res, rv_simp]
  · simp only [Result.toState_getMem, blk_52.res, PRIV]
    t3n [h13]
    rw [ofNat_or_disjoint' 3329 (level * 4294967296) 32 (by norm_num) (by omega),
      hdr0_eq 13 0 0 level (by norm_num) (by norm_num) (by norm_num) hlev]
    congr 1; ring
  · simp only [Result.toState_getMem, blk_52.res, PRIV]
    t3n [h19]
    rw [hdr1_eq 0 i (by norm_num) hi]
    congr 1; ring
  · intro r hr; simp at hr; cases r <;> simp_all [blk_52.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, blk_52.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_64 (s : MachineState) (hpc : s.pc = pcOf 64) : fetch image s = some (.base .ECALL) :=
  (codeAt_64.fetch s hpc).trans rfl

/-- `[ENDP] := node (STEP + I) xor MOUT`; `ENDP += 16`, `I += 1`. -/
theorem blk65_spec (s : MachineState) (hpc : s.pc = pcOf 65) (lo i endp : Nat)
    (hn : TOP + 16 * (lo + i) + 16 ≤ 2 ^ 24) (he8 : endp % 8 = 0) (he : endp + 16 ≤ 2 ^ 24)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 TOP) (h24 : s.getReg .x24 = BitVec.ofNat 64 endp) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 51 ∧
      t.getMem (BitVec.ofNat 64 endp) =
        s.getMem (BitVec.ofNat 64 (TOP + 16 * (lo + i))) ^^^ s.getMem (BitVec.ofNat 64 MOUT) ∧
      t.getMem (BitVec.ofNat 64 (endp + 8)) =
        s.getMem (BitVec.ofNat 64 (TOP + 16 * (lo + i) + 8)) ^^^ s.getMem (BitVec.ofNat 64 (MOUT + 8)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (endp + 16) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x6, .x7, .x19, .x24, .x28, .x29] ∧
      Frame s t (fun A => A = endp ∨ A = endp + 8) := by
  have hobl : Oblig.all s blk_65.res.st.obl := by
    simp only [blk_65.res]
    t3n [h20, h19, h2, h24]
    simp only [TOP] at *
    omega
  refine ⟨_, symRun_sound blk_65 codeAt_65 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_65.res, E.eval]
  · simp only [Result.toState_getMem, blk_65.res, MOUT]
    t3n [h20, h19, h2, h24]
    rw [if_neg (by omega), if_pos (by omega), show (lo + i) * 16 + TOP = TOP + 16 * (lo + i) by omega]
  · simp only [Result.toState_getMem, blk_65.res, MOUT]
    t3n [h20, h19, h2, h24]
    rw [show (lo + i) * 16 + TOP + 8 = TOP + 16 * (lo + i) + 8 by omega]
  · simp only [Result.toState_getReg, blk_65.res]; t3n [h24]
  · simp only [Result.toState_getReg, blk_65.res]; t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_65.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_65.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `kg_next_level`: `STEP >>= 1`, `L3 += 1`. -/
theorem blk81_spec (s : MachineState) (hpc : s.pc = pcOf 81) (lo level : Nat) (hlo : lo < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h13 : s.getReg .x13 = BitVec.ofNat 64 level) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 48 ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      t.getReg .x13 = BitVec.ofNat 64 (level + 1) ∧ RegsExcept s t [.x13, .x20] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_81 codeAt_81 s hpc (by simp [blk_81.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_81.res, E.eval]
  · simp only [Result.toState_getReg, blk_81.res]
    t3n [h20]
    rw [ofNat_shr lo 1 hlo, pow_one]
  · t3n [blk_81.res, h13]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_81.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_81.res, rv_simp]

/-- `kg_masks_done`: the MAC block `S0 | T14 | S1 | 0^16` at `0x8FE0` and the HASH arguments
`(0x8FE0, 32832, 0x9000)`. -/
theorem blk84_spec (s : MachineState) (hpc : s.pc = pcOf 84) :
    ∃ t, Steps image s 29 29 t ∧ t.pc = pcOf 113 ∧
      t.getReg .x10 = BitVec.ofNat 64 MACBLK ∧ t.getReg .x11 = BitVec.ofNat 64 32832 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x9000 ∧
      t.getMem (BitVec.ofNat 64 MACBLK) = s.getMem (BitVec.ofNat 64 0x80) ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 8)) = s.getMem (BitVec.ofNat 64 0x88) ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 16)) = BitVec.ofNat 64 3585 ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 32)) = s.getMem (BitVec.ofNat 64 0x90) ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 40)) = s.getMem (BitVec.ofNat 64 0x98) ∧
      t.getMem (BitVec.ofNat 64 (MACBLK + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (MACBLK + 56)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
      Frame s t (fun A => MACBLK ≤ A ∧ A < MACBLK + 64) := by
  refine ⟨_, symRun_sound blk_84 codeAt_84 s hpc (by simp [blk_84.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_84.res, E.eval]
  · simp [blk_84.res, rv_simp]
  · simp [blk_84.res, rv_simp]
  · simp [blk_84.res, rv_simp]
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · simp only [Result.toState_getMem, blk_84.res, MACBLK]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [blk_84.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [MACBLK] at hn
    simp only [Result.toState_getMem, blk_84.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem fetch_113 (s : MachineState) (hpc : s.pc = pcOf 113) : fetch image s = some (.base .ECALL) :=
  (codeAt_113.fetch s hpc).trans rfl

/-- `HALT 0`: `t0 = 1`, `a0 = 0`. -/
theorem blk114_spec (s : MachineState) (hpc : s.pc = pcOf 114) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 116 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_114 codeAt_114 s hpc (by simp [blk_114.res, rv_simp]), ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [blk_114.res, E.eval]
  · simp [blk_114.res, rv_simp]
  · simp [blk_114.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_114.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_114.res, rv_simp]

theorem fetch_116 (s : MachineState) (hpc : s.pc = pcOf 116) : fetch image s = some (.base .ECALL) :=
  (codeAt_116.fetch s hpc).trans rfl

end SigGolfCandidate.T3M.Keygen
