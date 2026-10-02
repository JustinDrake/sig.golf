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
/-- The masked region (`cache + 32`). -/
abbrev REGION : Nat := 0x80020

/-- `omega` after unfolding every scratch and buffer address. -/
macro "kg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP,
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

/-- After the unchanged tree kernels, enter the full-cache coordinator. -/
theorem blk39_spec (s : MachineState) (hpc : s.pc = pcOf 39) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 277 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_39 codeAt_39 s hpc (by simp [blk_39.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [blk_39.res, E.eval]
  · intro r hr; cases r <;> rfl
  · intro A hA hn; rfl

end SigGolfCandidate.T3M.Keygen
