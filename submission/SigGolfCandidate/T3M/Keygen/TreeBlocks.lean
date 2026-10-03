import SigGolfCandidate.T3M.Keygen.Chain
import SigGolfCandidate.T3M.RevNet

/-!
# Block specifications of the shared `build_levels` subroutine (offsets 113..159 from the base)

Registers: `x15` height `H`, `x21` header word 0 (`1 | tag << 8 | lay << 16`), `x9` tree, `x2` heap
arena (node `k` at `arena + 16 k`), `x20` level size `lo`, `x24` node index `k`, `x1` return address.
-/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- `lo := 2^(H-1)`. -/
theorem sub113_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 113)) (hh : Nat) (h1 : 1 ≤ hh) (h2 : hh ≤ 32)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (2 ^ (hh - 1)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_113 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_113 h) s hpc (by simp [st_113, blk117_113.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_113, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_113, blk117_113.res, rv_simp, h15]
    apply BitVec.eq_of_toNat_eq
    have e : (BitVec.ofNat 64 hh - 1#64).toNat = hh - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_shiftLeft, e, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show hh - 1 < 64 by omega)]
    have : 2 ^ (hh - 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    simp only [Nat.one_mod, Nat.one_mul, Nat.mod_eq_of_lt this]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk117_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk117_113.res, rv_simp]

/-- `lv_level`: `lo = 0` ends the levels. -/
theorem sub116_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]

theorem sub117_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]

/-- `lv_node`: `k ≥ 2 lo` ends the level. -/
theorem sub118_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]

/-- `x << 52` is negative iff bit 11 of `x` is set. -/
theorem slt_shl52n (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) 0#64 = decide (2048 ≤ h0 % 4096) := by
  have e : BitVec.ofNat 64 h0 <<< 52 = BitVec.ofNat 64 (h0 % 4096 * 2 ^ 52) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  rw [e, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hr := Nat.mod_lt h0 (show 0 < 4096 by norm_num)
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show h0 % 4096 * 2 ^ 52 < 2 ^ 64 by omega)]
  by_cases hc : 2048 ≤ h0 % 4096
  · simp only [hc, decide_true]
    rw [if_neg (by omega)]
    simp <;> omega
  · simp only [hc, decide_false]
    rw [if_pos (by omega)]
    simp <;> omega

theorem slt_shl52n' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) (0 : Word) = decide (2048 ≤ h0 % 4096) := slt_shl52n h0

theorem slt_shl52 (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) (0 : Word) = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0

theorem slt_shl52' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) 0#64 = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0

/-- The node block `node 2k | T(word0, tree) | 0 | node 2k+1` (words 0, 2, 3 of the node and the tag word),
`x7 := k`, `x30 := NODE + 48`; tag bit 3 (bit 11 of `x21`) selects the reversal stub. -/
theorem sub120_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧
      t.pc = (if 2048 ≤ h0 % 4096 then pcOf (b + 1004) else pcOf (b + 140)) ∧
      t.getReg .x7 = BitVec.ofNat 64 k ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 48 ∨ X = NODE + 56) := by
  have hrun := run_120 h.2.1
  have hobl : Oblig.all s st_120.obl := by
    simp only [st_120, blk117_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_120 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_120, rebase, blk117_120.res, E.eval, CmpOp.eval, BinOp.eval, h21]
    simp only [slt_shl52, slt_shl52', slt_shl52n, slt_shl52n']
    by_cases hc : 2048 ≤ h0 % 4096 <;> simp [hc]
  · simp [st_120, blk117_120.res, rv_simp, h24]
  · simp [st_120, blk117_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h9]
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120, blk117_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120, blk117_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120, blk117_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The reversal stub (offset 1004): `x7 := revBits 64 x24` for `x24 < 2^12`, back to offset 140. -/
theorem sub214_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]

theorem valid8_ofNat (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega

theorem node48_m24 : BitVec.ofNat 64 (NODE + 48) + BitVec.ofNat 64 18446744073709551592 = BitVec.ofNat 64 (NODE + 24) := by
  rw [ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, NODE]

theorem sub140_obl (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    Oblig.all s st_140.obl := by
  simp only [st_140, blk117_140.res, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
    BitVec.ofNat_eq_ofNat]
  rw [h30, node48_m24]
  exact valid8_ofNat _ (by simp only [NODE]) (by simp only [NODE]; omega)

theorem sub140_m24 (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    memEval s st_140.mem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]

theorem sub140_frame (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) (X : Nat)
    (hX : X < 2 ^ 64) (hn : X ≠ 131608) :
    memEval s st_140.mem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
  rw [if_neg (by omega)]

/-- Offset 140: the header word 1 (`x7`) to `NODE + 24`, the HASH arguments `(NODE, 64, NOUT)`. -/
theorem sub140_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun X => X = NODE + 24) := by
  have hrun := run_140 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_140 h) s hpc (sub140_obl s h30), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_140, Result.toState_pc, E.eval]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · simp [st_140, blk117_140.res, rv_simp]
  · rw [Result.toState_getMem]; exact sub140_m24 s h30
  · intro r hr; simp at hr; cases r <;> simp_all [st_140, blk117_140.res, rv_simp] <;> rfl
  · intro X hX hn
    rw [Result.toState_getMem]
    exact sub140_frame s h30 X hX (by simp only [NODE] at hn; omega)

/-- Extra steps (= cycles) of one node for the FTS node tag 10 (the reversal stub). -/
def revX (tag : Nat) : Nat := if tag = 10 then 28 else 0

/-- The whole node block (offsets 120..145, tag 3 or 10): `node 2k | T(word0, nodeWord tag 0 k) | 0 | node 2k+1`
and the HASH arguments. -/
theorem sub120_full {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (tag lay arena k tree : Nat) (htag : tag = 3 ∨ tag = 10)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (hk' : k < 2 ^ 12) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 (hdr0 tag lay tree 0)) :
    ∃ t, Steps image s (26 + revX tag) (26 + revX tag) t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (T3.nodeWord tag 0 k) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x7, t1x30, m0, m8, m16, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree (hdr0 tag lay tree 0) ha8 hk htree hdis h2 h24 h9 h21
  have hmod : hdr0 tag lay tree 0 % 4096 = 1 + 256 * (tag % 16) := by
    unfold hdr0; omega
  -- to offset 140 with the header word 1 in `x7`
  have mid : ∃ u, Steps image t1 (revX tag) (revX tag) u ∧ u.pc = pcOf (b + 140) ∧
      u.getReg .x7 = BitVec.ofNat 64 (T3.nodeWord tag 0 k) ∧ RegsExcept t1 u [.x6, .x7, .x28] ∧
      Frame t1 u (fun _ => False) := by
    rcases htag with rfl | rfl
    · rw [hmod, if_neg (by norm_num)] at t1pc
      refine ⟨t1, (Steps.refl _).of_eq (by decide) (by decide), t1pc, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [t1x7, nodeWord_3, hdr1_eq k 0 (by omega) (by norm_num)]; simp
    · rw [hmod, if_pos (by norm_num)] at t1pc
      obtain ⟨u, stu, upc, ux7, ur, uf⟩ := sub214_spec h t1 t1pc k hk'
        (by rw [t1r.get (by simp)]; exact h24)
      refine ⟨u, stu.of_eq (by decide) (by decide), upc, ?_, ur, uf⟩
      rw [ux7, nodeWord_10, hdr1_eq k 0 (by omega) (by norm_num)]; simp
  obtain ⟨u, stu, upc, ux7, ur, uf⟩ := mid
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tm24, tr, tf⟩ := sub140_spec h u upc
    (by rw [ur.get (by simp)]; exact t1x30)
  have g : ∀ X, X < 2 ^ 64 → X ≠ NODE + 24 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX hn => (tf.get hX hn).trans (uf.get hX (fun h => h))
  refine ⟨t, (st1.trans (stu.trans stt)).of_eq (by omega) (by omega),
    tpc, tx10, tx11, tx12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g NODE (by decide) (by decide), m0]
  · rw [g (NODE + 8) (by decide) (by decide), m8]
  · rw [g (NODE + 16) (by decide) (by decide), m16]
  · rw [tm24, ux7]
  · rw [g (NODE + 48) (by decide) (by decide), m48]
  · rw [g (NODE + 56) (by decide) (by decide), m56]
  · exact ((t1r.trans ur).trans tr).mono (by decide)
  · refine ((t1f.trans uf).trans tf).mono (fun X _ hX => ?_)
    rcases hX with (hX | hX) | hX
    · rcases hX with hX | hX | hX | hX | hX <;> simp [hX]
    · exact hX.elim
    · simp [hX]

theorem fetch_sub146 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_146 h).fetch s hpc).trans rfl

/-- Node `k := NOUT` (16 bytes), `k := k + 1`, back to `lv_node`. -/
theorem sub147_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 147)) (arena k : Nat) (ha8 : arena % 8 = 0) (hk : arena + 16 * k + 16 ≤ 2 ^ 24)
    (hdis : NOUT + 16 ≤ arena + 16 * k ∨ arena + 16 * k + 16 ≤ NOUT)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = BitVec.ofNat 64 (k + 1) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (arena + 16 * k + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x24, .x28, .x29] ∧
      Frame s t (fun X => X = arena + 16 * k ∨ X = arena + 16 * k + 8) := by
  have hrun := run_147 h.2.1
  have hobl : Oblig.all s st_147.obl := by
    simp only [st_147, blk117_147.res]
    t3n [h2, h24]
    omega
  refine ⟨_, symRun_sound hrun (codeAt_sub_147 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_147, Result.toState_pc, E.eval]
  · t3n [st_147, blk117_147.res, h24]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    simp only [NOUT] at hdis ⊢
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [st_147, blk117_147.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, st_147, blk117_147.res]
    t3n [h2, h24]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `lv_next_level`: `lo := lo / 2`. -/
theorem sub157_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 157)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 116) ∧ t.getReg .x20 = BitVec.ofNat 64 (lo / 2) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_157 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_157 h) s hpc (by simp [st_157, blk117_157.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_157, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_157, blk117_157.res, rv_simp, h20]
    rw [ofNat_shr _ _ hlo]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_157, blk117_157.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_157, blk117_157.res, rv_simp]

/-- `lv_done`: return. -/
theorem sub159_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]

end SigGolfCandidate.T3M.Keygen
