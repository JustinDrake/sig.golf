import SigGolfCandidate.T3M.Expand.FrontBlocks

/-!
# `expand`: block specifications of `recover_child` (stream E)

`recover_child` (words 824 .. 996; `a0` level, `a1` node, `ra` return, `sp` the frame `[ra | level | node | left live |
left value]` of 48 bytes, `s0` coordinate, `s1` index, `s2` the next proof slot, `s6` / `s7` / `s8` the open stream
segment: header pointer, folds so far, parity): the has-loop over the coordinate's selection row (`SEL + 24 s0`), the
empty subtree (the next proof slot to `NOUT`), the leaf (close / open a segment, the FTS leaf HASH), the inner node (two
recursive calls, the node block, a fold `L` / `R` or a merge, the node HASH), the return.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (NODE NOUT SEL)

set_option autoImplicit false
set_option maxRecDepth 8192

theorem ofNat_sub_ofNat (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- Memory-access obligations of a symbolic block with symbolic addresses: `toNat` arithmetic, then `omega`. -/
macro "ex_oblig" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| (simp only [rv_simp, accessValid_iff, MEMORY_BYTES, ne_eq, BitVec.toNat_eq, BitVec.toNat_add,
      BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reducePow,
      Nat.reduceMul, Nat.reduceAdd, $ts',*] <;> (try and_intros) <;> omega))

theorem secA (c j k : Nat) :
    (BitVec.ofNat 64 c <<< ((1#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 c + BitVec.ofNat 64 j) <<<
      ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 k = BitVec.ofNat 64 (16 * (3 * c + j) + k) := by
  rw [show ((1#64 : BitVec 64).toNat % 64) = 1 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
    ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat]
  congr 1; ring

section blocks
variable (s : MachineState)

/-- Entry: the frame (`ra`, level, node at `sp - 48 ..`), the row address `a4 = SEL + 24 s0`, `s4 = 0`. -/
theorem rc824_spec (hpc : s.pc = pcOf 824) (sp : Nat) (hsp : 48 ≤ sp) (hsp' : sp ≤ 2 ^ 24) (hsp8 : sp % 8 = 0)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 sp) (c : Nat) (hc : c < 7) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 835 ∧ t.getReg .x2 = BitVec.ofNat 64 (sp - 48) ∧
      t.getMem (BitVec.ofNat 64 (sp - 48)) = s.getReg .x1 ∧ t.getMem (BitVec.ofNat 64 (sp - 40)) = s.getReg .x10 ∧
      t.getMem (BitVec.ofNat 64 (sp - 32)) = s.getReg .x11 ∧
      t.getReg .x14 = BitVec.ofNat 64 (SEL + 24 * c) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x2, .x14, .x20, .x28] ∧
      Frame s t (fun A => A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) := by
  have e32 := ofNat_sub_ofNat sp 32 (by omega) (by omega)
  have e40 := ofNat_sub_ofNat sp 40 (by omega) (by omega)
  have e48 := ofNat_sub_ofNat sp 48 (by omega) (by omega)
  refine ⟨_, symRun_sound eblk_824 codeAt_824 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_824.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, rv_simp, e32, e40, e48]
    exact ⟨ex_valid _ (by omega) (by omega), ex_valid _ (by omega) (by omega), ex_valid _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_824.res, E.eval]
  · simp only [Result.toState_getReg, eblk_824.res, rv_simp, h2, e48]
  iterate 3
    · simp only [Result.toState_getMem, eblk_824.res, rv_simp, h2, e32, e40, e48]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | rfl)
  · simp only [Result.toState_getReg, eblk_824.res, rv_simp, h8, SEL]
    t3n []
    congr 1; omega
  · simp [eblk_824.res, rv_simp]
  · ex_regs eblk_824.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_824.res, rv_simp, h2, e32, e40, e48]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The has-loop body: row entry `j` (`t4 = g`), `t5 = g >> level`, found iff `t5 = node`. -/
theorem rc835_spec (hpc : s.pc = pcOf 835) (c j level node g : Nat) (hc : c < 7) (hj : j < 3) (hl : level < 64)
    (hg : g < 2 ^ 64) (hn : node < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h14 : s.getReg .x14 = BitVec.ofNat 64 (SEL + 24 * c))
    (h10 : s.getReg .x10 = BitVec.ofNat 64 level) (h11 : s.getReg .x11 = BitVec.ofNat 64 node)
    (hm : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = (if g / 2 ^ level = node then pcOf 858 else pcOf 840) ∧
      t.getReg .x29 = BitVec.ofNat 64 g ∧ RegsExcept s t [.x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  have ha : BitVec.ofNat 64 j <<< ((3#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 (SEL + 24 * c) =
      BitVec.ofNat 64 (SEL + 24 * c + 8 * j) := by
    rw [show ((3#64 : BitVec 64).toNat % 64) = 3 from rfl, ofNat_shl, ofNat_add_ofNat]; congr 1; ring
  refine ⟨_, symRun_sound eblk_835 codeAt_835 s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_835.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h20, h14, BitVec.ofNat_eq_ofNat]
    rw [ha, show (0#64 : BitVec 64) = 0 from rfl]; simp only [add_zero]
    exact ex_valid _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)
  · simp only [Result.toState_pc, eblk_835.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h20, h14, h10,
      h11, BitVec.ofNat_eq_ofNat, add_zero]
    rw [ha, hm, toNat_ofNat_lt (show level < 2 ^ 64 by omega), Nat.mod_eq_of_lt hl, ofNat_shr _ _ hg]
    rw [ex_beq _ _ (lt_of_le_of_lt (Nat.div_le_self _ _) hg) hn]
    by_cases h : g / 2 ^ level = node <;> simp [h]
  · simp only [Result.toState_getReg, eblk_835.res, E.eval, BinOp.eval, RegFile.get, h20, h14,
      BitVec.ofNat_eq_ofNat, add_zero]
    rw [ha, hm]
  · ex_regs eblk_835.res
  · intro A _ _; simp [eblk_835.res, rv_simp]

/-- The has-loop step: `s4 += 1`, again unless `s4 = 3`. -/
theorem rc840_spec (hpc : s.pc = pcOf 840) (j : Nat) (hj : j < 3) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if j + 1 = 3 then pcOf 843 else pcOf 835) ∧
      t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧ RegsExcept s t [.x20, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_840 codeAt_840 s hpc (by simp [eblk_840.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_840.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h20,
      BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    by_cases h : j + 1 = 3
    · have hj2 : j = 2 := by omega
      subst hj2; simp
    · have : (BitVec.ofNat 64 (j + 1) != 3#64) = true := by
        simp only [bne_iff_ne, ne_eq]; intro he; exact h ((ofNat_inj (by omega) (by omega)).mp he)
      rw [this, if_neg h]; rfl
  · simp only [Result.toState_getReg, eblk_840.res, rv_simp, h20, ofNat_add_ofNat]
  · ex_regs eblk_840.res
  · intro A _ _; simp [eblk_840.res, rv_simp]

/-- No leaf in the subtree: out of slots (`s2 ≥ 121`) fails. -/
theorem rc843_spec (hpc : s.pc = pcOf 843) (used : Nat) (hu : used < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 used) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 121 ≤ used then pcOf 354 else pcOf 845) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_843 codeAt_843 s hpc (by simp [eblk_843.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_843.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h18,
      BitVec.ofNat_eq_ofNat]
    rw [ex_slt used 121 hu (by omega)]
    by_cases h : 121 ≤ used
    · simp [h, show ¬ used < 121 by omega]
    · simp [h, show used < 121 by omega]
  · ex_regs eblk_843.res
  · intro A _ _; simp [eblk_843.res, rv_simp]

/-- The empty subtree: proof slot `s2` to `NOUT`, `s2 += 1`, `a0 = 0`, to `rc_ret`. -/
theorem rc845_spec (hpc : s.pc = pcOf 845) (used : Nat) (hu : used < 121)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 used) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 994 ∧
      t.getMem (BitVec.ofNat 64 NOUT) = s.getMem (BitVec.ofNat 64 (0x7160 + 16 * used)) ∧
      t.getMem (BitVec.ofNat 64 (NOUT + 8)) = s.getMem (BitVec.ofNat 64 (0x7160 + 16 * used + 8)) ∧
      t.getReg .x18 = BitVec.ofNat 64 (used + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x10, .x18, .x28, .x29, .x30] ∧ Frame s t (fun A => A = NOUT ∨ A = NOUT + 8) := by
  have ha : BitVec.ofNat 64 used <<< ((4#64 : BitVec 64).toNat % 64) + 29024#64 =
      BitVec.ofNat 64 (0x7160 + 16 * used) := by
    rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]
    apply BitVec.eq_of_toNat_eq; simp; omega
  refine ⟨_, symRun_sound eblk_845 codeAt_845 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ex_oblig [eblk_845.res, h18]
  · simp [Result.toState_pc, eblk_845.res, E.eval]
  · simp only [Result.toState_getMem, eblk_845.res, rv_simp, h18, ha, NOUT]
    t3n []
  · have ha' : BitVec.ofNat 64 used <<< ((4#64 : BitVec 64).toNat % 64) + 29032#64 =
        BitVec.ofNat 64 (0x7160 + 16 * used + 8) := by
      rw [show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl, ofNat_shl]
      apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [Result.toState_getMem, eblk_845.res, rv_simp, h18, ha', NOUT]
    t3n []
  · simp only [Result.toState_getReg, eblk_845.res, rv_simp, h18, ofNat_add_ofNat]
  · simp [eblk_845.res, rv_simp]
  · ex_regs eblk_845.res
  · intro A hA hn
    simp only [NOUT] at hn
    simp only [Result.toState_getMem, eblk_845.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `rc_has`: an inner node (level `≠ 0`) recurses. -/
theorem rc858_spec (hpc : s.pc = pcOf 858) (level : Nat) (hl : level < 64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 level) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if level = 0 then pcOf 859 else pcOf 902) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_858 codeAt_858 s hpc (by simp [eblk_858.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_858.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h10,
      BitVec.ofNat_eq_ofNat]
    by_cases h : level = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 level != 0#64) = true := by
        simp only [bne_iff_ne, ne_eq]; intro he; exact h ((ofNat_inj (by omega) (by omega)).mp he)
      rw [this, if_neg h]; rfl
  · ex_regs eblk_858.res
  · intro A _ _; simp [eblk_858.res, rv_simp]

/-- At a leaf: the first leaf of the coordinate (`s4 = 0`) opens a segment without closing one. -/
theorem rc859_spec (hpc : s.pc = pcOf 859) (j : Nat) (hj : j < 3) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if j = 0 then pcOf 868 else pcOf 860) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_859 codeAt_859 s hpc (by simp [eblk_859.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_859.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h20,
      BitVec.ofNat_eq_ofNat]
    by_cases h : j = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 j == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq]; intro he; exact h ((ofNat_inj (by omega) (by omega)).mp he)
      rw [this, if_neg h]; rfl
  · ex_regs eblk_859.res
  · intro A _ _; simp [eblk_859.res, rv_simp]

/-- Close the open segment (no merge): header byte `s7 | s8 << 5` at `s6`, `s6 += 8 + 80 s7`. -/
theorem rc860_spec (hpc : s.pc = pcOf 860) (ptr cnt par : Nat) (hp8 : ptr % 8 = 0) (hp : ptr + 8 ≤ 2 ^ 24)
    (hcnt : cnt < 16) (hpar : par < 2) (hfit : ptr + 8 + 80 * cnt < 2 ^ 24)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr) (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 par) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf 868 ∧
      t.getMem (BitVec.ofNat 64 ptr) =
        replaceByte (s.getMem (BitVec.ofNat 64 ptr)) 0 ((BitVec.ofNat 64 (32 * par + cnt)).truncate 8) ∧
      t.getReg .x22 = BitVec.ofNat 64 (ptr + 80 * cnt + 8) ∧
      RegsExcept s t [.x22, .x28, .x30] ∧ Frame s t (fun A => A = ptr) := by
  refine ⟨_, symRun_sound eblk_860 codeAt_860 s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_860.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, BitVec.ofNat_eq_ofNat]
    rw [show (0#64 : BitVec 64) = 0 from rfl]; simp only [add_zero]
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  · simp [Result.toState_pc, eblk_860.res, E.eval]
  · simp only [Result.toState_getMem, eblk_860.res, rv_simp, h22, h23, h24]
    t3n []
    rw [ofNat_or_disjoint cnt (par * 32) 5 (by omega) (by omega), show par * 32 + cnt = 32 * par + cnt by ring]
  · simp only [Result.toState_getReg, eblk_860.res, rv_simp, h22, h23]
    t3n []
    congr 1; omega
  · ex_regs eblk_860.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_860.res, rv_simp, h22]
    t3n []
    rw [if_neg (by omega)]

/-- Open a segment at leaf `g` (`s7 = 0`, `s8 = g mod 2`) and set up the FTS leaf block: the secret `3 s0 + s4`,
the header `T9(coord)`, `index | g << 32`; the HASH arguments `FLEAF`, 64, `NOUT`. -/
theorem rc868_spec (hpc : s.pc = pcOf 868) (c j g index : Nat) (hc : c < 7) (hj : j < 3) (hg : g < 2 ^ 32)
    (hi : index < 2 ^ 32) (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 g) (h9 : s.getReg .x9 = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 31 31 t ∧ t.pc = pcOf 899 ∧ t.getReg .x23 = BitVec.ofNat 64 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 (g % 2) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 32)) = s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j))) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 40)) = s.getMem (BitVec.ofNat 64 (0x7010 + 16 * (3 * c + j) + 8)) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 16)) = BitVec.ofNat 64 (2305 + 65536 * c + 2^32 * index) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 24)) = BitVec.ofNat 64 g ∧
      t.getReg .x10 = BitVec.ofNat 64 FLEAF ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x14, .x23, .x24, .x28, .x30] ∧
      Frame s t (fun A => A = FLEAF + 16 ∨ A = FLEAF + 24 ∨ A = FLEAF + 32 ∨ A = FLEAF + 40) := by
  refine ⟨_, symRun_sound eblk_868 codeAt_868 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_868.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h8, h20, BitVec.ofNat_eq_ofNat, secA]
    exact ⟨ex_valid _ (by omega) (by omega), ex_valid _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_868.res, E.eval]
  · simp [eblk_868.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_868.res, rv_simp, h29, ofNat_and1]
  · simp only [Result.toState_getMem, eblk_868.res, rv_simp, h8, h20, h9, h29, secA, FLEAF]
    t3n []
    congr 2; ring
  · simp only [Result.toState_getMem, eblk_868.res, rv_simp, h8, h20, h9, h29, secA, FLEAF]
    t3n []
    congr 2; ring
  · simp only [Result.toState_getMem, eblk_868.res, rv_simp, h8, h20, h9, h29, secA, FLEAF]
    t3n []
    rw [ofNat_or_disjoint' 2305 (c * 65536) 16 (by norm_num) (by omega),
      ofNat_or_disjoint' (2305 + c * 65536) (index * 4294967296) 32 (by omega) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_868.res, rv_simp, h8, h20, h9, h29, secA, FLEAF] <;>
      t3n [] <;> rfl
  · simp [eblk_868.res, rv_simp]
  · simp [eblk_868.res, rv_simp]
  · simp [eblk_868.res, rv_simp]
  · ex_regs eblk_868.res
  · intro A hA hn
    simp only [FLEAF] at hn
    simp only [Result.toState_getMem, eblk_868.res, rv_simp]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem fetch_899 (hpc : s.pc = pcOf 899) : fetch image s = some (.base .ECALL) :=
  (codeAt_899.fetch s hpc).trans rfl

theorem fetch_992 (hpc : s.pc = pcOf 992) : fetch image s = some (.base .ECALL) :=
  (codeAt_992.fetch s hpc).trans rfl

/-- After the leaf HASH: `a0 = 1`, to `rc_ret`. -/
theorem rc900_spec (hpc : s.pc = pcOf 900) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 994 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_900 codeAt_900 s hpc (by simp [eblk_900.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_900.res, E.eval]
  · simp [eblk_900.res, rv_simp]
  · ex_regs eblk_900.res
  · intro A _ _; simp [eblk_900.res, rv_simp]

/-- `rc_inner`: the left child (`level - 1`, `2 node`), `ra = 905`. -/
theorem rc902_spec (hpc : s.pc = pcOf 902) (level node : Nat) (hl : 1 ≤ level) (hl' : level < 2 ^ 63)
    (hn : 2 * node < 2 ^ 64)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 level) (h11 : s.getReg .x11 = BitVec.ofNat 64 node) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 824 ∧ t.getReg .x10 = BitVec.ofNat 64 (level - 1) ∧
      t.getReg .x11 = BitVec.ofNat 64 (2 * node) ∧ t.getReg .x1 = pcOf 905 ∧
      RegsExcept s t [.x1, .x10, .x11] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_902 codeAt_902 s hpc (by simp [eblk_902.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_902.res, E.eval]
  · simp only [Result.toState_getReg, eblk_902.res, rv_simp, h10]
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_ofNat _ _ hl (by omega)]
  · simp only [Result.toState_getReg, eblk_902.res, rv_simp, h11]
    t3n []
    congr 1; omega
  · simp [eblk_902.res, rv_simp]
  · ex_regs eblk_902.res
  · intro A _ _; simp [eblk_902.res, rv_simp]

/-- After the left child: its live flag and value to the frame (`fp + 24`, `fp + 32`), the right child
(`level - 1`, `2 node + 1`), `ra = 918`. -/
theorem rc905_spec (hpc : s.pc = pcOf 905) (fp : Nat) (hfp8 : fp % 8 = 0) (hfp : fp + 48 ≤ 2 ^ 24)
    (hfpl : 0x20300 ≤ fp) (h2 : s.getReg .x2 = BitVec.ofNat 64 fp) (level node : Nat) (hl : 1 ≤ level)
    (hl' : level < 2 ^ 63) (hn : 2 * node + 1 < 2 ^ 64)
    (hlv : s.getMem (BitVec.ofNat 64 (fp + 8)) = BitVec.ofNat 64 level)
    (hnd : s.getMem (BitVec.ofNat 64 (fp + 16)) = BitVec.ofNat 64 node) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 824 ∧ t.getReg .x1 = pcOf 918 ∧
      t.getReg .x10 = BitVec.ofNat 64 (level - 1) ∧ t.getReg .x11 = BitVec.ofNat 64 (2 * node + 1) ∧
      t.getMem (BitVec.ofNat 64 (fp + 24)) = s.getReg .x10 ∧
      t.getMem (BitVec.ofNat 64 (fp + 32)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (fp + 40)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x1, .x6, .x7, .x10, .x11, .x29] ∧
      Frame s t (fun A => A = fp + 24 ∨ A = fp + 32 ∨ A = fp + 40) := by
  refine ⟨_, symRun_sound eblk_905 codeAt_905 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_905.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_905.res, E.eval]
  · simp [eblk_905.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_905.res, rv_simp, h2, ofNat_add_ofNat]
    rw [hlv, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_ofNat _ _ hl (by omega)]
  · simp only [Result.toState_getReg, eblk_905.res, rv_simp, h2, ofNat_add_ofNat]
    rw [hnd, show ((1#64 : BitVec 64).toNat % 64) = 1 from rfl, ofNat_shl,
      show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add_ofNat]
    congr 1; ring
  iterate 3
    · simp only [Result.toState_getMem, eblk_905.res, rv_simp, h2, ofNat_add_ofNat, NOUT]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | rfl)
  · ex_regs eblk_905.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_905.res, rv_simp, h2, ofNat_add_ofNat]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- After both children: the node block (left value from the frame, right value from `NOUT`, the header
`T10(coord)`, `index | heap << 32`, `heap = 2^(11 - level) + node`), then by the left live flag. -/
theorem rc918_spec (hpc : s.pc = pcOf 918) (fp : Nat) (hfp8 : fp % 8 = 0) (hfp : fp + 48 ≤ 2 ^ 24)
    (hfpl : 0x20300 ≤ fp) (h2 : s.getReg .x2 = BitVec.ofNat 64 fp) (level node c index : Nat) (hl : 1 ≤ level)
    (hl' : level ≤ 11) (hn : node < 2 ^ 11) (hc : c < 7) (hi : index < 2 ^ 32) (ll : Bool)
    (hlv : s.getMem (BitVec.ofNat 64 (fp + 8)) = BitVec.ofNat 64 level)
    (hnd : s.getMem (BitVec.ofNat 64 (fp + 16)) = BitVec.ofNat 64 node)
    (hll : s.getMem (BitVec.ofNat 64 (fp + 24)) = BitVec.ofNat 64 (if ll then 1 else 0))
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h9 : s.getReg .x9 = BitVec.ofNat 64 index) :
    ∃ t, Steps image s 34 34 t ∧ t.pc = (if ll then pcOf 962 else pcOf 952) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (fp + 32)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (fp + 40)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (2561 + 65536 * c + 2^32 * index) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (2 ^ (11 - level) + node) ∧
      RegsExcept s t [.x6, .x7, .x13, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
        A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_918 codeAt_918 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_918.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [rv_simp, accessValid_iff, MEMORY_BYTES]; decide)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp only [Result.toState_pc, eblk_918.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h2,
      BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    rw [hll]; cases ll <;> simp
  iterate 4
    · simp only [Result.toState_getMem, eblk_918.res, rv_simp, h2, h8, h9, ofNat_add_ofNat, NODE, NOUT]
      t3n []
  · simp only [Result.toState_getMem, eblk_918.res, rv_simp, h2, h8, h9, ofNat_add_ofNat, NODE, NOUT]
    t3n []
    rw [ofNat_or_disjoint' 2561 (c * 65536) 16 (by norm_num) (by omega),
      ofNat_or_disjoint' (2561 + c * 65536) (index * 4294967296) 32 (by omega) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_918.res, rv_simp, h2, h8, h9, ofNat_add_ofNat, NODE, NOUT]
    t3n []
    rw [hlv, hnd, show (11#64 : BitVec 64) = BitVec.ofNat 64 11 from rfl, ofNat_sub_ofNat 11 level hl' (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 11 - level < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 11 - level < 64 by omega), Nat.one_mul, ofNat_add_ofNat]
  · ex_regs eblk_918.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_918.res, rv_simp]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

/-- Fold `L`: the left (empty) child's value from the frame into fold block `s7` of the open segment
(`s6 + 8 + 80 s7`), `s7 += 1`. -/
theorem rc952_spec (hpc : s.pc = pcOf 952) (fp : Nat) (hfp8 : fp % 8 = 0) (hfp : fp + 48 ≤ 2 ^ 24)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 fp) (ptr cnt : Nat) (hp8 : ptr % 8 = 0) (hcnt : cnt < 2 ^ 20)
    (hfit : ptr + 80 * cnt + 24 ≤ fp) (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 987 ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 8)) = s.getMem (BitVec.ofNat 64 (fp + 32)) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 16)) = s.getMem (BitVec.ofNat 64 (fp + 40)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (cnt + 1) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x30] ∧
      Frame s t (fun A => A = ptr + 80 * cnt + 8 ∨ A = ptr + 80 * cnt + 16) := by
  have ha : BitVec.ofNat 64 cnt <<< ((6#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 cnt <<<
      ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 ptr = BitVec.ofNat 64 (ptr + 80 * cnt) := by
    rw [show ((6#64 : BitVec 64).toNat % 64) = 6 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
      ofNat_shl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]; congr 1; ring
  refine ⟨_, symRun_sound eblk_952 codeAt_952 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_952.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, h22, h23, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat, ha]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_952.res, E.eval]
  iterate 2
    · simp only [Result.toState_getMem, eblk_952.res, rv_simp, h2, h22, h23, ofNat_add_ofNat, ha]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | rfl | (congr 2; ring))
  · simp only [Result.toState_getReg, eblk_952.res, rv_simp, h23, ofNat_add_ofNat]
  · ex_regs eblk_952.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_952.res, rv_simp, h2, h22, h23, ofNat_add_ofNat, ha]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `rc_lc`: the right child live means a merge. -/
theorem rc962_spec (hpc : s.pc = pcOf 962) (rl : Bool)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (if rl then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if rl then pcOf 975 else pcOf 963) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_962 codeAt_962 s hpc (by simp [eblk_962.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_962.res, E.eval, CmpOp.eval, BinOp.eval, rebase, RegFile.get, h10,
      BitVec.ofNat_eq_ofNat]
    cases rl <;> simp
  · ex_regs eblk_962.res
  · intro A _ _; simp [eblk_962.res, rv_simp]

/-- Fold `R`: the right (empty) child's value (`NOUT`) into fold block `s7` at `+48`, `s7 += 1`. -/
theorem rc963_spec (hpc : s.pc = pcOf 963) (ptr cnt : Nat) (hp8 : ptr % 8 = 0) (hcnt : cnt < 2 ^ 20)
    (hfit : ptr + 80 * cnt + 72 ≤ 0x20200) (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 987 ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 56)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ptr + 80 * cnt + 64)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (cnt + 1) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = ptr + 80 * cnt + 56 ∨ A = ptr + 80 * cnt + 64) := by
  have ha : BitVec.ofNat 64 cnt <<< ((6#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 cnt <<<
      ((4#64 : BitVec 64).toNat % 64) + BitVec.ofNat 64 ptr = BitVec.ofNat 64 (ptr + 80 * cnt) := by
    rw [show ((6#64 : BitVec 64).toNat % 64) = 6 from rfl, show ((4#64 : BitVec 64).toNat % 64) = 4 from rfl,
      ofNat_shl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]; congr 1; ring
  refine ⟨_, symRun_sound eblk_963 codeAt_963 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_963.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h23, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat, ha]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by simp only [NOUT]; omega)
        | (simp only [rv_simp, accessValid_iff, MEMORY_BYTES]; decide)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_963.res, E.eval]
  iterate 2
    · simp only [Result.toState_getMem, eblk_963.res, rv_simp, h22, h23, ofNat_add_ofNat, ha, NOUT]
      t3n []
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | rfl | (congr 2; ring))
  · simp only [Result.toState_getReg, eblk_963.res, rv_simp, h23, ofNat_add_ofNat]
  · ex_regs eblk_963.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_963.res, rv_simp, h22, h23, ofNat_add_ofNat, ha]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

/-- `rc_merge`: close the open segment with the merge flag, open a new one at the node (`s8 = node mod 2`). -/
theorem rc975_spec (hpc : s.pc = pcOf 975) (fp : Nat) (hfp8 : fp % 8 = 0) (hfp : fp + 48 ≤ 2 ^ 24)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 fp) (ptr cnt par node : Nat) (hp8 : ptr % 8 = 0)
    (hcnt : cnt < 16) (hpar : par < 2) (hfit : ptr + 8 + 80 * cnt < 2 ^ 24) (hpf : ptr + 8 ≤ fp)
    (hnd : s.getMem (BitVec.ofNat 64 (fp + 16)) = BitVec.ofNat 64 node)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 ptr) (h23 : s.getReg .x23 = BitVec.ofNat 64 cnt)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 par) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf 987 ∧
      t.getMem (BitVec.ofNat 64 ptr) =
        replaceByte (s.getMem (BitVec.ofNat 64 ptr)) 0 ((BitVec.ofNat 64 (32 * par + cnt + 16)).truncate 8) ∧
      t.getReg .x22 = BitVec.ofNat 64 (ptr + 80 * cnt + 8) ∧ t.getReg .x23 = BitVec.ofNat 64 0 ∧
      t.getReg .x24 = BitVec.ofNat 64 (node % 2) ∧
      RegsExcept s t [.x22, .x23, .x24, .x28, .x30] ∧ Frame s t (fun A => A = ptr) := by
  refine ⟨_, symRun_sound eblk_975 codeAt_975 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_975.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, h22, BitVec.ofNat_eq_ofNat, ofNat_add_ofNat]
    and_intros
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | (rw [toNat_ofNat_lt (by omega)]; exact hp8)
        | (simp only [Nat.add_zero]; rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega)
        | (intro he; have := congrArg BitVec.toNat he; simp at this; omega)
  · simp [Result.toState_pc, eblk_975.res, E.eval]
  · simp only [Result.toState_getMem, eblk_975.res, rv_simp, h2, h22, h23, h24, ofNat_add_ofNat]
    t3n []
    rw [BitVec.or_assoc, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_or_disjoint' cnt 16 4 (by omega) (by omega), ofNat_or_disjoint (cnt + 16) (par * 32) 5 (by omega) (by omega)]
    rw [if_pos (by simp)]
    congr 3; ring
  · simp only [Result.toState_getReg, eblk_975.res, rv_simp, h22, h23]
    t3n []
    congr 1; omega
  · simp [eblk_975.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_975.res, rv_simp, h2, ofNat_add_ofNat, hnd, ofNat_and1]
  · ex_regs eblk_975.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_975.res, rv_simp, h22]
    t3n []
    rw [if_neg (by omega)]

/-- The node HASH arguments `NODE`, 64, `NOUT`. -/
theorem rc987_spec (hpc : s.pc = pcOf 987) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf 992 ∧ t.getReg .x10 = BitVec.ofNat 64 NODE ∧
      t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_987 codeAt_987 s hpc (by simp [eblk_987.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_987.res, E.eval]
  · simp [eblk_987.res, rv_simp]
  · simp [eblk_987.res, rv_simp]
  · simp [eblk_987.res, rv_simp]
  · ex_regs eblk_987.res
  · intro A _ _; simp [eblk_987.res, rv_simp]

/-- After the node HASH: `a0 = 1`. -/
theorem rc993_spec (hpc : s.pc = pcOf 993) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 994 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_993 codeAt_993 s hpc (by simp [eblk_993.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_993.res, E.eval]
  · simp [eblk_993.res, rv_simp]
  · ex_regs eblk_993.res
  · intro A _ _; simp [eblk_993.res, rv_simp]

/-- `rc_ret`: `ra` from the frame, `sp += 48`, return. -/
theorem rc994_spec (hpc : s.pc = pcOf 994) (fp ret : Nat) (hfp8 : fp % 8 = 0) (hfp : fp + 48 ≤ 2 ^ 24)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 fp) (hra : s.getMem (BitVec.ofNat 64 fp) = pcOf ret) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf ret ∧ t.getReg .x2 = BitVec.ofNat 64 (fp + 48) ∧
      t.getReg .x1 = pcOf ret ∧ RegsExcept s t [.x1, .x2] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_994 codeAt_994 s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_994.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h2, BitVec.ofNat_eq_ofNat, add_zero]
    simp only [rv_simp, accessValid_iff, MEMORY_BYTES, BitVec.toNat_ofNat]
    try omega
  · simp only [Result.toState_pc, eblk_994.res, rv_simp, h2, hra, pcOf_and_max]
  · simp only [Result.toState_getReg, eblk_994.res, rv_simp, h2, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, eblk_994.res, rv_simp, h2, hra]
  · ex_regs eblk_994.res
  · intro A _ _; simp [eblk_994.res, rv_simp]

end blocks

end SigGolfCandidate.T3M.Expand
