import SigGolfCandidate.Expand.PorsBlk

/-!
# `expand`, phase 2: one PORS segment (`pr_seg` .. `pr_fold`, instructions 550 .. 594)

`segment_sim` : from `pr_seg` with the segment header at `W + ptr`, the heap index `E` in `s3`
and the pending hash staged (`PendOK`), the machine refines `Ref.segment` and stops at
`pr_segend` (595) with the header byte in `t1`, `a` in `t2`, the new `E` in `s3` and the new
node at `OUT` (`SegOut`), or HALT(1).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- Registers a segment writes. -/
def segRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x28, .x29]

/-- Registers the fold loop writes. -/
def foldRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x28, .x29]

/-- Addresses a segment writes: `PB` word 1, `PB`'s children, `OUT`. -/
def segW (a : Nat) : Prop := a = 0x30048 ∨ (0x30060 ≤ a ∧ a < 0x300A0)

theorem pctx_segW : ∀ a, pctxA a → ¬ segW a := by
  intro a h1 h2; unfold pctxA witA at h1; unfold segW at h2; omega

/-- The body of `segFolds`' `foldlM`. -/
def foldF (idx : Nat) (w : List Byte) (ptr : Nat) (st : Val × Nat) (i : Nat) :
    OracleComp HashSpec (Val × Nat) :=
  let sib := wbytes w (ptr + 64 + 64 * i) 16
  if st.2 % 2 = 1 then do
    let v ← hash16 (porsNodeInput idx (st.2 / 2) sib st.1)
    pure (v, st.2 / 2)
  else do
    let v ← hash16 (porsNodeInput idx (st.2 / 2) st.1 sib)
    pure (v, st.2 / 2)

theorem segFolds_eq (idx : Nat) (w : List Byte) (ptr a : Nat) (node : Val) (E : Nat) :
    segFolds idx w ptr a node E = (List.range a).foldlM (foldF idx w ptr) (node, E) := rfl

/-- Fold invariant after `j` of the `a` folds of the segment with header at `ptr` (`u`: the
state at the loop's start). -/
def FInv (w : List Byte) (idx : Nat) (K : Nat → Nat) (u : MachineState) (ptr a j : Nat) (st : Val × Nat)
    (t : MachineState) : Prop :=
  t.pc = pcOf 567 ∧ PCtx w idx K t ∧ j ≤ a ∧
  t.getReg .x28 = BitVec.ofNat 64 (0x800 + ptr + 64 + 64 * j) ∧ t.getReg .x29 = BitVec.ofNat 64 (a - j) ∧
  t.getReg .x19 = BitVec.ofNat 64 st.2 ∧ st.2 < 2 ^ 15 ∧ st.1.length = 16 ∧
  t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf st.1 ∧
  RegsEq u t foldRegs ∧ Frame u t segW

theorem fold_body (w : List Byte) (idx : Nat) (K : Nat → Nat) (u : MachineState) (ptr a : Nat)
    (hptr : ptr % 8 = 0) (hpa : ptr + 64 + 64 * a ≤ 0x10000) :
    ∀ j < a, ∀ (st : Val × Nat) (t : MachineState), FInv w idx K u ptr a j st t →
      Sim eimg t 59 (foldF idx w ptr st j) (FInv w idx K u ptr a (j + 1)) := by
  intro j hj st t hinv
  obtain ⟨node, E⟩ := st
  obtain ⟨tpc, tc, hja, t28, t29, t19, hE, hl, tout, tregs, tframe⟩ := hinv
  dsimp only at t19 hE hl tout
  have hidx := tc.hidx
  obtain ⟨t1, hs1, p1, r1, m1⟩ := blk567_run t tpc (a - j) (by omega) t29
  rw [if_neg (by omega)] at p1
  have c1 : PCtx w idx K t1 := tc.frame (W := fun _ => False) (fun x _ _ => m1 _) r1 (fun _ _ h => h)
  set o := ptr + 64 + 64 * j with ho
  obtain ⟨t2, hs2, p2, y14, y15, y16, y17, m72, r2, f2⟩ := blk568_run w idx t1 p1 E o hE (by omega) (by omega)
    c1.wit (by rw [r1.get .x19, t19]) c1.x25 c1.x26 (by rw [r1.get .x28, t28]; exact ofNat_congr (by omega))
  have c2 : PCtx w idx K t2 := c1.frame f2 r2 (fun a h1 h2 => by unfold pctxA witA at h1; omega)
  have hsib : [wword w o, wword w (o + 8)] = wordsOf (wbytes w o 16) := (wordsOf_wbytes16 w o).symm
  have hnode : [t1.getMem (BitVec.ofNat 64 0x30080), t1.getMem (BitVec.ofNat 64 0x30088)] = wordsOf node := by
    rw [← tout, readWords_ofNat_two, m1, m1]
  have hsl : (wbytes w o 16).length = 16 := length_wbytes _ _ _
  have hH : Rev.efield (E / 2) < 2 ^ 32 := Rev.efield_lt _
  -- the common tail: `PB` staged at `t3` (pc 587), hash, 591
  have tail : ∀ (t3 : MachineState) (k3 : Nat) (l r : Val), Steps eimg t2 k3 k3 t3 → k3 ≤ 5 →
      t3.pc = pcOf 587 → l.length = 16 → r.length = 16 →
      t3.readWords (BitVec.ofNat 64 0x30060) 2 = wordsOf l →
      t3.readWords (BitVec.ofNat 64 0x30070) 2 = wordsOf r → RegsEq t2 t3 [] →
      Frame t2 t3 (fun x => 0x30060 ≤ x ∧ x < 0x30080) →
      Sim eimg t 59 (do
          let v ← hash16 (porsNodeInput idx (E / 2) l r)
          pure (v, E / 2)) (FInv w idx K u ptr a (j + 1)) := by
    intro t3 k3 l r hs3 hk3 p3 hl' hr' w3l w3r r3 f3
    have c3 : PCtx w idx K t3 := c2.frame f3 r3 (fun a h1 h2 => by unfold pctxA witA at h1; omega)
    obtain ⟨t4, hs4, e4, p4, x10, x11, x12, r4, m4⟩ := blk587_run t3 p3 c3.x25
    have c4 : PCtx w idx K t4 := c3.frame (W := fun _ => False) (fun x _ _ => m4 _) r4 (fun _ _ h => h)
    have hq : hashInput t4 = pad64 (porsNodeInput idx (Rev.efield (E / 2)) l r) := by
      refine hashInput_eq_pad64 t4 _ 0 (words_th32 10 0 idx 0 (Rev.efield (E / 2)) l r hl' hr').1 x11 (by norm_num)
        (by rw [x10]; decide) ?_
      rw [x10]
      refine pb_words w idx K t4 c4 (Rev.efield (E / 2)) hH l r hl' hr' ?_ ?_ ?_
      · rw [m4, f3.getMem (by norm_num) (by omega), m72]
      · rw [readWords_ofNat_two, m4, m4, ← readWords_ofNat_two, w3l]
      · rw [readWords_ofNat_two, m4, m4, ← readWords_ofNat_two, w3r]
    have hbf : (fmt (porsNodeInput idx (E / 2) l r)).blocks = 1 := by
      rw [← addrFmt_blocks, fmt_porsNode _ _ _ _ hl' hr', blocks_porsNode _ _ _ _ hl' hr']
    refine (Sim.steps hs1 (Sim.steps hs2 (Sim.steps hs3 (Sim.steps hs4 (Sim.hash16_bindF (W := 4) e4 c4.x5
      (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)) (hq.trans (fmt_porsNode _ _ _ _ hl' hr').symm) (fun ans => ?_)))))).mono
      (by rw [hbf]; omega) (fun _ _ h => h)
    set t5 := writeHash t4 ans with ht5
    have p5 : t5.pc = pcOf 591 := by rw [ht5, writeHash_pc, p4]; rfl
    have f5 : Frame t4 t5 (fun x => 0x30080 ≤ x ∧ x < 0x30080 + 32) := frame_writeHash t4 ans _ x12 (by norm_num)
    have c5 : PCtx w idx K t5 := c4.frame f5 (regsEq_writeHash t4 ans [])
      (fun a h1 h2 => by unfold pctxA witA at h1; omega)
    have hx19 : t5.getReg .x19 = BitVec.ofNat 64 E := by
      rw [ht5, writeHash_getReg, r4.get .x19, r3.get .x19, r2.get .x19, r1.get .x19, t19]
    have hx28 : t5.getReg .x28 = BitVec.ofNat 64 (0x800 + ptr + 64 + 64 * j) := by
      rw [ht5, writeHash_getReg, r4.get .x28, r3.get .x28, r2.get .x28, r1.get .x28, t28]
    have hx29 : t5.getReg .x29 = BitVec.ofNat 64 (a - j) := by
      rw [ht5, writeHash_getReg, r4.get .x29, r3.get .x29, r2.get .x29, r1.get .x29, t29]
    obtain ⟨t6, hs6, p6, z19, z28, z29, r6, m6⟩ := blk591_run t5 p5 E _ (a - j) hE (by omega) (by omega)
      (by omega) hx19 hx28 hx29
    refine Sim.pure_steps hs6 ⟨p6, c5.frame (W := fun _ => False) (fun x _ _ => m6 _) r6 (fun _ _ h => h),
      by omega, ?_, ?_, z19, by omega, by simp [answerBytes], ?_, ?_, ?_⟩
    · rw [z28]; exact ofNat_congr (by omega)
    · rw [z29]; exact ofNat_congr (by omega)
    · rw [readWords_ofNat_two, m6, m6, ← readWords_ofNat_two, ht5,
        writeHash_readWords_val t4 ans _ x12 (by norm_num)]
    · have := ((((((tregs.trans r1).trans r2).trans r3).trans r4).trans (regsEq_writeHash t4 ans [])).trans r6)
      exact this.mono (by decide)
    · have f6 : Frame t5 t6 (fun _ => False) := fun x _ _ => m6 _
      have f1 : Frame t t1 (fun _ => False) := fun x _ _ => m1 _
      have f4 : Frame t3 t4 (fun _ => False) := fun x _ _ => m4 _
      exact ((((((tframe.trans f1).trans f2).trans f3).trans f4).trans f5).trans f6).mono (by
        intro x hx; simp only [segW, or_false, false_or] at hx ⊢; omega)
  unfold foldF
  dsimp only
  by_cases hodd : E % 2 = 1
  · rw [if_pos hodd]
    rw [if_neg (by omega)] at p2
    obtain ⟨t3, hs3, p3, w3l, w3r, r3, f3⟩ := blk578_run t2 p2 c2.x25
    refine tail t3 5 _ _ hs3 le_rfl p3 hsl hl ?_ ?_ r3 f3
    · rw [w3l, y14, y15, hsib]
    · rw [w3r, y16, y17, hnode]
  · rw [if_neg hodd]
    rw [if_pos (by omega)] at p2
    obtain ⟨t3, hs3, p3, w3l, w3r, r3, f3⟩ := blk583_run t2 p2 c2.x25
    refine tail t3 4 _ _ hs3 (by norm_num) p3 hl hsl ?_ ?_ r3 f3
    · rw [w3l, y16, y17, hnode]
    · rw [w3r, y14, y15, hsib]

/-! ## The segment -/

/-- The pending hash of a segment, staged: a leaf in `LB` (`s8 = 0`: word 1, secret) or a merge in
`PB` (`s8 = 1`: word 1, the popped node, the current node). -/
def PendOK (idx : Nat) (node : Val) : Pending → MachineState → Prop
  | .leaf x s, t => t.getReg .x24 = BitVec.ofNat 64 0 ∧ x < 2 ^ 32 ∧ s.length = 16 ∧
      t.getMem (BitVec.ofNat 64 0x30008) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * x) ∧
      t.readWords (BitVec.ofNat 64 0x30020) 2 = wordsOf s
  | .merge H l, t => t.getReg .x24 = BitVec.ofNat 64 1 ∧ H < 2 ^ 32 ∧ l.length = 16 ∧ node.length = 16 ∧
      t.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * Rev.efield H) ∧
      t.readWords (BitVec.ofNat 64 0x30060) 2 = wordsOf l ∧
      t.readWords (BitVec.ofNat 64 0x30070) 2 = wordsOf node

/-- The outcome of a segment at `pr_segend` (595); `u` is the state at `pr_seg`. -/
def SegOut (w : List Byte) (idx : Nat) (K : Nat → Nat) (u : MachineState) (ptr folds : Nat) :
    Nat × Nat × Nat × Val × Bool → MachineState → Prop
  | (ptr', E', folds', node', merge), t => t.pc = pcOf 595 ∧ PCtx w idx K t ∧
      ptr' = ptr + 64 + 64 * (wbyte w ptr % 16) ∧ folds' = folds + wbyte w ptr % 16 ∧
      wbyte w ptr % 16 ≤ 14 ∧ merge = decide (wbyte w ptr / 16 % 2 = 1) ∧
      t.getReg .x6 = BitVec.ofNat 64 (wbyte w ptr) ∧ t.getReg .x7 = BitVec.ofNat 64 (wbyte w ptr % 16) ∧
      t.getReg .x19 = BitVec.ofNat 64 E' ∧ E' < 2 ^ 15 ∧ node'.length = 16 ∧
      t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf node' ∧
      RegsEq u t segRegs ∧ Frame u t segW

/-- After the pending hash (pc 565): the folds, then `pr_segend`. -/
theorem seg_folds (w : List Byte) (idx : Nat) (K : Nat → Nat) (u : MachineState) (ptr E folds : Nat) (v : Val)
    (t : MachineState) (hc : PCtx w idx K t) (hpc : t.pc = pcOf 565) (hv : v.length = 16)
    (h6 : t.getReg .x6 = BitVec.ofNat 64 (wbyte w ptr)) (h7 : t.getReg .x7 = BitVec.ofNat 64 (wbyte w ptr % 16))
    (h9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr)) (h19 : t.getReg .x19 = BitVec.ofNat 64 E)
    (hE : E < 2 ^ 15) (hptr : ptr % 8 = 0) (hptr' : ptr + 960 ≤ 0x10000) (ha : wbyte w ptr % 16 ≤ 14)
    (hout : t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf v)
    (tregs : RegsEq u t segRegs) (tframe : Frame u t segW) :
    Sim eimg t 900 (segFolds idx w ptr (wbyte w ptr % 16) v E >>= fun x => match x with
      | (node, E) => pure (some (ptr + 64 + 64 * (wbyte w ptr % 16), E, folds + wbyte w ptr % 16, node,
          decide (wbyte w ptr / 16 % 2 = 1))))
      (OPost (SegOut w idx K u ptr folds)) := by
  obtain ⟨t1, hs1, p1, y28, y29, r1, m1⟩ := blk565_run t hpc ptr (wbyte w ptr % 16) h9 h7
  have c1 : PCtx w idx K t1 := hc.frame (W := fun _ => False) (fun x _ _ => m1 _) r1 (fun _ _ h => h)
  have h0 : FInv w idx K t1 ptr (wbyte w ptr % 16) 0 (v, E) t1 :=
    ⟨p1, c1, by omega, y28, y29, by rw [r1.get .x19, h19], hE, hv,
      by rw [readWords_ofNat_two, m1, m1, ← readWords_ofNat_two, hout], RegsEq.refl _ _, Frame.refl _ _⟩
  have hl := Sim.foldlM_range (image := eimg) (wbyte w ptr % 16) (foldF idx w ptr) (v, E)
    (FInv w idx K t1 ptr (wbyte w ptr % 16)) 59 (fold_body w idx K t1 ptr _ hptr (by omega)) h0
  rw [segFolds_eq]
  refine (Sim.steps hs1 (Sim.bind hl (W₂ := 1) (fun p t2 h2 => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨node', E'⟩ := p
  obtain ⟨p2, c2, -, z28, z29, z19, hE', hl', hout', r2, f2⟩ := h2
  dsimp only at z19 hE' hl' hout'
  obtain ⟨t3, hs3, p3, r3, m3⟩ := blk567_run t2 p2 _ (by omega) z29
  rw [if_pos (by omega)] at p3
  dsimp only
  have g3 : ∀ x, t3.getReg x = t2.getReg x := fun x => r3 x (by simp)
  refine Sim.pure_steps hs3 ⟨p3, c2.frame (W := fun _ => False) (fun x _ _ => m3 _) r3 (fun _ _ h => h),
    rfl, rfl, ha, rfl, ?_, ?_, by rw [g3, z19], hE', hl', ?_, ?_, ?_⟩
  · rw [g3, r2.get .x6, r1.get .x6, h6]
  · rw [g3, r2.get .x7, r1.get .x7, h7]
  · rw [readWords_ofNat_two, m3, m3, ← readWords_ofNat_two, hout']
  · exact ((tregs.trans r1).trans (r2.trans r3)).mono (by decide)
  · have f1 : Frame t t1 (fun _ => False) := fun x _ _ => m1 _
    have f3 : Frame t2 t3 (fun _ => False) := fun x _ _ => m3 _
    exact (((tframe.trans f1).trans f2).trans f3).mono (by intro x hx; simp only [segW, or_false, false_or] at hx ⊢; omega)

/-- **One segment** (`Ref.segment`), from `pr_seg` to `pr_segend` or HALT(1). -/
theorem segment_sim (w : List Byte) (idx : Nat) (K : Nat → Nat) (ptr E folds : Nat) (pending : Pending)
    (node : Val) (t : MachineState) (hc : PCtx w idx K t) (hpc : t.pc = pcOf 550)
    (h9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr)) (h19 : t.getReg .x19 = BitVec.ofNat 64 E)
    (hptr : ptr % 8 = 0) (hptr' : ptr + 960 ≤ 0x10000) (hE : E < 2 ^ 15) (hpend : PendOK idx node pending t) :
    Sim eimg t 950 (Ref.segment idx w ptr E folds pending node) (OPost (SegOut w idx K t ptr folds)) := by
  have hb : wbyte w ptr < 256 := (w.getD ptr 0).isLt
  obtain ⟨t1, hs1, p1, y6, y7, r1, m1⟩ := blk550_run w t ptr hpc h9 hptr (by omega) hc.wit
  unfold Ref.segment
  dsimp only
  by_cases ha : wbyte w ptr % 16 > porsH
  · rw [if_pos ha]
    rw [if_pos (by unfold porsH at ha; omega)] at p1
    exact (fail_sim_steps hs1 p1).mono (by norm_num) (fun _ _ h => h)
  rw [if_neg ha]
  have ha' : wbyte w ptr % 16 ≤ 14 := by unfold porsH at ha; omega
  rw [if_neg (by omega)] at p1
  have c1 : PCtx w idx K t1 := hc.frame (W := fun _ => False) (fun x _ _ => m1 _) r1 (fun _ _ h => h)
  suffices hmain : ∀ (t2 : MachineState) (k : Nat), Steps eimg t1 k k t2 → k ≤ 5 → t2.pc = pcOf 559 →
      RegsEq t1 t2 [.x13, .x14] → (∀ x, t2.getMem x = t1.getMem x) →
      Sim eimg t 950 (pendingHash idx node pending >>= fun node =>
        segFolds idx w ptr (wbyte w ptr % 16) node E >>= fun x => match x with
          | (node, E) => pure (some (ptr + 64 + 64 * (wbyte w ptr % 16), E, folds + wbyte w ptr % 16, node,
              decide (wbyte w ptr / 16 % 2 = 1))))
        (OPost (SegOut w idx K t ptr folds)) by
    obtain ⟨t2, hs2, p2, r2, m2⟩ := blk554_run t1 p1 _ (by omega) y7
    by_cases h0 : wbyte w ptr % 16 = 0
    · rw [if_neg (by omega)]
      rw [if_pos h0] at p2
      exact hmain t2 1 hs2 (by norm_num) p2 (r2.mono (by simp)) m2
    · rw [if_neg h0] at p2
      obtain ⟨t3, hs3, p3, r3, m3⟩ := blk555_run t2 p2 (wbyte w ptr) E hb hE (by rw [r2.get .x6, y6])
        (by rw [r2.get .x19, r1.get .x19, h19])
      by_cases hd : wbyte w ptr / 32 % 2 ≠ E % 2
      · rw [if_pos ⟨by omega, hd⟩]
        rw [if_pos hd] at p3
        exact (Sim.steps hs1 (Sim.steps hs2 (fail_sim_steps hs3 p3))).mono (by norm_num) (fun _ _ h => h)
      · rw [if_neg (by omega)]
        rw [if_neg hd] at p3
        exact hmain t3 5 (hs2.trans hs3) (by norm_num) p3 ((r2.trans r3).mono (by decide))
          (fun x => by rw [m3, m2])
  intro t2 k hs2 hk p2 r2 m2
  have c2 : PCtx w idx K t2 := c1.frame (W := fun _ => False) (fun x _ _ => m2 _) r2 (fun _ _ h => h)
  have g2 : ∀ x, t2.getMem x = t.getMem x := fun x => by rw [m2, m1]
  have x24 : t2.getReg .x24 = t.getReg .x24 := by rw [r2.get .x24, r1.get .x24]
  -- the hash, then the folds
  have after : ∀ (t4 : MachineState) (k4 c4 : Nat) (v : Val) (q p : List Byte), Steps eimg t2 k4 c4 t4 → c4 ≤ 5 →
      fetch eimg t4 = some (.base .ECALL) → t4.pc = pcOf 564 →
      t4.getReg .x10 = BitVec.ofNat 64 0x30000 ∨ t4.getReg .x10 = BitVec.ofNat 64 0x30040 →
      t4.getReg .x11 = BitVec.ofNat 64 64 → t4.getReg .x12 = BitVec.ofNat 64 0x30080 →
      RegsEq t2 t4 [.x10, .x11, .x12] → (∀ x, t4.getMem x = t2.getMem x) →
      hashInput t4 = pad64 p → addrFmt q = pad64 p → (pad64 p).blocks = 1 →
      Sim eimg t 950 (hash16 q >>= fun node =>
        segFolds idx w ptr (wbyte w ptr % 16) node E >>= fun x => match x with
          | (node, E) => pure (some (ptr + 64 + 64 * (wbyte w ptr % 16), E, folds + wbyte w ptr % 16, node,
              decide (wbyte w ptr / 16 % 2 = 1))))
        (OPost (SegOut w idx K t ptr folds)) := by
    intro t4 k4 c4 v q p hs4 hc4 e4 p4 x10 x11 x12 r4 m4 hq hfq hbq
    have c4' : PCtx w idx K t4 := c2.frame (W := fun _ => False) (fun x _ _ => m4 _) r4 (fun _ _ h => h)
    have hv : hashArgumentsValid t4 = true := by
      rcases x10 with x10 | x10 <;>
      exact hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
    have hbf : (fmt q).blocks = 1 := by rw [← addrFmt_blocks, hfq, hbq]
    refine (Sim.steps hs1 (Sim.steps hs2 (Sim.steps hs4 (Sim.hash16_bindF (W := 900) e4 c4'.x5 hv (hq.trans hfq.symm)
      (fun ans => ?_))))).mono (by rw [hbf]; clear * - hk hc4; omega) (fun _ _ h => h)
    set t5 := writeHash t4 ans with ht5
    have p5 : t5.pc = pcOf 565 := by rw [ht5, writeHash_pc, p4]; rfl
    have f5 : Frame t4 t5 (fun x => 0x30080 ≤ x ∧ x < 0x30080 + 32) := frame_writeHash t4 ans _ x12 (by norm_num)
    have r45 : RegsEq t t5 segRegs :=
      ((((r1.trans r2).trans r4).trans (regsEq_writeHash t4 ans [])).mono (by decide))
    have g5 : ∀ r, r ∉ segRegs → t5.getReg r = t.getReg r := r45
    refine seg_folds w idx K t ptr E folds (answerBytes 16 ans) t5
      (c4'.frame f5 (regsEq_writeHash t4 ans []) (fun a h1 h2 => by unfold pctxA witA at h1; omega))
      p5 (by simp [answerBytes]) ?_ ?_ (by rw [g5 .x9 (by decide), h9]) ?_ hE hptr hptr' ha' ?_ r45 ?_
    · rw [ht5, writeHash_getReg, r4.get .x6, r2.get .x6, y6]
    · rw [ht5, writeHash_getReg, r4.get .x7, r2.get .x7, y7]
    · rw [ht5, writeHash_getReg, r4.get .x19, r2.get .x19, r1.get .x19, h19]
    · rw [ht5, writeHash_readWords_val t4 ans _ x12 (by norm_num)]
    · have f14 : Frame t t4 (fun _ => False) := fun x _ _ => by rw [m4, g2]
      exact (f14.trans f5).mono (by intro x hx; simp only [segW, or_false, false_or] at hx ⊢; omega)
  cases pending with
  | leaf x s =>
    obtain ⟨k24, hx, hs, m8, msec⟩ := hpend
    obtain ⟨t3, c3, hs3, hc3, p3, x10, r3, m3⟩ := blk559_run t2 p2 0 (by norm_num) (by rw [x24, k24]) c2.x25
    rw [if_pos rfl] at x10
    obtain ⟨t4, hs4, e4, p4, x11, x12, r4, m4⟩ := blk562_run t3 p3 (by rw [r3.get .x25, c2.x25])
    have x10' : t4.getReg .x10 = BitVec.ofNat 64 0x30000 := by rw [r4.get .x10, x10]
    have c4 : PCtx w idx K t4 := (c2.frame (W := fun _ => False) (fun x _ _ => m3 _) r3 (fun _ _ h => h)).frame
      (W := fun _ => False) (fun x _ _ => m4 _) r4 (fun _ _ h => h)
    have g4 : ∀ x, t4.getMem x = t.getMem x := fun x => by rw [m4, m3, g2]
    have hq : hashInput t4 = pad64 (porsLeafInput idx x s) := by
      refine hashInput_eq_pad64 t4 _ 0 (words_th16 9 0 idx 0 x s hs).1 x11 (by norm_num)
        (by rw [x10']; decide) ?_
      rw [x10']
      refine lb_words w idx K t4 c4 x hx s hs (by rw [g4, m8]) ?_
      rw [readWords_ofNat_two, g4, g4, ← readWords_ofNat_two, msec]
    simp only [pendingHash]
    exact after t4 _ _ [] _ _ (hs3.trans hs4) (by omega) e4 p4 (Or.inl x10') x11 x12
      ((r3.trans r4).mono (by decide)) (fun x => by rw [m4, m3]) hq (fmt_porsLeaf _ _ _)
      (blocks_porsLeaf _ _ _ hs)
  | merge H l =>
    obtain ⟨k24, hH, hl, hn, m72, ml, mn⟩ := hpend
    obtain ⟨t3, c3, hs3, hc3, p3, x10, r3, m3⟩ := blk559_run t2 p2 1 (by norm_num) (by rw [x24, k24]) c2.x25
    rw [if_neg (by norm_num)] at x10
    obtain ⟨t4, hs4, e4, p4, x11, x12, r4, m4⟩ := blk562_run t3 p3 (by rw [r3.get .x25, c2.x25])
    have x10' : t4.getReg .x10 = BitVec.ofNat 64 0x30040 := by rw [r4.get .x10, x10]
    have c4 : PCtx w idx K t4 := (c2.frame (W := fun _ => False) (fun x _ _ => m3 _) r3 (fun _ _ h => h)).frame
      (W := fun _ => False) (fun x _ _ => m4 _) r4 (fun _ _ h => h)
    have g4 : ∀ x, t4.getMem x = t.getMem x := fun x => by rw [m4, m3, g2]
    have hq : hashInput t4 = pad64 (porsNodeInput idx (Rev.efield H) l node) := by
      refine hashInput_eq_pad64 t4 _ 0 (words_th32 10 0 idx 0 (Rev.efield H) l node hl hn).1 x11 (by norm_num)
        (by rw [x10']; decide) ?_
      rw [x10']
      refine pb_words w idx K t4 c4 (Rev.efield H) (Rev.efield_lt H) l node hl hn (by rw [g4, m72]) ?_ ?_
      · rw [readWords_ofNat_two, g4, g4, ← readWords_ofNat_two, ml]
      · rw [readWords_ofNat_two, g4, g4, ← readWords_ofNat_two, mn]
    simp only [pendingHash]
    exact after t4 _ _ [] _ _ (hs3.trans hs4) (by omega) e4 p4 (Or.inr x10') x11 x12
      ((r3.trans r4).mono (by decide)) (fun x => by rw [m4, m3]) hq (fmt_porsNode _ _ _ _ hl hn)
      (blocks_porsNode _ _ _ _ hl hn)

end SigGolfCandidate.ExP
