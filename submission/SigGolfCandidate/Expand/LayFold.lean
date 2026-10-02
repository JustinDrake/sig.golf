import SigGolfCandidate.Expand.LayChain

/-!
# `expand`, phase 2: the OTS leaf hash (438 .. 441) and the folds (`Ref.foldPath`, 442 .. 471)

`leaf_sim` : at `ch_done`'s exit (438) with the 42 chain ends at `LF + 32`, the machine hashes
`leafInput lay tau e ends` into `NO`; `folds_sim` : from 442, the `height lay` folds with the
witness path (`witPath w lay`) refine `foldPath (nodeInput lay tau) e leaf (witPath w lay)`,
ending at 472 with the root in `NO`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-! ## The leaf -/

/-- After the leaf hash (442): the leaf in `NO`. -/
def LeafOut (w : List Byte) (idx : Nat) (u : MachineState) (v : Val) (t : MachineState) : Prop :=
  t.pc = pcOf 442 ∧ LCtx w idx t ∧ v.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x30200) 2 = wordsOf v ∧
  RegsEq u t [.x10, .x11, .x12] ∧ Frame u t (fun a => 0x30200 ≤ a ∧ a < 0x30220)

theorem leaf_sim (w : List Byte) (idx : Nat) (lay tau e : Nat) (hl : lay < 5) (htau : tau < 2 ^ 30)
    (he : e < 2048) (ends : List Val) (hlen : ends.length = 42) (hv : ∀ v ∈ ends, v.length = 16)
    (t : MachineState) (hpc : t.pc = pcOf 438) (hc : LCtx w idx t) (hs : Slots t 0x30260 ends)
    (m0 : t.getMem (BitVec.ofNat 64 0x30240) = BitVec.ofNat 64 (LeafCarry.leafHeader lay))
    (m8 : t.getMem (BitVec.ofNat 64 0x30248) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)) :
    Sim eimg t 91 (hash16 (leafInput lay tau e ends)) (LeafOut w idx t) := by
  obtain ⟨t1, hs1, e1, p1, x10, x11, x12, r1, m1⟩ := blk438_run t hpc hc.x25
  have hw := words_thVals (carryLeafTag lay) (carryLeafLay lay) tau 0 e ends hv 10 (by rw [hlen])
  have hq : hashInput t1 = pad64 (thInput (tweak (carryLeafTag lay) (carryLeafLay lay) tau 0 e) ends.flatten) := by
    refine hashInput_eq_pad64 t1 _ 10 hw.1 (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [x10, hw.2, show 8 * (10 + 1) = 2 + (2 + 2 * ends.length) by rw [hlen],
      readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_two]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [m1, m1, m0, m8, readWords_congr _ _ _ _ (fun i _ => m1 _), hc.lfz,
      readWords_congr _ _ _ _ (fun i _ => m1 _), readWords_slots t 0x30260 ends hs]
    simp only [twWords_eq,List.cons_append,List.nil_append]
    rw [carryLeafWord lay tau (by omega) (by omega),
      Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : e < 2 ^ 32)]
  have haddr := addrFmt_leafInput_carry lay tau e ends (by omega : lay<7) (by omega : tau<2^32) hlen hv
  have hq' : hashInput t1 = addrFmt (leafInput lay tau e ends) := hq.trans haddr.symm
  have hb : (fmt (leafInput lay tau e ends)).blocks = 11 := by
    rw [← addrFmt_blocks, haddr]
    exact congrArg (· + 1) hw.1
  refine (Sim.steps hs1 (Sim.of_eq (Sim.hash16_bindF (f := pure) (W := 0) e1 (by rw [r1.get .x5, hc.x5])
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq' (fun ans => ?_)) (bind_pure _))).mono
    (by rw [hb]) (fun _ _ h => h)
  refine Sim.pure ⟨by rw [writeHash_pc, p1]; rfl,
    (hc.frame_nil m1 r1).frame (frame_writeHash t1 ans _ x12 (by norm_num)) (regsEq_writeHash t1 ans [])
      (fun a h1 h2 => by unfold lctxA witA at h1; omega), by simp [answerBytes],
    writeHash_readWords_val t1 ans _ x12 (by norm_num), (r1.trans (regsEq_writeHash t1 ans [])).mono (by decide), ?_⟩
  have f01 : Frame t t1 (fun _ => False) := fun a _ _ => m1 _
  exact (f01.trans (frame_writeHash t1 ans _ x12 (by norm_num))).mono
    (by intro a ha; simp only [false_or] at ha; omega)

/-! ## The folds -/

/-- The body of `foldPath`'s `foldlM` for the witness path of layer `lay`. -/
def fdF (w : List Byte) (lay tau e : Nat) (v : Val) (lam : Nat) : OracleComp HashSpec Val :=
  let sib := (witPath w lay).getD lam []
  let j := e / 2 ^ (lam + 1)
  if e / 2 ^ lam % 2 = 1 then hash16 (nodeInput lay tau (lam + 1) j sib v)
  else hash16 (nodeInput lay tau (lam + 1) j v sib)

theorem foldPath_eq (w : List Byte) (lay tau e : Nat) (leaf : Val) :
    foldPath (nodeInput lay tau) e leaf (witPath w lay) =
      (List.range (height lay)).foldlM (fdF w lay tau e) leaf := by
  unfold foldPath; rw [show (witPath w lay).length = height lay by simp [witPath]]; rfl

/-- The HASH input of a hypertree node (`nodeBlock` of `nodeInput`). -/
theorem hashInput_node (t : MachineState) (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) (hl0 : 0 < lay) (hlay : lay < 256) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) 8 =
      twWords 3 lay tau 0 (heapIndex (height lay) lam j) ++ [0, 0] ++ wordsOf l ++ wordsOf r) :
    hashInput t = addrFmt (nodeInput lay tau lam j l r) := by
  rw [addrFmt_nodeInput_nonTop lay tau lam j l r hl hr (by omega), fmt_nodeInput lay tau lam j l r hl hr hlay hlam hj]
  have hw' := words_th32 3 lay tau 0 (heapIndex (height lay) lam j) l r hl hr
  rw [hashInput_eq_pad64 t _ 0 hw'.1 h11 (by norm_num) h10 (by rw [show 8 * (0 + 1) = 8 from rfl, hw, hw'.2]),
    pad64_eq _ 0 (by simp [hl, hr]) (by simp [hl, hr])]
  simp [hl, hr, zeros]

/-- Registers the folds write. -/
def fdRegs : List Reg := [.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x18, .x19, .x23, .x28, .x29]

/-- Addresses the folds write: `NB` word 1, `NB`'s children, `NO`. -/
def fdW (a : Nat) : Prop := a = 0x301C8 ∨ (0x301E0 ≤ a ∧ a < 0x30220)

/-- Fold invariant after `lam` levels (`u`: the state at the loop's start). -/
def FdInv (w : List Byte) (idx : Nat) (u : MachineState) (lay e lam : Nat) (v : Val) (t : MachineState) :
    Prop :=
  t.pc = (if lam < height lay then pcOf 446 else pcOf 472) ∧ LCtx w idx t ∧ lam ≤ height lay ∧
  t.getReg .x18 = BitVec.ofNat 64 (2 ^ (height lay - lam) + e / 2 ^ lam) ∧ t.getReg .x19 = BitVec.ofNat 64 lam ∧
  t.getReg .x23 = BitVec.ofNat 64 (0x800 + pathOff lay + 16 * lam) ∧ v.length = 16 ∧
  t.readWords (BitVec.ofNat 64 0x30200) 2 = wordsOf v ∧ RegsEq u t fdRegs ∧ Frame u t fdW

/-- W1a: the paths sit at `pathOff lay`, below the chain array. -/
theorem pathOff_le (lay : Nat) (h : lay < 5) :
    pathOff lay + 16 * height lay ≤ 2944 ∧ pathOff lay % 8 = 0 := by
  interval_cases lay <;> decide

theorem height_le (lay : Nat) (hl : 1 ≤ lay) (hl' : lay < 5) : 5 ≤ height lay ∧ height lay ≤ 6 := by
  interval_cases lay <;> decide

/-- One fold; afterwards the node buffer still holds the two inputs of its hash (for the last level: the
root's two children). -/
theorem fold_step2 (w : List Byte) (idx : Nat) (u : MachineState) (lay tau e : Nat) (hl : 1 ≤ lay) (hl' : lay < 5)
    (htau : tau < 2 ^ 30) (he : e < 2 ^ height lay) (hw : w.length = 16384)
    (u9 : u.getReg .x9 = BitVec.ofNat 64 (height lay)) (u30 : u.getReg .x30 = BitVec.ofNat 64 tau)
    (u1C0 : u.getMem (BitVec.ofNat 64 0x301C0) = BitVec.ofNat 64 (769 + 65536 * lay)) :
    ∀ lam < height lay, ∀ (v : Val) (t : MachineState), FdInv w idx u lay e lam v t →
      Sim eimg t 30 (fdF w lay tau e v lam) (fun v' t' => FdInv w idx u lay e (lam + 1) v' t' ∧
        t'.readWords (BitVec.ofNat 64 0x301E0) 4 = wordsOf (if e / 2 ^ lam % 2 = 1
          then (witPath w lay).getD lam [] ++ v else v ++ (witPath w lay).getD lam [])) := by
  intro lam hlam v t ⟨tpc, tc, hlh, t18, t19, t23, hv, tv, tregs, tframe⟩
  have hh := height_le lay hl hl'
  have hwl := pathOff_le lay hl'
  rw [if_pos hlam] at tpc
  set H := 2 ^ (height lay - lam) + e / 2 ^ lam with hH
  have hHlt : H < 2 ^ 32 := by
    have : 2 ^ (height lay - lam) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : e / 2 ^ lam ≤ e := Nat.div_le_self _ _
    have : 2 ^ height lay ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set o := pathOff lay + 16 * lam with ho
  obtain ⟨t1, hs1, p1, y18, y16, y17, y28, y29, m1C8, r1, f1⟩ := blk446_run w t tpc H tau o hHlt (by omega)
    (by omega) (by omega) tc.wit t18 (by rw [t23]; exact ofNat_congr (by omega)) tc.x25
    (by rw [tregs.get .x30 (by decide), u30])
  have c1 := tc.frame f1 r1 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
  -- the heap arithmetic
  have hpow : 2 ^ (height lay - lam) = 2 * 2 ^ (height lay - (lam + 1)) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hHmod : H % 2 = e / 2 ^ lam % 2 := by rw [hH, hpow]; omega
  have hHdiv : H / 2 = heapIndex (height lay) (lam + 1) (e / 2 ^ (lam + 1)) := by
    unfold heapIndex; rw [hH, hpow, Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega
  have hsib : (witPath w lay).getD lam [] = wbytes w o 16 := by
    simp only [witPath, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlam,
      Option.map_some, Option.getD_some, witSib]
    rw [slice_eq_wbytes _ _ _ (by omega)]
  have hsl : (wbytes w o 16).length = 16 := length_wbytes _ _ _
  have hj : e / 2 ^ (lam + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) (by
    have : 2 ^ height lay ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  have hnode : [t.getMem (BitVec.ofNat 64 0x30200), t.getMem (BitVec.ofNat 64 0x30208)] = wordsOf v := by
    rw [← tv, readWords_ofNat_two]
  have tail : ∀ (t2 : MachineState) (k2 : Nat) (l r : Val), Steps eimg t1 k2 k2 t2 → k2 ≤ 5 → t2.pc = pcOf 465 →
      l.length = 16 → r.length = 16 →
      t2.readWords (BitVec.ofNat 64 0x301E0) 2 = wordsOf l → t2.readWords (BitVec.ofNat 64 0x301F0) 2 = wordsOf r →
      RegsEq t1 t2 [] → Frame t1 t2 (fun x => 0x301E0 ≤ x ∧ x < 0x30200) →
      Sim eimg t 30 (hash16 (nodeInput lay tau (lam + 1) (e / 2 ^ (lam + 1)) l r))
        (fun v' t' => FdInv w idx u lay e (lam + 1) v' t' ∧
          t'.readWords (BitVec.ofNat 64 0x301E0) 4 = wordsOf (l ++ r)) := by
    intro t2 k2 l r hs2 hk2 p2 hl2 hr2 w2l w2r r2 f2
    have c2 := c1.frame f2 r2 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
    obtain ⟨t3, hs3, e3, p3, x10, x11, x12, r3, m3⟩ := blk465_run t2 p2 c2.x25
    have c3 := c2.frame_nil m3 r3
    have hq : hashInput t3 = addrFmt (nodeInput lay tau (lam + 1) (e / 2 ^ (lam + 1)) l r) := by
      refine hashInput_node t3 lay tau (lam + 1) _ l r hl2 hr2 (by omega) (by omega) (by omega) hj x11
        (by rw [x10]; decide) ?_
      rw [x10, ← hHdiv, readWords8]
      simp only [Nat.reduceAdd, m3]
      rw [readWords_ofNat_two] at w2l w2r
      simp only [Nat.reduceAdd] at w2l w2r
      have hz := tc.nbz
      rw [readWords_ofNat_two] at hz
      simp only [Nat.reduceAdd, List.cons.injEq, and_true] at hz
      have f12 : Frame t t2 (fun x => x = 0x301C8 ∨ (0x301E0 ≤ x ∧ x < 0x30200)) := f1.trans f2
      rw [← w2l, ← w2r, f2.getMem (a := 0x301C8) (by norm_num) (by omega), m1C8,
        f12.getMem (a := 0x301C0) (by norm_num) (by omega),
        tframe.getMem (a := 0x301C0) (by norm_num) (by unfold fdW; omega), u1C0,
        f12.getMem (a := 0x301D0) (by norm_num) (by omega), hz.1,
        f12.getMem (a := 0x301D8) (by norm_num) (by omega), hz.2]
      unfold twWords
      rw [Nat.mod_eq_of_lt (by omega : lay < 256), Nat.div_eq_of_lt (by omega : tau < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : H / 2 < 2 ^ 32)]
      simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, List.append_assoc]
      exact ofNat_congr (by ring)
    have hbq : (fmt (nodeInput lay tau (lam + 1) (e / 2 ^ (lam + 1)) l r)).blocks = 1 := by
      rw [fmt_nodeInput _ _ _ _ _ _ hl2 hr2 (by omega) (by omega) hj]; rfl
    refine (Sim.steps hs1 (Sim.steps hs2 (Sim.steps hs3 (Sim.of_eq (Sim.hash16_bindF (f := pure) (W := 3) e3 c3.x5
      (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)) hq (fun ans => ?_)) (bind_pure _))))).mono (by rw [hbq]; omega) (fun _ _ h => h)
    set t4 := writeHash t3 ans with ht4
    have p4 : t4.pc = pcOf 469 := by rw [ht4, writeHash_pc, p3]; rfl
    have R3 := ((r1.trans r2).trans r3).trans (regsEq_writeHash t3 ans [])
    obtain ⟨t5, hs5, p5, y23, y19, r5, m5⟩ := blk469_run t4 p4 (0x800 + o) lam (height lay) (by omega) (by omega)
      (by omega) (by rw [R3.get .x23 (by decide), t23]; exact ofNat_congr (by omega))
      (by rw [R3.get .x19 (by decide), t19]) (by rw [R3.get .x9 (by decide), tregs.get .x9 (by decide), u9])
    have f4 : Frame t3 t4 (fun a => 0x30200 ≤ a ∧ a < 0x30200 + 32) := frame_writeHash t3 ans _ x12 (by norm_num)
    refine Sim.pure_steps hs5 ⟨⟨?_, (c3.frame f4 (regsEq_writeHash t3 ans []) (fun a h1 h2 => by
        unfold lctxA witA at h1; omega)).frame_nil m5 r5, by omega, ?_, y19, ?_, by simp [answerBytes], ?_, ?_, ?_⟩,
      ?_⟩
    · rw [p5]; split <;> split <;> first | rfl | omega
    · rw [r5.get .x18, ht4, writeHash_getReg, r3.get .x18, r2.get .x18, y18, hHdiv]; unfold heapIndex; rfl
    · rw [y23]; exact ofNat_congr (by omega)
    · rw [readWords_ofNat_two, m5, m5, ← readWords_ofNat_two, ht4, writeHash_readWords_val t3 ans _ x12 (by norm_num)]
    · exact ((tregs.trans R3).trans r5).mono (by decide)
    · have f23 : Frame t2 t3 (fun _ => False) := fun a _ _ => m3 _
      have f45 : Frame t4 t5 (fun _ => False) := fun a _ _ => m5 _
      have f15 : Frame t t5 (fun a => (a = 0x301C8 ∨ (0x301E0 ≤ a ∧ a < 0x30200)) ∨ (0x30200 ≤ a ∧ a < 0x30220)) :=
        ((((f1.trans f2).trans f23).trans f4).trans f45).mono (by
            intro a ha; simp only [or_false] at ha; omega)
      exact (tframe.trans f15).mono (by intro a ha; simp only [fdW] at ha ⊢; omega)
    · have e4 := readWords_ofNat_add t5 0x301E0 2 2
      rw [show (2 + 2 : Nat) = 4 from rfl, show (0x301E0 + 8 * 2 : Nat) = 0x301F0 from rfl] at e4
      rw [e4, wordsOf_append _ _ (by omega), ← w2l, ← w2r]
      congr 1
      · exact readWords_congr t2 t5 _ 2 (fun i hi => by
          rw [m5, f4.getMem (by omega) (by omega), m3])
      · exact readWords_congr t2 t5 _ 2 (fun i hi => by
          rw [m5, f4.getMem (by omega) (by omega), m3])
  unfold fdF
  dsimp only
  rw [hsib]
  by_cases hbit : e / 2 ^ lam % 2 = 1
  · simp only [if_pos hbit]
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, hs2, p2, w2l, w2r, r2, f2⟩ := blk456_run t1 p1 c1.x25
    exact tail t2 5 _ _ hs2 le_rfl p2 hsl hv (by rw [w2l, y16, y17, wordsOf_wbytes16])
      (by rw [w2r, y28, y29, hnode]) r2 f2
  · simp only [if_neg hbit]
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, hs2, p2, w2l, w2r, r2, f2⟩ := blk461_run t1 p1 c1.x25
    exact tail t2 4 _ _ hs2 (by norm_num) p2 hv hsl (by rw [w2l, y28, y29, hnode])
      (by rw [w2r, y16, y17, wordsOf_wbytes16]) r2 f2

theorem fold_step (w : List Byte) (idx : Nat) (u : MachineState) (lay tau e : Nat) (hl : 1 ≤ lay) (hl' : lay < 5)
    (htau : tau < 2 ^ 30) (he : e < 2 ^ height lay) (hw : w.length = 16384)
    (u9 : u.getReg .x9 = BitVec.ofNat 64 (height lay)) (u30 : u.getReg .x30 = BitVec.ofNat 64 tau)
    (u1C0 : u.getMem (BitVec.ofNat 64 0x301C0) = BitVec.ofNat 64 (769 + 65536 * lay)) :
    ∀ lam < height lay, ∀ (v : Val) (t : MachineState), FdInv w idx u lay e lam v t →
      Sim eimg t 30 (fdF w lay tau e v lam) (FdInv w idx u lay e (lam + 1)) :=
  fun lam hlam v t h =>
    (fold_step2 w idx u lay tau e hl hl' htau he hw u9 u30 u1C0 lam hlam v t h).mono le_rfl
      (fun _ _ h => h.1)

/-- Congruence on visited entries keeps the hash formatter opaque. -/
private theorem foldlM_congr_on {α β : Type} (f g : α → β → OracleComp HashSpec α)
    (xs : List β) (a : α) (h : ∀ x ∈ xs, ∀ v, f v x = g v x) :
    xs.foldlM f a = xs.foldlM g a := by
  induction xs generalizing a with
  | nil => simp only [List.foldlM_nil]
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    rw [h x (List.mem_cons_self ..) a]
    congr 1
    funext v
    exact ih v (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- The folds below the root: the fold over the first `height lay - 1` siblings of the path. -/
theorem foldPath_take_eq (w : List Byte) (lay tau e : Nat) (leaf : Val) :
    foldPath (nodeInput lay tau) e leaf ((witPath w lay).take (height lay - 1)) =
      (List.range (height lay - 1)).foldlM (fdF w lay tau e) leaf := by
  have hlen : ((witPath w lay).take (height lay - 1)).length = height lay - 1 := by
    simp [witPath]
  unfold foldPath
  rw [hlen]
  apply foldlM_congr_on
  intro lam hlam v
  have ha : lam < height lay - 1 := List.mem_range.mp hlam
  have e1 : ((witPath w lay).take (height lay - 1)).getD lam [] = (witPath w lay).getD lam [] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, ha]
  dsimp only
  rw [e1]
  rfl

/-- The dead root hash of `expandLayers` is the last fold. -/
theorem fdF_last (w : List Byte) (lay tau e : Nat) (he : e < 2 ^ height lay) (hh : 1 ≤ height lay)
    (node : Val) (hn : node.length = 16) (hs : (witSib w lay (height lay - 1)).length = 16) :
    hash16 (nodeInput lay tau (height lay) 0
        ((topPair e (height lay) node (witSib w lay (height lay - 1))).take 16)
        ((topPair e (height lay) node (witSib w lay (height lay - 1))).drop 16)) =
      fdF w lay tau e node (height lay - 1) := by
  have hsib : (witPath w lay).getD (height lay - 1) [] = witSib w lay (height lay - 1) := by
    simp [witPath, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show height lay - 1 < height lay by omega)]
  have hj : e / 2 ^ (height lay - 1 + 1) = 0 := by
    rw [show height lay - 1 + 1 = height lay by omega]; exact Nat.div_eq_of_lt he
  unfold fdF topPair
  dsimp only
  rw [hsib, hj, show height lay - 1 + 1 = height lay by omega]
  split
  · rw [List.take_left' hs, List.drop_left' hs]
  · rw [List.take_left' hn, List.drop_left' hn]

end SigGolfCandidate.ExP
