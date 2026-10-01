import SigGolfCandidate.Expand.PorsLoop

/-!
# `expand`, phase 2: the PORS leaf loop and the final checks (instructions 529 .. 638)

* `porsLeaves_sim` : from `pr_leaf` with leaf `s` and the reference state `st` (`LeafInv`),
  the machine refines `Ref.porsLeaves idx v w (range' s n) st`, the leaf index of slot `s` being
  `KEYS[s] >> 8` (hypothesis `hx`: the witness's pi byte selects it from `v ++ [porsT]`);
* `porsEnd_sim` : the final checks of `Ref.porsRoot` (at most 118 folds, `E = 1`, empty stack),
  to `pors_ok` (639) with the root at `OUT`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- The leaf loop invariant at `pr_leaf` (leaf `s < 15`) or after the last leaf (`s = 15`, at
the final checks, instruction 633). -/
structure LeafInv (w : List Byte) (idx : Nat) (K : Nat → Nat) (s : Nat) (st : PorsState) (t : MachineState) :
    Prop where
  ctx : PCtx w idx K t
  pc : t.pc = (if s < 15 then pcOf 529 else pcOf 633)
  hs : s ≤ 15
  x8 : t.getReg .x8 = BitVec.ofNat 64 s
  x9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + st.ptr)
  x18 : t.getReg .x18 = BitVec.ofNat 64 st.prev
  x19 : t.getReg .x19 = BitVec.ofNat 64 st.E
  x20 : t.getReg .x20 = BitVec.ofNat 64 st.folds
  x21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * st.stack.length)
  stk : StkOK t st.stack
  hk : st.stack.length ≤ s
  hk14 : st.stack.length ≤ 14
  hptr : st.ptr % 8 = 0
  hptr' : st.ptr ≤ 272 + 232 * (2 * s - st.stack.length)
  hf : st.folds ≤ 14 * (2 * s - st.stack.length)
  hprev : st.prev < 2 ^ 14
  hE : st.E < 2 ^ 15
  out : 0 < s → st.node.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf st.node

theorem porsT_or (x : Nat) (hx : x < 2 ^ 14) : porsT ||| x = 2 ^ 14 + x := by
  have := Nat.two_pow_add_eq_or_of_lt hx 1
  unfold porsT porsH; simpa using this.symm

set_option maxRecDepth 20000 in
/-- **The PORS leaf loop** (`Ref.porsLeaves` over `range' s n`). -/
theorem porsLeaves_sim (w : List Byte) (idx : Nat) (K : Nat → Nat) (v : List Nat) (hw : 272 ≤ w.length)
    (hx : ∀ s < 15, (v ++ [porsT]).getD (witPi w s / 8 % 16) 0 = K s / 256) :
    ∀ n s st t, s + n = 15 → LeafInv w idx K s st t →
      Sim eimg t (10000 * n) (porsLeaves idx v w (List.range' s n) st) (OPost (LeafInv w idx K 15)) := by
  intro n
  induction n with
  | zero =>
    intro s st t hsn hinv
    have : s = 15 := by omega
    subst this
    simp only [List.range'_zero, porsLeaves]
    exact Sim.pure (Q := OPost (LeafInv w idx K 15)) hinv
  | succ n ih =>
    intro s st t hsn hinv
    have hs15 : s < 15 := by omega
    rw [List.range'_succ]
    simp only [porsLeaves]
    rw [hx s hs15]
    have hc := hinv.ctx
    have tpc : t.pc = pcOf 529 := by rw [hinv.pc, if_pos hs15]
    have hK := hc.klt s hs15
    obtain ⟨t1, hs1, p1, y23, r1, m1⟩ := blk529_run t tpc s hs15 (K s) hK hinv.x8 (hc.keys s hs15)
    have hxlt : K s / 256 < 2 ^ 14 := by omega
    have c1 := hc.frame (W := fun _ => False) (fun y _ _ => m1 _) r1 (fun _ _ h => h)
    -- the order test (not for the first leaf)
    obtain ⟨t2, k2, hs2, hk2, pf2, pk2, r2, m2⟩ : ∃ t2 k2, Steps eimg t1 k2 k2 t2 ∧ k2 ≤ 1 ∧
        (s ≠ 0 ∧ ¬ st.prev < K s / 256 → t2.pc = pcOf 284) ∧
        (¬ (s ≠ 0 ∧ ¬ st.prev < K s / 256) → t2.pc = pcOf 534) ∧ RegsEq t1 t2 [] ∧
        ∀ y, t2.getMem y = t1.getMem y := by
      by_cases h0 : s = 0
      · rw [if_pos h0] at p1
        exact ⟨t1, 0, Steps.refl _, by norm_num, fun h => absurd h0 h.1, fun _ => p1, RegsEq.refl _ _,
          fun _ => rfl⟩
      · rw [if_neg h0] at p1
        obtain ⟨t2, hs2, p2, r2, m2⟩ := blk533_run t1 p1 st.prev (K s / 256) (by have := hinv.hprev; omega)
          (by omega) (by rw [r1.get .x18, hinv.x18]) y23
        refine ⟨t2, 1, hs2, le_refl _, fun h => by rw [p2, if_pos h.2], fun h => ?_, r2, m2⟩
        rw [p2, if_neg (by tauto)]
    by_cases hc1 : s ≠ 0 ∧ ¬ st.prev < K s / 256
    · rw [if_pos hc1]
      exact (Sim.steps hs1 (fail_sim_steps hs2 (pf2 hc1))).mono (by omega) (fun _ _ h => h)
    rw [if_neg hc1]
    have p2 := pk2 hc1
    have R2 := r1.trans r2
    -- the range test (only the last leaf)
    obtain ⟨t3, hs3, p3, r3, m3⟩ := blk534_run t2 p2 s hs15 (by rw [R2.get .x8 (by decide), hinv.x8])
    have y23' : t3.getReg .x23 = BitVec.ofNat 64 (K s / 256) := by rw [r3.get .x23, r2.get .x23, y23]
    obtain ⟨t4, k4, hs4, hk4, pf4, pk4, r4, m4⟩ : ∃ t4 k4, Steps eimg t2 k4 k4 t4 ∧ k4 ≤ 4 ∧
        (s = porsK - 1 ∧ ¬ K s / 256 < porsT → t4.pc = pcOf 284) ∧
        (¬ (s = porsK - 1 ∧ ¬ K s / 256 < porsT) → t4.pc = pcOf 538) ∧ RegsEq t2 t4 [.x13, .x17] ∧
        ∀ y, t4.getMem y = t2.getMem y := by
      by_cases h14 : s = 14
      · rw [if_pos h14] at p3
        obtain ⟨t4, hs4, p4, r4, m4⟩ := blk536_run t3 p3 (K s / 256) (by omega) y23'
        refine ⟨t4, 4, hs3.trans hs4, le_refl _, fun h => by rw [p4, if_pos h.2], fun h => ?_,
          (r3.trans r4).mono (by decide), fun y => by rw [m4, m3]⟩
        rw [p4, if_neg (by unfold porsK at h; omega)]
      · rw [if_neg h14] at p3
        exact ⟨t3, 2, hs3, by norm_num, fun h => absurd (by unfold porsK at h; omega) h14, fun _ => p3,
          r3.mono (by decide), m3⟩
    by_cases hc2 : s = porsK - 1 ∧ ¬ K s / 256 < porsT
    · rw [if_pos hc2]
      exact (Sim.steps hs1 (Sim.steps hs2 (fail_sim_steps hs4 (pf4 hc2)))).mono (by omega) (fun _ _ h => h)
    rw [if_neg hc2]
    have p4 := pk4 hc2
    have R4 := R2.trans r4
    have c4 : PCtx w idx K t4 :=
      (c1.frame (W := fun _ => False) (fun y _ _ => m2 _) r2 (fun _ _ h => h)).frame (W := fun _ => False)
        (fun y _ _ => m4 _) r4 (fun _ _ h => h)
    -- `LB`, `E`, `s8`
    obtain ⟨t5, hs5, p5, y19, y24, m8, msec, r5, f5⟩ := blk538_run w idx t4 p4 s (K s / 256) hs15 hxlt c4.wit
      (by rw [R4.get .x8 (by decide), hinv.x8]) (by rw [r4.get .x23, r2.get .x23, y23]) c4.x25 c4.x26 c4.x27
    have c5 : PCtx w idx K t5 := c4.frame f5 r5 (fun a h1 h2 => by unfold pctxA witA at h1; omega)
    have R5 := R4.trans r5
    have f15 : Frame t t5 (fun y => y = 0x30008 ∨ y = 0x30020 ∨ y = 0x30028) := fun y hy hW => by
      rw [f5 y hy hW, m4, m2, m1]
    have hk := hinv.hk
    have hk14 := hinv.hk14
    have hptr' := hinv.hptr'
    have hf := hinv.hf
    have hstk5 : StkOK t5 st.stack := hinv.stk.frame f15 (fun a h1 h2 => by unfold stkA at h1; omega) (by omega)
    have hsec : (witSecret w s).length = 16 := by
      unfold witSecret; rw [slice_eq_wbytes _ _ _ (by unfold wSec; omega), length_wbytes]
    have hseg := segLoop_sim w idx K st.stack st.ptr (porsT ||| K s / 256) st.folds (.leaf (K s / 256) (witSecret w s))
      st.node t5 c5 p5 (by rw [R5.get .x9 (by decide), hinv.x9]) y19 (by rw [R5.get .x20 (by decide), hinv.x20])
      (by rw [R5.get .x21 (by decide), hinv.x21]) hstk5 (by omega) hinv.hptr (by omega) (by omega)
      (by rw [porsT_or _ hxlt]; omega)
      ⟨y24, by omega, hsec, m8, by rw [msec]; unfold witSecret wSec; rw [slice_eq_wbytes _ _ _ (by omega)]⟩
    refine (Sim.steps hs1 (Sim.steps hs2 (Sim.steps hs4 (Sim.steps hs5 (Sim.bind hseg (W₂ := 20 + 10000 * n)
      (fun r t6 h6 => ?_)))))).mono (by omega) (fun _ _ h => h)
    rcases r with _ | ⟨ptr', E', folds', node', stk'⟩
    · dsimp only
      exact (Sim.pure (a := none) (Q := OPost (LeafInv w idx K 15)) h6).mono (by omega) (fun _ _ h => h)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14, q15, q16⟩ := h6
    dsimp only
    have R6 := R5.trans q15
    have y23'' : t6.getReg .x23 = BitVec.ofNat 64 (K s / 256) := by
      rw [q15.get .x23 (by decide), r5.get .x23, r4.get .x23, r2.get .x23, y23]
    obtain ⟨t7, hs7, p7, r7, m7⟩ := blk620_run t6 q1 s hs15 (by rw [R6.get .x8 (by decide), hinv.x8])
    -- the push (not after the last leaf)
    obtain ⟨t8, k8, hs8, hk8, p8, x21', stk8, r8, f8⟩ : ∃ t8 k8, Steps eimg t7 k8 k8 t8 ∧ k8 ≤ 7 ∧
        t8.pc = pcOf 629 ∧
        t8.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 *
          (if s < porsK - 1 then (node', E' ^^^ 1) :: stk' else stk').length) ∧
        StkOK t8 (if s < porsK - 1 then (node', E' ^^^ 1) :: stk' else stk') ∧
        RegsEq t7 t8 [.x13, .x14, .x15, .x21] ∧ Frame t7 t8 stkA := by
      have x21_7 : t7.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * stk'.length) := by rw [r7.get .x21, q6]
      have stk7 : StkOK t7 stk' := q7.frame (W := fun _ => False) (fun y _ _ => m7 _) (fun _ _ h => h) (by omega)
      by_cases h14 : s = 14
      · rw [if_pos h14] at p7
        rw [if_neg (by unfold porsK; omega)]
        exact ⟨t7, 0, Steps.refl _, by norm_num, p7, x21_7, stk7, RegsEq.refl _ _, Frame.refl _ _⟩
      · rw [if_neg h14] at p7
        rw [if_pos (by unfold porsK; omega)]
        obtain ⟨t8, hs8, p8, x21', w8, m8', r8, f8⟩ := blk622_run t7 p7 stk'.length E' (by omega) q12
          (by rw [r7.get .x19, q4]) x21_7 (by rw [r7.get .x25, q2.x25])
        refine ⟨t8, 7, hs8, le_refl _, p8, by simpa using x21', ?_, r8, f8.mono (by
          intro y hy; unfold stkA; omega)⟩
        refine stk7.push (by omega) f8 node' (E' ^^^ 1) q13 (Nat.xor_lt_two_pow q12 (by norm_num)) ?_ m8'
        rw [w8, readWords_ofNat_two, m7, m7, ← readWords_ofNat_two, q14]
    obtain ⟨t9, hs9, p9, x8', x18', r9, m9⟩ := blk629_run t8 p8 s (K s / 256) hs15
      (by rw [r8.get .x8, r7.get .x8, R6.get .x8 (by decide), hinv.x8]) (by rw [r8.get .x23, r7.get .x23, y23''])
    have c9 : PCtx w idx K t9 :=
      (((q2.frame (W := fun _ => False) (fun y _ _ => m7 _) r7 (fun _ _ h => h)).frame f8 r8
        (fun a h1 h2 => by unfold pctxA witA at h1; unfold stkA at h2; omega))).frame (W := fun _ => False)
        (fun y _ _ => m9 _) r9 (fun _ _ h => h)
    have hih := ih (s + 1) ⟨ptr', K s / 256, E', folds', node',
      if s < porsK - 1 then (node', E' ^^^ 1) :: stk' else stk'⟩ t9 (by omega) ?_
    · exact (Sim.steps hs7 (Sim.steps hs8 (Sim.steps hs9 hih))).mono (by omega) (fun _ _ h => h)
    have hlen : (if s < porsK - 1 then (node', E' ^^^ 1) :: stk' else stk').length =
        if s < 14 then stk'.length + 1 else stk'.length := by
      unfold porsK; split <;> simp_all
    refine ⟨c9, by rw [p9]; split <;> split <;> first | rfl | omega, by omega, x8', ?_, x18', ?_, ?_, ?_,
      stk8.frame (W := fun _ => False) (fun y _ _ => m9 _) (fun _ _ h => h) (by rw [hlen]; split <;> omega),
      by dsimp only; rw [hlen]; split <;> omega, by dsimp only; rw [hlen]; split <;> omega, q9,
      by dsimp only; rw [hlen]; split <;> omega, by dsimp only; rw [hlen]; split <;> omega, hxlt, q12,
      fun _ => ⟨q13, ?_⟩⟩
    · rw [r9.get .x9, r8.get .x9, r7.get .x9, q3]
    · rw [r9.get .x19, r8.get .x19, r7.get .x19, q4]
    · rw [r9.get .x20, r8.get .x20, r7.get .x20, q5]
    · rw [r9.get .x21, x21']
    · have f79 : Frame t7 t9 stkA := (f8.trans (fun y _ _ => m9 _ : Frame t8 t9 (fun _ => False))).mono (by
        intro y hy; simp only [or_false] at hy; exact hy)
      rw [f79.readWords _ _ (by norm_num) (fun i hi => by unfold stkA; omega), readWords_ofNat_two, m7, m7,
        ← readWords_ofNat_two, q14]

end SigGolfCandidate.ExP
