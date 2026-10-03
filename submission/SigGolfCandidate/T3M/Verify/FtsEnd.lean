import SigGolfCandidate.T3M.Verify.FtsSem

/-!
# The FTS stream machine: push/final tails, coordinate ends, the forest (T3M verify)

* `tailP_step`: the push tail (`Q = E ^^^ 1` under the node that the segment's last hash wrote into frame `d + 1`,
  then the next leaf's code through the link `s8`); `tailF_step`: the final tail (through the link to `coord_end_c`);
* `coord_step`: `coord_end_c` rejects unless `E = 1` and the stack is empty, then the next coordinate's leaf 0 (with the
  coordinate words, the forest slot and the root list advanced) or, after coordinate 6, the forest (`ForestIn`);
* `forest_step`: the pointer cap (reject after more than 115 folds: `streamEnd < ptr`), the forest frame
  `[root_0 | T(11) | root_1 .. root_6]` and its two-block HASH into the encoding block;
* **`FtsOut F root u`**: the state after the forest HASH at `xtr3_1` (pc 656), the layers phase's entry.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## Helpers -/

/-- t3-rl2: the sibling `xor gp, s7, t1` (`t1 = 2^63`, n3-99: x6). -/
theorem xor1_eval (m : MachineState) (E : Nat) (h : m.getReg .x23 = FtsRev.rv E) :
    (Rv.E.bin .xor (.reg .x23) (cw (2 ^ 63))).eval m = FtsRev.rv (E ^^^ 1) := by
  show BinOp.eval .xor (m.getReg .x23) (BitVec.ofNat 64 (2 ^ 63)) = _
  rw [h]; exact FtsRev.rv_xor E

theorem jmp24_eval (m : MachineState) (c j : Nat) (h : m.getReg .x24 = BitVec.ofNat 64 (lnk c j)) :
    (Rv.E.bin .and (.reg .x24) notOne).eval m = BitVec.ofNat 64 (lnk c j) := by
  show BinOp.eval .and (m.getReg .x24) (~~~1#64) = _
  rw [h]; exact even_andNot1 _ (by unfold lnk; omega)

theorem lnk_next (c j : Nat) (hj : j < 2) : lnk c j = 0x1000 + 4 * leafPc (3 * c + (j + 1)) := by
  unfold lnk leafRet leafPc
  omega

theorem lnk_end (c : Nat) : lnk c 2 = 0x1000 + 4 * coordEndPc c := by
  unfold lnk leafRet leafPc coordEndPc
  omega

theorem xor1_lt (E : Nat) (hE : E < 4096) : E ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hE (by norm_num)

/-! ## The push and final tails -/

/-- The push tail: `Q = E ^^^ 1` under the pushed node, then the next leaf's code. -/
theorem tailP_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (E ptr folds : Nat)
    (node : Digest) (m : MachineState) (h : TailIn F c j roots stk 1 E ptr folds node m) :
    ∃ u, Steps image m 4 4 u ∧ LeafIn F c (j + 1) roots ((node, E ^^^ 1) :: stk) ptr folds u := by
  obtain ⟨k, hk, hpc⟩ := h.pc
  rw [show tailPcT (tselJ j) 1 k = tailPc 1 k by simp [tailPcT, cpOff]] at hpc
  obtain ⟨hc7, hj3, hdj, hd2, folds0, a0, hb0, ha0, hf0⟩ := h.bnd
  have hj2 : j < 2 := h.hX.2.1 rfl
  have hE := h.hE
  have hkn : KnownOK (ka5 stk.length) m := by
    intro p hp
    simp only [ka5, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h.fb.glob.1 p hp
    · exact h.a5
  obtain ⟨u, hu⟩ := spec_run (tailPCheck1_at k stk.length hk (by omega)) m hpc hkn (by simp [tailPSpec]) (by simp)
  have exr := xor1_eval m E h.s7
  have hmem : ∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
      if B = frameA (stk.length + 1) - 16 then FtsRev.rv (E ^^^ 1) else m.getMem (BitVec.ofNat 64 B) := by
    intro B hB
    rw [hu.mem]; simp only [tailPSpec]
    rw [memEval_cons_ofNat _ _ _ _ _ hB (by unfold frameA; omega), memEval_nil, exr]
  have hfr : ∀ B, B < 2 ^ 64 → B ≠ frameA (stk.length + 1) - 16 →
      u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) :=
    fun B hB h1 => by rw [hmem B hB, if_neg h1]
  have hfb : FB F c u := by
    refine ⟨hu.glob _ _ _ h.fb.glob (RelOK.nil m), fun p hp => ?_, ?_, fun s hs => ?_, ?_, fun dd h1 h2 => ?_, hc7⟩
    · rw [hu.keep p.1 (by simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp)]
      exact h.fb.ck p hp
    · rw [hu.keep .x22 (by simp)]; exact h.fb.idx
    · rw [hfr _ (by unfold leafT WIT; omega) (by unfold leafT frameA WIT; omega)]
      exact h.fb.thdr s hs
    · rw [hfr _ (by unfold SENTINEL; omega) (by unfold SENTINEL frameA; omega)]
      exact h.fb.sent
    · rw [hfr _ (by unfold frameA; omega) (by unfold frameA; omega),
        hfr _ (by unfold frameA; omega) (by unfold frameA; omega)]
      exact h.fb.fpad dd h1 h2
  have hpcu : u.pc = pcOf (leafPc (3 * c + (j + 1))) := by
    rw [hu.spc _ rfl, jmp24_eval m c j h.s8, lnk_next c j hj2]
  have hn0 : DigAt m (frameA (stk.length + 1)) node := h.nd
  have hn : DigAt u (frameA (stk.length + 1)) node :=
    ⟨(hfr _ (by unfold frameA; omega) (by unfold frameA; omega)).trans hn0.1,
      (hfr _ (by unfold frameA; omega) (by unfold frameA; omega)).trans hn0.2⟩
  have hq : u.getMem (BitVec.ofNat 64 (frameA (stk.length + 1) - 16)) = FtsRev.rv (E ^^^ 1) := by
    rw [hmem _ (by unfold frameA; omega), if_pos rfl]
  have hstk : StackOK ((node, E ^^^ 1) :: stk) u :=
    stack_push (h.stack.frame (fun i hi => ⟨hfr _ (by unfold frameA; omega) (by unfold frameA; omega),
      hfr _ (by unfold frameA; omega) (by unfold frameA; omega),
      hfr _ (by unfold frameA; omega) (by unfold frameA; omega)⟩)) node (E ^^^ 1) hn hq (xor1_lt E hE)
  have hr := h.hroots
  refine ⟨u, hu.steps, ⟨hfb, hpcu, ?_, ?_, ?_, hstk, ?_, h.hroots, ?_, ?_⟩⟩
  · rw [hu.keep .x14 (by simp)]; exact h.a4
  · have := hu.known (.x15, BitVec.ofNat 64 (frameA (stk.length + 1))) (by simp [ka5])
    simpa using this
  · rw [hu.keep .x25 (by simp)]; exact h.s9
  · exact h.rts.frame (fun k' hkr => ⟨hfr (forestSlot k') (by unfold forestSlot; split <;> omega)
      (by unfold forestSlot frameA; split <;> omega),
      hfr (forestSlot k' + 8) (by unfold forestSlot; split <;> omega) (by unfold forestSlot frameA; split <;> omega)⟩)
  · intro jj h1 h2
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold frameA WIT; omega)]
    exact h.wit jj h1 h2
  · simp only [List.length_cons]
    refine ⟨hc7, by omega, ⟨by omega, by omega⟩, ?_, ?_⟩
    · have := hb0.hptr; unfold segsDone at *; omega
    · have := hb0.hf; have := hb0.hptr; unfold segsDone at *; omega

/-- The final tail (leaf 2): through the link to `coord_end_c`. -/
theorem tailF_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (E ptr folds : Nat)
    (node : Digest) (m : MachineState) (h : TailIn F c j roots stk 2 E ptr folds node m) :
    j = 2 ∧ ∃ u, Steps image m 1 1 u ∧ CoordIn F c roots stk E ptr folds node u := by
  obtain ⟨k, hk, hpc⟩ := h.pc
  rw [show tailPcT (tselJ j) 2 k = tailPc 2 k by simp [tailPcT, cpOff]] at hpc
  have hj : j = 2 := h.hX.2.2 rfl
  subst hj
  refine ⟨rfl, ?_⟩
  obtain ⟨u, hu⟩ := spec_run (tailFCheck1_at k hk) m hpc h.fb.glob.1 (by simp [tailFSpec]) (by simp)
  have hmem : ∀ A, u.getMem A = m.getMem A := fun A => by rw [hu.mem]; rfl
  have hn0 : DigAt m (forestSlot c) node := h.nd
  refine ⟨u, hu.steps, ⟨h.fb.transport (hu.glob _ _ _ h.fb.glob (RelOK.nil m)) hmem (hu.keep .x27 (by simp))
    (hu.keep .x28 (by simp)) (hu.keep .x22 (by simp)), ?_, ?_, ?_, ?_, ?_, h.stack.transport hmem,
    h.rts.transport hmem, h.hroots, ⟨(hmem _).trans hn0.1, (hmem _).trans hn0.2⟩, h.wit.transport hmem, ?_, h.hE⟩⟩
  · rw [hu.spc _ rfl, jmp24_eval m c 2 h.s8, lnk_end]
  · rw [hu.keep .x14 (by simp)]; exact h.a4
  · rw [hu.keep .x15 (by simp)]; exact h.a5
  · rw [hu.keep .x23 (by simp)]; exact h.s7
  · rw [hu.keep .x25 (by simp)]; exact h.s9
  · obtain ⟨-, -, -, hd2, rest⟩ := h.bnd; exact ⟨hd2, rest⟩

/-! ## The coordinate end -/

/-- At `forest` (pc 648) after coordinate 6: the seven roots in the forest frame, `a4` at the next header. -/
structure ForestIn (F : FCtx) (roots : List Digest) (ptr folds : Nat) (m : MachineState) : Prop where
  glob : Glob gkF F.w F.pk m
  idx : m.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : m.pc = pcOf forestPc
  a4 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)
  rts : RootsOK roots m
  hroots : roots.length = 7
  wit : WitF F.w ptr m
  hptr : ptr = 1368 + 80 * folds
  hf : folds ≤ 385

theorem coordCheck1_at (c : Nat) (hc : c < 7) : coordCheck1 c = true :=
  List.all_eq_true.mp coordCheck_all c (List.mem_range.mpr hc)

theorem eBr_holds (m : MachineState) (E : Nat) (h : m.getReg .x23 = FtsRev.rv E) (hE : E < 4096) (d : Bool) :
    Br.holds m (eBr d) ↔ d = decide (E ≠ 1) := by
  have key : (m.getReg .x23 != BitVec.ofNat 64 (2 ^ 63)) = decide (E ≠ 1) := by
    rw [h]
    by_cases hE1 : E = 1
    · rw [(FtsRev.rv_eq_top E (by omega)).mpr hE1]; simp [hE1]
    · have h1 : FtsRev.rv E ≠ BitVec.ofNat 64 (2 ^ 63) := fun h' => hE1 ((FtsRev.rv_eq_top E (by omega)).mp h')
      rw [bne_iff_ne.mpr h1]; simp [hE1]
  show (m.getReg .x23 != BitVec.ofNat 64 (2 ^ 63)) = d ↔ _
  rw [key]; exact eq_comm

theorem sBr_holds (m : MachineState) (d0 : Nat) (h : m.getReg .x15 = BitVec.ofNat 64 (frameA d0)) (hd : d0 ≤ 2)
    (d : Bool) : Br.holds m (sBr d) ↔ d = decide (d0 ≠ 0) := by
  simp only [Br.holds, sBr, CmpOp.eval, Rv.E.eval, h]
  by_cases h0 : d0 = 0
  · subst h0; cases d <;> simp
  · have : BitVec.ofNat 64 (frameA d0) ≠ BitVec.ofNat 64 (frameA 0) := by
      intro he
      have := congrArg BitVec.toNat he
      rw [toNat_ofNat_lt (by unfold frameA; omega), toNat_ofNat_lt (by unfold frameA; omega)] at this
      unfold frameA at this; omega
    cases d <;> simp [this, h0]

/-- `coord_end_c`: the final checks of coordinate `c` (`E = 1`, empty stack), then leaf 0 of `c + 1` or the forest. -/
theorem coord_step (F : FCtx) (c : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (E ptr folds : Nat)
    (node : Digest) (m : MachineState) (h : CoordIn F c roots stk E ptr folds node m) :
    (E ≠ 1 → ∃ u, Steps image m 4 4 u ∧ Halt1 u) ∧
    (E = 1 → stk ≠ [] → ∃ u, Steps image m 5 5 u ∧ Halt1 u) ∧
    (E = 1 → stk = [] → c < 6 → ∃ u, Steps image m 5 5 u ∧ LeafIn F (c + 1) 0 (roots ++ [node]) [] ptr folds u) ∧
    (E = 1 → stk = [] → c = 6 → ∃ u, Steps image m 2 2 u ∧ ForestIn F (roots ++ [node]) ptr folds u) := by
  have hc7 := h.fb.hc
  have hE := h.hE
  have hkn : KnownOK (coordKnown c) m := by
    intro p hp
    simp only [coordKnown, List.mem_append, List.mem_singleton] at hp
    rcases hp with (hp | hp) | rfl
    · exact h.fb.glob.1 p hp
    · exact h.fb.leafCK p hp
    · exact h.s9
  have tC := coordCheck1_at c hc7
  unfold coordCheck1 at tC
  simp only [Bool.and_eq_true] at tC
  obtain ⟨⟨tPass, tRejE⟩, tRejS⟩ := tC
  have heB := eBr_holds m E h.s7 hE
  have hsB := sBr_holds m stk.length h.a5 h.bnd.1
  have hpass : E = 1 → stk = [] → ∃ u, SpecRes [] [] gkF (coordSpec c) (coordPost c) [.x14, .x15, .x22, .x23] m u := by
    intro he1 hnil
    exact spec_run tPass m h.pc hkn (by
      intro b hb; simp only [coordSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (hsB false).mpr (by simp [hnil])
      · exact (heB false).mpr (by simp [he1])) (by simp)
  have hroots := h.hroots
  -- the common part of the two passing branches
  have hcommon : ∀ u, SpecRes [] [] gkF (coordSpec c) (coordPost c) [.x14, .x15, .x22, .x23] m u →
      (∀ A, u.getMem A = m.getMem A) ∧ RootsOK (roots ++ [node]) u ∧ (roots ++ [node]).length = c + 1 := by
    intro u hu
    have hmem : ∀ A, u.getMem A = m.getMem A := fun A => by rw [hu.mem]; rfl
    refine ⟨hmem, fun k hk => ?_, by simp [hroots]⟩
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hkc : k < roots.length
    · rw [List.getD_append _ _ _ _ hkc]
      obtain ⟨h1, h2⟩ := h.rts k hkc
      exact ⟨(hmem _).trans h1, (hmem _).trans h2⟩
    · have hk' : k = roots.length := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), hk', Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [hroots]
      exact ⟨(hmem _).trans h.nd.1, (hmem _).trans h.nd.2⟩
  refine ⟨fun hne => ?_, fun he1 hne => ?_, fun he1 hnil hc6 => ?_, fun he1 hnil hc6 => ?_⟩
  · obtain ⟨u, hu⟩ := spec_run tRejE m h.pc hkn (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (heB true).mpr (by simp [hne])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · have hlen : stk.length ≠ 0 := fun h0 => hne (List.length_eq_zero_iff.mp h0)
    obtain ⟨u, hu⟩ := spec_run tRejS m h.pc hkn (by
      intro b hb; simp only [rejSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact (hsB true).mpr (by simp [hlen])
      · exact (heB false).mpr (by simp [he1])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · obtain ⟨u, hu⟩ := hpass he1 hnil
    obtain ⟨hmem, hrts, hlen⟩ := hcommon u hu
    subst hnil
    obtain ⟨-, folds0, a0, hb0, ha0, hf0⟩ := h.bnd
    have hpost : KnownOK (coordKnown (c + 1)) u := by
      have := hu.known; simp only [coordPost, if_pos hc6] at this; exact this
    have hst : Steps image m 5 5 u := hu.steps.of_eq (by simp [coordSpec, hc6]) (by simp [coordSpec, hc6])
    have hck : KnownOK (packedCK (c + 1) F.idx) u := by
      intro p hp
      simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [hu.regs (.x27, .bin .add (.reg .x27) (cw 65536)) (by simp [coordSpec, hc6])]
        have hr := h.fb.ck (.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) F.idx)) (by simp [packedCK])
        simp only [Rv.E.eval, BinOp.eval, cw, hr, BitVec.ofNat_add_ofNat]
        have hi := F.idx_lt
        have hnum : hdr1 (0xa01 + 65536 * c) F.idx + 65536 =
            hdr1 (0xa01 + 65536 * (c + 1)) F.idx := by
          have hb : 0xa01 + 65536 * c < 2^32 := by omega
          have hb' : 0xa01 + 65536 * (c+1) < 2^32 := by omega
          simp only [hdr1, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb']
          omega
        exact congrArg (BitVec.ofNat 64) hnum
      · rw [hu.regs (.x28, .bin .add (.reg .x28) (cw 65536)) (by simp [coordSpec, hc6])]
        have hr := h.fb.ck (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) F.idx)) (by simp [packedCK])
        simp only [Rv.E.eval, BinOp.eval, cw, hr, BitVec.ofNat_add_ofNat]
        have hi := F.idx_lt
        have hnum : hdr1 (0x901 + 65536 * c) F.idx + 65536 =
            hdr1 (0x901 + 65536 * (c + 1)) F.idx := by
          have hb : 0x901 + 65536 * c < 2^32 := by omega
          have hb' : 0x901 + 65536 * (c+1) < 2^32 := by omega
          simp only [hdr1, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb']
          omega
        exact congrArg (BitVec.ofNat 64) hnum
    refine ⟨u, hst, ⟨⟨hu.glob _ _ _ h.fb.glob (RelOK.nil m), hck,
      by rw [hu.keep .x22 (by simp)]; exact h.fb.idx, fun s hs => by rw [hmem]; exact h.fb.thdr s hs,
      by rw [hmem]; exact h.fb.sent, fun d h1 h2 => by rw [hmem, hmem]; exact h.fb.fpad d h1 h2, by omega⟩,
      ?_, ?_, ?_, ?_, StackOK.nil u, hrts, hlen, h.wit.transport hmem, ?_⟩⟩
    · rw [hu.pc rfl]; simp only [coordSpec, coordNext, if_pos hc6]; rfl
    · rw [hu.keep .x14 (by simp)]; exact h.a4
    · rw [hu.keep .x15 (by simp)]; exact h.a5
    · exact hpost (.x25, BitVec.ofNat 64 (forestSlot (c + 1))) (by simp [coordKnown])
    · refine ⟨by omega, by decide, ⟨by decide, by decide⟩, ?_, ?_⟩
      · have := hb0.hptr; unfold segsDone at *; simp only [List.length_nil] at *; omega
      · have := hb0.hf; have := hb0.hptr; unfold segsDone at *; simp only [List.length_nil] at *; omega
  · obtain ⟨u, hu⟩ := hpass he1 hnil
    obtain ⟨hmem, hrts, hlen⟩ := hcommon u hu
    subst hnil hc6
    obtain ⟨-, folds0, a0, hb0, ha0, hf0⟩ := h.bnd
    have hst : Steps image m 2 2 u := hu.steps.of_eq (by simp [coordSpec]) (by simp [coordSpec])
    refine ⟨u, hst, ⟨hu.glob _ _ _ h.fb.glob (RelOK.nil m), by rw [hu.keep .x22 (by simp)]; exact h.fb.idx,
      ?_, ?_, hrts, hlen, h.wit.transport hmem, ?_, ?_⟩⟩
    · rw [hu.pc rfl]; simp only [coordSpec, coordNext]; rfl
    · rw [hu.keep .x14 (by simp)]; exact h.a4
    · have := hb0.hptr; unfold segsDone at *; simp only [List.length_nil] at *; omega
    · have := hb0.hf; have := hb0.hptr; unfold segsDone at *; simp only [List.length_nil] at *; omega

/-! ## The forest -/

/-- The state after the forest HASH, at `xtr3_1` (pc 656): the layers phase (V1) starts here. The forest pk `root` is
the encoding block's message field (`0x100`), `s6 = idx`, `Glob baseK` (`t0 = 0`, `s2 = 0xFFF`; the witness header with
the four counters; pk; the zero words and the counter's high half of the encoding block), and every witness word of
the header and of the layer region (offsets ≥ `streamEnd` = 10568, with the zero memory past W up to `WX`) is
original. -/
structure FtsOut (F : FCtx) (root : Digest) (u : MachineState) : Prop where
  glob : Glob baseK F.w F.pk u
  idx : u.getReg .x22 = BitVec.ofNat 64 F.idx
  pc : u.pc = pcOf layerPc
  root : DigAt u 0x100 root
  wit : Orig F.w (fun o => o < 64 ∨ 10568 ≤ o) u

theorem hdr0_forest (idx : Nat) (hi : idx < 2 ^ 32) : hdr0 11 0 idx 0 = 0xb01 := by
  rw [hdr0_eq 11 0 idx 0 (by decide) (by decide) hi (by decide)]; norm_num

theorem hdr1_forest (idx : Nat) (hi : idx < 2 ^ 32) : hdr1 idx 0 = idx := by
  unfold hdr1; rw [Nat.mod_eq_of_lt hi]; simp

theorem capBr_holds (m : MachineState) (folds : Nat) (h14 : m.getReg .x14 = BitVec.ofNat 64 (WIT + (1368 + 80 * folds) - 880))
    (hf : folds ≤ 385) (d : Bool) : Br.holds m (capBr d) ↔ d = decide (115 < folds) := by
  simp only [Br.holds, capBr, CmpOp.eval, Rv.E.eval, h14]
  have hlt : (BitVec.ofNat 64 A4_LIMIT).ult (BitVec.ofNat 64 (WIT + (1368 + 80 * folds) - 880)) =
      decide (115 < folds) := by
    simp only [BitVec.ult, toNat_ofNat_lt (show A4_LIMIT < 2 ^ 64 by unfold A4_LIMIT; omega),
      toNat_ofNat_lt (show WIT + (1368 + 80 * folds) - 880 < 2 ^ 64 by unfold WIT; omega), decide_eq_decide]
    unfold A4_LIMIT WIT; omega
  rw [hlt]; exact eq_comm

/-- The sixteen doublewords of the forest frame. -/
theorem forest_words (u : MachineState) (idx : Nat) (roots : List Digest) (hlen : roots.length = 7)
    (hr : RootsOK roots u) (h16 : u.getMem (BitVec.ofNat 64 0x710) = BitVec.ofNat 64 (hdr0 11 0 idx 0))
    (h24 : u.getMem (BitVec.ofNat 64 0x718) = BitVec.ofNat 64 (hdr1 idx 0)) :
    u.readWords (BitVec.ofNat 64 FOREST) 16 = wordsOf (forestInput idx roots) := by
  match roots, hlen, hr with
  | [r0, r1, r2, r3, r4, r5, r6], _, hr =>
    have d0 : DigAt u 0x700 r0 := hr 0 (by simp)
    have d1 : DigAt u 0x720 r1 := hr 1 (by simp)
    have d2 : DigAt u 0x730 r2 := hr 2 (by simp)
    have d3 : DigAt u 0x740 r3 := hr 3 (by simp)
    have d4 : DigAt u 0x750 r4 := hr 4 (by simp)
    have d5 : DigAt u 0x760 r5 := hr 5 (by simp)
    have d6 : DigAt u 0x770 r6 := hr 6 (by simp)
    have e0 : u.getMem (BitVec.ofNat 64 1792) = dlo r0 := d0.1
    have e1 : u.getMem (BitVec.ofNat 64 1800) = dhi r0 := d0.2
    have e2 : u.getMem (BitVec.ofNat 64 1808) = BitVec.ofNat 64 (hdr0 11 0 idx 0) := h16
    have e3 : u.getMem (BitVec.ofNat 64 1816) = BitVec.ofNat 64 (hdr1 idx 0) := h24
    have e4 : u.getMem (BitVec.ofNat 64 1824) = dlo r1 := d1.1
    have e5 : u.getMem (BitVec.ofNat 64 1832) = dhi r1 := d1.2
    have e6 : u.getMem (BitVec.ofNat 64 1840) = dlo r2 := d2.1
    have e7 : u.getMem (BitVec.ofNat 64 1848) = dhi r2 := d2.2
    have e8 : u.getMem (BitVec.ofNat 64 1856) = dlo r3 := d3.1
    have e9 : u.getMem (BitVec.ofNat 64 1864) = dhi r3 := d3.2
    have e10 : u.getMem (BitVec.ofNat 64 1872) = dlo r4 := d4.1
    have e11 : u.getMem (BitVec.ofNat 64 1880) = dhi r4 := d4.2
    have e12 : u.getMem (BitVec.ofNat 64 1888) = dlo r5 := d5.1
    have e13 : u.getMem (BitVec.ofNat 64 1896) = dhi r5 := d5.2
    have e14 : u.getMem (BitVec.ofNat 64 1904) = dlo r6 := d6.1
    have e15 : u.getMem (BitVec.ofNat 64 1912) = dhi r6 := d6.2
    rw [readWords_ofNat u FOREST 16 (by unfold FOREST; norm_num), wordsOf_forestInput,
      show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl]
    simp only [List.map_cons, List.map_nil, FOREST, Nat.reduceMul, Nat.reduceAdd, e0, e1, e2, e3, e4, e5, e6, e7,
      e8, e9, e10, e11, e12, e13, e14, e15, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
      List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil]

/-- The forest: the pointer cap, the frame header, the HASH of `[root_0 | T(11) | root_1 .. root_6]` into `0x100`. -/
theorem forest_step (F : FCtx) (roots : List Digest) (ptr folds : Nat) (m : MachineState)
    (h : ForestIn F roots ptr folds m) :
    (115 < folds → ∃ u, Steps image m 4 4 u ∧ Halt1 u) ∧
    (folds ≤ 115 → ∃ u, Steps image m 7 7 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧
      hashArgumentsValid u = true ∧ hashInput u = toQ (T3.pad64 (forestInput F.idx roots)) ∧
      ∀ ans : BitVec 256, FtsOut F (ans.extractLsb' 0 128) (Legacy.Riscv.writeHash u ans)) := by
  have hk : KnownOK gkF m := h.glob.1
  have tF := forestCheckF_ok
  unfold forestCheckF at tF
  simp only [Bool.and_eq_true] at tF
  obtain ⟨tPass, tRej⟩ := tF
  have hcap := capBr_holds m folds (by rw [← h.hptr]; exact h.a4) h.hf
  have hi32 : F.idx < 2 ^ 32 := lt_trans F.idx_lt (by norm_num)
  refine ⟨fun hgt => ?_, fun hle => ?_⟩
  · obtain ⟨u, hu⟩ := spec_run tRej m h.pc hk (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      exact (hcap true).mpr (by simp [hgt])) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · obtain ⟨u, hu⟩ := spec_run tPass m h.pc hk (by
      intro b hb; simp only [forestSpecF, List.mem_singleton] at hb; subst hb
      exact (hcap false).mpr (by simp; omega)) (by simp)
    have hmem : ∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
        if B = FOREST + 24 then BitVec.ofNat 64 F.idx
        else if B = FOREST + 16 then BitVec.ofNat 64 0xb01 else m.getMem (BitVec.ofNat 64 B) := by
      intro B hB
      rw [hu.mem]; simp only [forestSpecF]
      rw [memEval_cons_ofNat _ _ _ _ _ hB (by unfold FOREST; omega),
        memEval_cons_ofNat _ _ _ _ _ hB (by unfold FOREST; omega), memEval_nil]
      simp only [Rv.E.eval, h.idx, cw]
    have hfr : ∀ B, B < 2 ^ 64 → B ≠ FOREST + 16 → B ≠ FOREST + 24 →
        u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) :=
      fun B hB h1 h2 => by rw [hmem B hB, if_neg h2, if_neg h1]
    have h10 : u.getReg .x10 = BitVec.ofNat 64 FOREST := hu.regs (.x10, cw FOREST) (by simp [forestSpecF])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 128 := hu.regs (.x11, cw 128) (by simp [forestSpecF])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 0x100 := hu.regs (.x12, cw 0x100) (by simp [forestSpecF])
    have hr := h.hroots
    have hrts : RootsOK roots u :=
      h.rts.frame (fun k hk => ⟨hfr _ (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot FOREST; split <;> omega) (by unfold forestSlot FOREST; split <;> omega),
        hfr _ (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot FOREST; split <;> omega) (by unfold forestSlot FOREST; split <;> omega)⟩)
    have hlen := forestInput_length F.idx roots h.hroots
    have hin : hashInput u = toQ (T3.pad64 (forestInput F.idx roots)) := by
      rw [pad64_forestInput F.idx roots h.hroots]
      refine hashInput_toQ u _ 1 FOREST (by rw [hlen]) h10 (by unfold FOREST; omega) (by unfold FOREST; omega)
        (by rw [h11]) (by norm_num) ?_
      refine forest_words u F.idx roots h.hroots hrts ?_ ?_
      · rw [hmem _ (by norm_num), if_neg (by unfold FOREST; omega), if_pos (by unfold FOREST; omega),
          hdr0_forest F.idx hi32]
      · rw [hmem _ (by norm_num), if_pos (by unfold FOREST; omega), hdr1_forest F.idx hi32]
    refine ⟨u, hu.steps, hu.ecall rfl, hu.known (.x5, 0) (by simp [baseK]),
      hashArgs_of u _ 128 _ h10 h11 h12 (by unfold FOREST; omega) (by decide) (by unfold FOREST; norm_num)
        (by decide) (by norm_num), hin, fun ans => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact Glob_writeHash (hu.glob _ _ _ h.glob (RelOK.nil m)) ans 0x100 h12 (by decide)
    · rw [writeHash_getReg, hu.keep .x22 (by simp)]; exact h.idx
    · rw [writeHash_pc, hu.pc rfl]; exact pcOf_add4 655
    · exact writeHash_lo u ans 0x100 h12 (by norm_num)
    · have hw : Orig F.w (fun o => o < 64 ∨ leafNT o ∨ ptr ≤ o) u :=
        h.wit.frame (fun jj h1 h2 => hfr _ (by unfold WIT WX at *; omega) (by unfold WIT FOREST; omega)
          (by unfold WIT FOREST; omega))
      have hw2 := Orig_writeHash hw ans 0x100 h12 (by norm_num)
      have hp := h.hptr
      exact hw2.mono (fun o ho => ⟨by rcases ho with ho | ho; exact Or.inl ho; exact Or.inr (Or.inr (by omega)),
        Or.inr (by unfold WIT; omega)⟩)

end SigGolfCandidate.T3M.Verify
