import SigGolfCandidate.T3M.Verify.FtsDefs

/-!
# The FTS stream machine: one block at a time (T3M)

From a boundary invariant (`FtsDefs`) through one checked run (and, where the run ends at a HASH, the answer) to the
next boundary, or to HALT(1).
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## Helpers -/

/-- `spec_run` for the `noAlias` path runs (`runAtN`). -/
theorem spec_runN {allow : List Nat} {rel : List Reg} {gk known post : List (Reg × Word)} {stops : List Nat}
    {n : Nat} {dirs : List Dir} {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : specB allow rel gk (runAtN known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, SpecRes allow rel gk sp post keep s t := by
  unfold specB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  obtain ⟨hst', hec'⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl']; exact hob)
    (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro gk0 w pk hG hrel; exact Glob_toState_allow hG r.st _ hmok hrel hrok
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]

/-- t3-rl2: word 1 of a tag-10 header at position 0 is `FtsRev.rv index`. -/
theorem nw10_rv (n : Nat) (hn : n < 2 ^ 32) : BitVec.ofNat 64 (T3.nodeWord 10 0 n) = FtsRev.rv n := by
  unfold FtsRev.rv
  rw [nodeWord_10, hdr1_eq _ 0 hn (by norm_num), Nat.mul_zero, Nat.add_zero]

/-- t3-rl2: word 1 of the tag-9 header of leaf `g` is `FtsRev.rv (2048 + g)` (the table word). -/
theorem nw9_rv (g : Nat) (hg : g < 2048) : BitVec.ofNat 64 (T3.nodeWord 9 0 g) = FtsRev.rv (2048 + g) := by
  unfold FtsRev.rv
  rw [nodeWord_9, Nat.mod_eq_of_lt (show g < 2 ^ 32 by omega), FtsRev.xor_2048 g hg,
    hdr1_eq _ 0 (by omega) (by norm_num), Nat.mul_zero, Nat.add_zero]

theorem addC_reg_eval (s : MachineState) (r : Reg) (A k : Nat) (h : s.getReg r = BitVec.ofNat 64 A) :
    (addC (.reg r) (BitVec.ofNat 64 k)).eval s = BitVec.ofNat 64 (A + k) := by
  rw [addC_eval]; simp only [E.eval, h, BitVec.ofNat_add_ofNat]

theorem a4E_eval (s : MachineState) (A k : Nat) (h : s.getReg .x14 = BitVec.ofNat 64 A) :
    (a4E k).eval s = BitVec.ofNat 64 (A + k) := addC_reg_eval s .x14 A k h

theorem a4A_eval (s : MachineState) (A k : Nat) (h : s.getReg .x14 = BitVec.ofNat 64 A) :
    (a4A k).eval s = BitVec.ofNat 64 (A + k) := by
  simp only [a4A, Addr.eval, E.eval, h, BitVec.ofNat_add_ofNat]

theorem accessValid_ofNat (A w : Nat) (hA : A + w ≤ 2 ^ 24) (hw : A % w = 0) :
    accessValid (BitVec.ofNat 64 A) w = true := by
  simp only [accessValid, rangeValid, MEMORY_BYTES, Bool.and_eq_true, decide_eq_true_eq,
    toNat_ofNat_lt (show A < 2 ^ 64 by omega)]
  exact ⟨hA, hw⟩

theorem hdr0_node (c idx : Nat) (hc : c < 256) (hi : idx < 2 ^ 32) : hdr0 10 c idx idx = hdr1 (nodeW0 c) idx := by
  rw [hdr0_eq 10 c idx idx (by decide) hc hi hi]; unfold nodeW0 hdr1; omega

theorem hdr0_leaf (c idx : Nat) (hc : c < 256) (hi : idx < 2 ^ 32) : hdr0 9 c idx idx = hdr1 (leafW0 c) idx := by
  rw [hdr0_eq 9 c idx idx (by decide) hc hi hi]; unfold leafW0 hdr1; omega

/-- A sub-doubleword `sw2E` evaluated on a state. -/
theorem sw2E_eval (s : MachineState) (old v : E) (I V : Nat) (h22 : s.getReg .x22 = BitVec.ofNat 64 I)
    (hv : v.eval s = BitVec.ofNat 64 V) : (sw2E old v).eval s = BitVec.ofNat 64 (hdr1 I V) := by
  simp only [sw2E, E.eval, BinOp.eval, h22, hv]
  exact merge_sw2 _ I V

theorem swTreeE_eval (s : MachineState) (v : E) (I V : Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 I) (hv : v.eval s = BitVec.ofNat 64 V) :
    (swTreeE v).eval s = BitVec.ofNat 64 (hdr1 V I) := by
  apply BitVec.eq_of_toNat_eq
  simp only [swTreeE, E.eval, BinOp.eval, h22, hv, merge_w4_toNat, BitVec.toNat_ofNat]
  have h := hdr1_lt V I
  unfold hdr1 at h ⊢
  omega

/-! ## Frames and the stack -/

theorem frameA_lt (d : Nat) (hd : d ≤ 2) : frameA d + 80 ≤ 0x6F0 := by unfold frameA; omega

theorem StackOK.nil (m : MachineState) : StackOK [] m := fun i hi => by simp at hi

/-- The stack is unchanged by writes outside the frame words `[0x600, 0x6A0 + 16)` and the `Q` slots. -/
theorem StackOK.frame {stk : List (Digest × Nat)} {m u : MachineState} (h : StackOK stk m)
    (hf : ∀ i, i < stk.length → u.getMem (BitVec.ofNat 64 (frameA (i + 1))) = m.getMem (BitVec.ofNat 64 (frameA (i + 1))) ∧
      u.getMem (BitVec.ofNat 64 (frameA (i + 1) + 8)) = m.getMem (BitVec.ofNat 64 (frameA (i + 1) + 8)) ∧
      u.getMem (BitVec.ofNat 64 (frameA (i + 1) - 16)) = m.getMem (BitVec.ofNat 64 (frameA (i + 1) - 16))) :
    StackOK stk u := by
  intro i hi
  obtain ⟨e1, e2, e3⟩ := hf i hi
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h i hi
  exact ⟨⟨e1.trans h1, e2.trans h2⟩, e3.trans h3, h4⟩

theorem RootsOK.nil (m : MachineState) : RootsOK [] m := fun k hk => by simp at hk

theorem RootsOK.frame {roots : List Digest} {m u : MachineState} (h : RootsOK roots m)
    (hf : ∀ k, k < roots.length → u.getMem (BitVec.ofNat 64 (forestSlot k)) = m.getMem (BitVec.ofNat 64 (forestSlot k)) ∧
      u.getMem (BitVec.ofNat 64 (forestSlot k + 8)) = m.getMem (BitVec.ofNat 64 (forestSlot k + 8))) :
    RootsOK roots u := by
  intro k hk
  obtain ⟨e1, e2⟩ := hf k hk
  obtain ⟨h1, h2⟩ := h k hk
  exact ⟨e1.trans h1, e2.trans h2⟩

theorem FB.leafCK {F : FCtx} {c : Nat} {m : MachineState} (_h : FB F c m) : KnownOK (leafCK c) m := by
  intro p hp
  simp [SigGolfCandidate.T3M.Verify.leafCK] at hp

/-! ## The FTS setup (words 383 .. 400) -/

theorem fts_setup_step (pk : Digest) (w : WBytes) (a : HashOutput) (t : MachineState) (ht : FtsReady pk w a t) :
    ∃ u, Steps image t 18 18 u ∧ LeafIn ⟨pk, w, a⟩ 0 0 [] [] 1088 0 u := by
  obtain ⟨ht, hpc⟩ := ht
  have hk0 : KnownOK baseK t := ht.known
  have htidx : t.getReg .x22 = BitVec.ofNat 64 (a.toNat % 2 ^ 31) := ht.idx
  -- words 383 .. 389: the six setup constants from the embedded data
  obtain ⟨t1, h1⟩ := spec_run setupLdCheckF_ok t hpc hk0 (by simp [setupLdSpec]) (by simp)
  have hm1 : ∀ A, t1.getMem A = t.getMem A := fun A => by rw [h1.mem]; rfl
  have r14 : t1.getReg .x14 = (E.ld (cw (DATA + 40))).eval t := h1.regs (.x14, .ld (cw (DATA + 40))) (by simp [setupLdSpec])
  have r29 : t1.getReg .x29 = (E.ld (cw (DATA + 48))).eval t := h1.regs (.x29, .ld (cw (DATA + 48))) (by simp [setupLdSpec])
  have r27 : t1.getReg .x27 = (E.ld (cw (DATA + 56))).eval t := h1.regs (.x27, .ld (cw (DATA + 56))) (by simp [setupLdSpec])
  have r28 : t1.getReg .x28 = (E.ld (cw (DATA + 64))).eval t := h1.regs (.x28, .ld (cw (DATA + 64))) (by simp [setupLdSpec])
  have r26 : t1.getReg .x26 = (E.ld (cw (DATA + 72))).eval t := h1.regs (.x26, .ld (cw (DATA + 72))) (by simp [setupLdSpec])
  have r21 : t1.getReg .x21 = (E.ld (cw (DATA + 80))).eval t := h1.regs (.x21, .ld (cw (DATA + 80))) (by simp [setupLdSpec])
  have e14 : t1.getReg .x14 = BitVec.ofNat 64 A4_0 :=
    r14.trans (ht.data.word 5 (by omega) A4_0 (by decide) (DATA + 40) (by omega))
  have e29 : t1.getReg .x29 = BitVec.ofNat 64 A4_LIMIT :=
    r29.trans (ht.data.word 6 (by omega) A4_LIMIT (by decide) (DATA + 48) (by omega))
  have e27 : t1.getReg .x27 = BitVec.ofNat 64 0xa01 :=
    r27.trans (ht.data.word 7 (by omega) 0xa01 (by decide) (DATA + 56) (by omega))
  have e28 : t1.getReg .x28 = BitVec.ofNat 64 0x901 :=
    r28.trans (ht.data.word 8 (by omega) 0x901 (by decide) (DATA + 64) (by omega))
  have e26 : t1.getReg .x26 = BitVec.ofNat 64 tbN :=
    r26.trans (ht.data.word 9 (by omega) tbN (by decide) (DATA + 72) (by omega))
  have e21 : t1.getReg .x21 = BitVec.ofNat 64 tbL :=
    r21.trans (ht.data.word 10 (by omega) tbL (by decide) (DATA + 80) (by omega))
  have hk : KnownOK setupLdK t1 := by
    intro p hp
    simp only [setupLdK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1.known p hp
    · exact e14
    · exact e29
    · exact e27
    · exact e28
    · exact e26
    · exact e21
  -- words 390 .. 400: both packed headers, persistent comparands and fallthrough to leaf 401
  obtain ⟨u, hu⟩ := spec_run setupCheckF_ok t1 (h1.pc rfl) hk (by simp [setupSpecF]) (by simp)
  have hmem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) =
      if A = SENTINEL then -1#64 else t.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu.mem]; simp only [setupSpecF]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by unfold SENTINEL; omega), memEval_nil, hm1]; rfl
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ SENTINEL → u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => by rw [hmem A hA, if_neg hne]
  have hpost : KnownOK setupPost u := hu.known
  have hW : Orig w (fun o => ¬ T8 o) u := by
    intro j hj hT
    rw [hfr _ (by unfold WIT WX at *; omega) (by unfold WIT SENTINEL; omega)]
    exact ht.wit j hj hT
  have hz : ∀ A, A < WIT → 0xB0 ≤ A → (A < ETAB ∨ ETAB + 24 * 7 ≤ A) → A ≠ SENTINEL →
      u.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA h1 h2 h3
    rw [hfr A (by unfold WIT at hA; omega) h3]
    exact ht.zero A hA (Or.inr (Or.inr h1)) h2
  have hst := h1.steps.trans hu.steps
  refine ⟨u, hst, ⟨⟨⟨?_, fun j hj => hW j (by unfold WX; omega) (by unfold T8; omega), ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, by decide⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro p hp; exact hpost p (by simp only [setupPost, List.mem_append]; exact Or.inl (Or.inl hp))
  · exact ⟨(hfr 0xA0 (by omega) (by unfold SENTINEL; omega)).trans ht.pk.1,
      (hfr 0xA8 (by omega) (by unfold SENTINEL; omega)).trans ht.pk.2⟩
  · intro q hq
    simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact hz _ (by unfold WIT; omega) (by omega) (Or.inl (by unfold ETAB; omega))
      (by unfold SENTINEL; omega)
  · show (u.getMem (BitVec.ofNat 64 CTRW)).toNat / 2 ^ 32 = 0
    rw [hz CTRW (by unfold CTRW WIT; omega) (by unfold CTRW; omega) (Or.inl (by unfold CTRW ETAB; omega))
      (by unfold CTRW SENTINEL; omega)]
    rfl
  · apply ht.data.congr
    intro A hA hEnd
    exact hfr A (by omega) (by first | (unfold SENTINEL TAB at *; omega) | (simp only [SENTINEL, TAB] at *; omega))
  · intro p hp
    simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [hu.regs (.x27, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0xa01)) (by simp [setupSpecF])]
      simp only [E.eval, BinOp.eval, cw]
      rw [h1.keep .x22 (by simp), htidx]
      rw [ofNat_shl, BitVec.ofNat_add_ofNat]
      congr 1
      unfold hdr1 FCtx.idx
      change (a.toNat % 2^31) * 2^32 + 0xa01 = 0xa01 % 2^32 + ((a.toNat % 2^31) % 2^32) * 2^32
      have hi := Nat.mod_lt a.toNat (by decide : 0 < 2^31)
      omega
    · rw [hu.regs (.x28, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0x901)) (by simp [setupSpecF])]
      simp only [E.eval, BinOp.eval, cw]
      rw [h1.keep .x22 (by simp), htidx]
      rw [ofNat_shl, BitVec.ofNat_add_ofNat]
      congr 1
      unfold hdr1 FCtx.idx
      change (a.toNat % 2^31) * 2^32 + 0x901 = 0x901 % 2^32 + ((a.toNat % 2^31) % 2^32) * 2^32
      have hi := Nat.mod_lt a.toNat (by decide : 0 < 2^31)
      omega
  · rw [hu.keep .x22 (by simp), h1.keep .x22 (by simp)]; exact ht.idx
  · intro s hs
    rw [hfr _ (by unfold leafT WIT; omega) (by unfold leafT WIT SENTINEL; omega)]
    have := ht.thdr (s / 3) (s % 3) (by omega) (by omega)
    rw [show selT8 (s / 3) (s % 3) = leafT s + 8 by unfold selT8 leafT; omega] at this
    exact this
  · rw [hmem _ (by unfold SENTINEL; omega), if_pos rfl]
  · intro d h1 h2
    exact ⟨hz _ (by unfold frameA WIT; omega) (by unfold frameA; omega) (Or.inr (by unfold frameA ETAB; omega))
        (by unfold frameA SENTINEL; omega),
      hz _ (by unfold frameA WIT; omega) (by unfold frameA; omega) (Or.inr (by unfold frameA ETAB; omega))
        (by unfold frameA SENTINEL; omega)⟩
  · rw [hu.pc rfl]; rfl
  · exact hpost (.x14, BitVec.ofNat 64 A4_0) (by simp [setupPost])
  · exact hpost (.x15, BitVec.ofNat 64 (frameA 0)) (by simp [setupPost])
  · exact hpost (.x25, BitVec.ofNat 64 FOREST) (by simp [setupPost])
  · exact StackOK.nil u
  · exact RootsOK.nil u
  · rfl
  · exact hW.mono (fun o ho => by unfold T8; unfold leafNT at ho; omega)
  · exact ⟨by decide, by decide, by simp, by simp [segsDone], by simp [segsDone]⟩

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## Leaves of the selections -/

theorem FCtx.g_lt (F : FCtx) (s : Nat) (hs : s < 21) : F.g s < 2048 := by
  unfold FCtx.g FCtx.sel T3M.selLeaf
  have := selC_bucket_lt F.a (s / 3) (by omega)
  have := selC_leaf_lt F.a (s / 3) (s % 3) (by omega)
  omega

/-! ## The leaf code -/

def leafCode (_j : Nat) : Nat := 3

theorem leafCheck_at (s : Nat) (hs : s < 21) : leafCheck s = true :=
  List.all_eq_true.mp leafCheck_all s (List.mem_range.mpr hs)

theorem and2047_eval (x : Word) (g : Nat) (hx : x = BitVec.ofNat 64 (2048 + g)) (hg : g < 2048) :
    BinOp.eval .and x (BitVec.ofNat 64 2047) = BitVec.ofNat 64 g := by
  apply BitVec.eq_of_toNat_eq
  rw [andMask_toNat' x 2047 11 rfl (by decide), hx, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  omega

/-- F5: the leaf code writes the header word 0 and reads the header word 1 the selection stored (`FB.thdr`). -/
theorem leaf_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (ptr folds : Nat)
    (m : MachineState) (h : LeafIn F c j roots stk ptr folds m) (node : Digest) :
    ∃ u, Steps image m (leafCode j) (leafCode j) u ∧
      DispIn F c j roots stk (.leaf (3 * c + j) (F.g (3 * c + j))) (2048 + F.g (3 * c + j)) ptr folds node u := by
  have hc := h.fb.hc
  have hj := h.bnd.hj
  set s := 3 * c + j with hs
  have hs3 : s / 3 = c := by omega
  have hsm : s % 3 = j := by omega
  have hs21 : s < 21 := by omega
  have hg := F.g_lt s hs21
  have hk : KnownOK (leafKnown s) m := by
    intro p hp
    simp only [leafKnown, List.mem_append, hs3, hsm] at hp
    rcases hp with hp | hp
    · exact h.fb.glob.1 p hp
    · exact h.fb.leafCK p hp
  have hLD : (Rv.E.ld (cw (leafT s + 8))).eval m = FtsRev.rv (2048 + F.g s) := h.fb.thdr s hs21
  obtain ⟨u, hu⟩ := spec_run (leafCheck_at s hs21) m (by rw [h.pc]) hk (by simp [leafSpec]) (by simp)
  have hmem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) =
      if A = leafT s then BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx) else m.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu.mem]
    simp only [leafSpec]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by unfold leafT WIT; omega), memEval_nil]
    simp only [E.eval, h.fb.ck (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) F.idx))
      (by simp [packedCK]), leafW0]
  have hfr : ∀ A, A < 2 ^ 64 → A ≠ leafT s →
      u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1; rw [hmem A hA, if_neg h1]
  have hlo : ∀ A, A < leafT s → u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A) := fun A hA =>
    hfr A (by unfold leafT WIT at hA; omega) (by omega)
  have hpost : KnownOK (leafPost s) u := hu.known
  refine ⟨u, hu.steps.of_eq (by unfold leafCode; simp only [leafSpec]) (by unfold leafCode; simp only [leafSpec]), ?_⟩
  refine ⟨⟨hu.glob _ _ _ h.fb.glob (RelOK.nil m), ?_, ?_, ?_, ?_, ?_, hc⟩, Or.inl ⟨rfl, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, h.hroots, ?_, h.bnd, by omega, fun _ => by have := h.bnd.hd; omega⟩
  · intro p hp
    simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · rw [hu.keep .x27 (by simp)]
      exact h.fb.ck (.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) F.idx)) (by simp [packedCK])
    · rw [hu.keep .x28 (by simp)]
      exact h.fb.ck (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) F.idx)) (by simp [packedCK])
  · rw [hu.keep .x22 (by simp)]; exact h.fb.idx
  · intro s' hs'
    rw [hfr _ (by unfold leafT WIT; omega) (by unfold leafT; omega)]; exact h.fb.thdr s' hs'
  · rw [hlo _ (by unfold SENTINEL leafT WIT; omega)]; exact h.fb.sent
  · intro d h1 h2
    rw [hlo _ (by unfold frameA leafT WIT; omega), hlo _ (by unfold frameA leafT WIT; omega)]
    exact h.fb.fpad d h1 h2
  · rw [hu.pc rfl]; rfl
  · rw [hu.keep .x14 (by simp)]; exact h.a4
  · rw [hu.keep .x15 (by simp)]; exact h.a5
  · have := hu.regs (.x23, .ld (cw (leafT s + 8))) (by simp [leafSpec]); simp only at this
    rw [this]; exact hLD
  · rw [hu.keep .x25 (by simp)]; exact h.s9
  · refine h.stack.frame (fun i hi => ⟨?_, ?_, ?_⟩)
    · rw [hlo _ (by have := h.bnd.hd; unfold frameA leafT WIT; omega)]
    · rw [hlo _ (by have := h.bnd.hd; unfold frameA leafT WIT; omega)]
    · rw [hlo _ (by have := h.bnd.hd; unfold frameA leafT WIT; omega)]
  · refine ⟨hs3, hs21, rfl, ?_, ?_, ?_⟩
    · have := hu.regs (.x10, cw (WIT + 64 + 48 * s)) (by simp [leafSpec]); simpa using this
    · rw [hmem _ (by unfold leafT WIT; omega), if_pos rfl]
    · rw [hfr _ (by unfold leafT WIT; omega) (by omega)]; exact h.fb.thdr s hs21
  · refine h.rts.frame (fun k hk => ⟨?_, ?_⟩)
    · rw [hlo _ (by rw [h.hroots] at hk; unfold forestSlot leafT WIT; split <;> omega)]
    · rw [hlo _ (by rw [h.hroots] at hk; unfold forestSlot leafT WIT; split <;> omega)]
  · intro jj h1 h2
    have hne : WIT + 8 * jj ≠ leafT s := by
      unfold leafT; unfold leafNT at h2
      rcases h2 with h2 | h2 | h2
      · omega
      · omega
      · have := h.bnd.hptr; omega
    rw [hfr _ (by unfold WIT WX at *; omega) hne]
    exact h.wit jj h1 h2

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## The dispatch -/

theorem even_andNot1 (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]

theorem wbyte_toNat (w : WBytes) (i : Nat) : (wbyte w i).toNat = w.toNat / 2 ^ (8 * i) % 256 := by
  simp only [wbyte, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem wbyte_lt (w : WBytes) (i : Nat) : (wbyte w i).toNat < 256 := (wbyte w i).toNat_lt

/-- The header byte read by `lbu gp, 880(a4)`. -/
theorem hdrByte_eval (w : WBytes) (m : MachineState) (ptr : Nat)
    (h14 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)) (hw : WitF w ptr m) (hp8 : ptr % 8 = 0)
    (hpx : ptr < WX) : hdrByteE.eval m = BitVec.ofNat 64 (wbyte w ptr).toNat := by
  have hword : m.getMem (BitVec.ofNat 64 (WIT + ptr)) = wword w (ptr / 8) := by
    have := hw.word ptr hp8 hpx (Or.inr (Or.inr (le_refl _)))
    exact this
  apply BitVec.eq_of_toNat_eq
  show (LoadKind.bu.fromWord (m.getMem ((a4E 880).eval m)) 0).toNat = _
  rw [a4E_eval m _ 880 h14, show WIT + ptr - 880 + 880 = WIT + ptr by unfold WIT; omega, hword]
  simp only [LoadKind.fromWord, extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, wword_toNat, Nat.zero_mul, pow_zero, Nat.div_one]
  rw [toNat_ofNat_lt (lt_trans (wbyte_lt w ptr) (by norm_num)), wbyte_toNat,
    show 64 * (ptr / 8) = 8 * ptr by omega, Nat.mod_mod_of_dvd _ (show 2 ^ 8 ∣ 2 ^ 64 by norm_num)]
  rw [Nat.mod_eq_of_lt (show w.toNat / 2 ^ (8 * ptr) % 2 ^ 8 < 2 ^ 64 from
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))]
  norm_num

theorem tabPc_eq (tb : Nat) : tabPc tb = 0x1000 + 4 * tabBase tb := by
  unfold tabPc tabBase tbN tbL; split <;> rfl

/-- F4: the table register of `tb` holds the table's address (both are constants of `gkF`). -/
theorem tabReg_val (m : MachineState) (hk : KnownOK gkF m) (tb : Nat) (htb : tb < 2) :
    m.getReg (tabReg tb) = BitVec.ofNat 64 (tabPc tb) := by
  rcases (show tb = 0 ∨ tb = 1 by omega) with rfl | rfl
  · exact hk (.x26, BitVec.ofNat 64 tbN) (by simp [gkF])
  · exact hk (.x21, BitVec.ofNat 64 tbL) (by simp [gkF])

theorem disp_target (w : WBytes) (m : MachineState) (ptr tb : Nat)
    (h14 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880)) (h20 : m.getReg (tabReg tb) = BitVec.ofNat 64 (tabPc tb))
    (hw : WitF w ptr m) (hp8 : ptr % 8 = 0) (hpx : ptr < WX) :
    (E.bin .and (dispT tb) notOne).eval m = pcOf (slotPc tb (wbyte w ptr).toNat) := by
  have hb := wbyte_lt w ptr
  have hT : (dispT tb).eval m = BitVec.ofNat 64 (tabPc tb + 32 * (wbyte w ptr).toNat) := by
    apply BitVec.eq_of_toNat_eq
    show (BinOp.eval .add (BinOp.eval .sll (hdrByteE.eval m) (BitVec.ofNat 64 5)) (BitVec.ofNat 64 (tabPc tb))).toNat = _
    rw [hdrByte_eval w m ptr h14 hw hp8 hpx]
    simp only [BinOp.eval, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    have hb64 : (wbyte w ptr).toNat % 2 ^ 64 = (wbyte w ptr).toNat := Nat.mod_eq_of_lt (by omega)
    rw [show 5 % 2 ^ 64 % 64 = 5 by norm_num, hb64, tabPc_eq]
    unfold tabBase; split <;> omega
  show BinOp.eval .and ((dispT tb).eval m) (~~~1#64) = _
  rw [hT]
  simp only [BinOp.eval]
  rw [even_andNot1 _ (by rw [tabPc_eq]; omega), tabPc_eq]
  unfold slotPc pcOf
  congr 1; omega

theorem dispObl_holds (m : MachineState) (ptr : Nat) (h14 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880))
    (hp8 : ptr % 8 = 0) (hp : 1088 ≤ ptr) (hpx : ptr < WX) : ∀ o ∈ dispObl, o.holds m := by
  intro o ho
  simp only [dispObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · simp only [Oblig.holds, E.eval, h14, toNat_ofNat_lt (show WIT + ptr - 880 < 2 ^ 64 by unfold WIT WX at *; omega)]
    unfold WIT; omega
  · simp only [Oblig.holds]
    rw [a4A_eval m _ 880 h14]
    exact accessValid_ofNat _ 1 (by unfold WIT WX at *; omega) (by omega)

theorem leafDispCheck_at (s : Nat) (hs : s < 21) : leafDispCheck s = true :=
  List.all_eq_true.mp leafDispCheck_all s (List.mem_range.mpr hs)

theorem mDispCheck_at (tb k : Nat) (htb : tb < 2) (hk : k < 3) : mDispCheck tb k = true := by
  have h := mDispCheck_all
  simp only [List.all_eq_true, List.mem_range] at h
  exact h tb htb k hk

theorem slotCheck1_at (tb b : Nat) (htb : tb < 2) (hb : b < 256) : slotCheck1 tb b = true := by
  have h : ∀ lo, slotCheck tb lo 128 = true → lo ≤ b → b < lo + 128 → slotCheck1 tb b = true := by
    intro lo hc h1 h2
    simp only [slotCheck, List.all_eq_true, List.mem_range'] at hc
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < 128 ∧ b = lo + 1 * i := ⟨b - lo, by omega, by omega⟩
    exact hc _ ⟨i, hi, rfl⟩
  rcases (show tb = 0 ∨ tb = 1 by omega) with rfl | rfl
  · by_cases hb' : b < 128
    · exact h 0 slotCheck_N0 (by omega) (by omega)
    · exact h 128 slotCheck_N1 (by omega) (by omega)
  · by_cases hb' : b < 128
    · exact h 0 slotCheck_L0 (by omega) (by omega)
    · exact h 128 slotCheck_L1 (by omega) (by omega)

theorem entCheck1_at (tb b : Nat) (htb : tb < 2) (hb : b < 256) : entCheck1 tb b = true := by
  have hc : entCheck tb 0 256 = true := by
    rcases (show tb = 0 ∨ tb = 1 by omega) with rfl | rfl
    · exact entCheck_N
    · exact entCheck_L
  simp only [entCheck, List.all_eq_true, List.mem_range'] at hc
  exact hc b ⟨b, hb, by omega⟩

theorem parBr_holds {m : MachineState} {ev : Nat} (h : m.getReg .x23 = FtsRev.rv ev)
    (t : Nat) (ht : t < 2) (d : Bool) : Br.holds m (parBr t d) ↔ d = decide (ev % 2 ≠ t) := by
  have key : BitVec.slt (m.getReg .x23) 0 = decide (ev % 2 = 1) := by rw [h]; exact FtsRev.rv_slt ev
  show CmpOp.eval (if t = 1 then .ge else .lt) (m.getReg .x23) 0 = d ↔ _
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;>
    rcases Nat.mod_two_eq_zero_or_one ev with he | he <;>
    simp only [CmpOp.eval, key, he, if_true, if_false, show ((0 : Nat) = 1) = False by decide] <;>
    cases d <;> simp

/-! ## The pending block -/

/-- The block of the pending hash. -/
def pendBlk (F : FCtx) (c : Nat) (node : Digest) : Pending → List UInt8
  | .leaf s g => blk4 (wleafPad F.w s) (header 9 c F.idx 0 g) (wsecret F.w s) (wleafPad F.w (s + 1))
  | .merge heap left => blk4 left (header 10 c F.idx 0 heap) 0 node

theorem pendingHash_eq (F : FCtx) (c : Nat) (node : Digest) (pend : Pending) :
    pendingHash F.w F.idx c node pend = T3.shortHash (pendBlk F c node pend) := by
  cases pend with
  | leaf s g => rfl
  | merge heap left => exact nodeHash_eq 10 c F.idx heap left node

theorem pendBlk_length (F : FCtx) (c : Nat) (node : Digest) (pend : Pending) : (pendBlk F c node pend).length = 64 := by
  cases pend <;> exact blk4_length _ _ _ _

theorem pendBlk_blocks (F : FCtx) (c : Nat) (node : Digest) (pend : Pending) :
    (toQ (T3.pad64 (pendBlk F c node pend))).blocks = 1 := by
  cases pend <;> exact blocks_blk4 _ _ _ _

/-- The address of the pending block. -/
def pendAddr (d : Nat) : Pending → Nat
  | .leaf s' _ => WIT + 64 + 48 * s'
  | .merge _ _ => frameA (d + 1)

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

theorem leafNT_of (s k : Nat) (hs : s < 21) (hk : k = 0 ∨ k = 8 ∨ k = 32 ∨ k = 40 ∨ k = 48 ∨ k = 56) :
    leafNT (64 + 48 * s + k) := by
  unfold leafNT; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The pending block's HASH input. -/
theorem pend_hashInput {ptr : Nat} (F : FCtx) (c d : Nat) (node : Digest) (pend : Pending) (m u : MachineState)
    (hp : PendOK F c d node m pend) (hw : WitF F.w ptr m) (hfb : FB F c m)
    (hmem : ∀ A, u.getMem A = m.getMem A) (h10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr d pend))
    (h11 : u.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput u = toQ (T3.pad64 (pendBlk F c node pend)) := by
  have hc := hfb.hc
  have hidx := F.idx_lt
  rw [T3.pad64, pendBlk_length, show (64 - 64 % 64) % 64 = 0 by rfl, List.replicate_zero, List.append_nil]
  cases pend with
  | leaf s g =>
    obtain ⟨hs3, hs21, hg, -, hT0, hT1⟩ := hp
    have hA : pendAddr d (.leaf s g) = WIT + 64 + 48 * s := rfl
    rw [hA] at h10
    apply hashInput_words8 u _ _ (pendBlk_length F c node _) h10 (by unfold WIT; omega) (by unfold WIT; omega) h11
    simp only [hmem]
    have dP := hw.dig (64 + 48 * s) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 0 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 8 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    have dS := hw.dig (64 + 48 * s + 32) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 32 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 40 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    have dQ := hw.dig (64 + 48 * s + 48) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 48 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 56 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    simp only [pendBlk, wordsOf_blk4, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_leaf c F.idx (by omega) (by omega)]
    rw [nw9_rv g (by rw [hg]; exact F.g_lt s hs21)]
    rw [show WIT + 64 + 48 * s + 8 = WIT + (64 + 48 * s) + 8 by ring, show WIT + 64 + 48 * s = WIT + (64 + 48 * s) by ring,
      dP.1, dP.2]
    rw [show WIT + (64 + 48 * s) + 16 = leafT s by unfold leafT; ring, hT0,
      show WIT + (64 + 48 * s) + 24 = leafT s + 8 by unfold leafT; ring, hT1,
      show WIT + (64 + 48 * s) + 32 = WIT + (64 + 48 * s + 32) by ring, dS.1,
      show WIT + (64 + 48 * s) + 40 = WIT + (64 + 48 * s + 32) + 8 by ring, dS.2,
      show WIT + (64 + 48 * s) + 48 = WIT + (64 + 48 * s + 48) by ring, dQ.1,
      show WIT + (64 + 48 * s) + 56 = WIT + (64 + 48 * s + 48) + 8 by ring, dQ.2]
    simp only [wleafPad, wsecret, leafBlock]
    rw [show 64 + 48 * (s + 1) = 64 + 48 * s + 48 by ring]
  | merge heap left =>
    obtain ⟨hd, hh, -, hL, hT0, hT1, hN⟩ := hp
    have hA : pendAddr d (.merge heap left) = frameA (d + 1) := rfl
    rw [hA] at h10
    apply hashInput_words8 u _ _ (pendBlk_length F c node _) h10 (by unfold frameA; omega) (by unfold frameA; omega) h11
    simp only [hmem]
    obtain ⟨z0, z1⟩ := hfb.fpad (d + 1) (by omega) hd
    simp only [pendBlk, wordsOf_blk4, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_node c F.idx (by omega) (by omega)]
    rw [nw10_rv heap (by omega)]
    rw [hL.1, hL.2, hT0, hT1, z0, z1, show frameA (d + 1) + 56 = frameA (d + 1) + 48 + 8 by ring, hN.1, hN.2]
    rfl

/-! ## The common invariant across a HASH -/

/-- A hash destination avoiding the words of the common invariant. -/
def FBAvoid (d : Nat) : Prop :=
  (d + 32 ≤ WIT + 64 ∨ WIT + 1088 ≤ d) ∧ (d + 32 ≤ SENTINEL ∨ SENTINEL + 8 ≤ d) ∧
    ∀ dd, 1 ≤ dd → dd ≤ 2 → (d + 32 ≤ frameA dd + 32 ∨ frameA dd + 48 ≤ d)

theorem FB.hash {F : FCtx} {c : Nat} {u : MachineState} (h : FB F c u) (ans : BitVec 256) (d : Nat)
    (h12 : u.getReg .x12 = BitVec.ofNat 64 d) (hsafe : safeDest d = true) (hav : FBAvoid d) (hd : d + 32 < 2 ^ 64) :
    FB F c (Legacy.Riscv.writeHash u ans) := by
  obtain ⟨a1, a2, a3⟩ := hav
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (Legacy.Riscv.writeHash u ans).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA hp => writeHash_frame u ans d A h12 hA (by omega) hp
  refine ⟨Glob_writeHash h.glob ans d h12 hsafe, h.ck.writeHash ans, by rw [writeHash_getReg]; exact h.idx,
    fun s hs => ?_, ?_, fun dd h1 h2 => ?_, h.hc⟩
  · rw [fr (leafT s + 8) (by unfold leafT WIT; omega) (by unfold leafT WIT at *; omega)]; exact h.thdr s hs
  · rw [fr SENTINEL (by unfold SENTINEL; omega) (by unfold SENTINEL at *; omega)]; exact h.sent
  · have := a3 dd h1 h2
    rw [fr (frameA dd + 32) (by unfold frameA; omega) (by unfold frameA at *; omega),
      fr (frameA dd + 40) (by unfold frameA; omega) (by unfold frameA at *; omega)]
    exact h.fpad dd h1 h2

theorem StackOK.hash {stk : List (Digest × Nat)} {u : MachineState} (h : StackOK stk u) (hlen : stk.length ≤ 2)
    (ans : BitVec 256) (d : Nat) (h12 : u.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64)
    (hav : ∀ i, i < stk.length → (frameA (i + 1) + 16 ≤ d ∨ d + 32 ≤ frameA (i + 1)) ∧
      (frameA (i + 1) - 8 ≤ d ∨ d + 32 ≤ frameA (i + 1) - 16)) :
    StackOK stk (Legacy.Riscv.writeHash u ans) := by
  refine h.frame (fun i hi => ?_)
  obtain ⟨h1, h2⟩ := hav i hi
  have hf : frameA (i + 1) < 2 ^ 63 := by unfold frameA; omega
  refine ⟨writeHash_frame u ans d _ h12 (by omega) (by omega) (by omega),
    writeHash_frame u ans d _ h12 (by omega) (by omega) (by omega),
    writeHash_frame u ans d _ h12 (by unfold frameA; omega) (by omega) (by unfold frameA at *; omega)⟩

theorem RootsOK.hash {roots : List Digest} {u : MachineState} (h : RootsOK roots u) (hlen : roots.length ≤ 7)
    (ans : BitVec 256) (d : Nat) (h12 : u.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64)
    (hav : ∀ k, k < roots.length → forestSlot k + 16 ≤ d ∨ d + 32 ≤ forestSlot k) :
    RootsOK roots (Legacy.Riscv.writeHash u ans) := by
  refine h.frame (fun k hk => ?_)
  have := hav k hk
  have hf : forestSlot k < 2 ^ 63 := by unfold forestSlot; split <;> omega
  exact ⟨writeHash_frame u ans d _ h12 (by omega) (by omega) (by omega),
    writeHash_frame u ans d _ h12 (by omega) (by omega) (by omega)⟩

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

theorem SegBnd.ptr_lt {c j d ptr folds : Nat} (h : SegBnd c j d ptr folds) : 1088 ≤ ptr ∧ ptr % 8 = 0 ∧
    ptr + 888 ≤ 32168 := by
  obtain ⟨hc, hj, ⟨hd1, hd2⟩, hp, hf⟩ := h
  unfold segsDone at *
  omega

theorem tselJ_lt (j : Nat) : tselJ j < 2 := by unfold tselJ; split <;> omega

theorem segX_lt (tb b : Nat) : segX tb b < 3 := by unfold segX; split_ifs <;> omega

theorem segX_P (j b : Nat) (h : segX (tselJ j) b = 1) : j ≠ 2 := by
  intro hj; subst hj
  unfold segX tselJ at h; by_cases hm : segM b = 1 <;> simp_all

theorem segX_F (j b : Nat) (h : segX (tselJ j) b = 2) : j = 2 := by
  by_contra hj
  unfold segX tselJ at h; by_cases hm : segM b = 1 <;> simp_all

/-- The destination address is safe, avoids the common words and the stack. -/
theorem destA_props (c X d : Nat) (hc : c < 7) (hX : X < 3) (hd : d ≤ 2) (hP : X = 1 → d < 2) :
    safeDest (destA c X d) = true ∧ FBAvoid (destA c X d) ∧ destA c X d + 32 < 2 ^ 64 ∧
    (∀ i, i < d → (frameA (i + 1) + 16 ≤ destA c X d ∨ destA c X d + 32 ≤ frameA (i + 1)) ∧
      (frameA (i + 1) - 8 ≤ destA c X d ∨ destA c X d + 32 ≤ frameA (i + 1) - 16)) ∧
    (∀ k, k < c → forestSlot k + 16 ≤ destA c X d ∨ destA c X d + 32 ≤ forestSlot k) ∧
    destA c X d + 32 ≤ WIT := by
  unfold destA
  rcases (show X = 0 ∨ X = 1 ∨ X = 2 by omega) with rfl | rfl | rfl
  · simp only [if_true]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [safeDest, frameA, pSlots, CTRW, WIT, MEMORY_BYTES]
      rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;> decide
    · unfold frameA WIT; omega
    · unfold frameA SENTINEL; omega
    · intro dd h1 h2; unfold frameA; omega
    · unfold frameA; omega
    · intro i hi; unfold frameA; omega
    · intro k hk; unfold frameA forestSlot; split <;> omega
    · unfold frameA WIT; omega
  · simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]
    have := hP rfl
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [safeDest, frameA, pSlots, CTRW, WIT, MEMORY_BYTES]
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> decide
    · unfold frameA WIT; omega
    · unfold frameA SENTINEL; omega
    · intro dd h1 h2; unfold frameA; omega
    · unfold frameA; omega
    · intro i hi; unfold frameA; omega
    · intro k hk; unfold frameA forestSlot; split <;> omega
    · unfold frameA WIT; omega
  · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [safeDest, forestSlot, pSlots, CTRW, WIT, MEMORY_BYTES]
      rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · unfold forestSlot WIT; split <;> omega
    · unfold forestSlot SENTINEL; split <;> omega
    · intro dd h1 h2; unfold forestSlot frameA; split <;> omega
    · unfold forestSlot; split <;> omega
    · intro i hi; unfold forestSlot frameA; split <;> omega
    · intro k hk; unfold forestSlot; split <;> split <;> omega
    · unfold forestSlot WIT; split <;> omega

theorem destE_eval (c X d : Nat) (m : MachineState) (h15 : m.getReg .x15 = BitVec.ofNat 64 (frameA d))
    (h25 : m.getReg .x25 = BitVec.ofNat 64 (forestSlot c)) (hX : X < 3) :
    (destE X).eval m = BitVec.ofNat 64 (destA c X d) := by
  unfold destE destA
  rcases (show X = 0 ∨ X = 1 ∨ X = 2 by omega) with rfl | rfl | rfl
  · simp [E.eval, BinOp.eval, h15, BitVec.ofNat_add_ofNat]
  · simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true, E.eval, BinOp.eval, h15, cw, BitVec.ofNat_add_ofNat]
    unfold frameA; congr 1
  · simp [E.eval, h25]

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-- The dispatch: to the table slot of the header byte; registers and memory kept, the link set. -/
theorem disp_run (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (pend : Pending)
    (E ptr folds : Nat) (node : Digest) (m : MachineState) (h : DispIn F c j roots stk pend E ptr folds node m) :
    ∃ u1, Steps image m 4 4 u1 ∧ u1.pc = pcOf (slotPc (tselJ j) (wbyte F.w ptr).toNat) ∧
      KnownOK gkF u1 ∧ Glob gkF F.w F.pk u1 ∧ (∀ A, u1.getMem A = m.getMem A) ∧
      (∀ r ∈ dispKeep, u1.getReg r = m.getReg r) ∧ u1.getReg .x24 = BitVec.ofNat 64 (lnk c j) := by
  obtain ⟨hp1088, hp8, hpmax⟩ := h.bnd.ptr_lt
  have hpx : ptr < WX := by unfold WX; omega
  have hg : KnownOK gkF m := h.fb.glob.1
  have hob := dispObl_holds m ptr h.a4 hp8 hp1088 hpx
  rcases h.pc with ⟨-, hpc⟩ | ⟨-, k, hk, hpc, h24⟩
  · have hs : 3 * c + j < 21 := by have := h.fb.hc; have := h.bnd.hj; omega
    obtain ⟨u1, hu⟩ := spec_run (leafDispCheck_at _ hs) m hpc hg (by simp [dispSpec]) hob
    refine ⟨u1, hu.steps, ?_, hu.known, hu.glob _ _ _ h.fb.glob (RelOK.nil m), fun A => by rw [hu.mem]; rfl,
      fun r hr => hu.keep r (by simpa using hr), ?_⟩
    · rw [hu.spc _ rfl, show (3 * c + j) % 3 = j by have := h.bnd.hj; omega]
      exact disp_target F.w m ptr _ h.a4 (tabReg_val m hg _ (tselJ_lt j)) h.wit hp8 hpx
    · have := hu.regs (.x24, cw (0x1000 + 4 * leafRet (3 * c + j))) (by simp [dispSpec]); simpa [lnk] using this
  · obtain ⟨u1, hu⟩ := spec_run (mDispCheck_at (tselJ j) k (tselJ_lt j) hk) m hpc hg (by simp [dispSpec]) hob
    refine ⟨u1, hu.steps, ?_, hu.known, hu.glob _ _ _ h.fb.glob (RelOK.nil m), fun A => by rw [hu.mem]; rfl,
      fun r hr => hu.keep r (List.mem_append_left _ hr), ?_⟩
    · rw [hu.spc _ rfl]; exact disp_target F.w m ptr _ h.a4 (tabReg_val m hg _ (tselJ_lt j)) h.wit hp8 hpx
    · rw [hu.keep .x24 (List.mem_append_right _ (List.mem_singleton_self _))]; exact h24

/-- Cycles from a dispatch to the pending HASH: 4 + 3 (t3-rl2: the side test is one `blt`/`bge`). -/
def segPre (_a : Nat) : Nat := 7

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-- `FB` transported to a state with the same memory, the constant registers and `s6`. -/
theorem FB.transport {F : FCtx} {c : Nat} {m u : MachineState} (h : FB F c m) (hg : Glob gkF F.w F.pk u)
    (hmem : ∀ A, u.getMem A = m.getMem A) (h27 : u.getReg .x27 = m.getReg .x27) (h28 : u.getReg .x28 = m.getReg .x28)
    (h22 : u.getReg .x22 = m.getReg .x22) : FB F c u := by
  refine ⟨hg, fun p hp => ?_, by rw [h22]; exact h.idx, fun s hs => by rw [hmem]; exact h.thdr s hs,
    by rw [hmem]; exact h.sent, fun d h1 h2 => by rw [hmem, hmem]; exact h.fpad d h1 h2, h.hc⟩
  simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · rw [h27]; exact h.ck (.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) F.idx)) (by simp [packedCK])
  · rw [h28]; exact h.ck (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) F.idx)) (by simp [packedCK])

theorem StackOK.transport {stk : List (Digest × Nat)} {m u : MachineState} (h : StackOK stk m)
    (hmem : ∀ A, u.getMem A = m.getMem A) : StackOK stk u :=
  h.frame (fun i _ => ⟨hmem _, hmem _, hmem _⟩)

theorem RootsOK.transport {roots : List Digest} {m u : MachineState} (h : RootsOK roots m)
    (hmem : ∀ A, u.getMem A = m.getMem A) : RootsOK roots u :=
  h.frame (fun k _ => ⟨hmem _, hmem _⟩)

theorem Orig.transport {w : WBytes} {P : Nat → Prop} {m u : MachineState} (h : Orig w P m)
    (hmem : ∀ A, u.getMem A = m.getMem A) : Orig w P u :=
  h.frame (fun j _ _ => hmem _)

theorem slotCheck1_parts (tb b : Nat) (htb : tb < 2) (hb : b < 256) :
    (11 < segA b → specB [] [] [] (runAt gkF [] (slotPc tb b) []) (rejSpec 4 []) [] [] [] = true) ∧
    (segA b = 0 → specB [] [] gkF (runAt gkF [] (slotPc tb b) [])
      ⟨[(.x14, a4E 8), (.x12, destE (segX tb b))], [], entry0PcT tb (segX tb b) + 1, true, 3, [], none, 3⟩
      [] gkF slotKeep = true) ∧
    (0 < segA b → segA b ≤ 11 → specB [] [] gkF (runAt gkF [] (slotPc tb b) [.br false])
      ⟨[(.x14, a4E (8 + 80 * segA b)), (.x12, a4E (888 + 48 * segT b))], [], slotPc tb b + 3, true, 3,
        [parBr (segT b) false], none, 3⟩ [] gkF slotKeep = true) ∧
    (0 < segA b → segA b ≤ 11 →
      specB [] [] [] (runAt gkF [] (slotPc tb b) [.br true]) (rejSpec 6 [parBr (segT b) true]) [] [] [] = true) := by
  have hc := slotCheck1_at tb b htb hb
  unfold slotCheck1 at hc
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [if_pos h] at hc; unfold slotSpec at hc; rw [if_pos h] at hc; exact hc
  · rw [if_neg (by omega), if_pos h] at hc; unfold slotSpec at hc; rw [if_neg (by omega), if_pos h] at hc; exact hc
  · rw [if_neg (by omega), if_neg (by omega), Bool.and_eq_true] at hc
    have := hc.1; unfold slotSpec at this; rw [if_neg (by omega), if_neg (by omega)] at this; exact this
  · rw [if_neg (by omega), if_neg (by omega), Bool.and_eq_true] at hc; exact hc.2

theorem segT_lt (b : Nat) : segT b < 2 := by unfold segT; omega

theorem slot_disp : ∀ r ∈ slotKeep, r ≠ .x24 → r ∈ dispKeep := by decide

/-- A destination in the witness area avoids the stack frames and the forest slots. -/
theorem wit_dest_avoid (d : Nat) (hd : WIT ≤ d) :
    (∀ i, i < 2 → (frameA (i + 1) + 16 ≤ d ∨ d + 32 ≤ frameA (i + 1)) ∧
      (frameA (i + 1) - 8 ≤ d ∨ d + 32 ≤ frameA (i + 1) - 16)) ∧
    (∀ k, k < 7 → forestSlot k + 16 ≤ d ∨ d + 32 ≤ forestSlot k) := by
  unfold WIT at hd
  refine ⟨fun i hi => ⟨Or.inl ?_, Or.inl ?_⟩, fun k hk => Or.inl ?_⟩
  · unfold frameA; omega
  · unfold frameA; omega
  · unfold forestSlot; split <;> omega

theorem slot_ent : ∀ r ∈ slotKeep,
    r ∈ ([.x10, .x12, .x14, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28] : List Reg) := by decide

/-- A segment's start: the dispatch jumps to the slot of the header byte `b`; `a > 11` rejects; `a ≥ 1` with
`t ≠ E % 2` rejects (parity); otherwise the slot performs the pending hash, straight into the variant's destination
(`a = 0`, then `TailIn`) or into fold block 0's current slot (`a ≥ 1`, then `j lad` and `RungIn`). -/
theorem seg_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (pend : Pending)
    (E ptr folds : Nat) (node : Digest) (m : MachineState) (h : DispIn F c j roots stk pend E ptr folds node m) :
    (11 < segA (wbyte F.w ptr).toNat → ∃ u, Steps image m 8 8 u ∧ Halt1 u) ∧
    (0 < segA (wbyte F.w ptr).toNat → segA (wbyte F.w ptr).toNat ≤ 11 → segT (wbyte F.w ptr).toNat ≠ E % 2 →
        ∃ u, Steps image m 10 10 u ∧ Halt1 u) ∧
    (segA (wbyte F.w ptr).toNat ≤ 11 → (segA (wbyte F.w ptr).toNat = 0 ∨ segT (wbyte F.w ptr).toNat = E % 2) →
        ∃ u, Steps image m (segPre (segA (wbyte F.w ptr).toNat)) (segPre (segA (wbyte F.w ptr).toNat)) u ∧
          fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
          hashInput u = toQ (T3.pad64 (pendBlk F c node pend)) ∧
          ∀ ans : BitVec 256,
            (segA (wbyte F.w ptr).toNat = 0 → TailIn F c j roots stk (segX (tselJ j) (wbyte F.w ptr).toNat) E (ptr + 8)
              folds (ans.extractLsb' 0 128) (Legacy.Riscv.writeHash u ans)) ∧
            (0 < segA (wbyte F.w ptr).toNat → ∃ v, Steps image (Legacy.Riscv.writeHash u ans) 1 1 v ∧
              RungIn F c j roots stk (segX (tselJ j) (wbyte F.w ptr).toNat) (segA (wbyte F.w ptr).toNat) 0 E ptr folds
                (ans.extractLsb' 0 128) v)) := by
  obtain ⟨hp1088, hp8, hpmax⟩ := h.bnd.ptr_lt
  have hpx : ptr < WX := by unfold WX; omega
  set b := (wbyte F.w ptr).toNat with hbdef
  have hb256 : b < 256 := wbyte_lt F.w ptr
  have htb := tselJ_lt j
  have hd2 := h.bnd.hd
  have hc7 := h.fb.hc
  obtain ⟨u1, hst1, hpc1, hk1, hg1, hm1, hr1, h24⟩ := disp_run F c j roots stk pend E ptr folds node m h
  obtain ⟨cRej, cZero, cOk, cPar⟩ := slotCheck1_parts (tselJ j) b htb hb256
  have r1 : ∀ r ∈ dispKeep, u1.getReg r = m.getReg r := hr1
  have e14 : u1.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880) := by rw [r1 .x14 (by simp [dispKeep])]; exact h.a4
  have e23 : u1.getReg .x23 = FtsRev.rv E := by rw [r1 .x23 (by simp [dispKeep])]; exact h.s7
  have e15 : u1.getReg .x15 = BitVec.ofNat 64 (frameA stk.length) := by rw [r1 .x15 (by simp [dispKeep])]; exact h.a5
  have e25 : u1.getReg .x25 = BitVec.ofNat 64 (forestSlot c) := by rw [r1 .x25 (by simp [dispKeep])]; exact h.s9
  have ht2 := segT_lt b
  refine ⟨fun ha => ?_, fun h1 h11 hne => ?_, fun ha hpar => ?_⟩
  · obtain ⟨u, hu⟩ := spec_run (cRej ha) u1 hpc1 (fun p hp => hk1 p (by simpa using hp)) (by simp [rejSpec]) (by simp)
    exact ⟨u, (hst1.trans hu.steps).of_eq (by simp [rejSpec]) (by simp [rejSpec]), hu.ecall rfl,
      hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · obtain ⟨u, hu⟩ := spec_run (cPar h1 h11) u1 hpc1 (fun p hp => hk1 p (by simpa using hp))
      (by intro br hbr; simp only [rejSpec, List.mem_singleton] at hbr; subst hbr
          exact (parBr_holds e23 _ ht2 true).mpr (by simp; omega)) (by simp)
    exact ⟨u, (hst1.trans hu.steps).of_eq (by simp [rejSpec]) (by simp [rejSpec]), hu.ecall rfl,
      hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · -- the accepting slot: the pending hash
    have common : ∀ (sp : Spec) (dirs : List Dir) (u : MachineState), SpecRes [] [] gkF sp gkF slotKeep u1 u →
        sp.mem = [] → (∀ A, u.getMem A = m.getMem A) ∧ KnownOK gkF u ∧ Glob gkF F.w F.pk u ∧
          (∀ r ∈ slotKeep, u.getReg r = u1.getReg r) := by
      intro sp dirs u hu hsm
      exact ⟨fun A => by rw [hu.mem, hsm]; exact hm1 A, hu.known, hu.glob _ _ _ hg1 (RelOK.nil u1), hu.keep⟩
    have hX3 := segX_lt (tselJ j) b
    have hpend10 : m.getReg .x10 = BitVec.ofNat 64 (pendAddr stk.length pend) := by
      cases pend with
      | leaf s g => exact h.pnd.2.2.2.1
      | merge heap left => exact h.pnd.2.2.1
    have hpend_lt : pendAddr stk.length pend + 64 ≤ 2 ^ 24 ∧ pendAddr stk.length pend % 8 = 0 := by
      cases pend with
      | leaf s g =>
        have := h.pnd.2.1
        show 2048 + 64 + 48 * s + 64 ≤ 2 ^ 24 ∧ (2048 + 64 + 48 * s) % 8 = 0
        omega
      | merge heap left =>
        have := h.pnd.1
        show 0x600 + 80 * (stk.length + 1) + 64 ≤ 2 ^ 24 ∧ (0x600 + 80 * (stk.length + 1)) % 8 = 0
        omega
    -- the facts at the ecall state, for both slot kinds
    have atEcall : ∀ (u : MachineState) (dst : Nat), (∀ A, u.getMem A = m.getMem A) → KnownOK gkF u →
        Glob gkF F.w F.pk u → (∀ r ∈ slotKeep, u.getReg r = u1.getReg r) →
        u.getReg .x12 = BitVec.ofNat 64 dst → dst % 8 = 0 → dst + 32 ≤ 2 ^ 24 →
        u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧ hashInput u = toQ (T3.pad64 (pendBlk F c node pend)) := by
      intro u dst hmu hku hgu hru h12 hd8 hdm
      have h10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr stk.length pend) := by
        rw [hru .x10 (by simp [slotKeep]), r1 .x10 (by simp [dispKeep])]; exact hpend10
      have h11 : u.getReg .x11 = BitVec.ofNat 64 64 := hku (.x11, 64) (by simp [gkF])
      refine ⟨hku (.x5, 0) (by simp [gkF, baseK]), hashArgs_of u _ 64 dst h10 h11 h12 hpend_lt.2 (by decide)
        hpend_lt.1 hd8 hdm, ?_⟩
      exact pend_hashInput F c stk.length node pend m u h.pnd h.wit h.fb hmu h10 h11
    by_cases ha0 : segA b = 0
    · obtain ⟨u, hu⟩ := spec_run (cZero ha0) u1 hpc1 hk1 (by simp) (by simp)
      obtain ⟨hmu, hku, hgu, hru⟩ := common _ [] u hu rfl
      have hX := segX_lt (tselJ j) b
      have hdst : u.getReg .x12 = BitVec.ofNat 64 (destA c (segX (tselJ j) b) stk.length) := by
        have := hu.regs (.x12, destE (segX (tselJ j) b)) (by simp); simp only at this
        rw [this]; exact destE_eval c _ stk.length u1 e15 e25 hX
      have hPd : segX (tselJ j) b = 1 → stk.length < 2 := fun hP => by
        have := segX_P j b hP; have := h.bnd.hj; omega
      obtain ⟨dsafe, davoid, dlt, dstack, droots, dlow⟩ :=
        destA_props c (segX (tselJ j) b) stk.length hc7 hX hd2.2 hPd
      have hdest8 : destA c (segX (tselJ j) b) stk.length % 8 = 0 := by
        unfold destA frameA forestSlot; split_ifs <;> omega
      obtain ⟨h5, hv, hin⟩ := atEcall u _ hmu hku hgu hru hdst hdest8 (by unfold WIT at dlow; omega)
      refine ⟨u, (hst1.trans hu.steps).of_eq (by unfold segPre; rfl) (by unfold segPre; rfl),
        hu.ecall rfl, h5, hv, hin, fun ans => ⟨fun _ => ?_, fun h0 => absurd ha0 (by omega)⟩⟩
      have hfbu : FB F c u := h.fb.transport hgu hmu (by rw [hru .x27 (by simp [slotKeep]), r1 .x27 (by simp [dispKeep])])
        (by rw [hru .x28 (by simp [slotKeep]), r1 .x28 (by simp [dispKeep])])
        (by rw [hru .x22 (by simp [slotKeep]), r1 .x22 (by simp [dispKeep])])
      have rk : ∀ r ∈ slotKeep, r ≠ .x10 → r ≠ .x24 → (Legacy.Riscv.writeHash u ans).getReg r = m.getReg r := by
        intro r hr _ h24'
        rw [writeHash_getReg, hru r hr, r1 r (slot_disp r hr h24')]
      refine ⟨hfbu.hash ans _ hdst dsafe davoid dlt, ⟨2, by decide, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hroots, ?_, ?_, ?_, ?_, ?_⟩
      · rw [writeHash_pc, hu.pc rfl]
        show pcOf (entry0PcT (tselJ j) (segX (tselJ j) b) + 1) + 4 = pcOf (tailPcT (tselJ j) (segX (tselJ j) b) 2)
        rw [pcOf_add4]; unfold entry0PcT tailPcT tailPc; rw [if_pos rfl]; all_goals (congr 1; omega)
      · rw [writeHash_getReg]
        have := hu.regs (.x14, a4E 8) (by simp); simp only at this
        rw [this, a4E_eval u1 _ 8 e14]; congr 1; unfold WIT; omega
      · rw [rk .x15 (by simp [slotKeep]) (by decide) (by decide)]; exact h.a5
      · rw [rk .x23 (by simp [slotKeep]) (by decide) (by decide)]; exact h.s7
      · rw [writeHash_getReg, hru .x24 (by simp [slotKeep])]; exact h24
      · rw [rk .x25 (by simp [slotKeep]) (by decide) (by decide)]; exact h.s9
      · exact (h.stack.transport hmu).hash (by omega) ans _ hdst dlt dstack
      · exact (h.rts.transport hmu).hash (by rw [h.hroots]; omega) ans _ hdst dlt (fun k hk => droots k (by rw [h.hroots] at hk; exact hk))
      · exact DigAt.writeHash_lo u ans _ hdst dlt
      · have hw := (h.wit.transport hmu)
        intro jj h1 h2
        rw [writeHash_frame u ans _ _ hdst (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT at *; omega))]
        exact hw jj h1 (by rcases h2 with h2 | h2 | h2 <;> [exact Or.inl h2; exact Or.inr (Or.inl h2); exact Or.inr (Or.inr (by omega))])
      · exact ⟨hc7, h.bnd.hj, hd2.1, hd2.2, folds, 0, by simpa using h.bnd, by omega, rfl⟩
      · exact ⟨hX, fun hP => by have := segX_P j b hP; have := h.bnd.hj; omega, segX_F j b⟩
      · exact h.hE
    · have hpar' : segT b = E % 2 := by rcases hpar with h0 | h0 <;> [exact absurd h0 ha0; exact h0]
      have ha1 : 0 < segA b := by omega
      obtain ⟨u, hu⟩ := spec_run (cOk ha1 ha) u1 hpc1 hk1
        (by intro br hbr; simp only [List.mem_singleton] at hbr; subst hbr
            exact (parBr_holds e23 _ ht2 false).mpr (by simp; omega)) (by simp)
      obtain ⟨hmu, hku, hgu, hru⟩ := common _ [] u hu rfl
      have hdst : u.getReg .x12 = BitVec.ofNat 64 (WIT + fblk ptr 0 + 48 * (E % 2)) := by
        have := hu.regs (.x12, a4E (888 + 48 * segT b)) (by simp); simp only at this
        rw [this, a4E_eval u1 _ _ e14, hpar']; congr 1; unfold fblk WIT; omega
      have hdlt : WIT + fblk ptr 0 + 48 * (E % 2) + 32 ≤ 2 ^ 24 := by unfold fblk WIT; omega
      have hd8 : (WIT + fblk ptr 0 + 48 * (E % 2)) % 8 = 0 := by unfold fblk WIT; omega
      obtain ⟨h5, hv, hin⟩ := atEcall u _ hmu hku hgu hru hdst hd8 hdlt
      refine ⟨u, (hst1.trans hu.steps).of_eq (by unfold segPre; rfl) (by unfold segPre; rfl),
        hu.ecall rfl, h5, hv, hin, fun ans => ⟨fun h0 => absurd h0 ha0, fun _ => ?_⟩⟩
      -- after the hash: `j lad`
      set u3 := Legacy.Riscv.writeHash u ans
      have hk3 : KnownOK gkF u3 := hku.writeHash ans
      have hpc3 : u3.pc = pcOf (slotPc (tselJ j) b + 4) := by
        rw [writeHash_pc, hu.pc rfl, pcOf_add4]
      obtain ⟨v, hv⟩ := spec_run (show specB [] [] gkF (runAt gkF [ladPcT (tselJ j) (segX (tselJ j) b) (segT b) (11 - segA b)]
          (slotPc (tselJ j) b + 4) []) ⟨[], [], ladPcT (tselJ j) (segX (tselJ j) b) (segT b) (11 - segA b), false, 1, [], none, 1⟩
          [] gkF [.x10, .x12, .x14, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28] = true from by
          have := entCheck1_at (tselJ j) b htb hb256
          unfold entCheck1 at this
          simp only [Bool.or_eq_true, decide_eq_true_eq] at this
          rcases this with (h0 | h0) | h0
          · exact absurd h0 ha0
          · omega
          · exact h0) u3 hpc3 hk3 (by simp) (by simp)
      have hmv : ∀ A, v.getMem A = u3.getMem A := fun A => by rw [hv.mem]; rfl
      have rvK : ∀ r ∈ ([.x10, .x12, .x14, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28] : List Reg),
          v.getReg r = u3.getReg r := hv.keep
      have rk : ∀ r ∈ slotKeep, r ≠ .x10 → r ≠ .x24 → v.getReg r = m.getReg r := by
        intro r hr _ h24'
        rw [rvK r (slot_ent r hr), writeHash_getReg, hru r hr, r1 r (slot_disp r hr h24')]
      have hfbu : FB F c u := h.fb.transport hgu hmu (by rw [hru .x27 (by simp [slotKeep]), r1 .x27 (by simp [dispKeep])])
        (by rw [hru .x28 (by simp [slotKeep]), r1 .x28 (by simp [dispKeep])])
        (by rw [hru .x22 (by simp [slotKeep]), r1 .x22 (by simp [dispKeep])])
      have hav : FBAvoid (WIT + fblk ptr 0 + 48 * (E % 2)) := by
        refine ⟨Or.inr ?_, Or.inr ?_, fun dd h1 h2 => Or.inr ?_⟩
        · unfold fblk WIT; omega
        · unfold fblk SENTINEL WIT; omega
        · unfold fblk frameA WIT; omega
      have hfb3 : FB F c u3 := hfbu.hash ans _ hdst (safeDest_hi _ (by unfold fblk WLO WIT; omega) hd8
        (by unfold fblk WIT; omega))
        hav (by omega)
      have hfbv : FB F c v := hfb3.transport (hv.glob _ _ _ hfb3.glob (RelOK.nil u3)) hmv
        (rvK .x27 (by simp)) (rvK .x28 (by simp)) (rvK .x22 (by simp))
      refine ⟨v, hv.steps, hfbv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hroots, ?_, ?_, h.bnd, ⟨rfl, rfl⟩, ⟨ha1, ha⟩, h.hE⟩
      · rw [hv.pc rfl, hpar']; simp
      · rw [rvK .x14 (by simp), writeHash_getReg]
        have := hu.regs (.x14, a4E (8 + 80 * segA b)) (by simp); simp only at this
        rw [this, a4E_eval u1 _ _ e14]; congr 1; omega
      · rw [rk .x15 (by simp [slotKeep]) (by decide) (by decide)]; exact h.a5
      · rw [rk .x23 (by simp [slotKeep]) (by decide) (by decide)]; exact h.s7
      · rw [rvK .x24 (by simp), writeHash_getReg, hru .x24 (by simp [slotKeep])]; exact h24
      · rw [rk .x25 (by simp [slotKeep]) (by decide) (by decide)]; exact h.s9
      · have hav2 := wit_dest_avoid (WIT + fblk ptr 0 + 48 * (E % 2)) (by omega)
        exact (((h.stack.transport hmu).hash (by omega) ans _ hdst (by omega)
          (fun i hi => hav2.1 i (by omega)))).transport hmv
      · have hav2 := wit_dest_avoid (WIT + fblk ptr 0 + 48 * (E % 2)) (by omega)
        exact (((h.rts.transport hmu).hash (by rw [h.hroots]; omega) ans _ hdst (by omega)
          (fun k hk => hav2.2 k (by rw [h.hroots] at hk; omega)))).transport hmv
      · have := DigAt.writeHash_lo u ans _ hdst (by omega)
        exact ⟨(hmv _).trans this.1, (hmv _).trans this.2⟩
      · intro jj h1 h2
        have hA : WIT + 8 * jj + 8 ≤ WIT + fblk ptr 0 + 48 * (E % 2) ∨
            WIT + fblk ptr 0 + 48 * (E % 2) + 32 ≤ WIT + 8 * jj := by
          unfold fblk leafNT at h2; unfold fblk
          rcases Nat.mod_two_eq_zero_or_one E with he | he <;> rw [he] at h2 ⊢ <;> omega
        rw [hmv, writeHash_frame u ans _ _ hdst (by unfold WIT WX at *; omega) (by omega) hA, hmu]
        exact h.wit jj h1 (by
          rcases h2 with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (by unfold fblk at h2; omega)))

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## Rungs -/

theorem eHalf_eval (m : MachineState) (E : Nat) (h : m.getReg .x23 = FtsRev.rv E) (hE : E < 4096) :
    eHalf.eval m = FtsRev.rv (E / 2) := by
  show BinOp.eval .sll (m.getReg .x23) (BitVec.ofNat 64 1) = _
  rw [h]; exact FtsRev.rv_sll1 E (by omega)

theorem sideE_eval (m : MachineState) (E : Nat) (h : m.getReg .x23 = FtsRev.rv E) (hE : E < 4096) :
    sideE.eval m = FtsRev.rv (E / 2) := eHalf_eval m E h hE

theorem rungBr_holds (m : MachineState) (E t : Nat) (h : m.getReg .x23 = FtsRev.rv E) (hE : E < 4096)
    (ht : t = E % 2) : Br.holds m (rungBr t (E / 2 % 2)) := by
  have key : BitVec.slt (sideE.eval m) 0 = decide (E / 2 % 2 = 1) := by rw [sideE_eval m E h hE]; exact FtsRev.rv_slt _
  show CmpOp.eval (if t = 1 then .ge else .lt) (sideE.eval m) 0 = crossD t (E / 2 % 2)
  subst ht
  rcases Nat.mod_two_eq_zero_or_one E with he | he <;>
  rcases Nat.mod_two_eq_zero_or_one (E / 2) with h2 | h2 <;>
  simp only [CmpOp.eval, key, he, h2, crossD, if_true, if_false, show ((0 : Nat) = 1) = False by decide] <;> decide

theorem rungCheck1_at (tb X t r t' : Nat) (htb : tb < 2) (hX : X < 3) (ht : t < 2) (hr : r < 10) (ht' : t' < 2) :
    rungCheck1 tb X t r t' = true := by
  have h := rungCheck_ok
  simp only [rungCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h tb htb X hX t ht).2 r hr t' ht'

theorem lastCheck1_at (tb X t : Nat) (htb : tb < 2) (hX : X < 3) (ht : t < 2) : lastCheck1 tb X t = true := by
  have h := rungCheck_ok
  simp only [rungCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h tb htb X hX t ht).1

theorem rungObl_holds (m : MachineState) (A r : Nat) (h14 : m.getReg .x14 = BitVec.ofNat 64 A) (hA8 : A % 8 = 0)
    (hA : A + 80 * r + 32 ≤ 2 ^ 24) : ∀ o ∈ rungObl r, o.holds m := by
  intro o ho
  simp only [rungObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · simp only [Oblig.holds]; rw [a4A_eval m A _ h14]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  · simp only [Oblig.holds]; rw [a4A_eval m A _ h14]; exact accessValid_ofNat _ 8 (by omega) (by omega)

/-- The fold block's hash input: `[L | T(10, E/2) | pad | R]`, the node on its side. -/
def foldBlk (F : FCtx) (c ptr i E : Nat) (node : Digest) : List UInt8 :=
  if E % 2 = 1 then blk4 (wdig F.w (fblk ptr i)) (header 10 c F.idx 0 (E / 2)) (wdig F.w (fblk ptr i + 32)) node
  else blk4 node (header 10 c F.idx 0 (E / 2)) (wdig F.w (fblk ptr i + 32)) (wdig F.w (fblk ptr i + 48))

theorem foldStep_eq (F : FCtx) (c ptr i E : Nat) (node : Digest) :
    foldStep F.w F.idx c ptr (node, E) i =
      T3.shortHash (foldBlk F c ptr i E node) >>= fun v => pure (v, E / 2) := by
  unfold foldStep foldBlk
  simp only [foldBlock, fblk]
  split_ifs <;> rfl

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

theorem memEval_cons_rel (s : MachineState) (A0 off B : Nat) (v : E) (ws : SymMem)
    (h14 : s.getReg .x14 = BitVec.ofNat 64 A0) (hB : B < 2 ^ 64) (hA : A0 + off < 2 ^ 64) :
    memEval s ((a4A off, v) :: ws) (BitVec.ofNat 64 B) =
      if B = A0 + off then v.eval s else memEval s ws (BitVec.ofNat 64 B) := by
  rw [memEval_cons, a4A_eval s A0 off h14]
  by_cases hb : B = A0 + off
  · subst hb; simp
  · rw [if_neg (by rw [ofNat_eq_iff hB hA]; exact hb), if_neg hb]

/-- The memory after a rung's header stores. -/
theorem rung_mem (F : FCtx) (c X a i E ptr : Nat) (m u : MachineState) (r : Nat) (hr : r = 11 - a + i)
    (hia : i < a) (ha : a ≤ 11) (hp : ptr + 888 ≤ 32168)
    (h14 : m.getReg .x14 = BitVec.ofNat 64 (WIT + ptr - 880 + 8 + 80 * a)) (h1088 : 1088 ≤ ptr)
    (h22 : m.getReg .x22 = BitVec.ofNat 64 F.idx) (h23 : m.getReg .x23 = FtsRev.rv E) (hE : E < 4096)
    (h27 : m.getReg .x27 = BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx))
    (hmem : ∀ A, u.getMem A = memEval m (rungMem r) A) :
    ∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
      if B = WIT + fblk ptr i + 24 then FtsRev.rv (E / 2)
      else if B = WIT + fblk ptr i + 16 then BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) else m.getMem (BitVec.ofNat 64 B) := by
  intro B hB
  have e : WIT + ptr - 880 + 8 + 80 * a + (80 * r + 24) = WIT + fblk ptr i + 24 := by
    subst hr; unfold fblk WIT; omega
  have e' : WIT + ptr - 880 + 8 + 80 * a + (80 * r + 16) = WIT + fblk ptr i + 16 := by
    subst hr; unfold fblk WIT; omega
  rw [hmem, rungMem, memEval_cons_rel m _ _ B _ _ h14 hB (by unfold WIT; omega),
    memEval_cons_rel m _ _ B _ _ h14 hB (by unfold WIT; omega), memEval_nil, e, e']
  rw [eHalf_eval m E h23 hE]
  simp only [Rv.E.eval, h27]

theorem rung_hashInput (F : FCtx) (c ptr i E : Nat) (node : Digest) (u m : MachineState)
    (hc : c < 7) (hp : ptr + 888 ≤ 32168) (hi : i < 11) (h8 : ptr % 8 = 0)
    (h10 : u.getReg .x10 = BitVec.ofNat 64 (WIT + fblk ptr i)) (h11 : u.getReg .x11 = BitVec.ofNat 64 64)
    (hT0 : u.getMem (BitVec.ofNat 64 (WIT + fblk ptr i + 16)) = BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx))
    (hT1 : u.getMem (BitVec.ofNat 64 (WIT + fblk ptr i + 24)) = FtsRev.rv (E / 2))
    (hfr : ∀ k, k ≠ 16 → k ≠ 24 → k < 64 → u.getMem (BitVec.ofNat 64 (WIT + fblk ptr i + k)) =
      m.getMem (BitVec.ofNat 64 (WIT + fblk ptr i + k)))
    (hnd : DigAt m (WIT + fblk ptr i + 48 * (E % 2)) node)
    (hw : Orig F.w (fun o => o < 64 ∨ leafNT o ∨ fblk ptr i + 80 ≤ o ∨ o = fblk ptr i + 32 ∨ o = fblk ptr i + 40 ∨
      (E % 2 = 1 ∧ (o = fblk ptr i ∨ o = fblk ptr i + 8)) ∨ (E % 2 = 0 ∧ (o = fblk ptr i + 48 ∨ o = fblk ptr i + 56))) m)
    (hE : E < 4096) :
    hashInput u = toQ (T3.pad64 (foldBlk F c ptr i E node)) := by
  have hidx := F.idx_lt
  have hfb8 : fblk ptr i % 8 = 0 := by unfold fblk; omega
  have hlen : (foldBlk F c ptr i E node).length = 64 := by unfold foldBlk; split <;> exact blk4_length _ _ _ _
  rw [T3.pad64, hlen, show (64 - 64 % 64) % 64 = 0 by rfl, List.replicate_zero, List.append_nil]
  apply hashInput_words8 u _ _ hlen h10 (by unfold WIT; omega) (by unfold fblk WIT at *; omega) h11
  have dPad := hw.dig (fblk ptr i + 32) (by omega) (by unfold fblk WX; omega) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by ring))))))
  have f0 : u.getMem (BitVec.ofNat 64 (WIT + fblk ptr i)) = m.getMem (BitVec.ofNat 64 (WIT + fblk ptr i)) := by
    have := hfr 0 (by decide) (by decide) (by decide); simpa using this
  have f8 := hfr 8 (by decide) (by decide) (by decide)
  have f32 := hfr 32 (by decide) (by decide) (by decide)
  have f40 := hfr 40 (by decide) (by decide) (by decide)
  have f48 := hfr 48 (by decide) (by decide) (by decide)
  have f56 := hfr 56 (by decide) (by decide) (by decide)
  rw [f0, f8, hT0, hT1, f32, f40, f48, f56]
  rw [show WIT + fblk ptr i + 32 = WIT + (fblk ptr i + 32) by ring, dPad.1,
    show WIT + fblk ptr i + 40 = WIT + (fblk ptr i + 32) + 8 by ring, dPad.2]
  unfold foldBlk
  rcases Nat.mod_two_eq_zero_or_one E with he | he
  · rw [he] at hnd hw ⊢
    rw [if_neg (by omega), wordsOf_blk4]
    simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_node c F.idx (by omega) (by omega)]
    rw [nw10_rv (E / 2) (by omega)]
    have dSib := hw.dig (fblk ptr i + 48) (by omega) (by unfold fblk WX; omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩))))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (by ring)⟩))))))
    simp only [Nat.mul_zero, Nat.add_zero] at hnd
    rw [hnd.1, hnd.2, show WIT + fblk ptr i + 48 = WIT + (fblk ptr i + 48) by ring, dSib.1,
      show WIT + fblk ptr i + 56 = WIT + (fblk ptr i + 48) + 8 by ring, dSib.2]
  · rw [he] at hnd hw ⊢
    rw [if_pos rfl, wordsOf_blk4]
    simp only [dlo, dhi, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_node c F.idx (by omega) (by omega)]
    rw [nw10_rv (E / 2) (by omega)]
    have dSib := hw.dig (fblk ptr i) (by omega) (by unfold fblk WX; omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))))))
    simp only [Nat.mul_one] at hnd
    rw [dSib.1, dSib.2, show WIT + fblk ptr i + 56 = WIT + fblk ptr i + 48 + 8 by ring, hnd.1, hnd.2]

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

def rungSteps (i a : Nat) : Nat := if i + 1 < a then 6 else 5

/-- The rung predicate of the next fold: its words are not the current block's header words, and are original
for the current fold. -/
theorem rung_next (ptr i t o : Nat) (ht : t < 2)
    (h2 : o < 64 ∨ leafNT o ∨ fblk ptr (i + 1) + 80 ≤ o ∨ o = fblk ptr (i + 1) + 32 ∨ o = fblk ptr (i + 1) + 40 ∨
      (t = 1 ∧ (o = fblk ptr (i + 1) ∨ o = fblk ptr (i + 1) + 8)) ∨
      (t = 0 ∧ (o = fblk ptr (i + 1) + 48 ∨ o = fblk ptr (i + 1) + 56))) (hp : 1088 ≤ ptr) :
    o ≠ fblk ptr i + 16 ∧ o ≠ fblk ptr i + 24 ∧ (o < 64 ∨ leafNT o ∨ fblk ptr i + 80 ≤ o) := by
  unfold leafNT fblk at *
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> omega

theorem tail_next (ptr i a o : Nat) (hia : i + 1 = a) (hp : 1088 ≤ ptr)
    (h2 : o < 64 ∨ leafNT o ∨ ptr + 8 + 80 * a ≤ o) :
    o ≠ fblk ptr i + 16 ∧ o ≠ fblk ptr i + 24 ∧ (o < 64 ∨ leafNT o ∨ fblk ptr i + 80 ≤ o) := by
  unfold leafNT fblk at *
  omega

/-- The words of the rung predicate avoid the 32 bytes written at the block's current slot. -/
theorem rung_dest_avoid (ptr i t o : Nat) (ht : t < 2) (hp : 1088 ≤ ptr)
    (h2 : o < 64 ∨ leafNT o ∨ fblk ptr i + 80 ≤ o ∨ o = fblk ptr i + 32 ∨ o = fblk ptr i + 40 ∨
      (t = 1 ∧ (o = fblk ptr i ∨ o = fblk ptr i + 8)) ∨ (t = 0 ∧ (o = fblk ptr i + 48 ∨ o = fblk ptr i + 56))) :
    WIT + o + 8 ≤ WIT + fblk ptr i + 48 * t ∨ WIT + fblk ptr i + 48 * t + 32 ≤ WIT + o := by
  unfold leafNT fblk at *
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> omega

theorem rung_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (X a i E ptr folds : Nat)
    (node : Digest) (m : MachineState) (h : RungIn F c j roots stk X a i E ptr folds node m) :
    ∃ u, Steps image m (rungSteps i a) (rungSteps i a) u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧ hashInput u = toQ (T3.pad64 (foldBlk F c ptr i E node)) ∧
      ∀ ans : BitVec 256,
        (i + 1 < a → RungIn F c j roots stk X a (i + 1) (E / 2) ptr folds (ans.extractLsb' 0 128)
          (Legacy.Riscv.writeHash u ans)) ∧
        (i + 1 = a → TailIn F c j roots stk X (E / 2) (ptr + 8 + 80 * a) (folds + a) (ans.extractLsb' 0 128)
          (Legacy.Riscv.writeHash u ans)) := by
  obtain ⟨hp1088, hp8, hpmax⟩ := h.bnd.ptr_lt
  obtain ⟨hia, ha11⟩ := h.hi
  have hc7 := h.fb.hc
  have hd2 := h.bnd.hd
  have hE := h.hE
  have hX3 : X < 3 := by rw [h.hX.1]; exact segX_lt _ _
  obtain ⟨A, hAdef⟩ : ∃ A, A = WIT + ptr - 880 + 8 + 80 * a := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = 11 - a + i := ⟨_, rfl⟩
  have h14 : m.getReg .x14 = BitVec.ofNat 64 A := by rw [hAdef]; exact h.a4
  have hA8 : A % 8 = 0 := by unfold WIT at hAdef; omega
  have hAr : A + 80 * r = WIT + fblk ptr i := by unfold fblk WIT at *; omega
  have hk : KnownOK gkF m := h.fb.glob.1
  have h27 : m.getReg .x27 = BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) := by
    have := h.fb.ck (.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) F.idx)) (by simp [packedCK]); rw [this]; rfl
  have ht2 : E % 2 < 2 := Nat.mod_lt _ (by decide)
  have ht2' : E / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hrel : RelOK [.x14] m := by
    intro rr hrr
    simp only [List.mem_singleton] at hrr; subst hrr
    rw [h14, toNat_ofNat_lt (by unfold WIT at hAdef; omega)]
    exact ⟨by unfold WLO WIT at *; omega, by unfold WIT at hAdef; omega⟩
  have hob : ∀ rr, rr ≤ 10 → ∀ o ∈ rungObl rr, o.holds m := fun rr hrr =>
    rungObl_holds m A rr h14 hA8 (by unfold WIT at hAdef; omega)
  -- the two kinds of run share their effect on memory and registers
  have post : ∀ (sp : Spec) (u : MachineState), SpecRes [] [.x14] gkF sp gkF rungKeep m u → sp.mem = rungMem r →
      (∀ p ∈ sp.regs, u.getReg p.1 = p.2.eval m) → (.x10, a4E (80 * r)) ∈ sp.regs → (.x23, eHalf) ∈ sp.regs →
      FB F c u ∧ u.getReg .x10 = BitVec.ofNat 64 (WIT + fblk ptr i) ∧ u.getReg .x23 = FtsRev.rv (E / 2) ∧
      (∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
        if B = WIT + fblk ptr i + 24 then FtsRev.rv (E / 2)
        else if B = WIT + fblk ptr i + 16 then BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) else m.getMem (BitVec.ofNat 64 B)) := by
    intro sp u hu hsm hreg h10m h23m
    have hmem := rung_mem F c X a i E ptr m u r hrdef hia ha11 hpmax h.a4 hp1088 h.fb.idx h.s7 hE h27
      (fun B => by rw [hu.mem, hsm])
    have hlo : ∀ B, B < WIT → u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) := by
      intro B hB; rw [hmem B (by unfold WIT at hB; omega), if_neg (by unfold fblk at *; omega),
        if_neg (by unfold fblk at *; omega)]
    refine ⟨⟨hu.glob _ _ _ h.fb.glob hrel, fun p hp => ?_, ?_, fun s hs => ?_, ?_, fun dd h1 h2 => ?_, hc7⟩, ?_, ?_, hmem⟩
    · rw [hu.keep p.1 (by simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp [rungKeep])]
      exact h.fb.ck p hp
    · rw [hu.keep .x22 (by simp [rungKeep])]; exact h.fb.idx
    · rw [hmem _ (by unfold leafT WIT; omega), if_neg (by unfold leafT fblk; omega), if_neg (by unfold leafT fblk; omega)]
      exact h.fb.thdr s hs
    · rw [hlo _ (by unfold SENTINEL WIT; omega)]; exact h.fb.sent
    · rw [hlo _ (by unfold frameA WIT; omega), hlo _ (by unfold frameA WIT; omega)]; exact h.fb.fpad dd h1 h2
    · rw [hreg _ h10m, a4E_eval m _ _ h14, hAr]
    · rw [hreg _ h23m, eHalf_eval m E h.s7 hE]
  have hnd := h.nd
  by_cases hlast : i + 1 < a
  · -- an inner rung
    have hr10 : r < 10 := by omega
    obtain ⟨u, hu⟩ := spec_run (rungCheck1_at (tselJ j) X (E % 2) r (E / 2 % 2) (tselJ_lt j) hX3 ht2 hr10 ht2') m
      (by rw [h.pc, hrdef]) hk
      (by intro b hb; simp only [rungSpec, List.mem_singleton] at hb; subst hb
          exact rungBr_holds m E (E % 2) h.s7 hE rfl) (hob r (by omega))
    obtain ⟨hfbu, h10u, h23u, hmem⟩ := post _ u hu rfl hu.regs (by simp [rungSpec]) (by simp [rungSpec])
    have h12u : u.getReg .x12 = BitVec.ofNat 64 (WIT + fblk ptr (i + 1) + 48 * (E / 2 % 2)) := by
      rw [hu.regs (.x12, a4E (80 * (r + 1) + 48 * (E / 2 % 2))) (by simp [rungSpec]), a4E_eval m _ _ h14]
      congr 1; unfold fblk WIT at *; omega
    have hdlt : WIT + fblk ptr (i + 1) + 48 * (E / 2 % 2) + 32 ≤ 2 ^ 24 := by unfold fblk WIT; omega
    have hd8 : (WIT + fblk ptr (i + 1) + 48 * (E / 2 % 2)) % 8 = 0 := by unfold fblk WIT; omega
    refine ⟨u, by rw [show rungSteps i a = 6 by unfold rungSteps; rw [if_pos hlast]]; exact hu.steps, hu.ecall rfl,
      hu.known (.x5, 0) (by simp [gkF, baseK]),
      hashArgs_of u _ 64 _ h10u (hu.known (.x11, 64) (by simp [gkF])) h12u (by unfold fblk WIT; omega) (by decide)
        (by unfold fblk WIT; omega) hd8 hdlt, ?_, fun ans => ⟨fun _ => ?_, fun he => absurd he (by omega)⟩⟩
    · exact rung_hashInput F c ptr i E node u m hc7 hpmax (by omega) hp8 h10u (hu.known (.x11, 64) (by simp [gkF]))
        (by rw [hmem _ (by unfold fblk WIT; omega), if_neg (by omega), if_pos rfl])
        (by rw [hmem _ (by unfold fblk WIT; omega), if_pos rfl])
        (fun k hk16 hk24 hk64 => by rw [hmem _ (by unfold fblk WIT; omega), if_neg (by omega), if_neg (by omega)])
        hnd h.wit hE
    · set u3 := Legacy.Riscv.writeHash u ans
      have hav : FBAvoid (WIT + fblk ptr (i + 1) + 48 * (E / 2 % 2)) := by
        refine ⟨Or.inr ?_, Or.inr ?_, fun dd h1 h2 => Or.inr ?_⟩
        · unfold fblk WIT; omega
        · unfold fblk SENTINEL WIT; omega
        · unfold fblk frameA WIT; omega
      have hav2 := wit_dest_avoid (WIT + fblk ptr (i + 1) + 48 * (E / 2 % 2)) (by omega)
      have hlo : ∀ B, B < WIT → u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) := by
        intro B hB; rw [hmem B (by unfold WIT at hB; omega), if_neg (by unfold fblk at *; omega),
          if_neg (by unfold fblk at *; omega)]
      refine ⟨hfbu.hash ans _ h12u (safeDest_hi _ (by unfold fblk WLO WIT; omega) hd8 (by unfold fblk WIT; omega))
        hav (by omega), ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, h.hroots, ?_, ?_, h.bnd, h.hX, ⟨by omega, ha11⟩, by omega⟩
      · rw [writeHash_pc, hu.pc rfl]
        show pcOf (lbrPcT (tselJ j) X (E / 2 % 2) (r + 1) + 1) + 4 =
          pcOf (ladPcT (tselJ j) X (E / 2 % 2) (11 - a + (i + 1)))
        rw [pcOf_add4]; unfold lbrPcT ladPcT lbrPc ladPc; congr 1; omega
      · rw [writeHash_getReg, hu.keep .x14 (by simp [rungKeep])]; exact h.a4
      · rw [writeHash_getReg, hu.keep .x15 (by simp [rungKeep])]; exact h.a5
      · rw [writeHash_getReg]; exact h23u
      · rw [writeHash_getReg, hu.keep .x24 (by simp [rungKeep])]; exact h.s8
      · rw [writeHash_getReg, hu.keep .x25 (by simp [rungKeep])]; exact h.s9
      · exact (h.stack.frame (fun i' hi' => ⟨(hlo _ (by unfold frameA WIT; have := h.bnd.hd; omega)),
          (hlo _ (by unfold frameA WIT; have := h.bnd.hd; omega)), (hlo _ (by unfold frameA WIT; have := h.bnd.hd; omega))⟩)).hash
          (by omega) ans _ h12u (by omega) (fun i' hi' => hav2.1 i' (by omega))
      · exact (h.rts.frame (fun k hk => ⟨hlo _ (by rw [h.hroots] at hk; unfold forestSlot WIT; split <;> omega),
          hlo _ (by rw [h.hroots] at hk; unfold forestSlot WIT; split <;> omega)⟩)).hash
          (by rw [h.hroots]; omega) ans _ h12u (by omega) (fun k hk => hav2.2 k (by rw [h.hroots] at hk; omega))
      · exact DigAt.writeHash_lo u ans _ h12u (by omega)
      · intro jj h1 h2
        have hA := rung_dest_avoid ptr (i + 1) (E / 2 % 2) (8 * jj) ht2' hp1088 h2
        obtain ⟨n16, n24, hold⟩ := rung_next ptr i (E / 2 % 2) (8 * jj) ht2' h2 hp1088
        rw [writeHash_frame u ans _ _ h12u (by unfold WIT WX at *; omega) (by omega) hA,
          hmem _ (by unfold WIT WX at *; omega), if_neg (by omega), if_neg (by omega)]
        exact h.wit jj h1 (by
          rcases hold with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h2)))
  · -- the last rung
    have hia1 : i + 1 = a := by omega
    have hr10 : r = 10 := by omega
    obtain ⟨u, hu⟩ := spec_run (lastCheck1_at (tselJ j) X (E % 2) (tselJ_lt j) hX3 ht2) m (by rw [h.pc, ← hrdef, hr10]) hk
      (by simp [lastSpec]) (by rw [← hr10]; exact hob r (by omega))
    obtain ⟨hfbu, h10u, h23u, hmem⟩ := post _ u hu (by rw [hr10]; rfl) hu.regs
      (by rw [hr10]; simp [lastSpec]) (by simp [lastSpec])
    have hPd : X = 1 → stk.length < 2 := fun hP => by
      have := segX_P j _ (h.hX.1 ▸ hP); have := h.bnd.hj; omega
    obtain ⟨dsafe, davoid, dlt, dstack, droots, dlow⟩ := destA_props c X stk.length hc7 hX3 hd2.2 hPd
    have h12u : u.getReg .x12 = BitVec.ofNat 64 (destA c X stk.length) := by
      rw [hu.regs (.x12, destE X) (by simp [lastSpec])]
      exact destE_eval c X stk.length m h.a5 h.s9 hX3
    have hdest8 : destA c X stk.length % 8 = 0 := by unfold destA frameA forestSlot; split_ifs <;> omega
    refine ⟨u, by rw [show rungSteps i a = 5 by unfold rungSteps; rw [if_neg hlast]]; exact hu.steps, hu.ecall rfl,
      hu.known (.x5, 0) (by simp [gkF, baseK]),
      hashArgs_of u _ 64 _ h10u (hu.known (.x11, 64) (by simp [gkF])) h12u (by unfold fblk WIT; omega) (by decide)
        (by unfold fblk WIT; omega) hdest8 (by unfold WIT at dlow; omega), ?_,
      fun ans => ⟨fun h' => absurd h' (by omega), fun _ => ?_⟩⟩
    · exact rung_hashInput F c ptr i E node u m hc7 hpmax (by omega) hp8 h10u (hu.known (.x11, 64) (by simp [gkF]))
        (by rw [hmem _ (by unfold fblk WIT; omega), if_neg (by omega), if_pos rfl])
        (by rw [hmem _ (by unfold fblk WIT; omega), if_pos rfl])
        (fun k hk16 hk24 hk64 => by rw [hmem _ (by unfold fblk WIT; omega), if_neg (by omega), if_neg (by omega)])
        hnd h.wit hE
    · have hlo : ∀ B, B < WIT → u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) := by
        intro B hB; rw [hmem B (by unfold WIT at hB; omega), if_neg (by unfold fblk at *; omega),
          if_neg (by unfold fblk at *; omega)]
      refine ⟨hfbu.hash ans _ h12u dsafe davoid dlt, ⟨E % 2, by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hroots, ?_, ?_,
        ⟨hc7, h.bnd.hj, hd2.1, hd2.2, folds, a, by rw [show ptr + 8 + 80 * a - 8 - 80 * a = ptr by omega]; exact h.bnd,
          ha11, rfl⟩, ⟨hX3, fun hP => by have := segX_P j _ (h.hX.1 ▸ hP); have := h.bnd.hj; omega,
          fun hF => segX_F j _ (h.hX.1 ▸ hF)⟩, by omega⟩
      · rw [writeHash_pc, hu.pc rfl]
        show pcOf (ladPcT (tselJ j) X (E % 2) 10 + 5) + 4 = pcOf (tailPcT (tselJ j) X (E % 2))
        rw [pcOf_add4]; unfold ladPcT tailPcT tailPc; rw [if_neg (by omega)]; all_goals (congr 1; omega)
      · rw [writeHash_getReg, hu.keep .x14 (by simp [rungKeep]), h.a4]; congr 1; unfold WIT; omega
      · rw [writeHash_getReg, hu.keep .x15 (by simp [rungKeep])]; exact h.a5
      · rw [writeHash_getReg]; exact h23u
      · rw [writeHash_getReg, hu.keep .x24 (by simp [rungKeep])]; exact h.s8
      · rw [writeHash_getReg, hu.keep .x25 (by simp [rungKeep])]; exact h.s9
      · exact (h.stack.frame (fun i' hi' => ⟨(hlo _ (by unfold frameA WIT; omega)),
          (hlo _ (by unfold frameA WIT; omega)), (hlo _ (by unfold frameA WIT; omega))⟩)).hash
          (by omega) ans _ h12u dlt dstack
      · exact (h.rts.frame (fun k hk => ⟨hlo _ (by rw [h.hroots] at hk; unfold forestSlot WIT; split <;> omega),
          hlo _ (by rw [h.hroots] at hk; unfold forestSlot WIT; split <;> omega)⟩)).hash
          (by rw [h.hroots]; omega) ans _ h12u dlt (fun k hk => droots k (by rw [h.hroots] at hk; exact hk))
      · exact DigAt.writeHash_lo u ans _ h12u dlt
      · intro jj h1 h2
        obtain ⟨n16, n24, hold⟩ := tail_next ptr i a (8 * jj) hia1 hp1088 h2
        rw [writeHash_frame u ans _ _ h12u (by unfold WIT WX at *; omega) (by omega) (Or.inr (by unfold WIT at *; omega)),
          hmem _ (by unfold WIT WX at *; omega), if_neg (by omega), if_neg (by omega)]
        exact h.wit jj h1 (by
          rcases hold with h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h2)))

end SigGolfCandidate.T3M.Verify

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-! ## Tails -/

theorem tailMCheck1_at (tb c d : Nat) (htb : tb < 2) (hc : c < 3) (hd : d ≤ 2) : tailMCheck1 tb c d = true := by
  have h := tailCheck_ok
  simp only [tailCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h c hc
  rcases (show tb = 0 ∨ tb = 1 by omega) with rfl | rfl
  · rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  · rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
    · exact h3
    · exact h4
    · exact h5

theorem tailPCheck1_at (c d : Nat) (hc : c < 3) (hd : d ≤ 1) : tailPCheck1 c d = true := by
  have h := tailCheck_ok
  simp only [tailCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h0⟩, h1⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h c hc
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> assumption

theorem tailFCheck1_at (c : Nat) (hc : c < 3) : tailFCheck1 c = true := by
  have h := tailCheck_ok
  simp only [tailCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact (h c hc).1.1.1.1.1.1.1.1

theorem stack_top {stk : List (Digest × Nat)} {m : MachineState} {pn : Digest} {Q : Nat} {rest : List (Digest × Nat)}
    (h : StackOK stk m) (he : stk = (pn, Q) :: rest) :
    DigAt m (frameA stk.length) pn ∧ m.getMem (BitVec.ofNat 64 (frameA stk.length - 16)) = FtsRev.rv Q ∧
      Q < 4096 := by
  subst he
  have := h rest.length (by simp)
  simp only [List.reverse_cons, List.length_cons] at this ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self] at this
  simpa using this

theorem stack_rest {stk : List (Digest × Nat)} {m : MachineState} {e : Digest × Nat} {rest : List (Digest × Nat)}
    (h : StackOK stk m) (he : stk = e :: rest) : StackOK rest m := by
  subst he
  intro i hi
  have := h i (by simp; omega)
  simp only [List.reverse_cons] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi), ← List.getD_eq_getElem?_getD] at this
  exact this

theorem stack_push {stk : List (Digest × Nat)} {m : MachineState} (h : StackOK stk m) (n : Digest) (Q : Nat)
    (hn : DigAt m (frameA (stk.length + 1)) n)
    (hq : m.getMem (BitVec.ofNat 64 (frameA (stk.length + 1) - 16)) = FtsRev.rv Q) (hQ : Q < 4096) :
    StackOK ((n, Q) :: stk) m := by
  intro i hi
  simp only [List.length_cons] at hi
  simp only [List.reverse_cons]
  by_cases hil : i < stk.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hil), ← List.getD_eq_getElem?_getD]
    exact h i hil
  · have : i = stk.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self]
    exact ⟨hn, hq, hQ⟩

/-- The merge tail: the `Q` check, then the merge header in the popped frame and the next dispatch. -/
theorem tailM_step (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (E ptr folds : Nat)
    (node : Digest) (m : MachineState) (h : TailIn F c j roots stk 0 E ptr folds node m) :
    (stk = [] → ∃ u, Steps image m 5 5 u ∧ Halt1 u) ∧
    (∀ pn Q rest, stk = (pn, Q) :: rest → Q ≠ E → ∃ u, Steps image m 5 5 u ∧ Halt1 u) ∧
    (∀ pn rest, stk = (pn, E) :: rest → ∃ u, Steps image m 7 7 u ∧
      DispIn F c j roots rest (.merge (E / 2) pn) (E / 2) ptr folds node u) := by
  obtain ⟨k, hk, hpc⟩ := h.pc
  obtain ⟨hc7, hj3, hdj, hd2, folds0, a0, hb0, ha0, hf0⟩ := h.bnd
  have hE := h.hE
  have hkn : KnownOK (ka5 stk.length) m := by
    intro p hp
    simp only [ka5, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h.fb.glob.1 p hp
    · exact h.a5
  have tM := tailMCheck1_at (tselJ j) k stk.length (tselJ_lt j) hk hd2
  unfold tailMCheck1 at tM
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at tM
  obtain ⟨tPass, tRej⟩ := tM
  have qrej : (m.getMem (BitVec.ofNat 64 (frameA stk.length - 16)) ≠ FtsRev.rv E) →
      ∃ u, Steps image m 5 5 u ∧ Halt1 u := by
    intro hne
    obtain ⟨u, hu⟩ := spec_run tRej m hpc hkn (by
      intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
      simp only [Br.holds, qBr, CmpOp.eval, Rv.E.eval, h.s7, cw]
      simpa using hne) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  refine ⟨fun hnil => qrej ?_, fun pn Q rest he hQ => qrej ?_, fun pn rest he => ?_⟩
  · rw [hnil, show frameA ([] : List (Digest × Nat)).length - 16 = SENTINEL by rfl, h.fb.sent]
    intro heq
    exact FtsRev.rv_ne_neg1 E hE heq.symm
  · obtain ⟨-, hq, hQ4⟩ := stack_top h.stack he
    rw [hq]; exact fun heq => hQ ((FtsRev.rv_inj (by omega) (by omega)).mp heq)
  · obtain ⟨hpn, hq, -⟩ := stack_top h.stack he
    have hd1 : stk.length = rest.length + 1 := by rw [he]; rfl
    obtain ⟨u, hu⟩ := spec_run (tPass.resolve_left (by omega)) m hpc hkn (by
      intro b hb; simp only [tailMSpec, List.mem_singleton] at hb; subst hb
      simp only [Br.holds, qBr, CmpOp.eval, Rv.E.eval, h.s7, hq, cw]; simp) (by simp)
    have e27 : Rv.E.eval m (.reg .x27) = BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) := by
      show m.getReg .x27 = _
      have := h.fb.ck (.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) F.idx)) (by simp [packedCK]); rw [this]; rfl
    have e24 : eHalf.eval m = FtsRev.rv (E / 2) := eHalf_eval m E h.s7 hE
    have hmem : ∀ B, B < 2 ^ 64 → u.getMem (BitVec.ofNat 64 B) =
        if B = frameA stk.length + 24 then FtsRev.rv (E / 2)
        else if B = frameA stk.length + 16 then BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) else m.getMem (BitVec.ofNat 64 B) := by
      intro B hB
      rw [hu.mem]; simp only [tailMSpec]
      rw [memEval_cons_ofNat _ _ _ _ _ hB (by unfold frameA; omega), memEval_cons_ofNat _ _ _ _ _ hB (by unfold frameA; omega),
        memEval_nil, e24, e27]
    have hfr : ∀ B, B < 2 ^ 64 → B ≠ frameA stk.length + 16 → B ≠ frameA stk.length + 24 →
        u.getMem (BitVec.ofNat 64 B) = m.getMem (BitVec.ofNat 64 B) :=
      fun B hB h1 h2 => by rw [hmem B hB, if_neg h2, if_neg h1]
    have hk' : KnownOK (ka5 (stk.length - 1)) u := hu.known
    have hfb : FB F c u := by
      refine ⟨hu.glob _ _ _ h.fb.glob (RelOK.nil m), fun p hp => ?_, ?_, fun s hs => ?_, ?_, fun dd h1 h2 => ?_, hc7⟩
      · rw [hu.keep p.1 (by simp only [packedCK, List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> simp)]
        exact h.fb.ck p hp
      · rw [hu.keep .x22 (by simp)]; exact h.fb.idx
      · rw [hfr _ (by unfold leafT WIT; omega) (by unfold leafT frameA WIT; omega) (by unfold leafT frameA WIT; omega)]
        exact h.fb.thdr s hs
      · rw [hfr _ (by unfold SENTINEL; omega) (by unfold SENTINEL frameA; omega) (by unfold SENTINEL frameA; omega)]
        exact h.fb.sent
      · rw [hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega),
          hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)]
        exact h.fb.fpad dd h1 h2
    have hpcu : u.pc = pcOf (mDispPcT (tselJ j) k) := by rw [hu.pc rfl]; rfl
    have h24 : u.getReg .x24 = BitVec.ofNat 64 (lnk c j) := by rw [hu.keep .x24 (by simp)]; exact h.s8
    refine ⟨u, hu.steps, ⟨hfb, Or.inr ⟨rfl, k, hk, hpcu, h24⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.hroots, ?_, ?_,
      Nat.lt_of_le_of_lt (Nat.div_le_self E 2) hE, fun hl => by cases hl⟩⟩
    · rw [hu.keep .x14 (by simp)]; exact h.a4
    · have := hk' (.x15, BitVec.ofNat 64 (frameA (stk.length - 1))) (by simp [ka5]); rw [this, hd1, Nat.add_sub_cancel]
    · have := hu.regs (.x23, eHalf) (by simp [tailMSpec]); simp only at this
      rw [this, eHalf_eval m E h.s7 hE]
    · rw [hu.keep .x25 (by simp)]; exact h.s9
    · refine (stack_rest h.stack he).frame (fun i hi => ⟨?_, ?_, ?_⟩) <;>
        exact hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)
    · refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · have := hu.regs (.x10, cw (frameA stk.length)) (by simp [tailMSpec]); simp only at this
        rw [this, ← hd1]; rfl
      · rw [← hd1]
        exact ⟨(hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)).trans hpn.1,
          (hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)).trans hpn.2⟩
      · rw [← hd1, hmem _ (by unfold frameA; omega), if_neg (by omega), if_pos rfl]
      · rw [← hd1, hmem _ (by unfold frameA; omega), if_pos rfl]
      · rw [← hd1]
        have hn := h.nd
        simp only [destA, if_true] at hn
        exact ⟨(hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)).trans hn.1,
          (hfr _ (by unfold frameA; omega) (by unfold frameA; omega) (by unfold frameA; omega)).trans hn.2⟩
    · have hr := h.hroots
      exact h.rts.frame (fun k' hkr => ⟨hfr (forestSlot k') (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot frameA; split <;> omega) (by unfold forestSlot frameA; split <;> omega),
        hfr (forestSlot k' + 8) (by unfold forestSlot; split <;> omega)
        (by unfold forestSlot frameA; split <;> omega) (by unfold forestSlot frameA; split <;> omega)⟩)
    · intro jj h1 h2
      rw [hfr _ (by unfold WIT WX at *; omega) (by unfold frameA WIT; omega) (by unfold frameA WIT; omega)]
      exact h.wit jj h1 h2
    · refine ⟨hc7, hj3, ⟨by omega, by omega⟩, ?_, ?_⟩
      · have := hb0.hptr; unfold segsDone at *; omega
      · have := hb0.hf; have := hb0.hptr; unfold segsDone at *; omega

end SigGolfCandidate.T3M.Verify
