import SigGolfCandidate.Verify.LayerSem
import SigGolfCandidate.Verify.FoldCheck
import SigGolfCandidate.Verify.FoldSem
import SigGolfCandidate.Verify.ChainGood
set_option Elab.async false

/-! # The OTS leaf hash of a layer (at the return of the chain code), into its fold region -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem flat_get? (f g : Val → Word) : ∀ (vs : List Val) (m : Nat), m < 2 * vs.length →
    ((vs.map fun v => [f v, g v]).flatten)[m]? =
      some (if m % 2 = 0 then f (vs.getD (m / 2) []) else g (vs.getD (m / 2) [])) := by
  intro vs
  induction vs with
  | nil => intro m h; simp at h
  | cons v vs ih =>
    intro m h
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
    rcases m with _ | _ | m
    · simp
    · simp
    · simp only [List.getElem?_cons_succ]
      rw [ih m (by simp at h; omega)]
      congr 1
      rw [show (m + 1 + 1) / 2 = m / 2 + 1 by omega, List.getD_cons_succ,
        show (m + 1 + 1) % 2 = m % 2 by omega]

theorem length_flat (f g : Val → Word) (vs : List Val) :
    ((vs.map fun v => [f v, g v]).flatten).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.flatten_cons] at ih ⊢; omega

/-- The fold context of layer `L`: tag 3, the layer's path and root destination. -/
def layFC (L : LCtx) : FCtx :=
  ⟨L.wl, L.pk, L.e, heightL L.lay, L.lay, 3, L.lay, L.tau, pathOffL L.lay, dstOf L.lay⟩

theorem layFC_ok (L : LCtx) (hL : L.ok) : (layFC L).ok := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hh := heightL_le L.lay hlay
  refine ⟨?_, ?_, ?_, by simp [layFC], ?_, hwl, ?_, ?_, ?_, ?_, hlay, rfl, rfl, rfl⟩ <;> simp only [layFC]
  · omega
  · omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · omega
  · interval_cases L.lay <;> decide
  · interval_cases L.lay <;> decide
  · unfold dstOf; split <;> decide
  · unfold dstOf; split <;> omega

theorem layFC_check (L : LCtx) (hL : L.ok) :
    ∀ ci, ci < nCh (layFC L).lay → ∀ v, v < 2 ^ chBits (layFC L).lay ci → blockCheck (layFC L).lay ci v = true :=
  blockCheck_at L.lay hL.1

/-- Carried through the leaf and the fold of layer `lay` to the transition of layer `lay - 1`:
the table base `0x29000` in `x27`, `tau`, the CB word, and the chain array of the layers `< lay` still
the witness. -/
def LeafCarry (L : LCtx) (s : MachineState) : Prop :=
  s.getReg .x27 = 0x29000#64 ∧ s.getReg .x30 = BitVec.ofNat 64 (if L.lay = 0 then L.e else L.tau) ∧
  CB0 L.lay s ∧ Fresh L.wl L.lay 42 s ∧ s.getReg .x22 = BitVec.ofNat 64 (s6N L.lay) ∧ EncHeader L.lay s

/-- The leaf tweak word 0 with byte 1 (the tag 2) replaced by 3: the node tweak word 0. -/
theorem leaf_nb0 (lay : Nat) (hl : lay < 5) :
    StoreKind.merge .b (BitVec.ofNat 64 (Ref.LeafCarry.leafHeader lay))
      (if lay < 4 then 2 else 1) (BitVec.ofNat 64 (if lay < 4 then lay else 3)) =
      BitVec.ofNat 64 (1 + 256 * 3 + 65536 * lay) := by
  interval_cases lay <;> decide +kernel

/-- After the return of the chain code. -/
theorem chainNext_42 {c : CCtx} {acc : List Val} {s : MachineState} (h : ChainNext c 42 acc s) :
    ChBase c 42 acc s ∧ Fresh c.wl c.lay 42 s ∧ s.pc = c.ret := by
  unfold ChainNext at h; rwa [if_neg (by omega)] at h

def leafEntrySpec (lay : Nat) : Spec :=
  { specLeaf lay with steps := leafSteps lay, cycles := leafSteps lay, spc := some (dispTgt lay 0) }

set_option maxHeartbeats 0 in
theorem topDispVal_tab : ∀ E, E < 2048 →
    (((BitVec.ofNat 64 (4095 - E) <<< 3) + BitVec.ofNat 64 779264) &&& ~~~1#64) =
      pcOf (topSlotPc E) := by decide +kernel

theorem leaf_dispatch_run (lay t E : Nat) (hlay : lay < 5) (ht : t < nCopy lay)
    (hE : E < 2 ^ heightL lay) (s : MachineState) (hpc : s.pc = pcOf (retPc lay t))
    (hK : KnownOK (leafK lay) s) (h23 : s.getReg .x23 = BitVec.ofNat 64 (heapU lay E)) :
    ∃ u, SpecRes gkL (leafEntrySpec lay) (leafPost lay) leafKeep s u ∧
      (lay = 0 → u.getReg .x16 = pcOf (topSlotPc E + 1)) := by
  obtain ⟨u0, hu⟩ := spec_run (lc_leaf hlay ht) s hpc hK (by simp [specLeaf])
  by_cases h0 : lay = 0
  · subst lay
    have he : E < 2048 := by simpa [heightL] using hE
    have hpSlot : u0.pc = pcOf (topSlotPc E) := by
      rw [hu.spc topDispTgt (by simp [specLeaf])]
      have hv := topDispVal_tab E he
      simpa [topDispTgt, mkBin_eval, mkAdd_eval, BinOp.eval, Rv.E.eval, cw, h23, heightL, heapU] using hv
    have hkSlot : KnownOK (foldK 0 704) u0 := by
      intro p hp
      apply hu.known p
      simp only [foldK, fk, gkOf, leafPost, s6N_eq, List.mem_append, List.mem_singleton] at hp ⊢
      aesop
    obtain ⟨u, hs⟩ := slotEnter_run E he u0 hpSlot hkSlot
    refine ⟨u, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [leafEntrySpec, specLeaf, leafRawSteps, leafSteps, slotEnterSpec] using hu.steps.trans hs.steps
      · intro hec; simp [leafEntrySpec, specLeaf] at hec
      · intro gk0 wl pk hg; exact hs.glob _ _ _ (hu.glob _ _ _ hg)
      · intro wl hw; exact hs.wall _ (hu.wall _ hw)
      · intro p hp
        simp only [leafPost, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with hp | hp | hp
        · exact hs.known p (by simpa [foldK, fk, gkOf] using List.mem_append_left [(.x22, BitVec.ofNat 64 (6336 + 2688 * 0))] hp)
        · subst hp
          rw [hs.keep .x27 (by simp [slotEnterKeep])]
          exact hu.known (.x27, 0x29000#64) (by simp [leafPost])
        · subst hp
          rw [s6N_eq]
          exact hs.known _ (by simp [foldK])
      · intro x hx
        exact (hs.keep x (by
          simp only [leafKeep, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl <;> simp [slotEnterKeep])).trans (hu.keep x hx)
      · intro p hp
        simp only [leafEntrySpec, specLeaf, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hs.known (.x10, BitVec.ofNat 64 832) (by simp [foldK, fk])
        · exact hs.known (.x11, BitVec.ofNat 64 704) (by simp [foldK, fk])
      · intro A
        rw [hs.mem A]; exact hu.mem A
      · intro hn; simp [leafEntrySpec] at hn
      · intro e heq
        simp only [leafEntrySpec, Option.some.injEq] at heq
        subst e
        rw [hs.pc rfl]
        simpa [slotEnterSpec, chB0, chBits] using
          (disp_eval 0 0 (by decide) (by decide) E hE s h23).symm
    · intro _
      have hr := hs.regs (.x16, cw (0x1000 + 4 * (topSlotPc E + 1))) (by simp [slotEnterSpec])
      simpa [cw, Rv.E.eval, pcOf] using hr
  · refine ⟨u0, ?_, fun h => (h0 h).elim⟩
    simpa [leafEntrySpec, specLeaf, leafRawSteps, leafSteps, h0] using hu

theorem leaf_step (L : LCtx) (hL : L.ok) (t : Nat) (ht : t < nCopy L.lay) (a : BitVec 256) (ends : List Val)
    (s : MachineState) (hs : ChainNext (L.cctx t a) 42 ends s) :
    ∃ u, Steps image s (leafSteps L.lay + 1) (leafSteps L.lay + 1) u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = addrFmt (leafInput L.lay L.tau L.e ends) ∧
      ∀ ans, FoldInv (layFC L) (writeHash u ans) 0 (answerBytes 16 ans) (writeHash u ans) ∧
        LeafCarry L (writeHash u ans) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB, hEH⟩, hF, hpc⟩ := chainNext_42 hs
  obtain ⟨h16, h17, h23, h30, h31⟩ := hR
  have hpc' : s.pc = pcOf (retPc L.lay t) := hpc
  have hKl : KnownOK (leafK L.lay) s := by
    intro p hp
    simp only [leafK, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp
    · exact hK p hp
    · subst hp; exact h27
    · subst hp; exact h22
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have hh := heightL_le L.lay hlay
  have hpw : 2 ^ heightL L.lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hh.2
  have heh : L.e < 2 ^ heightL L.lay := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨u1, hu, hlink⟩ := leaf_dispatch_run L.lay t L.e hlay ht heh s hpc' hKl h23
  -- the dispatch into block `e mod 2^bits` of chunk 0
  have hpc1 : u1.pc = pcOf (m4Pc L.lay 0 (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0) 0) := by
    rw [hu.spc _ rfl]
    have hn0 : 0 < nCh L.lay := by unfold nCh; split <;> decide
    exact disp_eval L.lay 0 hlay hn0 L.e heh s h23
  have hbits : 1 ≤ chBits L.lay 0 := by unfold chBits; split_ifs <;> omega
  have hvb2 : L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0 % 2 = L.e % 2 := by
    have := blk_bit L.e (chB0 L.lay 0) (chBits L.lay 0) 0 (by omega)
    simp only [pow_zero, Nat.div_one, Nat.add_zero] at this
    rw [this]; simp [chB0]
  have hc := blockCheck_at L.lay hlay 0 (by unfold nCh; split <;> decide)
    (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0) (Nat.mod_lt _ (Nat.two_pow_pos _))
  have e0 : lvlK L.lay (chB0 L.lay 0) = foldK L.lay 704 := by simp [lvlK, chB0]
  have hK1 : KnownOK (lvlK L.lay (chB0 L.lay 0)) u1 := by
    intro p hp
    rw [e0] at hp
    apply hu.known p
    simp only [foldK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact List.mem_append_left _ hp
    · simp [leafPost, s6N_eq]
  obtain ⟨u, hst2, hec2, hK2, hkeep2, hglob2, hmem2, hpc2⟩ :=
    blk_entry_run L.lay 0 (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0) hc u1 hpc1 hK1
  have hK2' := KnownOK_append.mp hK2
  rw [e0] at hK2'
  have hdv : 0x360 + 16 * (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0 % 2) = 0x360 + 16 * (L.e % 2) := by
    rw [hvb2]
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x340 := hK2'.1 (.x10, _) (by simp [foldK, fk])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (10 + 1)) := hK2'.1 (.x11, _) (by simp [foldK, fk])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * (L.e % 2)) := by
    rw [← hdv]; exact hK2'.2 _ (List.mem_singleton_self _)
  have hmem : ∀ A, u.getMem A = memEval s (leafEntrySpec L.lay).mem A := fun A => (hmem2 A).trans (hu.mem A)
  have hkp : ∀ x ∈ leafKeep, u.getReg x = s.getReg x := by
    intro x hx
    have hx' : x ∈ fkeep false := by
      simp only [leafKeep, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> simp [fkeep]
    exact (hkeep2 x hx').trans (hu.keep x hx)
  have h27u : u.getReg .x27 = 0x29000#64 := by
    rw [hkeep2 .x27 (by simp [fkeep])]
    exact hu.known (.x27, 0x29000#64) (by simp [leafPost])
  have h22u : u.getReg .x22 = BitVec.ofNat 64 (s6N L.lay) := by
    rw [s6N_eq]
    exact hK2'.1 (.x22, BitVec.ofNat 64 (6336 + 2688 * L.lay)) (by simp [foldK])
  have hm0 : u.getMem (BitVec.ofNat 64 832) = BitVec.ofNat 64 (Ref.LeafCarry.leafHeader L.lay) := by
    rw [hmem]
    by_cases h4 : L.lay < 4
    · simp only [leafEntrySpec, specLeaf, if_pos h4, List.append_nil]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne)]
      simpa only [Ref.LeafCarry.leafHeader, if_pos h4, memEval, LCtx.cctx] using hCB h4
    · have heq : L.lay = 4 := by omega
      simp only [leafEntrySpec, specLeaf, if_neg h4, List.cons_append, List.nil_append]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw, heq]
      rfl
  have hm1 : u.getMem (BitVec.ofNat 64 840) = s.getReg .x31 := by
    rw [hmem]
    simp only [leafEntrySpec, specLeaf, List.cons_append]
    rw [memEval_cons_eq _ _ _ _ _ rfl]
    rfl
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 840 → A ≠ 832 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      intro p hp
      by_cases h4 : L.lay < 4 <;>
        simp only [leafEntrySpec, specLeaf, h4, if_true, if_false, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false, false_or] at hp
      · rcases hp with rfl; simp; omega
      · rcases hp with rfl | rfl <;> simp <;> omega)]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hGu : Glob gkL L.wl L.pk u := hglob2 _ _ (hu.glob _ _ _ hG)
  refine ⟨u, hu.steps.trans hst2, hec2, hK2'.1 (.x5, 0) (by simp [foldK, fk, gkOf, gkL, gkL0, baseK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · have hends : ∀ v ∈ ends, v.length = 16 := hvs
    rw [hashInput_ofNat _ 0x340 10 h10 h11 (by decide) (by decide),
      addrFmt_leafInput_words _ _ _ _ (by rw [hlen]) hends]
    congr 1
    rw [show 8 * (10 + 1) = 4 + 84 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [hm0]
        have hw : (BitVec.ofNat 64 (twLo 4 L.lay L.tau 0)).toNat = 1025 + 65536 * L.lay := by
          simp only [BitVec.toNat_ofNat]; unfold twLo; omega
        rw [hw, Ref.LeafCarry.header_leaf L.lay hlay]
      · rw [hm1, h31]
        simp only [CCtx.x31, LCtx.cctx]; congr 1; unfold twHi; omega
      · rw [mfr 0x350 (by omega) (by omega) (by omega)]; exact hP _ (by decide)
      · rw [mfr 0x358 (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 84
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr _ (by omega) (by omega) (by omega)]
        obtain ⟨hl0, hl1⟩ := hLB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x340 + 8 * (4 + m) = 0x360 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x340 + 8 * (4 + m) = 0x368 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x360 + 16 * (L.e % 2) ∨ 0x360 + 16 * (L.e % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    have hbit : bitOf L.e 0 = L.e % 2 := by simp [bitOf]
    have hFresh : Fresh L.wl L.lay 42 (writeHash u ans) := by
      refine Fresh_frame hF (fun A hA hA' => ?_)
      rw [wf A hA (Or.inr (by omega)), mfr A hA (by omega) (by omega)]
    have hvA : (layFC L).vA 0 = 0x360 + 16 * (L.e % 2) := by
      rw [FCtx.vA_lt _ (layFC_ok L ⟨hlay, hidx, hwl⟩) 0 (by simp only [layFC]; omega)]
      simp only [layFC, hbit]
    refine ⟨⟨Glob_writeHash hGu ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one L.e with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, by simp, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_, hFresh, ?_, ?_⟩, ?_, ?_, ?_, hFresh, ?_, ?_⟩
    · have := Known_writeHash hK2'.1 ans
      simpa [lvlK, layFC] using this
    · rw [writeHash_getReg, hkp .x23 (by simp [leafKeep])]; exact h23
    · unfold NBhdr
      refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
      rw [wf 0x340 (by omega) (by omega), hm0]
      apply Eq.trans (leaf_nb0 L.lay hlay)
      congr 1; unfold FCtx.lo0; simp only [layFC]; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]
      omega
    · rw [wf 0x348 (by omega) (by omega), hm1, h31]
      simp only [CCtx.x31, LCtx.cctx, BitVec.toNat_ofNat, layFC]
      omega
    · rw [hvA, writeHash_at0 _ ans _ h12 (by omega)]; exact (vw0_answer ans).symm
    · rw [hvA, writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · have hc0 : chOf L.lay 0 = 0 := by simp [chOf]
      rw [writeHash_pc, hpc2, pcOf_add4]
      simp only [FCtx.X, FCtx.ci, FCtx.kk, FCtx.blk, layFC, hc0, Nat.zero_sub]
      try rfl
    · rw [hvA, writeHash_getReg]; exact h12
    · intro h0
      rw [writeHash_getReg, hkeep2 .x16 (by simp [fkeep])]
      exact hlink h0
    · rw [writeHash_getReg]; exact h27u
    · rw [writeHash_getReg, hkp .x30 (by simp [leafKeep])]; exact h30
    · intro h4
      rw [wf 0x340 (by omega) (by omega), hm0]
      simp only [Ref.LeafCarry.leafHeader, if_pos h4]
    · rw [writeHash_getReg]; exact h22u
    · unfold EncHeader
      rw [wf 0x100 (by omega) (Or.inl (by omega)), mfr 0x100 (by omega) (by omega) (by omega)]
      exact hEH

end SigGolfCandidate.Verify
