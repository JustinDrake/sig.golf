import SigGolfCandidate.Verify.LayerSem
import SigGolfCandidate.Verify.FoldCheck
import SigGolfCandidate.Verify.FoldSem
import SigGolfCandidate.Verify.ChainGood

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
the tweak word, `tau`, the CB word, and the chain array of the layers `< lay` still the witness. -/
def LeafCarry (L : LCtx) (s : MachineState) : Prop :=
  s.getReg .x27 = BitVec.ofNat 64 (hWord L.lay + 256) ∧ tauCarry L.lay s = BitVec.ofNat 64 L.tau ∧
  CB0 s ∧ Fresh L.wl L.lay 42 s

/-- After the return of the chain code. -/
theorem chainNext_42 {c : CCtx} {acc : List Val} {s : MachineState} (h : ChainNext c 42 acc s) :
    ChBase c 42 acc s ∧ Fresh c.wl c.lay 42 s ∧ s.pc = c.ret := by
  unfold ChainNext at h; rwa [if_neg (by omega)] at h

theorem leaf_step (L : LCtx) (hL : L.ok) (t : Nat) (ht : t < nCopy L.lay) (a : BitVec 256) (ends : List Val)
    (s : MachineState) (hs : ChainNext (L.cctx t a) 42 ends s) :
    ∃ u, Steps image s (leafSteps L.lay + 1) (leafSteps L.lay + 1) u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (leafInput L.lay L.tau L.e ends) ∧
      ∀ ans, FoldInv (layFC L) (writeHash u ans) 0 (answerBytes 16 ans) (writeHash u ans) ∧
        LeafCarry L (writeHash u ans) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩, hF, hpc⟩ := chainNext_42 hs
  obtain ⟨h16, h17, h23, h30, h31⟩ := hR
  have hpc' : s.pc = pcOf (retPc L.lay t) := hpc
  have hKl : KnownOK (leafK L.lay) s := by
    intro p hp
    simp only [leafK, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | hp
    · exact hK p hp
    · subst hp; exact h27
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have hh := heightL_le L.lay hlay
  have hpw : 2 ^ heightL L.lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hh.2
  have heh : L.e < 2 ^ heightL L.lay := Nat.mod_lt _ (Nat.two_pow_pos _)
  obtain ⟨u1, hu⟩ := spec_run (lc_leaf hlay ht) s hpc' hKl (by simp [specLeaf])
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
  have e0 : lvlK (chB0 L.lay 0) = fk false 0x340 704 := by simp [lvlK, chB0]
  have hK1 : KnownOK (lvlK (chB0 L.lay 0)) u1 := by
    intro p hp
    rw [e0] at hp
    exact hu.known p (List.mem_append_left _ hp)
  obtain ⟨u, hst2, hec2, hK2, hkeep2, hglob2, hmem2, hpc2⟩ :=
    blk_entry_run L.lay 0 (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0) hc u1 hpc1 hK1
  have hK2' := KnownOK_append.mp hK2
  rw [e0] at hK2'
  have hdv : 0x1E0 + 16 * (L.e / 2 ^ chB0 L.lay 0 % 2 ^ chBits L.lay 0 % 2) = 0x1E0 + 16 * (L.e % 2) := by
    rw [hvb2]
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x340 := hK2'.1 (.x10, _) (by simp [fk])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (10 + 1)) := hK2'.1 (.x11, _) (by simp [fk])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2)) := by
    rw [← hdv]; exact hK2'.2 _ (List.mem_singleton_self _)
  have hmem : ∀ A, u.getMem A = memEval s (specLeaf L.lay).mem A := fun A => (hmem2 A).trans (hu.mem A)
  have hkp : ∀ x ∈ leafKeep, u.getReg x = s.getReg x := by
    intro x hx
    have hx' : x ∈ fkeep false := by
      simp only [leafKeep, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [fkeep]
    exact (hkeep2 x hx').trans (hu.keep x hx)
  have h27u : u.getReg .x27 = BitVec.ofNat 64 (hWord L.lay + 256) := by
    rw [hkeep2 .x27 (by simp [fkeep])]
    exact hu.known (.x27, BitVec.ofNat 64 (hWord L.lay + 256)) (by simp [leafPost])
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 456 → A ≠ 448 → A ≠ 840 → A ≠ 832 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      simp only [specLeaf, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hGu : Glob gkL L.wl L.pk u := hglob2 _ _ (hu.glob _ _ _ hG)
  refine ⟨u, hu.steps.trans hst2, hec2, hK2'.1 (.x5, 0) (by simp [fk, gkOf, gkL, gkL0, baseK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · have hends : ∀ v ∈ ends, v.length = 16 := hvs
    rw [hashInput_ofNat _ 0x340 10 h10 h11 (by decide) (by decide),
      pad64_leafInput _ _ _ _ (by rw [hlen]) hends]
    congr 1
    rw [show 8 * (10 + 1) = 4 + 84 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [hmem]; simp only [specLeaf]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval, cw]
        congr 1; unfold twLo hWord; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
      · rw [hmem]; simp only [specLeaf]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_eq _ _ _ _ _ rfl]
        (try simp only [Rv.E.eval]); rw [h31]
        simp only [CCtx.x31, LCtx.cctx]; congr 1; unfold twHi; omega
      · rw [mfr 0x350 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
      · rw [mfr 0x358 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 84
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        obtain ⟨hl0, hl1⟩ := hLB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x340 + 8 * (4 + m) = 0x360 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x340 + 8 * (4 + m) = 0x368 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (L.e % 2) ∨ 0x1E0 + 16 * (L.e % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    have hbit : bitOf L.e 0 = L.e % 2 := by simp [bitOf]
    refine ⟨⟨Glob_writeHash hGu ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one L.e with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, by simp, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
    · have := Known_writeHash hK2'.1 ans
      simpa [lvlK] using this
    · rw [writeHash_getReg, hkp .x23 (by simp [leafKeep])]; exact h23
    · simp only [NBhdr]
      rw [wf 0x1C0 (by omega) (by omega), hmem]; simp only [specLeaf]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold FCtx.lo0 hWord; simp only [layFC]; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]
      omega
    · rw [wf 0x1C8 (by omega) (by omega), hmem]; simp only [specLeaf, layFC]
      rw [memEval_cons_eq _ _ _ _ _ rfl]
      simp only [stW0, ldE, cw, Rv.E.eval, BinOp.eval]
      have htau : ((if L.lay = 0 then E.c (0#64) else E.reg .x30).eval s) = BitVec.ofNat 64 L.tau := by
        by_cases h0 : L.lay = 0 <;> simpa [LCtx.cctx, tauCarry, E.eval, cw, h0] using h30
      rw [merge_w0_toNat, htau, BitVec.toNat_ofNat]
      simp only [LCtx.cctx]
      norm_num
    · simp only [layFC, hbit]
      rw [writeHash_at0 _ ans _ h12 (by omega)]; exact (vw0_answer ans).symm
    · simp only [layFC, hbit]
      rw [show 0x1E8 + 16 * (L.e % 2) = 0x1E0 + 16 * (L.e % 2) + 8 by omega,
        writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · have hc0 : chOf L.lay 0 = 0 := by simp [chOf]
      rw [writeHash_pc, hpc2, pcOf_add4]
      simp only [FCtx.X, FCtx.ci, FCtx.kk, FCtx.blk, layFC, hc0, Nat.zero_sub]
      try rfl
    · rw [writeHash_getReg]; exact h27u
    · exact (tauCarry_frame L.lay (by
        rw [writeHash_getReg, hkp .x30 (by simp [leafKeep])])).trans h30
    · unfold CB0
      rw [wf 0xC0 (by omega) (by omega), mfr 0xC0 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hCB
    · refine Fresh_frame hF (fun A hA hA' => ?_)
      rw [wf A hA (Or.inr (by omega)), mfr A hA (by omega) (by omega) (by omega) (by omega)]

end SigGolfCandidate.Verify
