import SigGolfCandidate.T3M.Verify.CanonicalForest

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Selection selections)

structure SelState (pk : Digest) (w : WBytes) (a : HashOutput) (c : Nat)
    (s : MachineState) extends SigGolfCandidate.T3M.Verify.SelIn pk w a c s : Prop where
  tables : TablesOK s

def selCheckC (c p : Nat) : Bool :=
  specB [] [] baseK (runAtC {} selK [selJoin c] (selStart c) (selDirs p))
    (selSpec c p) [] selK selKeep
def selRCheckC (c r : Nat) : Bool :=
  specB [] [] [] (runAtC {} selK [] (selStart c) (selRDirs r))
    (rejSpec (selRSteps c r) (selRBrs c r)) [] [] []
theorem select_checked : ∀ c : Fin 7, ∀ p : Fin 6,
    selCheckC c.val p.val=true ∧ selRCheckC c.val p.val=true := by decide +kernel
theorem selCheckC_at (c p : Nat) (hc : c<7) (hp : p<6) : selCheckC c p=true :=
  (select_checked ⟨c,hc⟩ ⟨p,hp⟩).1
theorem selRCheckC_at (c p : Nat) (hc : c<7) (hp : p<6) : selRCheckC c p=true :=
  (select_checked ⟨c,hc⟩ ⟨p,hp⟩).2

theorem sel_acc_path (pk : Digest) (w : WBytes) (a : HashOutput) (c p : Nat) (hc : c < 7) (hp : p < 6)
    (s : MachineState) (hs : SelState pk w a c s) (hbr : ∀ b ∈ selBrs c p, b.holds s)
    (hsort : [selX a.toNat c 0, selX a.toNat c 1, selX a.toNat c 2].mergeSort (fun x y => decide (x ≤ y)) =
      (selPerm p).map (selX a.toNat c))
    (hok : selOk1 (selC a c) = true) :
    ∃ u, Steps fixture s (selExt c + 12 + selTree p) (selExt c + 12 + selTree p) u ∧ SelState pk w a (c + 1) u := by
  obtain ⟨u, hu⟩ := spec_runC (selCheckC_at c p hc hp) s hs.pc (selK_of hs.known hs.sp) hbr (by simp)
  have hmem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) =
      if A = ETAB + 24 * c + 16 then (xE c ((selPerm p).getD 2 0)).eval s
      else if A = ETAB + 24 * c + 8 then (xE c ((selPerm p).getD 1 0)).eval s
      else if A = ETAB + 24 * c then (xE c ((selPerm p).getD 0 0)).eval s
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [hu.mem]
    simp only [selSpec, selMem]
    unfold ETAB at *
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_cons_ofNat _ _ _ _ _ hA (by omega),
      memEval_cons_ofNat _ _ _ _ _ hA (by omega), memEval_nil]
  have hperm : ∀ k, k < 3 → (selPerm p).getD k 0 < 3 := by
    intro k hk
    rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> decide
  have hstore : ∀ k, k < 3 → u.getMem (BitVec.ofNat 64 (ETAB + 24 * c + 8 * k)) =
      BitVec.ofNat 64 (TAB + 8 * T3M.selLeaf (selC a c) k) := by
    intro k hk
    rw [hmem _ (by unfold ETAB; omega)]
    have hv : ∀ k', k' < 3 → (xE c ((selPerm p).getD k' 0)).eval s =
        BitVec.ofNat 64 (TAB + 8 * T3M.selLeaf (selC a c) k') := by
      intro k' hk'
      rw [xE_eval a s hs.nregs c _ hc (hperm k' hk'), selC_eq a c hc]
      unfold T3M.selLeaf eVal
      simp only []
      rw [hsort]
      rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 by omega) with rfl | rfl | rfl <;>
      simp only [selPerm, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ] <;> ring
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; exact hv 0 (by decide)
    · rw [if_neg (by omega), if_pos (by omega)]; exact hv 1 (by decide)
    · rw [if_pos (by omega)]; exact hv 2 (by decide)
  have hframe : ∀ A, A < 2 ^ 64 → (A < ETAB + 24 * c ∨ ETAB + 24 * c + 24 ≤ A) →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    rw [hmem A hA, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨u, hu.steps, ⟨⟨?_, selK_base hu.known, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, selK_sp hu.known⟩,hu.tables hs.tables (RelOK.nil s)⟩⟩
  · rw [hu.pc rfl]; rfl
  · intro k hk; rw [hu.keep (nReg k) (by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> simp [selKeep, nReg])]
    exact hs.nregs k hk
  · rw [hu.keep .x22 (by simp [selKeep])]; exact hs.idx
  · intro c' k hc' hk
    by_cases hcc : c' = c
    · subst hcc; exact hstore k hk
    · rw [hframe _ (by unfold ETAB; omega) (by unfold ETAB; omega)]
      exact hs.etab c' k (by omega) hk
  · intro c' hc'
    by_cases hcc : c' = c
    · subst hcc; exact hok
    · exact hs.ok c' (by omega)
  · intro j hj
    rw [hframe _ (by unfold WIT WX at *; omega) (Or.inr (by unfold ETAB WIT; omega))]
    exact hs.wit j hj
  · exact ⟨(hframe 0xA0 (by omega) (Or.inl (by unfold ETAB; omega))).trans hs.pk.1,
      (hframe 0xA8 (by omega) (Or.inl (by unfold ETAB; omega))).trans hs.pk.2⟩
  · intro A hA hz hE
    rw [hframe A (by unfold WIT at hA; omega) (by omega)]
    exact hs.zero A hA hz (by omega)
  · apply hs.data.congr
    intro A hA hEnd
    exact hframe A (by omega) (Or.inr (by unfold ETAB TAB at *; omega))

theorem sel_rej_path (pk : Digest) (w : WBytes) (a : HashOutput) (c r : Nat) (hc : c < 7) (hr : r < 6)
    (s : MachineState) (hs : SelState pk w a c s) (hq : ∀ q ∈ selRBrsQ r, condQ (selX a.toNat c) q) :
    ∃ u, Steps fixture s (selRSteps c r) (selRSteps c r) u ∧ HaltC1 u := by
  have hbr : ∀ b ∈ selRBrs c r, b.holds s := by
    rw [selRBrs_eq c r hr]; exact holds_of_condQ a s hs.nregs c hc _ (selRBrsQ_idx r hr) hq
  obtain ⟨u, hu⟩ := spec_runC (selRCheckC_at c r hc hr) s hs.pc (selK_of hs.known hs.sp) hbr (by simp)
  exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec]),
    hu.regs (.x10, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec])⟩

theorem sel_step (pk : Digest) (w : WBytes) (a : HashOutput) (c : Nat) (hc : c < 7) (s : MachineState)
    (hs : SelState pk w a c s) :
    (selOk1 (selC a c) = true → ∃ u, Steps fixture s (selCost a c) (selCost a c) u ∧ SelState pk w a (c + 1) u) ∧
    (selOk1 (selC a c) = false → ∃ u k, Steps fixture s k k u ∧ k ≤ 23 ∧ HaltC1 u) := by
  have hsel := selC_eq a c hc
  set x0 := selX a.toNat c 0 with hx0
  set x1 := selX a.toNat c 1 with hx1
  set x2 := selX a.toNat c 2 with hx2
  have hok : ∀ y0 y1 y2 : Nat, [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = [y0, y1, y2] →
      selOk1 (selC a c) = (decide (y0 < y1) && decide (y1 < y2)) := by
    intro y0 y1 y2 h
    rw [hsel]; unfold selOk1; simp only []; rw [h]
  -- the accepting/rejecting path from the order of the leaves
  have acc : ∀ p, p < 6 → (∀ q ∈ selBrsQ p, condQ (selX a.toNat c) q) →
      [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = (selPerm p).map (selX a.toNat c) →
      selPath x0 x1 x2 = p → selOk1 (selC a c) = true →
      ∃ u, Steps fixture s (selCost a c) (selCost a c) u ∧ SelState pk w a (c + 1) u := by
    intro p hp hq hsort hpath hokc
    have hbr : ∀ b ∈ selBrs c p, b.holds s := by
      rw [selBrs_eq c p hp]; exact holds_of_condQ a s hs.nregs c hc _ (selBrsQ_idx p hp) hq
    have hcost : selCost a c = selExt c + 12 + selTree p := by
      unfold selCost; rw [← hx0, ← hx1, ← hx2, hpath]
    rw [hcost]
    exact sel_acc_path pk w a c p hc hp s hs hbr hsort hokc
  have rej : ∀ r, r < 6 → (∀ q ∈ selRBrsQ r, condQ (selX a.toNat c) q) →
      ∃ u k, Steps fixture s k k u ∧ k ≤ 23 ∧ HaltC1 u := by
    intro r hr hq
    obtain ⟨u, hu1, hu2⟩ := sel_rej_path pk w a c r hc hr s hs hq
    exact ⟨u, _, hu1, selRSteps_le c r hc, hu2⟩
  by_cases h01 : x0 < x1
  · by_cases h12 : x1 < x2
    · have hs' := mergeSort3 x0 x1 x2 x0 x1 x2 (perm3_0 x0 x1 x2) (by omega) (by omega)
      have hk := hok _ _ _ hs'
      refine ⟨fun _ => acc 0 (by decide) ?_ hs' ?_ (by rw [hk]; simp; omega), fun h => ?_⟩
      · simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp; omega
      · simp only [selPath, if_pos h01, if_pos h12]
      · rw [hk] at h; simp at h; omega
    · by_cases h02 : x0 < x2
      · have hs' := mergeSort3 x0 x1 x2 x0 x2 x1 (perm3_1 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 1 (by decide) ?_ hs' ?_ h, fun h => rej 0 (by decide) ?_⟩
        · have : x2 < x1 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_pos h01, if_neg h12, if_pos h02]
        · have : x2 = x1 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
      · have hs' := mergeSort3 x0 x1 x2 x2 x0 x1 (perm3_2 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 2 (by decide) ?_ hs' ?_ h, fun h => rej 1 (by decide) ?_⟩
        · have : x2 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_pos h01, if_neg h12, if_neg h02]
        · have : x2 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
  · by_cases h12 : x1 < x2
    · by_cases h02 : x0 < x2
      · have hs' := mergeSort3 x0 x1 x2 x1 x0 x2 (perm3_3 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 3 (by decide) ?_ hs' ?_ h, fun h => rej 2 (by decide) ?_⟩
        · have : x1 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_neg h01, if_pos h12, if_pos h02]
        · have : x1 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
      · have hs' := mergeSort3 x0 x1 x2 x1 x2 x0 (perm3_4 x0 x1 x2) (by omega) (by omega)
        have hk := hok _ _ _ hs'
        refine ⟨fun h => acc 4 (by decide) ?_ hs' ?_ h, fun h => rej 3 (by decide) ?_⟩
        · have : x2 < x0 := by rw [hk] at h; simp at h; omega
          simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · simp only [selPath, if_neg h01, if_pos h12, if_neg h02]
        · have : x2 = x0 := by rw [hk] at h; simp at h; omega
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
    · have hs' := mergeSort3 x0 x1 x2 x2 x1 x0 (perm3_5 x0 x1 x2) (by omega) (by omega)
      have hk := hok _ _ _ hs'
      refine ⟨fun h => acc 5 (by decide) ?_ hs' ?_ h, fun h => ?_⟩
      · have : x2 < x1 ∧ x1 < x0 := by rw [hk] at h; simp at h; omega
        simp only [selBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp; omega
      · simp only [selPath, if_neg h01, if_neg h12]
      · by_cases h21 : x2 = x1
        · apply rej 4 (by decide)
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega
        · have : x1 = x0 := by rw [hk] at h; simp at h; omega
          apply rej 5 (by decide)
          simp only [selRBrsQ, condQ, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          simp; omega

theorem sel_prefix (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) (hs : SelState pk w a 0 s) :
    ∀ n, n ≤ 7 →
      (∃ u, Steps fixture s (sumTo (selCost a) n) (sumTo (selCost a) n) u ∧ SelState pk w a n u) ∨
      (∃ u k, Steps fixture s k k u ∧ k ≤ 23 * n ∧ HaltC1 u ∧ ∃ c, c < n ∧ selOk1 (selC a c) = false) := by
  intro n
  induction n with
  | zero => intro _; exact Or.inl ⟨s, Steps.refl s, hs⟩
  | succ n ih =>
    intro hn
    rcases ih (by omega) with ⟨u, hst, hu⟩ | ⟨u, k, hst, hk, hh, c, hc, hc'⟩
    · obtain ⟨hacc, hrej⟩ := sel_step pk w a n (by omega) u hu
      cases hok : selOk1 (selC a n)
      · obtain ⟨v, k, hst', hk, hh⟩ := hrej hok
        right
        have := sumTo_selCost_le a n
        exact ⟨v, _, hst.trans hst', by omega, hh, n, by omega, hok⟩
      · obtain ⟨v, hst', hv⟩ := hacc hok
        left
        exact ⟨v, (hst.trans hst').of_eq (by simp [sumTo]) (by simp [sumTo]), hv⟩
    · right; exact ⟨u, k, hst, by omega, hh, c, by omega, hc'⟩

theorem select_phase (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) (hs : SelState pk w a 0 s) :
    (selectionsOk (selections a) = true →
      ∃ u, Steps fixture s (selCostAll a) (selCostAll a) u ∧ SelState pk w a 7 u) ∧
    (selectionsOk (selections a) = false → ∃ u k, Steps fixture s k k u ∧ k ≤ 161 ∧ HaltC1 u) := by
  constructor
  · intro h
    rcases sel_prefix pk w a s hs 7 (le_refl _) with hu | ⟨u, k, _, _, _, c, hc, hc'⟩
    · exact hu
    · rw [(selectionsOk_iff a).mp h c hc] at hc'; cases hc'
  · intro h
    rcases sel_prefix pk w a s hs 7 (le_refl _) with ⟨u, _, hu⟩ | ⟨u, k, hst, hk, hh, _⟩
    · have : selectionsOk (selections a) = true := (selectionsOk_iff a).mpr hu.ok
      rw [this] at h; cases h
    · exact ⟨u, k, hst, by omega, hh⟩

/-! ## The selection piece of `verifyP` -/

/-- `verifyP` after the selection check: the FTS, the layers, the comparison. -/
theorem select_from_ready (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelState pk w a 0 s) {N C A : Nat} {Q : Prop}
    (REST : T3.M Bool) (K : Bool → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (hK : K false=pure (false,0))
    (hrest : ∀ t, SelState pk w a 7 t → GQ t N C Q A (CanonicalPort.Verify.ccM REST K)) :
    GQ s (N+162) (C+162) Q (A+153)
      (CanonicalPort.Verify.ccM (if (!selectionsOk (selections a))=true then pure false else REST) K) := by
  obtain ⟨hacc,hrej⟩ := select_phase pk w a s hs
  have hle := selCostAll_le a
  cases hsel : selectionsOk (selections a)
  · simp only [Bool.not_false,if_true,CanonicalPort.Verify.ccM_pure,hK]
    obtain ⟨u,k,hsteps,hk,hh⟩ := hrej hsel
    exact CanonicalPort.Verify.GoodQ.steps' hsteps
      (CanonicalPort.Verify.GoodQ.reject (Q:=False) (A:=0) hh.1 hh.2.1 hh.2.2)
      (by omega) (by omega) (fun hq => hq.elim)
  · simp only [Bool.not_true,Bool.false_eq_true,if_false]
    obtain ⟨u,hsteps,hu⟩ := hacc hsel
    exact CanonicalPort.Verify.GoodQ.steps' hsteps (hrest u hu)
      (by omega) (by omega) (fun hq => ⟨hq,by omega⟩)

#print axioms select_phase
#print axioms select_from_ready
end SigGolfCandidate.T3M.CanonicalNative
