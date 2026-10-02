import SigGolfCandidate.T3M.Verify.FtsEnd

/-!
# The FTS stream machine refines `ftsP` (T3M verify)

From `SelIn pk w a 7 t` (after the selections), every run of the frozen verify image through `fts_setup`, the 21
leaf codes, the segment dispatch/slots/ladders/tails, the 7 coordinate ends, the pointer cap and the forest HASH
observes `ccM (ftsP w idx (selections a)) R`, and ends either in HALT(1) (exactly where `ftsP` returns `none`) or in
**`FtsOut`** with the forest pk that `ftsP` returns (`fts_good`).

Budgets (fuel = all-oracle cycles `B`, accepting cycles `A`; `fo` = folds consumed so far):
* folds: 16 cycles per fold (rung 8 + HASH 8), the segment's last fold 14 (`folds_good`);
* one segment: at most 191 cycles, accepting `15 + 16 a` (dispatch 4, slot 3 / 4, pending HASH 8, `j lad` 1, folds
  `16 a - 2`) (`seg_good`);
* a segment loop from stack depth `d`: `B0 + 197 + 199 d` / `A0 + 15 + 23 d + 16 (124 - fo)` (merge tail 8, its
  reject 6) (`segLoop_good`);
* a coordinate from its leaf 0: `Cent c = 1046 + 1025 (6 - c)` / `Aent c = 148 + 127 (6 - c)` (+ `16 (124 - fo)`)
  (`coord_good`); the forest 24 / 24 (cap check, frame, two-block HASH) (`fin_good`);
* the FTS from `SelIn`: **7214 / 2912** (`fts_good`). Every accepting run has 5 segments per coordinate (3 leaves,
  2 merges): its accepting cost is exactly `928 + 16 F` (`F` = folds, at most 124 by the pointer cap); the bound
  `2912 = 928 + 16 · 124`. Accepting runs satisfy `fo ≤ 124` at every point (`Q ∧ fo ≤ 124`).

`verifyP_good_fts`: `verifyP` from the initial state, given the layers phase (V1, V3) from `FtsOut`.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

/-- `omega` after normalizing list lengths. -/
macro "lomega" : tactic => `(tactic| ((try simp only [List.length_nil, List.length_cons]) <;> omega))

/-! ## Core's programs in named pieces -/

/-- The end of a segment of Core's `segLoop` (after the folds), by the stack. -/
def segTail (F : FCtx) (c : Nat) (stk : List (Digest × Nat)) (b : Nat) (node : Digest) (E ptr : Nat) :
    T3.M (Option (Digest × Nat × Nat × List (Digest × Nat))) :=
  match stk with
  | [] => pure (if b / 16 % 2 = 1 then none else some (node, E, ptr, []))
  | (pnode, Q) :: rest =>
      if b / 16 % 2 = 0 then pure (some (node, E, ptr, (pnode, Q) :: rest))
      else if Q ≠ E then pure none else segLoop F.w F.idx c rest (.merge (E / 2) pnode) (E / 2) ptr node

/-- One segment of Core's `segLoop` with the tail `TL` after the folds. -/
def segProg {γ : Type} (F : FCtx) (c : Nat) (pend : Pending) (E ptr : Nat) (node : Digest)
    (TL : Digest → Nat → T3.M (Option γ)) : T3.M (Option γ) :=
  if 11 < (wbyte F.w ptr).toNat % 16 then pure none
  else if 0 < (wbyte F.w ptr).toNat % 16 ∧ (wbyte F.w ptr).toNat / 32 % 2 ≠ E % 2 then pure none
  else pendingHash F.w F.idx c node pend >>= fun node1 =>
    foldsP F.w F.idx c ptr ((wbyte F.w ptr).toNat % 16) node1 E >>= fun p => TL p.1 p.2

theorem segLoop_eq (F : FCtx) (c : Nat) (stk : List (Digest × Nat)) (pend : Pending) (E ptr : Nat) (node : Digest) :
    segLoop F.w F.idx c stk pend E ptr node = segProg F c pend E ptr node (fun node2 E2 =>
      segTail F c stk (wbyte F.w ptr).toNat node2 E2 (segNext ptr ((wbyte F.w ptr).toNat % 16))) := by
  rw [segLoop.eq_1]; rfl

/-- `ftsCoordP` after leaf 2's segment loop. -/
def coordK2 (r : Option (Digest × Nat × Nat × List (Digest × Nat))) : T3.M (Option (Digest × Nat)) :=
  match r with
  | some (n2, E2, p2, s2) => if E2 = 1 ∧ s2 = [] then pure (some (n2, p2)) else pure none
  | none => pure none

/-- `ftsCoordP` after leaf 1's segment loop. -/
def coordK1 (F : FCtx) (c : Nat) (r : Option (Digest × Nat × Nat × List (Digest × Nat))) :
    T3.M (Option (Digest × Nat)) :=
  match r with
  | some (n1, E1, p1, s1) => segLoop F.w F.idx c ((n1, E1 ^^^ 1) :: s1) (.leaf (3 * c + 2) (T3M.selLeaf (F.sel c) 2))
      (2048 + T3M.selLeaf (F.sel c) 2) p1 n1 >>= coordK2
  | none => pure none

/-- `ftsCoordP` after leaf 0's segment loop. -/
def coordK0 (F : FCtx) (c : Nat) (r : Option (Digest × Nat × Nat × List (Digest × Nat))) :
    T3.M (Option (Digest × Nat)) :=
  match r with
  | some (n0, E0, p0, s0) => segLoop F.w F.idx c ((n0, E0 ^^^ 1) :: s0) (.leaf (3 * c + 1) (T3M.selLeaf (F.sel c) 1))
      (2048 + T3M.selLeaf (F.sel c) 1) p0 n0 >>= coordK1 F c
  | none => pure none

theorem ftsCoordP_eq (F : FCtx) (c ptr : Nat) :
    ftsCoordP F.w F.idx c (F.sel c) ptr = segLoop F.w F.idx c [] (.leaf (3 * c) (T3M.selLeaf (F.sel c) 0))
      (2048 + T3M.selLeaf (F.sel c) 0) ptr 0 >>= coordK0 F c := by
  unfold ftsCoordP
  congr 1; funext r
  rcases r with _ | ⟨n0, E0, p0, s0⟩
  · rfl
  · simp only [coordK0]
    congr 1; funext r1
    rcases r1 with _ | ⟨n1, E1, p1, s1⟩
    · rfl
    · simp only [coordK1]
      congr 1; funext r2
      rcases r2 with _ | ⟨n2, E2, p2, s2⟩ <;> rfl

/-- `ftsP`'s fold step after a coordinate. -/
def coordNext' (roots : List Digest) (x : Option (Digest × Nat)) : T3.M (Option (List Digest × Nat)) :=
  match x with
  | some (root, ptr) => pure (some (roots ++ [root], ptr))
  | none => pure none

/-- `ftsP`'s fold step. -/
def ftsStep (F : FCtx) (state : Option (List Digest × Nat)) (coord : Nat) : T3.M (Option (List Digest × Nat)) :=
  match state with
  | some (roots, ptr) => ftsCoordP F.w F.idx coord (F.sel coord) ptr >>= coordNext' roots
  | none => pure none

/-- `ftsP` after the seven coordinates: the pointer cap and the forest pk. -/
def ftsFin (F : FCtx) (state : Option (List Digest × Nat)) : T3.M (Option Digest) :=
  match state with
  | some (roots, ptr) => if streamEnd < ptr then pure none else T3.forestPk F.idx roots >>= fun r => pure (some r)
  | none => pure none

theorem ftsP_eq (F : FCtx) :
    ftsP F.w F.idx (selections F.a) = List.foldlM (ftsStep F) (some ([], 1088)) (List.range 7) >>= ftsFin F := by
  unfold ftsP
  congr 1
  · congr 1
    funext state coord
    rcases state with _ | ⟨roots, ptr⟩
    · rfl
    · simp only [ftsStep]; congr 1; funext x; rcases x with _ | ⟨root, ptr'⟩ <;> rfl
  · funext st; rcases st with _ | ⟨roots, ptr⟩ <;> rfl

theorem foldlM_none (F : FCtx) : ∀ l : List Nat, List.foldlM (ftsStep F) none l = pure none
  | [] => rfl
  | c :: l => by
    rw [List.foldlM_cons]
    show (pure none >>= fun b => List.foldlM (ftsStep F) b l) = pure none
    rw [pure_bind]; exact foldlM_none F l

/-! ## Judgment helpers -/

/-- A run that HALTs with exit code 1 after `k` steps. -/
theorem GoodQ.rejectAfter {m u : MachineState} {k N C A : Nat} {Q : Prop} (hst : Steps image m k k u) (hh : Halt1 u)
    (hN : k + 1 ≤ N) (hC : k + 1 ≤ C) : GoodQ m N C Q A (pure (false, 0)) :=
  GoodQ.steps' hst (GoodQ.reject (Q := False) (A := 0) hh.1 hh.2.1 hh.2.2) (by omega) (by omega) (fun q => q.elim)

/-! ## Folds -/

theorem foldBlk_blocks (F : FCtx) (c ptr i E : Nat) (node : Digest) :
    (toQ (T3.pad64 (foldBlk F c ptr i E node))).blocks = 1 := by
  unfold foldBlk; split <;> exact blocks_blk4 _ _ _ _

theorem foldStep_bind {β : Type} (F : FCtx) (c ptr i E : Nat) (node : Digest) (g : Digest × Nat → T3.M β) :
    (foldStep F.w F.idx c ptr (node, E) i >>= g) =
      (T3.shortHash (foldBlk F c ptr i E node) >>= fun v => g (v, E / 2)) := by
  rw [foldStep_eq, bind_assoc]; simp only [pure_bind]

/-- The folds `i .. i + n - 1` of a segment (`n ≥ 1`): `16 n - 2` cycles. -/
theorem folds_good (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (X a ptr folds : Nat)
    (R : Digest × Nat → OracleComp HashSpec Obs) (B A : Nat) (Q : Prop)
    (hK : ∀ E' node' u, TailIn F c j roots stk X E' (ptr + 8 + 80 * a) (folds + a) node' u →
      GoodQ u B B Q A (R (node', E'))) :
    ∀ n i E node m, i + n = a → 0 < n → RungIn F c j roots stk X a i E ptr folds node m →
      GoodQ m (B + (16 * n - 2)) (B + (16 * n - 2)) Q (A + (16 * n - 2))
        (ccM ((List.range' i n).foldlM (foldStep F.w F.idx c ptr) (node, E)) R) := by
  intro n
  induction n with
  | zero => intro i E node m _ h0; omega
  | succ n ih =>
    intro i E node m hia _ h
    obtain ⟨u, hst, hf, h5, hv, hin, hnext⟩ := rung_step F c j roots stk X a i E ptr folds node m h
    have hb := foldBlk_blocks F c ptr i E node
    simp only [List.range'_succ, List.foldlM_cons, foldStep_bind]
    by_cases hn : n = 0
    · subst hn
      have hrs : rungSteps i a = 6 := by unfold rungSteps; split <;> omega
      have hg := GoodQ.shortHash_bind (N := B) (C := B) (A := A) (Q := Q)
        (f := fun v => List.foldlM (foldStep F.w F.idx c ptr) (v, E / 2) (List.range' (i + 1) 0)) (K := R)
        hf h5 hv hin (fun ans => by
          simp only [List.range'_zero, List.foldlM_nil, ccM_pure]
          exact hK _ _ _ ((hnext ans).2 (by omega)))
      rw [hb] at hg
      exact GoodQ.steps' (hst.of_eq hrs hrs) hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    · have hrs : rungSteps i a = 8 := by unfold rungSteps; split <;> omega
      have hg := GoodQ.shortHash_bind (N := B + (16 * n - 2)) (C := B + (16 * n - 2)) (A := A + (16 * n - 2))
        (Q := Q) (f := fun v => List.foldlM (foldStep F.w F.idx c ptr) (v, E / 2) (List.range' (i + 1) n)) (K := R)
        hf h5 hv hin (fun ans => ih (i + 1) (E / 2) _ _ (by omega) (by omega) ((hnext ans).1 (by omega)))
      rw [hb] at hg
      exact GoodQ.steps' (hst.of_eq hrs hrs) hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)

/-! ## One segment -/

/-- One segment from its dispatch: the two rejects, the pending HASH, the folds, then the tail `TL` at `TailIn`.
At most 191 cycles; accepting `15 + 16 a` (the fold budget `16 (124 - fo)` pays the folds). -/
theorem seg_good {γ : Type} (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (pend : Pending)
    (E ptr folds : Nat) (node : Digest) (m : MachineState) (h : DispIn F c j roots stk pend E ptr folds node m)
    (TL : Digest → Nat → T3.M (Option γ)) (Rs : Option γ → OracleComp HashSpec Obs) (hRs : Rs none = pure (false, 0))
    (B A : Nat) (Q : Prop)
    (hT : ∀ E' node' u, TailIn F c j roots stk (segX (tselJ j) (wbyte F.w ptr).toNat) E'
        (ptr + 8 + 80 * segA (wbyte F.w ptr).toNat) (folds + segA (wbyte F.w ptr).toNat) node' u →
      GoodQ u B B (Q ∧ folds + segA (wbyte F.w ptr).toNat ≤ 124)
        (A + 16 * (124 - (folds + segA (wbyte F.w ptr).toNat))) (ccM (TL node' E') Rs)) :
    GoodQ m (B + 191) (B + 191) (Q ∧ folds ≤ 124) (A + 15 + 16 * (124 - folds))
      (ccM (segProg F c pend E ptr node TL) Rs) := by
  obtain ⟨sRej, sPar, sOk⟩ := seg_step F c j roots stk pend E ptr folds node m h
  unfold segProg
  by_cases h11 : 11 < (wbyte F.w ptr).toNat % 16
  · rw [if_pos h11, ccM_pure, hRs]
    obtain ⟨u, hu, hh⟩ := sRej h11
    exact GoodQ.rejectAfter hu hh (by omega) (by omega)
  rw [if_neg h11]
  by_cases hpar : 0 < (wbyte F.w ptr).toNat % 16 ∧ (wbyte F.w ptr).toNat / 32 % 2 ≠ E % 2
  · rw [if_pos hpar, ccM_pure, hRs]
    obtain ⟨u, hu, hh⟩ := sPar hpar.1 (by unfold segA; omega) hpar.2
    exact GoodQ.rejectAfter hu hh (by omega) (by omega)
  rw [if_neg hpar]
  have ha11 : segA (wbyte F.w ptr).toNat ≤ 11 := by unfold segA; omega
  have hor : segA (wbyte F.w ptr).toNat = 0 ∨ segT (wbyte F.w ptr).toNat = E % 2 := by
    unfold segA segT; omega
  obtain ⟨u, hst, hf, h5, hv, hin, hnext⟩ := sOk ha11 hor
  have hb1 := pendBlk_blocks F c node pend
  rw [pendingHash_eq]
  by_cases ha0 : segA (wbyte F.w ptr).toNat = 0
  · have hb0 : (wbyte F.w ptr).toNat % 16 = 0 := ha0
    have e1 : ptr + 8 + 80 * segA (wbyte F.w ptr).toNat = ptr + 8 := by omega
    have e2 : folds + segA (wbyte F.w ptr).toNat = folds := by omega
    have hg := GoodQ.shortHash_bind (N := B) (C := B) (A := A + 16 * (124 - (folds + segA (wbyte F.w ptr).toNat)))
      (Q := Q ∧ folds + segA (wbyte F.w ptr).toNat ≤ 124)
      (f := fun node1 => foldsP F.w F.idx c ptr ((wbyte F.w ptr).toNat % 16) node1 E >>= fun p => TL p.1 p.2)
      (K := Rs) hf h5 hv hin (fun ans => by
        rw [hb0]
        simp only [foldsP, List.range_zero, List.foldlM_nil, pure_bind]
        exact hT _ _ _ (by rw [e1, e2]; exact (hnext ans).1 ha0))
    rw [hb1] at hg
    have hsp : segPre (segA (wbyte F.w ptr).toNat) = 7 := by rw [ha0]; rfl
    exact GoodQ.steps' (hst.of_eq hsp hsp) hg (by omega) (by omega) (fun q => ⟨⟨q.1, by omega⟩, by omega⟩)
  · have hapos : 0 < segA (wbyte F.w ptr).toNat := Nat.pos_of_ne_zero ha0
    have hg := GoodQ.shortHash_bind (N := B + (16 * segA (wbyte F.w ptr).toNat - 2) + 1)
      (C := B + (16 * segA (wbyte F.w ptr).toNat - 2) + 1)
      (A := A + 16 * (124 - (folds + segA (wbyte F.w ptr).toNat)) + (16 * segA (wbyte F.w ptr).toNat - 2) + 1)
      (Q := Q ∧ folds + segA (wbyte F.w ptr).toNat ≤ 124)
      (f := fun node1 => foldsP F.w F.idx c ptr ((wbyte F.w ptr).toNat % 16) node1 E >>= fun p => TL p.1 p.2)
      (K := Rs) hf h5 hv hin (fun ans => by
        obtain ⟨v, hv1, hrung⟩ := (hnext ans).2 hapos
        rw [ccM_bind]
        have hfg := folds_good F c j roots stk (segX (tselJ j) (wbyte F.w ptr).toNat) (segA (wbyte F.w ptr).toNat)
          ptr folds (fun p => ccM (TL p.1 p.2) Rs) B
          (A + 16 * (124 - (folds + segA (wbyte F.w ptr).toNat))) (Q ∧ folds + segA (wbyte F.w ptr).toNat ≤ 124)
          (fun E' node' u' hu' => hT E' node' u' hu') (segA (wbyte F.w ptr).toNat) 0 E _ v (by omega) hapos hrung
        have hr : List.range ((wbyte F.w ptr).toNat % 16) = List.range' 0 (segA (wbyte F.w ptr).toNat) :=
          List.range_eq_range'
        simp only [foldsP]
        rw [hr]
        exact GoodQ.steps' hv1 hfg (by omega) (by omega) (fun q => ⟨q, by omega⟩))
    rw [hb1] at hg
    have hsp : segPre (segA (wbyte F.w ptr).toNat) = 8 := by unfold segPre; rw [if_neg ha0]
    exact GoodQ.steps' (hst.of_eq hsp hsp) hg (by omega) (by omega) (fun q => ⟨⟨q.1, by omega⟩, by omega⟩)

/-! ## The segment loop -/

theorem segX_nm (j b : Nat) (h : segM b = 0) : segX (tselJ j) b = if j = 2 then 2 else 1 := by
  by_cases hj : j = 2 <;> simp [segX, tselJ, h, hj]

theorem segX_m (j b : Nat) (h : segM b = 1) : segX (tselJ j) b = 0 := by
  unfold segX; rw [if_pos h]

/-- Core's `segLoop` from a dispatch at stack depth `d`: `B0 + 197 + 199 d` cycles, accepting
`A0 + 15 + 23 d + 16 (124 - fo)`, given the continuation at the final (non-merge) tail at depth `d'`. -/
theorem segLoop_good (F : FCtx) (c j : Nat) (roots : List Digest)
    (Rs : Option (Digest × Nat × Nat × List (Digest × Nat)) → OracleComp HashSpec Obs)
    (hRs : Rs none = pure (false, 0)) (B0 A0 : Nat) (Q : Prop)
    (hK : ∀ stk' E' ptr' folds' node' u, TailIn F c j roots stk' (if j = 2 then 2 else 1) E' ptr' folds' node' u →
      GoodQ u (B0 + 199 * stk'.length) (B0 + 199 * stk'.length) (Q ∧ folds' ≤ 124)
        (A0 + 23 * stk'.length + 16 * (124 - folds')) (Rs (some (node', E', ptr', stk')))) :
    ∀ stk pend E ptr folds node m, DispIn F c j roots stk pend E ptr folds node m →
      GoodQ m (B0 + 197 + 199 * stk.length) (B0 + 197 + 199 * stk.length) (Q ∧ folds ≤ 124)
        (A0 + 15 + 23 * stk.length + 16 * (124 - folds)) (ccM (segLoop F.w F.idx c stk pend E ptr node) Rs) := by
  intro stk
  induction stk with
  | nil =>
    intro pend E ptr folds node m h
    rw [segLoop_eq]
    refine (seg_good F c j roots [] pend E ptr folds node m h _ Rs hRs (B0 + 6) A0 Q
      (fun E' node' u hu => ?_)).mono (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
    simp only [segTail]
    by_cases hm : (wbyte F.w ptr).toNat / 16 % 2 = 1
    · rw [if_pos hm, ccM_pure, hRs]
      rw [segX_m j _ hm] at hu
      obtain ⟨u', hu', hh⟩ := (tailM_step F c j roots [] E' _ _ node' u hu).1 rfl
      exact GoodQ.rejectAfter hu' hh (by omega) (by omega)
    · rw [if_neg hm, ccM_pure]
      rw [segX_nm j (wbyte F.w ptr).toNat (by unfold segM; omega)] at hu
      have := hK [] E' _ _ node' u hu
      exact this.mono (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
  | cons top rest ih =>
    intro pend E ptr folds node m h
    rw [segLoop_eq]
    obtain ⟨pn, Qv⟩ := top
    refine (seg_good F c j roots ((pn, Qv) :: rest) pend E ptr folds node m h _ Rs hRs
      (B0 + 6 + 199 * (rest.length + 1)) (A0 + 23 * (rest.length + 1)) Q
      (fun E' node' u hu => ?_)).mono (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
    simp only [segTail]
    by_cases hm : (wbyte F.w ptr).toNat / 16 % 2 = 0
    · rw [if_pos hm, ccM_pure]
      rw [segX_nm j (wbyte F.w ptr).toNat hm] at hu
      have := hK _ E' _ _ node' u hu
      exact this.mono (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
    · rw [if_neg hm]
      rw [segX_m j _ (by unfold segM; omega)] at hu
      obtain ⟨-, tQ, tE⟩ := tailM_step F c j roots ((pn, Qv) :: rest) E' _ _ node' u hu
      by_cases hq : Qv ≠ E'
      · rw [if_pos hq, ccM_pure, hRs]
        obtain ⟨u', hu', hh⟩ := tQ pn Qv rest rfl hq
        exact GoodQ.rejectAfter hu' hh (by omega) (by omega)
      · rw [if_neg hq]
        have hq' : Qv = E' := by omega
        subst hq'
        obtain ⟨u', hu', hd⟩ := tE pn rest rfl
        exact GoodQ.steps' hu' (ih _ _ _ _ _ _ hd) (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)

/-! ## Leaves and coordinates -/

theorem FCtx.g_eq (F : FCtx) (c j : Nat) (hj : j < 3) : F.g (3 * c + j) = T3M.selLeaf (F.sel c) j := by
  unfold FCtx.g; rw [show (3 * c + j) / 3 = c by omega, show (3 * c + j) % 3 = j by omega]

/-- A leaf's code and its segment loop. -/
theorem leaf_good (F : FCtx) (c j : Nat) (roots : List Digest) (stk : List (Digest × Nat)) (ptr folds : Nat)
    (m : MachineState) (h : LeafIn F c j roots stk ptr folds m) (node : Digest)
    (Rs : Option (Digest × Nat × Nat × List (Digest × Nat)) → OracleComp HashSpec Obs)
    (hRs : Rs none = pure (false, 0)) (B0 A0 : Nat) (Q : Prop)
    (hK : ∀ stk' E' ptr' folds' node' u, TailIn F c j roots stk' (if j = 2 then 2 else 1) E' ptr' folds' node' u →
      GoodQ u (B0 + 199 * stk'.length) (B0 + 199 * stk'.length) (Q ∧ folds' ≤ 124)
        (A0 + 23 * stk'.length + 16 * (124 - folds')) (Rs (some (node', E', ptr', stk')))) :
    GoodQ m (B0 + 197 + 199 * stk.length + leafCode j) (B0 + 197 + 199 * stk.length + leafCode j) (Q ∧ folds ≤ 124)
      (A0 + 15 + 23 * stk.length + 16 * (124 - folds) + leafCode j)
      (ccM (segLoop F.w F.idx c stk (.leaf (3 * c + j) (T3M.selLeaf (F.sel c) j)) (2048 + T3M.selLeaf (F.sel c) j)
        ptr node) Rs) := by
  obtain ⟨u, hu, hd⟩ := leaf_step F c j roots stk ptr folds m h node
  rw [F.g_eq c j h.bnd.hj] at hd
  exact GoodQ.steps' hu (segLoop_good F c j roots Rs hRs B0 A0 Q hK stk _ _ ptr folds node u hd) (by omega)
    (by omega) (fun q => ⟨q, by omega⟩)

/-- All-oracle cycles from a coordinate's leaf 0 (`c < 7`) or the forest (`c = 7`) to the end of the FTS. -/
def Cent (c : Nat) : Nat := if c < 7 then 1046 + 1025 * (6 - c) else 24
/-- Accepting cycles from a coordinate's leaf 0 or the forest, beyond the fold budget `16 (124 - fo)`. -/
def Aent (c : Nat) : Nat := if c < 7 then 148 + 127 * (6 - c) else 24

/-- The start of coordinate `c` (its leaf 0, empty stack) or, for `c = 7`, the forest. -/
def NextIn (F : FCtx) (c : Nat) (roots : List Digest) (ptr folds : Nat) (m : MachineState) : Prop :=
  if c < 7 then LeafIn F c 0 roots [] ptr folds m else ForestIn F roots ptr folds m

/-- One coordinate (`ftsCoordP`): three leaves with their segment loops, the push and final tails, `coord_end`. -/
theorem coord_good (F : FCtx) (c : Nat) (roots : List Digest) (ptr folds : Nat) (m : MachineState)
    (h : LeafIn F c 0 roots [] ptr folds m) (R : Option (Digest × Nat) → OracleComp HashSpec Obs)
    (hR : R none = pure (false, 0)) (Bf Af : Nat) (Q : Prop)
    (hK : ∀ root ptr' folds' u, NextIn F (c + 1) (roots ++ [root]) ptr' folds' u →
      GoodQ u (Bf + Cent (c + 1)) (Bf + Cent (c + 1)) (Q ∧ folds' ≤ 124) (Af + Aent (c + 1) + 16 * (124 - folds'))
        (R (some (root, ptr')))) :
    GoodQ m (Bf + Cent c) (Bf + Cent c) (Q ∧ folds ≤ 124) (Af + Aent c + 16 * (124 - folds))
      (ccM (ftsCoordP F.w F.idx c (F.sel c) ptr) R) := by
  have hc7 := h.fb.hc
  have ce : Cent c = 1046 + 1025 * (6 - c) := if_pos hc7
  have ae : Aent c = 148 + 127 * (6 - c) := if_pos hc7
  have lc0 : leafCode 0 = 7 := rfl
  have lc1 : leafCode 1 = 6 := rfl
  have lc2 : leafCode 2 = 7 := rfl
  rw [ftsCoordP_eq, ccM_bind]
  refine (leaf_good F c 0 roots [] ptr folds m h 0 _ (by simp only [coordK0, ccM_pure, hR])
    (Bf + 842 + 1025 * (6 - c)) (Af + 126 + 127 * (6 - c)) Q (fun stk0 E0 p0 f0 n0 u0 hu0 => ?_)).mono
    (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
  -- leaf 0 ended: push, leaf 1
  have hu0' : TailIn F c 0 roots stk0 1 E0 p0 f0 n0 u0 := hu0
  obtain ⟨u1, hu1, hl1⟩ := tailP_step F c 0 roots stk0 E0 p0 f0 n0 u0 hu0'
  simp only [coordK0]
  rw [ccM_bind]
  refine GoodQ.steps' hu1 (leaf_good F c 1 roots ((n0, E0 ^^^ 1) :: stk0) p0 f0 u1 hl1 n0 _
    (by simp only [coordK1, ccM_pure, hR]) (Bf + 436 + 1025 * (6 - c)) (Af + 78 + 127 * (6 - c)) Q
    (fun stk1 E1 p1 f1 n1 u2 hu2 => ?_)) (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
  -- leaf 1 ended: push, leaf 2
  have hu2' : TailIn F c 1 roots stk1 1 E1 p1 f1 n1 u2 := hu2
  obtain ⟨u3, hu3, hl2⟩ := tailP_step F c 1 roots stk1 E1 p1 f1 n1 u2 hu2'
  simp only [coordK1]
  rw [ccM_bind]
  refine GoodQ.steps' hu3 (leaf_good F c 2 roots ((n1, E1 ^^^ 1) :: stk1) p1 f1 u3 hl2 n1 _
    (by simp only [coordK2, ccM_pure, hR]) (Bf + 29 + 1025 * (6 - c)) (Af + 29 + 127 * (6 - c)) Q
    (fun stk2 E2 p2 f2 n2 u4 hu4 => ?_)) (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
  -- leaf 2 ended: final tail, coord_end
  have hu4' : TailIn F c 2 roots stk2 2 E2 p2 f2 n2 u4 := hu4
  obtain ⟨-, u5, hu5, hci⟩ := tailF_step F c 2 roots stk2 E2 p2 f2 n2 u4 hu4'
  obtain ⟨cE, cS, cL, cF⟩ := coord_step F c roots stk2 E2 p2 f2 n2 u5 hci
  simp only [coordK2]
  by_cases hE1 : E2 = 1
  · by_cases hs : stk2 = []
    · rw [if_pos ⟨hE1, hs⟩, ccM_pure]
      subst hs
      by_cases hc6 : c < 6
      · obtain ⟨u6, hu6, hl⟩ := cL hE1 rfl hc6
        have hn : NextIn F (c + 1) (roots ++ [n2]) p2 f2 u6 := by
          unfold NextIn; rw [if_pos (by omega)]; exact hl
        have ce1 : Cent (c + 1) = 1046 + 1025 * (6 - (c + 1)) := if_pos (by omega)
        have ae1 : Aent (c + 1) = 148 + 127 * (6 - (c + 1)) := if_pos (by omega)
        exact GoodQ.steps' (hu5.trans hu6) (hK n2 p2 f2 u6 hn) (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
      · have hc6' : c = 6 := by omega
        obtain ⟨u6, hu6, hf⟩ := cF hE1 rfl hc6'
        have hn : NextIn F (c + 1) (roots ++ [n2]) p2 f2 u6 := by
          unfold NextIn; rw [if_neg (by omega)]; exact hf
        have ce1 : Cent (c + 1) = 24 := if_neg (by omega)
        have ae1 : Aent (c + 1) = 24 := if_neg (by omega)
        exact GoodQ.steps' (hu5.trans hu6) (hK n2 p2 f2 u6 hn) (by lomega) (by lomega) (fun q => ⟨q, by lomega⟩)
    · rw [if_neg (fun hh => hs hh.2), ccM_pure, hR]
      obtain ⟨u6, hu6, hh⟩ := cS hE1 hs
      exact GoodQ.rejectAfter (hu5.trans hu6) hh (by lomega) (by lomega)
  · rw [if_neg (fun hh => hE1 hh.1), ccM_pure, hR]
    obtain ⟨u6, hu6, hh⟩ := cE hE1
    exact GoodQ.rejectAfter (hu5.trans hu6) hh (by lomega) (by lomega)

/-! ## The seven coordinates, the cap and the forest -/

/-- The coordinates `c .. 6` of `ftsP`'s fold. -/
theorem coords_good (F : FCtx) (R7 : Option (List Digest × Nat) → OracleComp HashSpec Obs)
    (hR7 : R7 none = pure (false, 0)) (Bf Af : Nat) (Q : Prop)
    (hfin : ∀ roots ptr folds m, ForestIn F roots ptr folds m →
      GoodQ m (Bf + 24) (Bf + 24) (Q ∧ folds ≤ 124) (Af + 24 + 16 * (124 - folds)) (R7 (some (roots, ptr)))) :
    ∀ n c roots ptr folds m, c + n = 7 → NextIn F c roots ptr folds m →
      GoodQ m (Bf + Cent c) (Bf + Cent c) (Q ∧ folds ≤ 124) (Af + Aent c + 16 * (124 - folds))
        (ccM ((List.range' c n).foldlM (ftsStep F) (some (roots, ptr))) R7) := by
  intro n
  induction n with
  | zero =>
    intro c roots ptr folds m hc h
    have hc7 : c = 7 := by omega
    subst hc7
    have hf : ForestIn F roots ptr folds m := by unfold NextIn at h; rwa [if_neg (by omega)] at h
    simp only [List.range'_zero, List.foldlM_nil, ccM_pure]
    exact hfin roots ptr folds m hf
  | succ n ih =>
    intro c roots ptr folds m hc h
    have hc7 : c < 7 := by omega
    have hl : LeafIn F c 0 roots [] ptr folds m := by unfold NextIn at h; rwa [if_pos hc7] at h
    rw [List.range'_succ, List.foldlM_cons]
    show GoodQ m _ _ _ _ (ccM ((ftsCoordP F.w F.idx c (F.sel c) ptr >>= coordNext' roots) >>= fun s =>
      List.foldlM (ftsStep F) s (List.range' (c + 1) n)) R7)
    rw [bind_assoc, ccM_bind]
    refine coord_good F c roots ptr folds m hl _ ?_ Bf Af Q (fun root ptr' folds' u hn => ?_)
    · simp only [coordNext', pure_bind, foldlM_none, ccM_pure, hR7]
    · simp only [coordNext', pure_bind]
      exact ih (c + 1) (roots ++ [root]) ptr' folds' u (by omega) hn

/-- The pointer cap and the forest pk. -/
theorem fin_good (F : FCtx) (R : Option Digest → OracleComp HashSpec Obs) (hR : R none = pure (false, 0))
    (Bf Af : Nat) (Q : Prop) (hout : ∀ root u, FtsOut F root u → GoodQ u Bf Bf Q Af (R (some root))) :
    ∀ roots ptr folds m, ForestIn F roots ptr folds m →
      GoodQ m (Bf + 24) (Bf + 24) (Q ∧ folds ≤ 124) (Af + 24 + 16 * (124 - folds))
        (ccM (ftsFin F (some (roots, ptr))) R) := by
  intro roots ptr folds m h
  obtain ⟨fRej, fOk⟩ := forest_step F roots ptr folds m h
  have hp := h.hptr
  simp only [ftsFin]
  by_cases hgt : 124 < folds
  · rw [if_pos (by unfold streamEnd; omega), ccM_pure, hR]
    obtain ⟨u, hu, hh⟩ := fRej hgt
    exact GoodQ.rejectAfter hu hh (by omega) (by omega)
  · rw [if_neg (by unfold streamEnd; omega)]
    obtain ⟨u, hu, hf, h5, hv, hin, hout'⟩ := fOk (by omega)
    rw [forestPk_eq]
    have hg := GoodQ.shortHash_bind (N := Bf) (C := Bf) (A := Af) (Q := Q) (f := fun r => pure (some r)) (K := R)
      hf h5 hv hin (fun ans => by simp only [ccM_pure]; exact hout _ _ (hout' ans))
    rw [blocks_forestInput F.idx roots h.hroots] at hg
    exact GoodQ.steps' hu hg (by omega) (by omega) (fun q => ⟨⟨q, by omega⟩, by omega⟩)

/-- **The FTS stream machine refines `ftsP`**: from `SelIn` (after the selections), 7214 cycles on every oracle;
accepting runs take at most 2912 = 928 + 16 · 124 cycles to `FtsOut`. -/
theorem fts_good (pk : Digest) (w : WBytes) (a : HashOutput) (t : MachineState) (ht : SelIn pk w a 7 t)
    (R : Option Digest → OracleComp HashSpec Obs) (hR : R none = pure (false, 0)) (Bf Af : Nat) (Q : Prop)
    (hout : ∀ root u, FtsOut ⟨pk, w, a⟩ root u → GoodQ u Bf Bf Q Af (R (some root))) :
    GoodQ t (Bf + 7214) (Bf + 7214) Q (Af + 2912) (ccM (ftsP w (a.toNat % 2 ^ 31) (selections a)) R) := by
  obtain ⟨u, hu, hl⟩ := fts_setup_step pk w a t ht
  have e : ftsP w (a.toNat % 2 ^ 31) (selections a) =
      List.foldlM (ftsStep ⟨pk, w, a⟩) (some ([], 1088)) (List.range 7) >>= ftsFin ⟨pk, w, a⟩ :=
    ftsP_eq ⟨pk, w, a⟩
  rw [e, ccM_bind, List.range_eq_range']
  have hn : NextIn ⟨pk, w, a⟩ 0 [] 1088 0 u := by unfold NextIn; rw [if_pos (by omega)]; exact hl
  have hc := coords_good ⟨pk, w, a⟩ (fun s => ccM (ftsFin ⟨pk, w, a⟩ s) R) (by simp only [ftsFin, ccM_pure, hR])
    Bf Af Q (fin_good ⟨pk, w, a⟩ R hR Bf Af Q hout) 7 0 [] 1088 0 u (by omega) hn
  have ce : Cent 0 = 7196 := rfl
  have ae : Aent 0 = 910 := rfl
  exact GoodQ.steps' hu hc (by omega) (by omega) (fun q => ⟨q.1, by omega⟩)

/-- `afterSel` (V2's interface of `verifyP_good_sel`) from the layers phase at `FtsOut`. -/
theorem afterSel_good (pk : Digest) (w : WBytes) (Bf Af : Nat) (Q : Prop)
    (hout : ∀ a root u, FtsOut ⟨pk, w, a⟩ root u →
      GoodQ u Bf Bf Q Af (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb)) :
    ∀ a t, SelIn pk w a 7 t → GoodQ t (Bf + 7214) (Bf + 7214) Q (Af + 2912) (ccM (afterSel pk w a) Kb) := by
  intro a t ht
  unfold afterSel
  rw [ccM_bind]
  exact fts_good pk w a t ht _ (by simp only [afterFts, ccM_pure, Kb]) Bf Af Q (hout a)

/-- **`verifyP` from the initial state up to the layers phase**: given the layers phase (V1/V3: layers 3..0 and the
comparison, `afterFts`) from `FtsOut`, the whole verify run. Accepting cycles through the forest HASH:
`184 + 2912 = 3096` (`128 + P` with `P ≤ 56` for the words 0..358, `928 + 16 F` with `F ≤ 124` for the FTS). -/
theorem verifyP_good_fts (m : T3.Message) (pk : Digest) (w : WBytes) (s : MachineState) (hs : InitOK m pk w s)
    (Bf Af : Nat) (Q : Prop)
    (hout : ∀ a root u, FtsOut ⟨pk, w, a⟩ root u →
      GoodQ u Bf Bf Q Af (ccM (afterFts pk w (a.toNat % 2 ^ 31) (some root)) Kb)) :
    GoodQ s (Bf + 7400) (Bf + 7407) Q (Af + 3096) (ccM (verifyP m pk w) Kb) :=
  (verifyP_good_sel m pk w s hs (afterSel_good pk w Bf Af Q hout)).mono (by omega) (by omega)
    (fun q => ⟨q, by omega⟩)

end SigGolfCandidate.T3M.Verify
