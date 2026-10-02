import SigGolfCandidate.T3M.Witness.Dfs

/-! # The stream machine on a matching stream (stream W)

On a coordinate whose five segment headers match the schedule, `ftsCoordP` (the W2 stack machine) issues exactly
the queries of `coordCanon` with the sibling values and pads read from the stream (`ftsCoordP_canon`). -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Folds -/

/-- The stream's sibling and pad of fold `r` of the segment at `ptr` agree with `val`/`pad` at the sibling of the
level-`k` ancestor of `g`. -/
def FoldOk (w : WBytes) (val pad : Nat × Nat → Digest) (g k ptr r : Nat) : Prop :=
  val (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + sibOff (g / 2 ^ k % 2)) ∧
    pad (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + 32)

/-- `a` folds from fold index `r0` of the segment at `ptr`, starting at the level-`k` ancestor of `g`, climb. -/
theorem folds_climb (w : WBytes) (index coord ptr : Nat) (val pad : Nat × Nat → Digest) (g : Nat) :
    ∀ (a r0 k : Nat) (v : Digest), k + a ≤ 11 → (∀ r < a, FoldOk w val pad g (k + r) ptr (r0 + r)) →
      (List.range' r0 a).foldlM (foldStep w index coord ptr) (v, (2048 + g) / 2 ^ k) =
        (fun v' => (v', (2048 + g) / 2 ^ (k + a))) <$> climbV index coord val pad g k a v := by
  intro a
  induction a with
  | zero => intro r0 k v _ _; simp
  | succ a ih =>
      intro r0 k v hk hok
      have h0 := hok 0 (by omega)
      simp only [Nat.add_zero] at h0
      obtain ⟨hv, hp⟩ := h0
      rw [List.range'_succ, List.foldlM_cons, climbV_succ, map_bind]
      have hmod := heap_mod_two (g := g) (show k < 11 by omega)
      have hpar := heap_parent (g := g) (show k < 11 by omega)
      have hdiv := heap_div_two g k
      have hrest := fun x => ih (r0 + 1) (k + 1) x (by omega) (fun r hr => by
        have := hok (r + 1) (by omega); simpa only [Nat.add_assoc, Nat.add_comm 1 r] using this)
      have hstep : foldStep w index coord ptr (v, (2048 + g) / 2 ^ k) r0 =
          (fun p => (p, (2048 + g) / 2 ^ (k + 1))) <$> climbStep index coord val pad g k v := by
        unfold foldStep climbStep
        rcases Nat.mod_two_eq_zero_or_one (g / 2 ^ k) with hg | hg
        · simp only [sibOff, hg, show (0 : Nat) ≠ 1 by decide, if_false] at hv
          simp only [hmod, hg, show (0 : Nat) ≠ 1 by decide, if_false, hpar, hv, hp, map_eq_bind_pure_comp,
            Function.comp_def, ← hdiv]
        · simp only [sibOff, hg, if_true, Nat.add_zero] at hv
          simp only [hmod, hg, if_true, hpar, hv, hp, map_eq_bind_pure_comp, Function.comp_def, ← hdiv]
      rw [hstep, bind_map_left]
      congr 1; funext x
      rw [hrest x, show k + 1 + a = k + (a + 1) by omega]

theorem foldsP_climb (w : WBytes) (index coord ptr : Nat) (val pad : Nat × Nat → Digest) (g a k : Nat)
    (v : Digest) (hk : k + a ≤ 11) (hok : ∀ r < a, FoldOk w val pad g (k + r) ptr r) :
    foldsP w index coord ptr a v ((2048 + g) / 2 ^ k) =
      (fun v' => (v', (2048 + g) / 2 ^ (k + a))) <$> climbV index coord val pad g k a v := by
  unfold foldsP
  rw [List.range_eq_range']
  exact folds_climb w index coord ptr val pad g a 0 k v hk (fun r hr => by simpa using hok r hr)

/-! ## Segments -/

/-- A header byte claiming `A ≤ 11` folds with the right parity. -/
structure HdrOk (b A merge E : Nat) : Prop where
  a : b % 16 = A
  le : A ≤ 11
  m : b / 16 % 2 = merge
  t : 0 < A → b / 32 % 2 = E % 2

/-- A segment without merge (or on an empty stack, which must not merge). -/
theorem segLoop_stop (w : WBytes) (index coord : Nat) (stack : List (Digest × Nat)) (pending : Pending)
    (E ptr A : Nat) (node : Digest) (h : HdrOk (wbyte w ptr).toNat A 0 E) :
    segLoop w index coord stack pending E ptr node = (do
      let n ← pendingHash w index coord node pending
      let r ← foldsP w index coord ptr A n E
      pure (some (r.1, r.2, segNext ptr A, stack))) := by
  rw [segLoop.eq_1]
  have h1 : ¬ 11 < A := Nat.not_lt.mpr h.le
  have h2 : ¬ (0 < A ∧ (wbyte w ptr).toNat / 32 % 2 ≠ E % 2) := by
    rintro ⟨hp, hne⟩; exact hne (h.t hp)
  simp only [h.a, h.m]
  rw [if_neg h1, if_neg h2]
  congr 1; funext n; congr 1; funext r
  rcases stack with _ | ⟨⟨pn, Q⟩, rest⟩ <;> simp

/-- A segment that merges with the stacked node `(pnode, Q)`. -/
theorem segLoop_merge (w : WBytes) (index coord : Nat) (pnode : Digest) (Q : Nat) (rest : List (Digest × Nat))
    (pending : Pending) (E ptr A : Nat) (node : Digest) (h : HdrOk (wbyte w ptr).toNat A 1 E) :
    segLoop w index coord ((pnode, Q) :: rest) pending E ptr node = (do
      let n ← pendingHash w index coord node pending
      let r ← foldsP w index coord ptr A n E
      if Q ≠ r.2 then pure none
      else segLoop w index coord rest (.merge (r.2 / 2) pnode) (r.2 / 2) (segNext ptr A) r.1) := by
  rw [segLoop.eq_1]
  have h1 : ¬ 11 < A := Nat.not_lt.mpr h.le
  have h2 : ¬ (0 < A ∧ (wbyte w ptr).toNat / 32 % 2 ≠ E % 2) := by
    rintro ⟨hp, hne⟩; exact hne (h.t hp)
  simp only [h.a, h.m]
  rw [if_neg h1, if_neg h2]
  simp

/-! ## Segments in climb form -/

section seg
variable (w : WBytes) (index coord : Nat) (val pad : Nat × Nat → Digest)

/-- A stopping segment of `a` folds from the level-`k` ancestor of `g`. -/
theorem seg_stop (stack : List (Digest × Nat)) (pending : Pending) (g k ptr A : Nat) (node : Digest)
    (hdr : HdrOk (wbyte w ptr).toNat A 0 ((2048 + g) / 2 ^ k)) (hk : k + A ≤ 11)
    (hf : ∀ r < A, FoldOk w val pad g (k + r) ptr r) :
    segLoop w index coord stack pending ((2048 + g) / 2 ^ k) ptr node =
      (fun v => some (v, (2048 + g) / 2 ^ (k + A), segNext ptr A, stack)) <$>
        (pendingHash w index coord node pending >>= climbV index coord val pad g k A) := by
  rw [segLoop_stop w index coord stack pending _ ptr A node hdr]
  simp only [map_bind]
  congr 1; funext n
  rw [foldsP_climb w index coord ptr val pad g A k n hk hf]
  simp [map_eq_bind_pure_comp]

/-- A merging segment: after `a` folds the stacked `Q` must be the current heap; then the merge is pending. -/
theorem seg_merge (pnode : Digest) (Q : Nat) (rest : List (Digest × Nat)) (pending : Pending) (g k ptr A : Nat)
    (node : Digest) (hdr : HdrOk (wbyte w ptr).toNat A 1 ((2048 + g) / 2 ^ k)) (hk : k + A ≤ 11)
    (hf : ∀ r < A, FoldOk w val pad g (k + r) ptr r) (hQ : Q = (2048 + g) / 2 ^ (k + A)) :
    segLoop w index coord ((pnode, Q) :: rest) pending ((2048 + g) / 2 ^ k) ptr node =
      (pendingHash w index coord node pending >>= climbV index coord val pad g k A) >>= fun v =>
        segLoop w index coord rest (.merge ((2048 + g) / 2 ^ (k + A + 1)) pnode) ((2048 + g) / 2 ^ (k + A + 1))
          (segNext ptr A) v := by
  rw [segLoop_merge w index coord pnode Q rest pending _ ptr A node hdr, bind_assoc]
  congr 1; funext n
  rw [foldsP_climb w index coord ptr val pad g A k n hk hf]
  simp [hQ, heap_div_two]

end seg

/-- `Segment.Matches` gives the machine's header conditions at the segment's start heap. -/
theorem hdrOk_of_matches {seg : Segment} {b : Nat} (h : seg.Matches b) (hle : seg.a ≤ 11) :
    HdrOk b seg.a (if seg.merge then 1 else 0) ((2048 + seg.g) / 2 ^ seg.lo) where
  a := h.1
  le := hle
  m := by
    have := h.2.1
    cases hm : seg.merge <;> simp [hm] at this ⊢ <;> omega
  t := fun hp => by have := h.2.2 hp; simpa [Segment.t, Segment.heap] using this

/-- A segment's stream reads agree with `val`/`pad` and its header matches. -/
def SegOk (w : WBytes) (val pad : Nat × Nat → Digest) (seg : Segment) (ptr : Nat) : Prop :=
  seg.Matches (wbyte w ptr).toNat ∧ ∀ r < seg.a, FoldOk w val pad seg.g (seg.lo + r) ptr r

/-- Every segment of a list is `SegOk` at its pointer. -/
def SegsOk (w : WBytes) (val pad : Nat × Nat → Digest) : Nat → List Segment → Prop
  | _, [] => True
  | ptr, s :: rest => SegOk w val pad s ptr ∧ SegsOk w val pad (segNext ptr s.a) rest

/-- The pointer after a segment list. -/
def segsEnd : Nat → List Segment → Nat
  | ptr, [] => ptr
  | ptr, s :: rest => segsEnd (segNext ptr s.a) rest

/-- The leaf hash of a stream coordinate (slot `3 coord + j` for the `j`-th leaf of `gs`). -/
def leafAt (w : WBytes) (index coord : Nat) (gs : List Nat) (g : Nat) : M Digest :=
  pendingHash w index coord 0 (.leaf (3 * coord + gs.idxOf g) g)

/-- `coordCanon` only depends on `leafH` at the three leaves. -/
theorem coordCanon_congr_leaf {index coord : Nat} {leafH leafH' : Nat → M Digest} {val pad : Nat × Nat → Digest}
    {g0 g1 g2 : Nat} (h0 : leafH g0 = leafH' g0) (h1 : leafH g1 = leafH' g1) (h2 : leafH g2 = leafH' g2) :
    coordCanon index coord leafH val pad g0 g1 g2 = coordCanon index coord leafH' val pad g0 g1 g2 := by
  unfold coordCanon; rw [h0, h1, h2]

/-! ## One coordinate -/

/-- **Schedule ≡ DFS (stream side).** On a coordinate whose five segments are `SegOk`, the stream machine is the
canonical coordinate program with the stream's siblings and pads; it ends at `segsEnd` with heap 1 and an empty
stack. -/
theorem ftsCoordP_canon (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat)
    (val pad : Nat × Nat → Digest) (hb : sel.bucket < 8) (h2 : sel.leaves.getD 2 0 < 256)
    (h01 : sel.leaves.getD 0 0 < sel.leaves.getD 1 0) (h12 : sel.leaves.getD 1 0 < sel.leaves.getD 2 0)
    (hok : SegsOk w val pad ptr (coordSchedule coord sel)) :
    ftsCoordP w index coord sel ptr =
      (fun v => some (v, segsEnd ptr (coordSchedule coord sel))) <$>
        coordCanon index coord (leafAt w index coord [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2]) val pad
          (selLeaf sel 0) (selLeaf sel 1) (selLeaf sel 2) := by
  unfold ftsCoordP
  unfold coordSchedule at hok ⊢
  unfold coordCanon
  simp only [] at hok ⊢
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; omega
  have g2l : selLeaf sel 2 < 2048 := by unfold selLeaf; omega
  have bk0 : selLeaf sel 0 / 2 ^ 8 = sel.bucket := bucket_div_eight (by omega)
  have bk1 : selLeaf sel 1 / 2 ^ 8 = sel.bucket := bucket_div_eight (by omega)
  have bk2 : selLeaf sel 2 / 2 ^ 8 = sel.bucket := bucket_div_eight (by omega)
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 8 := (div_eq_iff_lca (by omega) 8).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 8 := (div_eq_iff_lca (by omega) 8).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have i0 : [g0, g1, g2].idxOf g0 = 0 := by simp
  have i1 : [g0, g1, g2].idxOf g1 = 1 := by simp [List.idxOf_cons_ne _ (show g0 ≠ g1 by omega)]
  have i2 : [g0, g1, g2].idxOf g2 = 2 := by
    simp [List.idxOf_cons_ne _ (show g0 ≠ g2 by omega), List.idxOf_cons_ne _ (show g1 ≠ g2 by omega)]
  have lf : ∀ j g (nd : Digest), j < 3 → [g0, g1, g2].idxOf g = j →
      pendingHash w index coord nd (.leaf (3 * coord + j) g) = leafAt w index coord [g0, g1, g2] g := by
    intro j g nd _ hj; unfold leafAt; rw [hj]; rfl
  have lf0 : ∀ (nd : Digest), pendingHash w index coord nd (.leaf (3 * coord) g0) =
      leafAt w index coord [g0, g1, g2] g0 := by
    intro nd; have := lf 0 g0 nd (by omega) i0; simpa using this
  have e0 : ∀ g, 2048 + g = (2048 + g) / 2 ^ 0 := by intro g; simp
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · simp only [if_pos hA] at hok ⊢
    simp only [SegsOk, SegOk, segsEnd, Nat.zero_add] at hok ⊢
    obtain ⟨⟨m0, f0⟩, ⟨m1, f1⟩, ⟨m2, f2⟩, ⟨m3, f3⟩, ⟨m4, f4⟩, -⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    -- leaf 0: stop with empty stack
    rw [e0 g0, seg_stop w index coord val pad [] _ g0 0 _ (d01 - 1) 0 H0 (by omega) (by simpa using f0)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf0]
    congr 1; funext v0; congr 1; funext v0'
    -- leaf 1: merge with leaf 0's node, then the merged node climbs and stops
    have hq1 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g1) / 2 ^ (0 + (d01 - 1)) := by
      rw [Nat.zero_add]; exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g1, seg_merge w index coord val pad v0' _ [] _ g1 0 _ (d01 - 1) v0' H1 (by omega)
      (by simpa using f1) hq1]
    simp only [Nat.zero_add, show d01 - 1 + 1 = d01 by omega, bind_assoc]
    rw [lf 1 g1 v0' (by omega) i1]
    congr 1; funext v1; congr 1; funext v1'
    rw [seg_stop w index coord val pad [] _ g1 d01 _ (d12 - 1 - d01) _ (by simpa using H2) (by omega)
      (by simpa using f2)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d01 ≤ 11 by omega)]
    congr 1; funext mm; congr 1; funext mm'
    -- leaf 2: merge with the merged node, then climb to the root and stop
    have hq3 : (2048 + g1) / 2 ^ (d01 + (d12 - 1 - d01)) ^^^ 1 = (2048 + g2) / 2 ^ (0 + (d12 - 1)) := by
      rw [show d01 + (d12 - 1 - d01) = d12 - 1 by omega, Nat.zero_add]
      exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g2, seg_merge w index coord val pad mm' _ [] _ g2 0 _ (d12 - 1) mm' H3 (by omega)
      (by simpa using f3) hq3]
    simp only [Nat.zero_add, show d12 - 1 + 1 = d12 by omega, bind_assoc]
    rw [lf 2 g2 mm' (by omega) i2]
    congr 1; funext v2; congr 1; funext v2'
    rw [seg_stop w index coord val pad [] _ g2 d12 _ (11 - d12) _ (by simpa using H4) (by omega)
      (by simpa using f4)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d12 ≤ 11 by omega)]
    congr 1; funext r
    have hroot : (2048 + g2) / 2 ^ (d12 + (11 - d12)) = 1 := by
      rw [show d12 + (11 - d12) = 11 by omega]; omega
    simp only [hroot, and_self, if_true, map_eq_bind_pure_comp, Function.comp_def]
  · simp only [if_neg hA] at hok ⊢
    have hB : d12 < d01 := by omega
    simp only [SegsOk, SegOk, segsEnd, Nat.zero_add] at hok ⊢
    obtain ⟨⟨m0, f0⟩, ⟨m1, f1⟩, ⟨m2, f2⟩, ⟨m3, f3⟩, ⟨m4, f4⟩, -⟩ := hok
    have H0 := hdrOk_of_matches m0 (by dsimp only; omega)
    have H1 := hdrOk_of_matches m1 (by dsimp only; omega)
    have H2 := hdrOk_of_matches m2 (by dsimp only; omega)
    have H3 := hdrOk_of_matches m3 (by dsimp only; omega)
    have H4 := hdrOk_of_matches m4 (by dsimp only; omega)
    simp only [Bool.false_eq_true, if_false, if_true] at H0 H1 H2 H3 H4
    rw [e0 g0, seg_stop w index coord val pad [] _ g0 0 _ (d01 - 1) 0 H0 (by omega) (by simpa using f0)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf0]
    congr 1; funext v0; congr 1; funext v0'
    -- leaf 1: stops with leaf 0's node stacked
    rw [e0 g1, seg_stop w index coord val pad _ _ g1 0 _ (d12 - 1) v0' H1 (by omega) (by simpa using f1)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf 1 g1 v0' (by omega) i1]
    congr 1; funext v1; congr 1; funext v1'
    -- leaf 2: merges twice, then climbs to the root
    have hq2 : (2048 + g1) / 2 ^ (d12 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (0 + (d12 - 1)) := by
      rw [Nat.zero_add]; exact heap_sib (by omega) (by omega) (by omega)
    rw [e0 g2, seg_merge w index coord val pad v1' _ _ _ g2 0 _ (d12 - 1) v1' H2 (by omega)
      (by simpa using f2) hq2]
    simp only [Nat.zero_add, show d12 - 1 + 1 = d12 by omega, bind_assoc]
    rw [lf 2 g2 v1' (by omega) i2]
    congr 1; funext v2; congr 1; funext v2'
    have hq3 : (2048 + g0) / 2 ^ (d01 - 1) ^^^ 1 = (2048 + g2) / 2 ^ (d12 + (d01 - 1 - d12)) := by
      rw [show d12 + (d01 - 1 - d12) = d01 - 1 by omega]
      exact heap_sib (by omega) (by omega) (by rw [l02]; omega)
    rw [seg_merge w index coord val pad v0' _ [] _ g2 d12 _ (d01 - 1 - d12) _ (by simpa using H3) (by omega)
      (by simpa using f3) hq3]
    simp only [show d12 + (d01 - 1 - d12) + 1 = d01 by omega, bind_assoc, pendingHash,
      heap_eq (show d12 ≤ 11 by omega)]
    congr 1; funext mm; congr 1; funext mm'
    rw [seg_stop w index coord val pad [] _ g2 d01 _ (11 - d01) _ (by simpa using H4) (by omega)
      (by simpa using f4)]
    simp only [map_bind, bind_map_left, bind_assoc, pendingHash, heap_eq (show d01 ≤ 11 by omega)]
    congr 1; funext nn
    have hroot : (2048 + g2) / 2 ^ (d01 + (11 - d01)) = 1 := by
      rw [show d01 + (11 - d01) = 11 by omega]; omega
    simp only [hroot, and_self, if_true, map_eq_bind_pure_comp, Function.comp_def]

end SigGolfCandidate.T3M
