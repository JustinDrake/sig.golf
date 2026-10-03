import SigGolfCandidate.T3M.Witness.Dfs
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3M.Witness.Encode

section

namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def FoldOk (w : WBytes) (val pad : Nat × Nat → Digest) (g k ptr r : Nat) : Prop :=
  val (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + sibOff (g / 2 ^ k % 2)) ∧
    pad (k, g / 2 ^ k ^^^ 1) = wdig w (foldBlock ptr r + 32)
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
structure HdrOk (b A merge E : Nat) : Prop where
  a : b % 16 = A
  le : A ≤ 11
  m : b / 16 % 2 = merge
  t : 0 < A → b / 32 % 2 = E % 2
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
section seg
variable (w : WBytes) (index coord : Nat) (val pad : Nat × Nat → Digest)
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
theorem hdrOk_of_matches {seg : Segment} {b : Nat} (h : seg.Matches b) (hle : seg.a ≤ 11) :
    HdrOk b seg.a (if seg.merge then 1 else 0) ((2048 + seg.g) / 2 ^ seg.lo) where
  a := h.1
  le := hle
  m := by
    have := h.2.1
    cases hm : seg.merge <;> simp [hm] at this ⊢ <;> omega
  t := fun hp => by have := h.2.2 hp; simpa [Segment.t, Segment.heap] using this
def SegOk (w : WBytes) (val pad : Nat × Nat → Digest) (seg : Segment) (ptr : Nat) : Prop :=
  seg.Matches (wbyte w ptr).toNat ∧ ∀ r < seg.a, FoldOk w val pad seg.g (seg.lo + r) ptr r
def SegsOk (w : WBytes) (val pad : Nat × Nat → Digest) : Nat → List Segment → Prop
  | _, [] => True
  | ptr, s :: rest => SegOk w val pad s ptr ∧ SegsOk w val pad (segNext ptr s.a) rest
def segsEnd : Nat → List Segment → Nat
  | ptr, [] => ptr
  | ptr, s :: rest => segsEnd (segNext ptr s.a) rest
def leafAt (w : WBytes) (index coord : Nat) (gs : List Nat) (g : Nat) : M Digest :=
  pendingHash w index coord 0 (.leaf (3 * coord + gs.idxOf g) g)
theorem coordCanon_congr_leaf {index coord : Nat} {leafH leafH' : Nat → M Digest} {val pad : Nat × Nat → Digest}
    {g0 g1 g2 : Nat} (h0 : leafH g0 = leafH' g0) (h1 : leafH g1 = leafH' g1) (h2 : leafH g2 = leafH' g2) :
    coordCanon index coord leafH val pad g0 g1 g2 = coordCanon index coord leafH' val pad g0 g1 g2 := by
  unfold coordCanon; rw [h0, h1, h2]
theorem ftsCoordP_canon (w : WBytes) (index coord : Nat) (sel : Selection) (ptr : Nat)
    (val pad : Nat × Nat → Digest) (hb : sel.bucket < 16) (h2 : sel.leaves.getD 2 0 < 128)
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
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight (by omega)
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
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
    rw [e0 g0, seg_stop w index coord val pad [] _ g0 0 _ (d01 - 1) 0 H0 (by omega) (by simpa using f0)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf0]
    congr 1; funext v0; congr 1; funext v0'
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
    rw [e0 g1, seg_stop w index coord val pad _ _ g1 0 _ (d12 - 1) v0' H1 (by omega) (by simpa using f1)]
    simp only [map_bind, bind_map_left, bind_assoc, Nat.zero_add]
    rw [lf 1 g1 v0' (by omega) i1]
    congr 1; funext v1; congr 1; funext v1'
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
end

section


namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem hasLeaf_up {leaves : List Nat} {j n : Nat} (h : hasLeaf leaves j n = true) (d : Nat) :
    hasLeaf leaves (j + d) (n / 2 ^ d) = true := by
  obtain ⟨leaf, hm, he⟩ := (hasLeaf_iff _ _ _).mp h
  exact (hasLeaf_iff _ _ _).mpr ⟨leaf, hm, by rw [pow_add, ← Nat.div_div_eq_div_mul, he]⟩
theorem frontier_inside {leaves : List Nat} : ∀ L N p, p ∈ T3.frontier leaves L N →
    p.1 ≤ L ∧ p.2 / 2 ^ (L - p.1) = N := by
  intro L
  induction L with
  | zero =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp; subst hp; simp
  | succ L ih =>
      intro N p hp
      simp only [T3.frontier] at hp
      split at hp
      · rcases List.mem_append.mp hp with h | h
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
        · obtain ⟨h1, h2⟩ := ih _ _ h
          refine ⟨by omega, ?_⟩
          rw [show L + 1 - p.1 = (L - p.1) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul, h2]; omega
      · simp only [List.mem_singleton] at hp; subst hp; simp
theorem frontier_nodup {leaves : List Nat} : ∀ L N, (T3.frontier leaves L N).Nodup := by
  intro L
  induction L with
  | zero => intro N; simp only [T3.frontier]; split <;> simp
  | succ L ih =>
      intro N
      simp only [T3.frontier]
      split
      · refine List.nodup_append.mpr ⟨ih _, ih _, ?_⟩
        intro a ha b hb hab
        subst hab
        have h1 := (frontier_inside _ _ _ ha).2
        have h2 := (frontier_inside _ _ _ hb).2
        omega
      · simp
theorem frontier_mem {leaves : List Nat} : ∀ L N k s, k ≤ L → s / 2 ^ (L - k) = N →
    hasLeaf leaves k s = false → (k = L ∨ hasLeaf leaves (k + 1) (s / 2) = true) →
    (k, s) ∈ T3.frontier leaves L N := by
  intro L
  induction L with
  | zero =>
      intro N k s hk hN he _
      obtain rfl : k = 0 := by omega
      simp only [Nat.sub_zero, pow_zero, Nat.div_one] at hN; subst hN
      simp [T3.frontier, he]
  | succ L ih =>
      intro N k s hk hN he hp
      by_cases hkL : k = L + 1
      · subst hkL
        simp only [Nat.sub_self, pow_zero, Nat.div_one] at hN; subst hN
        simp [T3.frontier, he]
      · have hp' : hasLeaf leaves (k + 1) (s / 2) = true := by rcases hp with h | h; omega; exact h
        have hup := hasLeaf_up hp' (L - k)
        have hsN : s / 2 / 2 ^ (L - k) = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ', show L - k + 1 = L + 1 - k by omega, hN]
        rw [show k + 1 + (L - k) = L + 1 by omega, hsN] at hup
        simp only [T3.frontier, hup, ite_true]
        have hdiv : s / 2 ^ (L - k) / 2 = N := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show L - k + 1 = L + 1 - k by omega, hN]
        rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ (L - k)) with h2 | h2
        · exact List.mem_append_left _ (ih (2 * N) k s (by omega) (by omega) he (Or.inr hp'))
        · exact List.mem_append_right _ (ih (2 * N + 1) k s (by omega) (by omega) he (Or.inr hp'))
theorem slotPositions_nodup (sel : Selection) : (slotPositions sel).Nodup := by
  unfold slotPositions
  refine List.nodup_append.mpr ⟨frontier_nodup _ _, ?_, ?_⟩
  · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.singleton_append, List.cons_append]
    simp
  · intro a ha b hb hab
    subst hab
    have h1 := frontier_inside _ _ _ ha
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    simp only at h1
    rcases j with _ | j
    · simp only [Nat.add_zero, Nat.sub_self, pow_zero, Nat.div_one] at h1
      exact xor_one_ne _ h1.2
    · omega
theorem sib_eq_imp {g g' k k' : Nat} (h : (k, g / 2 ^ k ^^^ 1) = (k', g' / 2 ^ k' ^^^ 1)) :
    k = k' ∧ (g = g' ∨ (g ≠ g' ∧ lcaLevel g g' ≤ k)) := by
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  refine ⟨rfl, ?_⟩
  by_cases hg : g = g'
  · exact Or.inl hg
  · refine Or.inr ⟨hg, (div_eq_iff_lca hg k).mp ?_⟩
    have := congrArg (· ^^^ 1) h
    simpa only [xor_one_xor_one] using this
structure SelOk (sel : Selection) : Prop where
  len : sel.leaves.length = 3
  b : sel.bucket < 16
  l2 : sel.leaves.getD 2 0 < 128
  s01 : sel.leaves.getD 0 0 < sel.leaves.getD 1 0
  s12 : sel.leaves.getD 1 0 < sel.leaves.getD 2 0
theorem SelOk.leaves_eq {sel : Selection} (h : SelOk sel) :
    sel.leaves = [sel.leaves.getD 0 0, sel.leaves.getD 1 0, sel.leaves.getD 2 0] := by
  have := h.len
  match hl : sel.leaves, this with
  | [a, b, c], _ => simp
theorem SelOk.selected {sel : Selection} (h : SelOk sel) :
    selectedLeaves sel = [selLeaf sel 0, selLeaf sel 1, selLeaf sel 2] := by
  unfold selectedLeaves selLeaf; rw [h.leaves_eq]; simp
structure FoldFacts (leaves : List Nat) (segs : List Segment) : Prop where
  empty : ∀ i < 5, ∀ r < (segs.getD i default).a,
    hasLeaf leaves ((segs.getD i default).lo + r)
      ((segs.getD i default).g / 2 ^ ((segs.getD i default).lo + r) ^^^ 1) = false
  top : ∀ i < 5, (segs.getD i default).lo + (segs.getD i default).a ≤ 11
  leaf : ∀ i < 5, (segs.getD i default).g ∈ leaves
  inj : ∀ i < 5, ∀ i' < 5, ∀ r < (segs.getD i default).a, ∀ r' < (segs.getD i' default).a,
    (segs.getD i default).sib r = (segs.getD i' default).sib r' → i = i' ∧ r = r'
  len : segs.length = 5
theorem foldFacts (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    FoldFacts (selectedLeaves sel) (coordSchedule coord sel) := by
  have hsel := hs.selected
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have bk0 : selLeaf sel 0 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s01; have := hs.s12; have := hs.l2; omega)
  have bk1 : selLeaf sel 1 / 2 ^ 7 = sel.bucket := bucket_div_eight (by have := hs.s12; have := hs.l2; omega)
  have bk2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := bucket_div_eight hs.l2
  unfold coordSchedule
  rw [hsel]
  simp only []
  generalize selLeaf sel 0 = g0 at *
  generalize selLeaf sel 1 = g1 at *
  generalize selLeaf sel 2 = g2 at *
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk0, bk1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [bk1, bk2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer g01 g12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne g01 g12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  have sib : ∀ g k, (∀ g' ∈ [g0, g1, g2], g' ≠ g → lcaLevel g g' ≠ k + 1) →
      hasLeaf [g0, g1, g2] k (g / 2 ^ k ^^^ 1) = false := fun g k h => hasLeaf_sib_false h
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · simp only [if_pos hA]
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)
  · simp only [if_neg hA]
    have hB : d12 < d01 := by omega
    refine ⟨?_, ?_, ?_, ?_, by simp⟩
    · intro i hi r hr
      interval_cases i <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hr ⊢ <;>
        apply sib <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] <;>
        rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' |
          (simp only [c10, c21, c20, l02, hd01, hd12]; omega)
    · intro i hi; interval_cases i <;> simp <;> omega
    · intro i hi; interval_cases i <;> simp
    · intro i hi i' hi' r hr r' hr' h
      interval_cases i <;> interval_cases i' <;>
        simp only [List.getD_cons_zero, List.getD_cons_succ, Segment.sib] at hr hr' h <;>
        obtain ⟨hk, hg | ⟨hg, hl⟩⟩ := sib_eq_imp h <;>
        first | omega | (simp only [c10, c21, c20, l02, hd01, hd12] at hl; omega)
theorem xor_one_div_pow (x m : Nat) (hm : 1 ≤ m) : (x ^^^ 1) / 2 ^ m = x / 2 ^ m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, xor_one_div_two]
theorem SelOk.bucket_div {sel : Selection} (hs : SelOk sel) {g : Nat} (hg : g ∈ selectedLeaves sel) :
    g / 2 ^ 7 = sel.bucket := by
  rw [hs.selected] at hg
  have := hs.s01; have := hs.s12; have := hs.l2
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> exact bucket_div_eight (by omega)
theorem fold_sib_mem (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ∀ i < 5, ∀ r < ((coordSchedule coord sel).getD i default).a,
      ((coordSchedule coord sel).getD i default).sib r ∈ slotPositions sel := by
  intro i hi r hr
  have F := foldFacts coord sel hs
  set seg := (coordSchedule coord sel).getD i default with hseg
  have hb := hs.bucket_div (F.leaf i hi)
  have htop := F.top i hi
  have hem := F.empty i hi r hr
  rw [← hseg] at hb htop hem
  unfold slotPositions Segment.sib
  by_cases hk : seg.lo + r < 7
  · apply List.mem_append_left
    apply frontier_mem 7 sel.bucket _ _ (by omega)
    · rw [xor_one_div_pow _ _ (by omega), Nat.div_div_eq_div_mul, ← pow_add,
        show seg.lo + r + (7 - (seg.lo + r)) = 7 by omega, hb]
    · exact hem
    · right
      rw [xor_one_div_two, Nat.div_div_eq_div_mul, ← pow_succ]
      exact hasLeaf_self (F.leaf i hi) _
  · apply List.mem_append_right
    simp only [List.mem_map, List.mem_range]
    refine ⟨seg.lo + r - 7, by omega, ?_⟩
    have e : seg.g / 2 ^ (seg.lo + r) = sel.bucket / 2 ^ (seg.lo + r - 7) := by
      rw [show seg.lo + r = 7 + (seg.lo + r - 7) by omega, pow_add, ← Nat.div_div_eq_div_mul, hb]
      simp
    rw [e, show 7 + (seg.lo + r - 7) = seg.lo + r by omega]
theorem SelOk.exists {sel : Selection} (h : SelOk sel) :
    ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 ∧ x2 < 128 := by
  have hl := h.leaves_eq
  refine ⟨_, _, _, hl, h.s01, h.s12, h.l2⟩
theorem coord_fold_count (coord : Nat) (sel : Selection) (hs : SelOk sel) :
    ((coordSchedule coord sel).map Segment.a).sum = (slotPositions sel).length := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  have hf := Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb
  unfold slotPositions selectedLeaves
  rw [List.length_append, hf]
  simp only [List.length_map, List.length_range]
  have ha : authCount sel.leaves = 3 + lcaLevel x0 x1 + lcaLevel x1 x2 := by
    rw [hl]; simp [authCount, lcaLevel]; omega
  rw [ha]
  have e01 := lca_bucket (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have e12 := lca_bucket (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have l01 := lca_le_eight (b := sel.bucket) (show x0 < 128 by omega) (show x1 < 128 by omega) (by omega)
  have l12 := lca_le_eight (b := sel.bucket) (show x1 < 128 by omega) h2 (by omega)
  have p01 := lcaLevel_pos (sel.bucket * 128 + x0) (sel.bucket * 128 + x1)
  have p12 := lcaLevel_pos (sel.bucket * 128 + x1) (sel.bucket * 128 + x2)
  have hne := lca_ne (show sel.bucket * 128 + x0 < sel.bucket * 128 + x1 by omega)
    (show sel.bucket * 128 + x1 < sel.bucket * 128 + x2 by omega)
  unfold coordSchedule selLeaf
  simp only [hl, List.getD_cons_zero, List.getD_cons_succ]
  rw [e01, e12] at *
  split <;> simp <;> omega
theorem getD_flatMap_five {α : Type} (f : Nat → List α) (hf : ∀ c, (f c).length = 5) (d : α) :
    ∀ m n, n < 5 * m → ((List.range m).flatMap f).getD n d = (f (n / 5)).getD (n % 5) d := by
  intro m
  induction m with
  | zero => intro n hn; omega
  | succ m ih =>
      intro n hn
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      have hlen : ((List.range m).flatMap f).length = 5 * m := by
        rw [List.length_flatMap]; simp [hf, List.sum_replicate]; ring
      by_cases h : n < 5 * m
      · rw [List.getD_append _ _ _ _ (by omega), ih n h]
      · rw [List.getD_append_right _ _ _ _ (by omega), hlen]
        rw [show n / 5 = m by omega, show n % 5 = n - 5 * m by omega]
theorem coordSchedule_length (coord : Nat) (sel : Selection) : (coordSchedule coord sel).length = 5 := by
  unfold coordSchedule; dsimp only; split <;> rfl
theorem schedule_length (chosen : List Selection) : (schedule chosen).length = 35 := by
  unfold schedule; rw [List.length_flatMap]; simp [coordSchedule_length]
theorem schedule_getD (chosen : List Selection) {n : Nat} (hn : n < 35) :
    (schedule chosen).getD n default = (coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default :=
  getD_flatMap_five _ (fun c => coordSchedule_length _ _) default 7 n (by omega)
theorem coordSchedule_coord (coord : Nat) (sel : Selection) {i : Nat} (hi : i < 5) :
    ((coordSchedule coord sel).getD i default).coord = coord := by
  unfold coordSchedule; dsimp only; split <;> interval_cases i <;> rfl
theorem schedule_coord (chosen : List Selection) {n : Nat} (hn : n < 35) :
    ((schedule chosen).getD n default).coord = n / 5 := by
  rw [schedule_getD chosen hn, coordSchedule_coord _ _ (by omega)]
theorem slotBase_succ (chosen : List Selection) (c : Nat) :
    slotBase chosen (c + 1) = slotBase chosen c + (slotPositions (chosen.getD c ⟨0, []⟩)).length := by
  unfold slotBase; rw [List.range_succ, List.map_append, List.sum_append]; simp
theorem slotBase_mono (chosen : List Selection) {c c' : Nat} (h : c ≤ c') : slotBase chosen c ≤ slotBase chosen c' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [slotBase_succ]; omega
theorem slotBase_inj (chosen : List Selection) {c c' x x' : Nat}
    (hx : x < (slotPositions (chosen.getD c ⟨0, []⟩)).length)
    (hx' : x' < (slotPositions (chosen.getD c' ⟨0, []⟩)).length)
    (h : slotBase chosen c + x = slotBase chosen c' + x') : c = c' ∧ x = x' := by
  rcases Nat.lt_trichotomy c c' with hc | rfl | hc
  · have := slotBase_mono chosen (show c + 1 ≤ c' by omega)
    rw [slotBase_succ] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := slotBase_mono chosen (show c' + 1 ≤ c by omega)
    rw [slotBase_succ] at this; omega
def ChosenOk (chosen : List Selection) : Prop := ∀ c < 7, SelOk (chosen.getD c ⟨0, []⟩)
theorem mem_foldPositions {segs : List Segment} {p : Nat × Nat} :
    p ∈ foldPositions segs ↔ p.1 < segs.length ∧ p.2 < (segs.getD p.1 default).a := by
  obtain ⟨n, r⟩ := p
  simp only [foldPositions, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨n', hn', r', hr', rfl, rfl⟩; exact ⟨hn', hr'⟩
  · rintro ⟨hn, hr⟩; exact ⟨n, hn, r, hr, rfl, rfl⟩
theorem foldSlot_split (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a) :
    foldSlot chosen ((schedule chosen).getD n default) r =
      slotBase chosen (n / 5) + (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) ∧
    (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).idxOf
        (((coordSchedule (n / 5) (chosen.getD (n / 5) ⟨0, []⟩)).getD (n % 5) default).sib r) <
      (slotPositions (chosen.getD (n / 5) ⟨0, []⟩)).length := by
  rw [schedule_getD chosen hn] at hr ⊢
  refine ⟨?_, List.idxOf_lt_length_of_mem (fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr)⟩
  unfold foldSlot
  rw [coordSchedule_coord _ _ (by omega)]
theorem foldSlot_inj (chosen : List Selection) (hc : ChosenOk chosen) {n n' r r' : Nat} (hn : n < 35)
    (hn' : n' < 35) (hr : r < ((schedule chosen).getD n default).a) (hr' : r' < ((schedule chosen).getD n' default).a)
    (h : foldSlot chosen ((schedule chosen).getD n default) r = foldSlot chosen ((schedule chosen).getD n' default) r') :
    n = n' ∧ r = r' := by
  obtain ⟨e1, l1⟩ := foldSlot_split chosen hc hn hr
  obtain ⟨e2, l2⟩ := foldSlot_split chosen hc hn' hr'
  rw [e1, e2] at h
  obtain ⟨hcc, hx⟩ := slotBase_inj chosen l1 l2 h
  rw [schedule_getD chosen hn] at hr
  rw [schedule_getD chosen hn'] at hr'
  rw [← hcc] at hx hr'
  have hm := fold_sib_mem _ _ (hc _ (by omega)) _ (by omega) _ hr
  have hsib := (List.idxOf_inj hm).mp hx
  obtain ⟨hi, hrr⟩ := (foldFacts _ _ (hc _ (by omega))).inj _ (by omega) _ (by omega) _ hr _ hr' hsib
  exact ⟨by omega, hrr⟩
theorem find?_unique {α : Type} (l : List α) (p : α → Bool) (x : α) (hx : x ∈ l) (hp : p x = true)
    (hu : ∀ y ∈ l, p y = true → y = x) : l.find? p = some x := by
  cases h : l.find? p with
  | none => exact absurd hp (by simpa using List.find?_eq_none.mp h x hx)
  | some y => exact congrArg some (hu y (List.mem_of_find?_eq_some h) (List.find?_some h))
theorem streamPlan_foldSlot (chosen : List Selection) (hc : ChosenOk chosen) {n r : Nat} (hn : n < 35)
    (hr : r < ((schedule chosen).getD n default).a)
    (hk : foldSlot chosen ((schedule chosen).getD n default) r < 115) :
    streamPlan chosen ⟨_, hk⟩ = some (n, r) := by
  unfold streamPlan
  apply find?_unique
  · exact mem_foldPositions.mpr ⟨by rw [schedule_length]; exact hn, hr⟩
  · simp
  · rintro ⟨n', r'⟩ hy hp
    have := mem_foldPositions.mp hy
    rw [schedule_length] at this
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h1, h2⟩ := foldSlot_inj chosen hc this.1 hn this.2 hr hp
    exact Prod.ext h1 h2
end SigGolfCandidate.T3M
end

section


set_option maxRecDepth 10000
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def valOf (proof : Fin 115 → Digest) (base : Nat) (ps : List (Nat × Nat)) (p : Nat × Nat) : Digest :=
  proof ⟨(base + ps.idxOf p) % 115, Nat.mod_lt _ (by decide)⟩
theorem slotsMatch_valOf (proof : Fin 115 → Digest) (pads : Pads) (base : Nat) (ps : List (Nat × Nat))
    (hnd : ps.Nodup) : SlotsMatch proof pads (valOf proof base ps) (valOf pads.fold base ps) base ps := by
  intro i hi h
  refine ⟨?_, ?_⟩ <;> simp only [valOf, List.Nodup.idxOf_getElem hnd, Nat.mod_eq_of_lt h]
def outerStepP (sig : Signature) (pads : Pads) (index coord bucket : Nat) (state : Option (Digest × Nat)) (j : Nat) :
    M (Option (Digest × Nat)) := do
  let some (value, used) := state | pure none
  if h : used < 115 then
    let other := sig.proof ⟨used, h⟩
    let pair := if bucket / 2 ^ j % 2 = 0 then (value, other) else (other, value)
    let parent ← nodeHashP 10 coord index (2 ^ (4 - j - 1) + bucket / 2 ^ (j + 1)) pair.1
      (pads.fold ⟨used, h⟩) pair.2
    pure (some (parent, used + 1))
  else pure none
def ftsStepP (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (state : Option (List Digest × Nat)) (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, used) := state | pure none
  let sel := chosen.getD coord ⟨0, []⟩
  let selected := sel.leaves.map (fun s => sel.bucket * 128 + s)
  let values := (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
  let some (value, next) ← recoverChildP index coord selected values sig.proof pads 7 sel.bucket used
    | pure none
  let result ← (List.range 4).foldlM (outerStepP sig pads index coord sel.bucket) (some (value, next))
  let some (root, next) := result | pure none
  pure (some (roots ++ [root], next))
theorem recoverFtsP_eq (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection) :
    recoverFtsP sig pads index chosen = (do
      let state ← (List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0))
      let some (roots, used) := state | pure none
      if !(List.range (115 - used)).all (fun j =>
          decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) then return none
      pure (some (← forestPk index roots))) := rfl
theorem outer_climb (sig : Signature) (pads : Pads) (index coord bucket g : Nat) (hg : g / 2 ^ 7 = bucket)
    (val pad : Nat × Nat → Digest) : ∀ n j0 (v : Digest) (u : Nat), j0 + n ≤ 4 → u + n ≤ 115 →
      (∀ j < n, ∀ h : u + j < 115, sig.proof ⟨u + j, h⟩ = val (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1) ∧
        pads.fold ⟨u + j, h⟩ = pad (7 + j0 + j, g / 2 ^ (7 + j0 + j) ^^^ 1)) →
      (List.range' j0 n).foldlM (outerStepP sig pads index coord bucket) (some (v, u)) =
        (fun v' => some (v', u + n)) <$> climbV index coord val pad g (7 + j0) n v := by
  intro n
  induction n with
  | zero => intro j0 v u _ _ _; simp
  | succ n ih =>
      intro j0 v u hj hu hm
      have hb : g / 2 ^ (7 + j0) = bucket / 2 ^ j0 := by
        rw [pow_add, ← Nat.div_div_eq_div_mul, hg]
      obtain ⟨hv, hp⟩ := hm 0 (by omega) (by omega)
      simp only [Nat.add_zero] at hv hp
      rw [List.range'_succ, List.foldlM_cons, climbV_succ, map_bind]
      have hstep : outerStepP sig pads index coord bucket (some (v, u)) j0 =
          (fun p => some (p, u + 1)) <$> climbStep index coord val pad g (7 + j0) v := by
        unfold outerStepP climbStep
        simp only [dif_pos (show u < 115 by omega), hb, hv, hp]
        have hh : 2 ^ (11 - (7 + j0 + 1)) + bucket / 2 ^ j0 / 2 = 2 ^ (4 - j0 - 1) + bucket / 2 ^ (j0 + 1) := by
          rw [Nat.div_div_eq_div_mul, ← pow_succ, show 11 - (7 + j0 + 1) = 4 - j0 - 1 by omega]
        rw [hh]
        rcases Nat.mod_two_eq_zero_or_one (bucket / 2 ^ j0) with h0 | h0 <;>
          simp [h0, map_eq_bind_pure_comp]
      rw [hstep, bind_map_left]
      congr 1; funext x
      rw [ih (j0 + 1) x (u + 1) (by omega) (by omega) (fun j hj h => by
        have := hm (j + 1) (by omega) (by omega)
        simpa only [show u + (j + 1) = u + 1 + j by omega, show 7 + j0 + (j + 1) = 7 + (j0 + 1) + j by omega]
          using this)]
      simp only [show u + 1 + n = u + (n + 1) by omega, show 7 + j0 + 1 = 7 + (j0 + 1) by omega]
theorem ftsStepP_some (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) :
    ftsStepP sig pads index chosen (some (roots, used)) coord = (do
      let some (value, next) ← recoverChildP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
        ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩))
        sig.proof pads 7 (chosen.getD coord ⟨0, []⟩).bucket used | pure none
      let result ← (List.range 4).foldlM (outerStepP sig pads index coord (chosen.getD coord ⟨0, []⟩).bucket)
        (some (value, next))
      let some (root, next) := result | pure none
      pure (some (roots ++ [root], next))) := rfl
theorem ftsStepP_canon (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (used coord : Nat) (hs : SelOk (chosen.getD coord ⟨0, []⟩))
    (hfit : used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length ≤ 115)
    (val pad : Nat × Nat → Digest)
    (hm : SlotsMatch sig.proof pads val pad used (slotPositions (chosen.getD coord ⟨0, []⟩))) :
    ftsStepP sig pads index chosen (some (roots, used)) coord =
      (fun v => some (roots ++ [v], used + (slotPositions (chosen.getD coord ⟨0, []⟩)).length)) <$>
        coordCanon index coord (leafHP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
            ((List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) pads)
          val pad (selLeaf (chosen.getD coord ⟨0, []⟩) 0) (selLeaf (chosen.getD coord ⟨0, []⟩) 1)
          (selLeaf (chosen.getD coord ⟨0, []⟩) 2) := by
  rw [ftsStepP_some]
  generalize chosen.getD coord ⟨0, []⟩ = sel at *
  generalize hvals : (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩) =
    values
  have hsp : slotPositions sel = T3.frontier (selectedLeaves sel) 7 sel.bucket ++
      (List.range 4).map (fun j => (7 + j, sel.bucket / 2 ^ j ^^^ 1)) := rfl
  rw [hsp] at hfit hm ⊢
  rw [List.length_append] at hfit ⊢
  simp only [List.length_map, List.length_range] at hfit ⊢
  have hF := recoverChildP_eq_dfsP index coord (selectedLeaves sel) values sig.proof pads val pad 7 sel.bucket used
    (by omega) hm.left
  have g01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; have := hs.s12; omega
  have hb2 : selLeaf sel 2 / 2 ^ 7 = sel.bucket := hs.bucket_div (by rw [hs.selected]; simp)
  have hO := outer_climb sig pads index coord sel.bucket (selLeaf sel 2) hb2 val pad 4 0
  have hbk : ∀ j, selLeaf sel 2 / 2 ^ (7 + 0 + j) = sel.bucket / 2 ^ j := by
    intro j; rw [Nat.add_zero]; exact bucket_div_outer hs.l2
  have hD := dfsP_bucket (index := index) (coord := coord)
    (leafH := leafHP index coord (selectedLeaves sel) values pads)
    (val := val) (pad := pad) g01 g12 (hs.bucket_div (by rw [hs.selected]; simp))
    (hs.bucket_div (by rw [hs.selected]; simp)) hb2
  rw [← hs.selected] at hD
  rw [hF, bind_map_left, ← hD, map_bind]
  congr 1; funext v
  dsimp only
  rw [show List.range 4 = List.range' 0 4 from List.range_eq_range' ..]
  rw [hO v _ (by omega) (by omega) (fun j hj h => by
    have := hm.right j (by simp; omega) h
    simp only [List.getElem_map, List.getElem_range] at this
    rw [hbk j, Nat.add_zero]; exact this)]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, List.length_map, List.length_range,
    Nat.add_assoc, Nat.zero_add, Nat.add_zero, bind_assoc, pure_bind]
theorem selectionsOk_sel {chosen : List Selection} (h : selectionsOk chosen = true) {sel : Selection}
    (hm : sel ∈ chosen) : ∃ x0 x1 x2, sel.leaves = [x0, x1, x2] ∧ x0 < x1 ∧ x1 < x2 := by
  unfold selectionsOk at h
  have := List.all_eq_true.mp h sel hm
  match hl : sel.leaves, this with
  | [x0, x1, x2], h' =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h'
      exact ⟨x0, x1, x2, rfl, h'.1, h'.2⟩
theorem chosenOk_of (N : HashOutput) (h : selectionsOk (selections N) = true) : ChosenOk (selections N) := by
  intro c hc
  have hm := Correctness.selection_getD_mem N c hc
  obtain ⟨x0, x1, x2, hl, h01, h12⟩ := selectionsOk_sel h hm
  have hb := selection_bucket_bound N _ hm
  have h2 := selection_leaf_bound N _ x2 hm (by rw [hl]; simp)
  exact ⟨by rw [hl]; rfl, hb, by rw [hl]; simpa using h2, by rw [hl]; simpa using h01, by rw [hl]; simpa using h12⟩
theorem slotPositions_length {sel : Selection} (hs : SelOk sel) :
    (slotPositions sel).length = authCount sel.leaves + 4 := by
  obtain ⟨x0, x1, x2, hl, h01, h12, h2⟩ := hs.exists
  have hb : ∀ leaf ∈ sel.leaves, leaf < 128 := by
    rw [hl]; simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
  have hn : sel.leaves.Nodup := by rw [hl]; simp; omega
  have hsorted : sel.leaves.SortedLE := by
    rw [hl, List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨by omega, by omega⟩, by omega, fun _ h => h.elim⟩
  unfold slotPositions selectedLeaves
  rw [List.length_append, Correctness.bucket_frontier_length sel.leaves sel.bucket hs.len hn hsorted hb]
  simp
theorem sum_range_getD {α : Type} (items : List α) (d : α) (f : α → Nat) :
    ((List.range items.length).map (fun i => f (items.getD i d))).sum = (items.map f).sum := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
      simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
theorem slotBase_seven_eq (N : HashOutput) (hc : ChosenOk (selections N)) :
    slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  unfold slotBase
  rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
    List.sum_map_add]
  simp
  omega
theorem slotBase_seven_le (N : HashOutput) (hc : ChosenOk (selections N))
    (hadm : admissible (selections N) = true) : slotBase (selections N) 7 ≤ 115 := by
  have h := hadm
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  have e : ((List.range 7).map fun c => (slotPositions ((selections N).getD c ⟨0, []⟩)).length) =
      (List.range 7).map fun c => authCount ((selections N).getD c ⟨0, []⟩).leaves + 4 :=
    List.map_congr_left (fun c hc' => slotPositions_length (hc c (List.mem_range.mp hc')))
  have hsum : slotBase (selections N) 7 = 28 + ((selections N).map fun s => authCount s.leaves).sum := by
    unfold slotBase
    rw [e, ← sum_range_getD (selections N) ⟨0, []⟩ (fun s => authCount s.leaves), selections_length,
      List.sum_map_add]
    simp
    omega
  omega
theorem segPtr_succ (segs : List Segment) {m : Nat} (hm : m < segs.length) :
    segPtr segs (m + 1) = segNext (segPtr segs m) (segs.getD m default).a := by
  unfold segPtr segNext
  rw [List.take_add_one, List.getElem?_eq_getElem hm, List.map_append, List.sum_append]
  simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD,
    List.getElem?_eq_getElem hm, Option.getD_some]
  omega
theorem segsOk_of_getD (w : WBytes) (val pad : Nat × Nat → Digest) : ∀ (segs : List Segment) (f : Nat → Nat),
    (∀ i < segs.length, f (i + 1) = segNext (f i) (segs.getD i default).a) →
    (∀ i < segs.length, SegOk w val pad (segs.getD i default) (f i)) →
    SegsOk w val pad (f 0) segs ∧ segsEnd (f 0) segs = f segs.length := by
  intro segs
  induction segs with
  | nil => intro f _ _; exact ⟨trivial, rfl⟩
  | cons s rest ih =>
      intro f hf hok
      have h0 := hf 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      obtain ⟨h1, h2⟩ := ih (fun i => f (i + 1)) (fun i hi => by
          have := hf (i + 1) (by simp; omega); simpa using this)
        (fun i hi => by have := hok (i + 1) (by simp; omega); simpa using this)
      simp only [h0] at h1 h2
      refine ⟨⟨by simpa using hok 0 (by simp), h1⟩, ?_⟩
      simp only [segsEnd, h2, List.length_cons]
theorem sum_flatMap_nat {β : Type} (l : List β) (f : β → List Nat) :
    (l.flatMap f).sum = (l.map fun b => (f b).sum).sum := by
  induction l with
  | nil => simp
  | cons b l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]
theorem schedule_folds (chosen : List Selection) (hc : ChosenOk chosen) :
    ((schedule chosen).map Segment.a).sum = slotBase chosen 7 := by
  unfold schedule slotBase
  rw [List.map_flatMap, sum_flatMap_nat]
  congr 1
  apply List.map_congr_left
  intro c hc'
  rw [List.mem_range] at hc'
  exact coord_fold_count c _ (hc c hc')
theorem segPtr_end (chosen : List Selection) (hc : ChosenOk chosen) :
    segPtr (schedule chosen) 35 = streamBase + 280 + 80 * slotBase chosen 7 := by
  unfold segPtr
  rw [List.take_of_length_le (by rw [schedule_length])]
  have h1 := schedule_folds chosen hc
  have h2 : ((schedule chosen).map fun s => 8 + 80 * s.a).sum = 8 * 35 + 80 * ((schedule chosen).map Segment.a).sum := by
    rw [List.sum_map_add, List.map_const', List.sum_replicate, schedule_length, List.sum_map_mul_left]; rfl
  rw [h2, h1]; omega
def decVal (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (witDecP N w).signature.proof (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))
def decPad (N : HashOutput) (w : WBytes) (c : Nat) : Nat × Nat → Digest :=
  valOf (padDecP N w).fold (slotBase (selections N) c) (slotPositions ((selections N).getD c ⟨0, []⟩))
theorem decoded_foldOk (N : HashOutput) (w : WBytes) (hc : ChosenOk (selections N))
    (hle : slotBase (selections N) 7 ≤ 115) {c i r : Nat} (hc7 : c < 7) (hi : i < 5)
    (hr : r < ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).a) :
    FoldOk w (decVal N w c) (decPad N w c) ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r)
      (segPtr (schedule (selections N)) (5 * c + i)) r := by
  have hn : 5 * c + i < 35 := by omega
  have hsg := schedule_getD (selections N) hn
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsg
  have hr' : r < ((schedule (selections N)).getD (5 * c + i) default).a := by rw [hsg]; exact hr
  obtain ⟨hsplit, hlt⟩ := foldSlot_split (selections N) hc hn hr'
  rw [show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at hsplit hlt
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1
  have hk : foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r < 115 := by omega
  have hplan := streamPlan_foldSlot (selections N) hc hn hr' hk
  have htop := (foldFacts c _ (hc c hc7)).top i hi
  have hpar : ((schedule (selections N)).getD (5 * c + i) default).heap r % 2 =
      ((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).g /
        2 ^ (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).lo + r) % 2 := by
    rw [hsg]; unfold Segment.heap; exact heap_mod_two (by omega)
  have hidx : (slotBase (selections N) c + (slotPositions ((selections N).getD c ⟨0, []⟩)).idxOf
      (((coordSchedule c ((selections N).getD c ⟨0, []⟩)).getD i default).sib r)) % 115 =
      foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r := by
    rw [hsplit, Nat.mod_eq_of_lt (by omega)]
  have hP : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (witDecP N w).signature.proof x = (witDecP N w).signature.proof ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  have hQ : ∀ (x : Fin 115), x.val = foldSlot (selections N) ((schedule (selections N)).getD (5 * c + i) default) r →
      (padDecP N w).fold x = (padDecP N w).fold ⟨_, hk⟩ := fun x hx => congrArg _ (Fin.ext hx)
  constructor
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hP _ hidx]
    unfold witDecP
    simp only [slotOffset, hplan, Option.map_some, hpar]
  · show valOf _ _ _ _ = _
    unfold valOf
    rw [hQ _ hidx]
    unfold padDecP
    simp only [slotBlock, hplan, Option.map_some]
theorem segPtr_zero (segs : List Segment) : segPtr segs 0 = streamBase := by simp [segPtr]
theorem decoded_segsOk (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7) :
    SegsOk w (decVal N w c) (decPad N w c) (segPtr (schedule (selections N)) (5 * c))
      (coordSchedule c ((selections N).getD c ⟨0, []⟩)) ∧
    segsEnd (segPtr (schedule (selections N)) (5 * c)) (coordSchedule c ((selections N).getD c ⟨0, []⟩)) =
      segPtr (schedule (selections N)) (5 * (c + 1)) := by
  obtain ⟨hok, hadm, hmatch⟩ := h
  have hc := chosenOk_of N hok
  have hle := slotBase_seven_le N hc hadm
  have hlen := coordSchedule_length c ((selections N).getD c ⟨0, []⟩)
  have := segsOk_of_getD w (decVal N w c) (decPad N w c) (coordSchedule c ((selections N).getD c ⟨0, []⟩))
    (fun i => segPtr (schedule (selections N)) (5 * c + i))
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      have := segPtr_succ (schedule (selections N)) (m := 5 * c + i) (by rw [schedule_length]; exact hn)
      rw [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this
      simpa only [Nat.add_assoc] using this)
    (fun i hi => by
      rw [hlen] at hi
      have hn : 5 * c + i < 35 := by omega
      refine ⟨?_, fun r hr => decoded_foldOk N w hc hle hc7 hi hr⟩
      have := hmatch (5 * c + i) (by rw [schedule_length]; exact hn)
      rwa [schedule_getD _ hn, show (5 * c + i) / 5 = c by omega, show (5 * c + i) % 5 = i by omega] at this)
  simp only [Nat.add_zero, hlen] at this
  exact ⟨this.1, by rw [this.2]; ring_nf⟩
def ftsStreamStep (w : WBytes) (index : Nat) (chosen : List Selection) (state : Option (List Digest × Nat))
    (coord : Nat) : M (Option (List Digest × Nat)) := do
  let some (roots, ptr) := state | pure none
  let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
  pure (some (roots ++ [root], ptr))
theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← (List.range 7).foldlM (ftsStreamStep w index chosen) (some ([], streamBase))
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl
def canonD (N : HashOutput) (w : WBytes) (c : Nat) : M Digest :=
  coordCanon (N.toNat % 2 ^ 31) c
    (leafAt w (N.toNat % 2 ^ 31) c [selLeaf ((selections N).getD c ⟨0, []⟩) 0, selLeaf ((selections N).getD c ⟨0, []⟩) 1,
      selLeaf ((selections N).getD c ⟨0, []⟩) 2])
    (decVal N w c) (decPad N w c) (selLeaf ((selections N).getD c ⟨0, []⟩) 0)
    (selLeaf ((selections N).getD c ⟨0, []⟩) 1) (selLeaf ((selections N).getD c ⟨0, []⟩) 2)
theorem stream_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStreamStep w (N.toNat % 2 ^ 31) (selections N) (some (roots, segPtr (schedule (selections N)) (5 * c))) c =
      (fun v => some (roots ++ [v], segPtr (schedule (selections N)) (5 * (c + 1)))) <$> canonD N w c := by
  have hs := chosenOk_of N h.1 c hc7
  obtain ⟨hok, hend⟩ := decoded_segsOk N w h hc7
  unfold ftsStreamStep
  simp only []
  rw [ftsCoordP_canon w _ c _ _ (decVal N w c) (decPad N w c) hs.b hs.l2 hs.s01 hs.s12 hok, hend]
  simp only [bind_map_left, map_eq_bind_pure_comp, Function.comp_def, canonD, bind_assoc, pure_bind]
theorem leafHP_dec (N : HashOutput) (w : WBytes) {c : Nat} (hc7 : c < 7) (gs : List Nat) (g : Nat)
    (hg : gs.idxOf g < 3) :
    leafHP (N.toNat % 2 ^ 31) c gs ((List.range 3).map (fun j =>
        (witDecP N w).signature.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)) (padDecP N w) g =
      leafAt w (N.toNat % 2 ^ 31) c gs g := by
  unfold leafHP leafAt pendingHash
  have h1 : (3 * c + gs.idxOf g) % 22 = 3 * c + gs.idxOf g := Nat.mod_eq_of_lt (by omega)
  have h2 : (3 * c + gs.idxOf g + 1) % 22 = 3 * c + gs.idxOf g + 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (c * 3 + gs.idxOf g) % 21 = 3 * c + gs.idxOf g := by rw [Nat.mod_eq_of_lt (by omega)]; ring
  simp only [padDecP, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hg,
    Option.map_some, Option.getD_some, witDecP, h3]
theorem core_step_dec (N : HashOutput) (w : WBytes) (h : Shaped N w) {c : Nat} (hc7 : c < 7)
    (roots : List Digest) :
    ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)
        (some (roots, slotBase (selections N) c)) c =
      (fun v => some (roots ++ [v], slotBase (selections N) (c + 1))) <$> canonD N w c := by
  have hc := chosenOk_of N h.1
  have hs := hc c hc7
  have hle := slotBase_seven_le N hc h.2.1
  have hb1 := slotBase_mono (selections N) (show c + 1 ≤ 7 by omega)
  rw [slotBase_succ] at hb1 ⊢
  rw [ftsStepP_canon _ _ _ _ roots _ c hs (by omega) (decVal N w c) (decPad N w c)
    (slotsMatch_valOf _ _ _ _ (slotPositions_nodup _))]
  unfold canonD
  rw [hs.selected]
  congr 1
  have hg := hs.selected
  have g01 : selLeaf ((selections N).getD c ⟨0, []⟩) 0 < selLeaf ((selections N).getD c ⟨0, []⟩) 1 := by
    unfold selLeaf; have := hs.s01; omega
  have g12 : selLeaf ((selections N).getD c ⟨0, []⟩) 1 < selLeaf ((selections N).getD c ⟨0, []⟩) 2 := by
    unfold selLeaf; have := hs.s12; omega
  apply coordCanon_congr_leaf <;> apply leafHP_dec N w hc7 <;>
    exact List.idxOf_lt_length_of_mem (by simp)
theorem foldlM_canon (step : Option (List Digest × Nat) → Nat → M (Option (List Digest × Nat)))
    (P : Nat → M Digest) (pos : Nat → Nat)
    (hstep : ∀ c < 7, ∀ roots, step (some (roots, pos c)) c = (fun v => some (roots ++ [v], pos (c + 1))) <$> P c) :
    ∀ n ≤ 7, (List.range n).foldlM step (some ([], pos 0)) =
      (fun roots => some (roots, pos n)) <$> (List.range n).foldlM (fun roots c => (fun v => roots ++ [v]) <$> P c) [] := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldlM_append, List.foldlM_append, ih (by omega), bind_map_left, map_bind]
      congr 1; funext roots
      simp only [List.foldlM_cons, List.foldlM_nil, hstep n (by omega), bind_map_left, map_bind,
        Functor.map_map, bind_pure]
theorem dec_proof_tail (N : HashOutput) (w : WBytes) (h : Shaped N w) (k : Fin 115)
    (hk : slotBase (selections N) 7 ≤ k.val) : (witDecP N w).signature.proof k = 0 := by
  have hc := chosenOk_of N h.1
  have hnone : streamPlan (selections N) k = none := by
    unfold streamPlan
    rw [List.find?_eq_none]
    rintro ⟨n, r⟩ hp
    obtain ⟨hm1, hm2⟩ := mem_foldPositions.mp hp
    rw [schedule_length] at hm1
    simp only at hm1 hm2
    obtain ⟨e, l⟩ := foldSlot_split (selections N) hc hm1 hm2
    have hb1 := slotBase_mono (selections N) (show n / 5 + 1 ≤ 7 by omega)
    rw [slotBase_succ] at hb1
    simp only [decide_eq_true_eq]
    omega
  show (match slotOffset (selections N) k with | some off => wdig w off | none => 0) = 0
  simp [slotOffset, hnone]
theorem ftsP_shaped (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    ftsP w (N.toNat % 2 ^ 31) (selections N) =
      recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N) := by
  have hc := chosenOk_of N h.1
  have hle := slotBase_seven_le N hc h.2.1
  rw [ftsP_eq, recoverFtsP_eq]
  have A := foldlM_canon (ftsStreamStep w (N.toNat % 2 ^ 31) (selections N)) (canonD N w)
      (fun c => segPtr (schedule (selections N)) (5 * c)) (fun c hc7 roots => stream_step_dec N w h hc7 roots) 7 le_rfl
  have B := foldlM_canon (ftsStepP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))
      (canonD N w) (fun c => slotBase (selections N) c) (fun c hc7 roots => core_step_dec N w h hc7 roots) 7 le_rfl
  simp only [Nat.mul_zero, segPtr_zero] at A
  simp only [show slotBase (selections N) 0 = 0 from rfl] at B
  rw [A, B, bind_map_left, bind_map_left]
  refine bind_congr (fun roots => ?_)
  have hend : ¬ streamEnd < segPtr (schedule (selections N)) (5 * 7) := by
    rw [show 5 * 7 = 35 by rfl, segPtr_end _ hc]; unfold streamEnd streamBase; omega
  have htail : ((List.range (115 - slotBase (selections N) 7)).all fun j =>
      decide ((witDecP N w).signature.proof ⟨(slotBase (selections N) 7 + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0)) =
        true := by
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    exact dec_proof_tail N w h _ (by simp only [Nat.mod_eq_of_lt (show slotBase (selections N) 7 + j < 115 by omega)]; omega)
  dsimp only
  rw [if_neg hend, htail]
  rfl
theorem layerP_dec (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat) :
    layerP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayerP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) lay digits := rfl
theorem layersP_dec (N : HashOutput) (w : WBytes) : ∀ n root,
    layersP w (N.toNat % 2 ^ 31) n root = verifyLayersP (witDecP N w) (padDecP N w) (N.toNat % 2 ^ 31) n root := by
  intro n
  induction n with
  | zero => intro root; rfl
  | succ n ih =>
      intro root
      simp only [layersP, verifyLayersP, layerP_dec, ih]
      rfl
def verifyTailP (pk : Digest) (w : WBytes) (N : HashOutput) : M Bool := do
  let chosen := selections N
  if !selectionsOk chosen then return false
  if !digestGate N then return false
  let index := N.toNat % 2 ^ 31
  let some root ← ftsP w index chosen | pure false
  let some root ← layersP w index 4 root | pure false
  pure (root == pk)
theorem verifyP_eq_tail (m : Message) (pk : Digest) (w : WBytes) :
    verifyP m pk w = ((do
      let some N ← digestP m w | pure false
      verifyTailP pk w N) : M Bool) := rfl
theorem verifyTailP_shaped (pk : Digest) (N : HashOutput) (w : WBytes) (h : Shaped N w) :
    verifyTailP pk w N = verifyPadsTail pk N (witDecP N w) (padDecP N w) := by
  unfold verifyTailP verifyPadsTail
  simp only []
  rw [if_neg (by simp [h.1])]
  cases hg : digestGate N with
  | false => simp [digestAdmissible, hg]
  | true =>
      have ha : digestAdmissible N=true := by simp [digestAdmissible,h.2.1,hg]
      simp only [ha, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [ftsP_shaped N w h]
      simp only [layersP_dec]
      refine bind_congr (fun r => ?_)
      rcases r with _ | root
      · rfl
      · refine bind_congr (fun r => ?_)
        rcases r with _ | root <;> rfl
end SigGolfCandidate.T3M
end
