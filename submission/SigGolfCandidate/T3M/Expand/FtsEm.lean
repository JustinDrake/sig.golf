import SigGolfCandidate.T3M.Expand.RcInner
import SigGolfCandidate.T3M.Witness.Honest

/-!
# `expand`: the FTS emission is the honest stream schedule (stream E)

`emV` is the emission model `rcEm` with the empty subtrees' proof slots replaced by a valuation of their positions
(`rcEm_eq_emV`: equal when slot `used + i` holds the `i`-th frontier position's value). `emV_climb` peels a root
path with empty off-path siblings (a run of folds `climbE`), `emV_merge` a node with two non-empty children;
`emV_bucket`: the emission of one coordinate (the bucket DFS, the three outer folds, the closing header) is the
five segments of `coordSchedule` (`toMSeg`), whose doublewords are those of W's `segBytes` (`wordsOf_segBytes`).
-/

namespace SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3 (Digest hasLeaf Selection Signature)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

/-! ## The emission with positional values -/

/-- `rcEm` with the proof slots replaced by a valuation `val` of the empty positions `(level, node)`. -/
def emV (leaves : List Nat) (val : Nat × Nat → Digest) : Nat → Nat → Em → Em
  | level, node, e =>
    if hasLeaf leaves level node = false then e
    else match level with
    | 0 => if leaves.idxOf node = 0 then ⟨e.segs, e.cur, node % 2⟩ else e.close false (node % 2)
    | l + 1 =>
      let e2 := emV leaves val l (2 * node + 1) (emV leaves val l (2 * node) e)
      if hasLeaf leaves l (2 * node) = false then ⟨e2.segs, e2.cur ++ [(true, val (l, 2 * node))], e2.par⟩
      else if hasLeaf leaves l (2 * node + 1) = false then
        ⟨e2.segs, e2.cur ++ [(false, val (l, 2 * node + 1))], e2.par⟩
      else e2.close true (node % 2)

section emv
variable (leaves : List Nat) (val : Nat × Nat → Digest)

theorem emV_empty {level node : Nat} (e : Em) (h : hasLeaf leaves level node = false) :
    emV leaves val level node e = e := by
  unfold emV; simp [h]

theorem emV_inner {l node : Nat} (e : Em) (h : hasLeaf leaves (l + 1) node = true) :
    emV leaves val (l + 1) node e =
      (let e2 := emV leaves val l (2 * node + 1) (emV leaves val l (2 * node) e)
       if hasLeaf leaves l (2 * node) = false then ⟨e2.segs, e2.cur ++ [(true, val (l, 2 * node))], e2.par⟩
       else if hasLeaf leaves l (2 * node + 1) = false then
         ⟨e2.segs, e2.cur ++ [(false, val (l, 2 * node + 1))], e2.par⟩
       else e2.close true (node % 2)) := by
  rw [emV]; simp [h]

/-- **Slots to positions.** -/
theorem rcEm_eq_emV (pf : Nat → Digest) : ∀ level node used e,
    (∀ i (hi : i < (T3.frontier leaves level node).length),
      pf (used + i) = val ((T3.frontier leaves level node)[i])) →
    rcEm leaves pf level node used e = emV leaves val level node e := by
  intro level
  induction level with
  | zero =>
    intro node used e _
    unfold rcEm emV
    rfl
  | succ l ih =>
    intro node used e hm
    by_cases h : hasLeaf leaves (l + 1) node = false
    · rw [rcEm_empty _ _ _ _ _ _ h, emV_empty _ _ _ h]
    · have h' : hasLeaf leaves (l + 1) node = true := by simpa using h
      have hsplit := frontier_succ leaves l node h'
      have hmL : ∀ i (hi : i < (T3.frontier leaves l (2 * node)).length),
          pf (used + i) = val ((T3.frontier leaves l (2 * node))[i]) := by
        intro i hi
        have := hm i (by rw [hsplit, List.length_append]; omega)
        simp only [hsplit] at this
        rwa [List.getElem_append_left hi] at this
      have hmR : ∀ i (hi : i < (T3.frontier leaves l (2 * node + 1)).length),
          pf (used + (T3.frontier leaves l (2 * node)).length + i) =
            val ((T3.frontier leaves l (2 * node + 1))[i]) := by
        intro i hi
        have := hm ((T3.frontier leaves l (2 * node)).length + i) (by rw [hsplit, List.length_append]; omega)
        simp only [hsplit] at this
        rw [List.getElem_append_right (by omega)] at this
        simpa only [Nat.add_sub_cancel_left, Nat.add_assoc] using this
      rw [rcEm_inner _ _ _ _ _ _ h', emV_inner _ _ _ h']
      simp only []
      rw [ih (2 * node) used e hmL, ih (2 * node + 1) _ _ hmR]
      split_ifs with hl hr
      · have hf := frontier_empty leaves l (2 * node) hl
        have := hmL 0 (by rw [hf]; simp)
        simp only [hf, Nat.add_zero, List.getElem_cons_zero] at this
        rw [this]
      · have hf := frontier_empty leaves l (2 * node + 1) hr
        have := hmR 0 (by rw [hf]; simp)
        simp only [hf, Nat.add_zero, List.getElem_cons_zero] at this
        rw [this]
      · rfl

end emv

/-! ## Climbs -/

/-- Fold `r` of the climb of leaf `g` from level `lo`: the node `g / 2^(lo+r)` (a right child iff odd) with its
sibling's value. -/
def climbF (val : Nat × Nat → Digest) (g lo r : Nat) : Fold :=
  (decide (g / 2 ^ (lo + r) % 2 = 1), val (lo + r, g / 2 ^ (lo + r) ^^^ 1))

/-- `a` folds of the climb of `g` from level `lo` appended to the open segment. -/
def climbE (val : Nat × Nat → Digest) (g lo a : Nat) (e : Em) : Em :=
  ⟨e.segs, e.cur ++ (List.range a).map (climbF val g lo), e.par⟩

section climb
variable {leaves : List Nat} {val : Nat × Nat → Digest}

/-- **Path lemma.** Above a non-empty node on `g`'s root path, with every off-path sibling empty, the emission
climbs. -/
theorem emV_climb {g : Nat} (hg : g ∈ leaves) (lo : Nat) : ∀ d (e : Em),
    (∀ k, lo ≤ k → k < lo + d → hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false) →
    emV leaves val (lo + d) (g / 2 ^ (lo + d)) e = climbE val g lo d (emV leaves val lo (g / 2 ^ lo) e) := by
  intro d
  induction d with
  | zero =>
    intro e _
    simp only [Nat.add_zero, climbE, List.range_zero, List.map_nil, List.append_nil]
  | succ d ih =>
    intro e hsib
    have ihd := ih e (fun k h1 h2 => hsib k h1 (by omega))
    have hk : lo + (d + 1) = (lo + d) + 1 := by omega
    rw [hk]
    have hdiv : g / 2 ^ (lo + d + 1) = g / 2 ^ (lo + d) / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    have hself : hasLeaf leaves (lo + d) (g / 2 ^ (lo + d)) = true := hasLeaf_self hg _
    have hsk : hasLeaf leaves (lo + d) (g / 2 ^ (lo + d) ^^^ 1) = false := hsib _ (by omega) (by omega)
    have hpar : hasLeaf leaves (lo + d + 1) (g / 2 ^ (lo + d + 1)) = true := hasLeaf_self hg _
    rw [emV_inner _ _ _ hpar]
    simp only []
    have hx := xor_one_eq (g / 2 ^ (lo + d))
    rcases Nat.mod_two_eq_zero_or_one (g / 2 ^ (lo + d)) with h0 | h0
    · have e2 : 2 * (g / 2 ^ (lo + d + 1)) + 1 = g / 2 ^ (lo + d) ^^^ 1 := by omega
      have e1 : 2 * (g / 2 ^ (lo + d + 1)) = g / 2 ^ (lo + d) := by omega
      rw [e2, e1, emV_empty _ _ _ hsk, ihd, if_neg (by rw [hself]; decide), if_pos hsk]
      simp only [climbE, List.range_succ, List.map_append, List.map_singleton, List.append_assoc, climbF, h0]
      rfl
    · have e2 : 2 * (g / 2 ^ (lo + d + 1)) + 1 = g / 2 ^ (lo + d) := by omega
      have e1 : 2 * (g / 2 ^ (lo + d + 1)) = g / 2 ^ (lo + d) ^^^ 1 := by omega
      rw [e2, e1, emV_empty _ _ _ hsk, ihd, if_pos hsk]
      simp only [climbE, List.range_succ, List.map_append, List.map_singleton, List.append_assoc, climbF, h0]
      rfl

/-- A node with two non-empty children closes the open segment with the merge flag. -/
theorem emV_merge {l n : Nat} (e : Em) (hl : hasLeaf leaves l (2 * n) = true)
    (hr : hasLeaf leaves l (2 * n + 1) = true) :
    emV leaves val (l + 1) n e = (emV leaves val l (2 * n + 1) (emV leaves val l (2 * n) e)).close true (n % 2) := by
  have hp : hasLeaf leaves (l + 1) n = true := by
    have := hasLeaf_parent (leaves := leaves) hl; rwa [show 2 * n / 2 = n by omega] at this
  rw [emV_inner _ _ _ hp]; simp [hl, hr]

theorem emV_leaf {g : Nat} (hg : g ∈ leaves) (e : Em) :
    emV leaves val 0 g e = if leaves.idxOf g = 0 then ⟨e.segs, e.cur, g % 2⟩ else e.close false (g % 2) := by
  have h := hasLeaf_self hg 0
  simp only [pow_zero, Nat.div_one] at h
  rw [emV]; simp [h]

end climb

/-! ## One coordinate: the five segments of the schedule -/

/-- The emitted form of a schedule segment: its header byte (parity of `g`'s ancestor at `lo`) and folds. -/
def toMSeg (val : Nat × Nat → Digest) (seg : Segment) : MSeg :=
  ⟨seg.a + (if seg.merge then 16 else 0) + 32 * (seg.g / 2 ^ seg.lo % 2), (List.range seg.a).map (climbF val seg.g seg.lo)⟩

theorem climbF_range_add (val : Nat × Nat → Digest) (g lo a b : Nat) :
    (List.range (a + b)).map (climbF val g lo) =
      (List.range a).map (climbF val g lo) ++ (List.range b).map (climbF val g (lo + a)) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  simp only [Function.comp, climbF, Nat.add_assoc]

/-- **Schedule ≡ emission.** The emission of the bucket DFS of three sorted leaves `g0 < g1 < g2`, the three outer
folds and the closing header is the five segments of the schedule. -/
theorem emV_bucket_aux (val : Nat × Nat → Digest) (c g0 g1 g2 b : Nat) (h01 : g0 < g1) (h12 : g1 < g2)
    (hb0 : g0 / 2 ^ 7 = b) (hb1 : g1 / 2 ^ 7 = b) (hb2 : g2 / 2 ^ 7 = b) (segs : List MSeg) (p : Nat) :
    (climbE val g2 7 4 (emV [g0, g1, g2] val 7 b ⟨segs, [], p⟩)).close false 0 =
      ⟨segs ++ (if lcaLevel g0 g1 < lcaLevel g1 g2 then
        [⟨c, g0, 0, lcaLevel g0 g1 - 1, false⟩, ⟨c, g1, 0, lcaLevel g0 g1 - 1, true⟩,
          ⟨c, g1, lcaLevel g0 g1, lcaLevel g1 g2 - 1 - lcaLevel g0 g1, false⟩,
          ⟨c, g2, 0, lcaLevel g1 g2 - 1, true⟩, ⟨c, g2, lcaLevel g1 g2, 11 - lcaLevel g1 g2, false⟩]
      else
        [⟨c, g0, 0, lcaLevel g0 g1 - 1, false⟩, ⟨c, g1, 0, lcaLevel g1 g2 - 1, false⟩,
          ⟨c, g2, 0, lcaLevel g1 g2 - 1, true⟩, ⟨c, g2, lcaLevel g1 g2, lcaLevel g0 g1 - 1 - lcaLevel g1 g2, true⟩,
          ⟨c, g2, lcaLevel g0 g1, 11 - lcaLevel g0 g1, false⟩] : List Segment).map (toMSeg val), [], 0⟩ := by
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb0, hb1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb1, hb2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer h01 h12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne h01 h12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  have sib : ∀ g k, (∀ g' ∈ [g0, g1, g2], g' ≠ g → lcaLevel g g' ≠ k + 1) →
      hasLeaf [g0, g1, g2] k (g / 2 ^ k ^^^ 1) = false := fun g k h => hasLeaf_sib_false h
  have s0 : ∀ k, k + 1 < lcaLevel g0 g1 → hasLeaf [g0, g1, g2] k (g0 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | omega
  have s1lo : ∀ k, k + 1 < min (lcaLevel g0 g1) (lcaLevel g1 g2) →
      hasLeaf [g0, g1, g2] k (g1 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | (rw [c10]; omega) | omega
  have s1hi : ∀ k, lcaLevel g0 g1 ≤ k → k + 1 < lcaLevel g1 g2 →
      hasLeaf [g0, g1, g2] k (g1 / 2 ^ k ^^^ 1) = false := by
    intro k hk1 hk2; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;> first | exact absurd rfl hne' | (rw [c10]; omega) | omega
  have s2lo : ∀ k, k + 1 < lcaLevel g1 g2 → hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have s2mid : ∀ k, lcaLevel g1 g2 ≤ k → k + 1 < lcaLevel g0 g1 →
      hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk1 hk2; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have s2hi : ∀ k, max (lcaLevel g0 g1) (lcaLevel g1 g2) ≤ k →
      hasLeaf [g0, g1, g2] k (g2 / 2 ^ k ^^^ 1) = false := by
    intro k hk; apply sib; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro g' (rfl | rfl | rfl) hne' <;>
      first | exact absurd rfl hne' | (rw [c20, l02]; omega) | (rw [c21]; omega) | omega
  have m0 : g0 ∈ [g0, g1, g2] := by simp
  have m1 : g1 ∈ [g0, g1, g2] := by simp
  have m2 : g2 ∈ [g0, g1, g2] := by simp
  have i0 : [g0, g1, g2].idxOf g0 = 0 := by simp
  have i1 : [g0, g1, g2].idxOf g1 = 1 := by simp [show g0 ≠ g1 by omega]
  have i2 : [g0, g1, g2].idxOf g2 = 2 := by simp [show g0 ≠ g2 by omega, show g1 ≠ g2 by omega]
  have leaf0 : ∀ e, emV [g0, g1, g2] val 0 g0 e = ⟨e.segs, e.cur, g0 % 2⟩ := fun e => by
    rw [emV_leaf m0, if_pos i0]
  have leaf1 : ∀ e, emV [g0, g1, g2] val 0 g1 e = e.close false (g1 % 2) := fun e => by
    rw [emV_leaf m1, if_neg (by rw [i1]; decide)]
  have leaf2 : ∀ e, emV [g0, g1, g2] val 0 g2 e = e.close false (g2 % 2) := fun e => by
    rw [emV_leaf m2, if_neg (by rw [i2]; decide)]
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · rw [if_pos hA]
    obtain ⟨l, rfl⟩ : ∃ l, d12 = l + 1 := ⟨d12 - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, d01 = m + 1 := ⟨d01 - 1, by omega⟩
    have top : ∀ e, emV [g0, g1, g2] val 7 b e =
        climbE val g2 (l + 1) (7 - (l + 1)) (emV [g0, g1, g2] val (l + 1) (g2 / 2 ^ (l + 1)) e) := fun e => by
      have := emV_climb (val := val) m2 (l + 1) (7 - (l + 1)) e (fun k h1 _ => s2hi k (by omega))
      rwa [show l + 1 + (7 - (l + 1)) = 7 by omega, hb2] at this
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = l + 1 from hd12)
    have mid : ∀ e, emV [g0, g1, g2] val (l + 1) (g2 / 2 ^ (l + 1)) e =
        (emV [g0, g1, g2] val l (g2 / 2 ^ l) (emV [g0, g1, g2] val l (g1 / 2 ^ l) e)).close true
          (g2 / 2 ^ (l + 1) % 2) := fun e => by
      have := emV_merge (val := val) (l := l) (n := g2 / 2 ^ (l + 1)) e (by rw [c12a]; exact hasLeaf_self m1 l)
        (by rw [c12b]; exact hasLeaf_self m2 l)
      rwa [c12b, c12a] at this
    have left : ∀ e, emV [g0, g1, g2] val l (g1 / 2 ^ l) e =
        climbE val g1 (m + 1) (l - (m + 1)) (emV [g0, g1, g2] val (m + 1) (g1 / 2 ^ (m + 1)) e) := fun e => by
      have := emV_climb (val := val) m1 (m + 1) (l - (m + 1)) e (fun k h1 h2 => s1hi k h1 (by omega))
      rwa [show m + 1 + (l - (m + 1)) = l by omega] at this
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = m + 1 from hd01)
    have low : ∀ e, emV [g0, g1, g2] val (m + 1) (g1 / 2 ^ (m + 1)) e =
        (emV [g0, g1, g2] val m (g1 / 2 ^ m) (emV [g0, g1, g2] val m (g0 / 2 ^ m) e)).close true
          (g1 / 2 ^ (m + 1) % 2) := fun e => by
      have := emV_merge (val := val) (l := m) (n := g1 / 2 ^ (m + 1)) e (by rw [c01a]; exact hasLeaf_self m0 m)
        (by rw [c01b]; exact hasLeaf_self m1 m)
      rwa [c01b, c01a] at this
    have p0 : ∀ e, emV [g0, g1, g2] val m (g0 / 2 ^ m) e = climbE val g0 0 m (emV [g0, g1, g2] val 0 g0 e) :=
      fun e => by
        have := emV_climb (val := val) m0 0 m e (fun k _ h2 => s0 k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    have p1 : ∀ e, emV [g0, g1, g2] val m (g1 / 2 ^ m) e = climbE val g1 0 m (emV [g0, g1, g2] val 0 g1 e) :=
      fun e => by
        have := emV_climb (val := val) m1 0 m e (fun k _ h2 => s1lo k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    have p2 : ∀ e, emV [g0, g1, g2] val l (g2 / 2 ^ l) e = climbE val g2 0 l (emV [g0, g1, g2] val 0 g2 e) :=
      fun e => by
        have := emV_climb (val := val) m2 0 l e (fun k _ h2 => s2lo k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    rw [top, mid, p2, leaf2, left, low, p1, leaf1, p0, leaf0]
    have hlast : (List.range (7 - (l + 1))).map (climbF val g2 (l + 1)) ++ (List.range 4).map (climbF val g2 7) =
        (List.range (11 - (l + 1))).map (climbF val g2 (l + 1)) := by
      rw [show 11 - (l + 1) = (7 - (l + 1)) + 4 by omega, climbF_range_add, show l + 1 + (7 - (l + 1)) = 7 by omega]
    simp only [climbE, Em.close, toMSeg, List.map_cons, List.map_nil, List.nil_append, List.length_map,
      List.length_range, List.append_assoc, pow_zero, Nat.div_one, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      hlast, Nat.add_sub_cancel]
  · rw [if_neg hA]
    have hB : d12 < d01 := by omega
    obtain ⟨l, rfl⟩ : ∃ l, d01 = l + 1 := ⟨d01 - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, d12 = m + 1 := ⟨d12 - 1, by omega⟩
    have top : ∀ e, emV [g0, g1, g2] val 7 b e =
        climbE val g2 (l + 1) (7 - (l + 1)) (emV [g0, g1, g2] val (l + 1) (g2 / 2 ^ (l + 1)) e) := fun e => by
      have := emV_climb (val := val) m2 (l + 1) (7 - (l + 1)) e (fun k h1 _ => s2hi k (by omega))
      rwa [show l + 1 + (7 - (l + 1)) = 7 by omega, hb2] at this
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = l + 1 from hd01)
    have e21 : g2 / 2 ^ (l + 1) = g1 / 2 ^ (l + 1) := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have e21' : g2 / 2 ^ l = g1 / 2 ^ l := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have mid : ∀ e, emV [g0, g1, g2] val (l + 1) (g2 / 2 ^ (l + 1)) e =
        (emV [g0, g1, g2] val l (g2 / 2 ^ l) (emV [g0, g1, g2] val l (g0 / 2 ^ l) e)).close true
          (g2 / 2 ^ (l + 1) % 2) := fun e => by
      have := emV_merge (val := val) (l := l) (n := g2 / 2 ^ (l + 1)) e
        (by rw [e21, c01a]; exact hasLeaf_self m0 l) (by rw [e21, c01b, ← e21']; exact hasLeaf_self m2 l)
      rwa [e21, c01b, c01a, ← e21', ← e21] at this
    have p0 : ∀ e, emV [g0, g1, g2] val l (g0 / 2 ^ l) e = climbE val g0 0 l (emV [g0, g1, g2] val 0 g0 e) :=
      fun e => by
        have := emV_climb (val := val) m0 0 l e (fun k _ h2 => s0 k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    have right : ∀ e, emV [g0, g1, g2] val l (g2 / 2 ^ l) e =
        climbE val g2 (m + 1) (l - (m + 1)) (emV [g0, g1, g2] val (m + 1) (g2 / 2 ^ (m + 1)) e) := fun e => by
      have := emV_climb (val := val) m2 (m + 1) (l - (m + 1)) e (fun k h1 h2 => s2mid k h1 (by omega))
      rwa [show m + 1 + (l - (m + 1)) = l by omega] at this
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = m + 1 from hd12)
    have low : ∀ e, emV [g0, g1, g2] val (m + 1) (g2 / 2 ^ (m + 1)) e =
        (emV [g0, g1, g2] val m (g2 / 2 ^ m) (emV [g0, g1, g2] val m (g1 / 2 ^ m) e)).close true
          (g2 / 2 ^ (m + 1) % 2) := fun e => by
      have := emV_merge (val := val) (l := m) (n := g2 / 2 ^ (m + 1)) e (by rw [c12a]; exact hasLeaf_self m1 m)
        (by rw [c12b]; exact hasLeaf_self m2 m)
      rwa [c12b, c12a] at this
    have p1 : ∀ e, emV [g0, g1, g2] val m (g1 / 2 ^ m) e = climbE val g1 0 m (emV [g0, g1, g2] val 0 g1 e) :=
      fun e => by
        have := emV_climb (val := val) m1 0 m e (fun k _ h2 => s1lo k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    have p2 : ∀ e, emV [g0, g1, g2] val m (g2 / 2 ^ m) e = climbE val g2 0 m (emV [g0, g1, g2] val 0 g2 e) :=
      fun e => by
        have := emV_climb (val := val) m2 0 m e (fun k _ h2 => s2lo k (by omega))
        simpa only [Nat.zero_add, pow_zero, Nat.div_one] using this
    rw [top, mid, right, low, p2, leaf2, p1, leaf1, p0, leaf0]
    have hlast : (List.range (7 - (l + 1))).map (climbF val g2 (l + 1)) ++ (List.range 4).map (climbF val g2 7) =
        (List.range (11 - (l + 1))).map (climbF val g2 (l + 1)) := by
      rw [show 11 - (l + 1) = (7 - (l + 1)) + 4 by omega, climbF_range_add, show l + 1 + (7 - (l + 1)) = 7 by omega]
    simp only [climbE, Em.close, toMSeg, List.map_cons, List.map_nil, List.nil_append, List.length_map,
      List.length_range, List.append_assoc, pow_zero, Nat.div_one, Bool.false_eq_true, ↓reduceIte, List.cons_append,
      hlast, Nat.add_sub_cancel]

/-- **One coordinate's emission** (`coordSchedule`). -/
theorem emV_bucket (val : Nat × Nat → Digest) (c : Nat) (sel : Selection) (hs : SelOk sel) (segs : List MSeg)
    (p : Nat) :
    (climbE val (selLeaf sel 2) 7 4 (emV (selectedLeaves sel) val 7 sel.bucket ⟨segs, [], p⟩)).close false 0 =
      ⟨segs ++ (coordSchedule c sel).map (toMSeg val), [], 0⟩ := by
  rw [hs.selected]
  have h0 := hs.s01; have h1 := hs.s12; have h2 := hs.l2
  have h01 : selLeaf sel 0 < selLeaf sel 1 := by unfold selLeaf; omega
  have h12 : selLeaf sel 1 < selLeaf sel 2 := by unfold selLeaf; omega
  have hb : ∀ j, sel.leaves.getD j 0 < 128 → selLeaf sel j / 2 ^ 7 = sel.bucket := fun j hj => by
    unfold selLeaf; exact bucket_div_eight hj
  unfold coordSchedule
  exact emV_bucket_aux val c _ _ _ _ h01 h12 (hb 0 (by omega)) (hb 1 (by omega)) (hb 2 h2) segs p

/-! ## The doublewords of a segment -/

theorem length_foldBytes (E : Nat) (d : Digest) : (foldBytes E d).length = 80 := by
  unfold foldBytes; split_ifs <;> simp [bytesLE_length, T3M.zeros]

theorem wordsOf_foldBytes (E : Nat) (d : Digest) : wordsOf (foldBytes E d) = foldWords (decide (E % 2 = 1), d) := by
  unfold foldBytes foldWords
  by_cases h : E % 2 = 1
  · simp only [h, ↓reduceIte, decide_true]
    rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
      show T3M.zeros 64 = List.replicate (8 * 8) 0 from rfl, wordsOf_replicate_zero]
    rfl
  · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true]
    rw [wordsOf_append _ _ (by simp [bytesLE_length, T3M.zeros]),
      wordsOf_append _ _ (by simp [T3M.zeros]), wordsOf_bytesLE16,
      show T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, show T3M.zeros 16 = List.replicate (8 * 2) 0 from rfl,
      wordsOf_replicate_zero, wordsOf_replicate_zero]
    rfl

theorem wordsOf_flatMap8 {α : Type} (f : α → List UInt8) (hf : ∀ x, (f x).length % 8 = 0) :
    ∀ (xs : List α), wordsOf (xs.flatMap f) = xs.flatMap (fun x => wordsOf (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (hf x), wordsOf_flatMap8 f hf xs]

/-- **A segment's doublewords**: W's bytes (`segBytes`, siblings by `foldSlot`) are the emitted ones. -/
theorem wordsOf_segBytes (chosen : List Selection) (proof : Fin 119 → Digest) (val : Nat × Nat → Digest)
    (seg : Segment) (htop : seg.lo + seg.a ≤ 11) (hlo : seg.lo < 11)
    (hval : ∀ r < seg.a, val (seg.sib r) = proof ⟨foldSlot chosen seg r % 119, Nat.mod_lt _ (by decide)⟩) :
    wordsOf (segBytes chosen proof seg) = segWords (toMSeg val seg) := by
  unfold segBytes segWords toMSeg
  rw [wordsOf_append8 _ _ (by rfl)]
  congr 1
  · have ht : seg.t = seg.g / 2 ^ seg.lo % 2 := by
      unfold Segment.t Segment.heap; rw [Nat.add_zero]; exact heap_mod_two hlo
    have hb : seg.byte0 = seg.a + (if seg.merge then 16 else 0) + 32 * (seg.g / 2 ^ seg.lo % 2) := by
      unfold Segment.byte0; rw [ht]; split_ifs <;> rfl
    have hlt : seg.byte0 < 256 := by
      rw [hb]; have := Nat.mod_lt (seg.g / 2 ^ seg.lo) (show 0 < 2 by decide); split_ifs <;> omega
    rw [List.singleton_append, readLE_cons, show T3M.zeros 7 = List.replicate 7 0 from rfl, readLE_replicate_zero,
      Nat.mul_zero, Nat.add_zero]
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    rw [Nat.mod_eq_of_lt hlt, hb]
  · rw [wordsOf_flatMap8 _ (fun r => by rw [length_foldBytes]), List.flatMap_map]
    apply List.flatMap_congr
    intro r hr
    have hr' := List.mem_range.mp hr
    rw [wordsOf_foldBytes]
    congr 1
    simp only [climbF, Segment.heap, Prod.mk.injEq]
    refine ⟨by simp only [heap_mod_two (show seg.lo + r < 11 by omega)], ?_⟩
    rw [← hval r hr']
    rfl

/-! ## The seven coordinates -/

/-- Coordinate `c`'s valuation of the empty positions: the proof slot Core consumes there. -/
def valC (chosen : List Selection) (proof : Fin 119 → Digest) (c : Nat) (q : Nat × Nat) : Digest :=
  pfN proof (slotBase chosen c + (slotPositions (chosen.getD c ⟨0, []⟩)).idxOf q)

/-- The emitted segments of the coordinates `< n`. -/
def emSegs (chosen : List Selection) (proof : Fin 119 → Digest) (n : Nat) : List MSeg :=
  (List.range n).flatMap fun c => (coordSchedule c (chosen.getD c ⟨0, []⟩)).map (toMSeg (valC chosen proof c))

theorem emSegs_succ (chosen : List Selection) (proof : Fin 119 → Digest) (n : Nat) :
    emSegs chosen proof (n + 1) =
      emSegs chosen proof n ++ (coordSchedule n (chosen.getD n ⟨0, []⟩)).map (toMSeg (valC chosen proof n)) := by
  simp only [emSegs, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem length_segs_words (v : Nat × Nat → Digest) : ∀ L : List Segment,
    ((L.map (toMSeg v)).flatMap segWords).length = L.length + 10 * (L.map Segment.a).sum
  | [] => rfl
  | seg :: L => by
    rw [List.map_cons, List.flatMap_cons, List.length_append, length_segs_words v L]
    simp only [segWords, toMSeg, List.length_cons, length_flatMap_foldWords, List.length_map, List.length_range,
      List.map_cons, List.sum_cons]
    ring

theorem length_emSegs_words (chosen : List Selection) (proof : Fin 119 → Digest) (hc : ChosenOk chosen) :
    ∀ n ≤ 7, ((emSegs chosen proof n).flatMap segWords).length = 5 * n + 10 * slotBase chosen n
  | 0, _ => rfl
  | n + 1, h => by
    rw [emSegs_succ, List.flatMap_append, List.length_append, length_emSegs_words chosen proof hc n (by omega),
      length_segs_words, coordSchedule_length, coord_fold_count _ _ (hc n (by omega)), slotBase_succ]
    ring

theorem coordSchedule_lo (c : Nat) (sel : Selection) (hs : SelOk sel) :
    ∀ seg ∈ coordSchedule c sel, seg.lo ≤ 8 := by
  have h0 := hs.s01; have h1 := hs.s12; have h2 := hs.l2
  have l01 : lcaLevel (selLeaf sel 0) (selLeaf sel 1) ≤ 7 := by
    unfold selLeaf; exact lca_le_eight (by omega) (by omega) (by omega)
  have l12 : lcaLevel (selLeaf sel 1) (selLeaf sel 2) ≤ 7 := by
    unfold selLeaf; exact lca_le_eight (by omega) (by omega) (by omega)
  intro seg hseg
  unfold coordSchedule at hseg
  simp only [] at hseg
  split_ifs at hseg <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hseg <;>
    rcases hseg with rfl | rfl | rfl | rfl | rfl <;> simp only [] <;> omega

/-- The proof slot of a schedule fold lies below the used slots. -/
theorem foldSlot_lt (chosen : List Selection) (hc : ChosenOk chosen) {c : Nat} (hc7 : c < 7) {seg : Segment}
    (hseg : seg ∈ coordSchedule c (chosen.getD c ⟨0, []⟩)) {r : Nat} (hr : r < seg.a) :
    seg.coord = c ∧ foldSlot chosen seg r < slotBase chosen (c + 1) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hseg
  have hi5 : i < 5 := by rw [coordSchedule_length] at hi; exact hi
  have hco := coordSchedule_coord c (chosen.getD c ⟨0, []⟩) hi5
  have hgd : (coordSchedule c (chosen.getD c ⟨0, []⟩)).getD i default =
      (coordSchedule c (chosen.getD c ⟨0, []⟩))[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [hgd] at hco
  refine ⟨hco, ?_⟩
  have hm := fold_sib_mem c _ (hc c hc7) i hi5 r (by rw [hgd]; exact hr)
  rw [hgd] at hm
  unfold foldSlot
  rw [hco, slotBase_succ]
  have := List.idxOf_lt_length_of_mem hm
  omega

/-- **The stream doublewords**: W's honest stream bytes are the emitted segments of the seven coordinates. -/
theorem wordsOf_schedule (chosen : List Selection) (proof : Fin 119 → Digest) (hc : ChosenOk chosen)
    (h7 : slotBase chosen 7 ≤ 119) :
    wordsOf ((schedule chosen).flatMap (segBytes chosen proof)) = (emSegs chosen proof 7).flatMap segWords := by
  unfold schedule emSegs
  rw [List.flatMap_assoc, List.flatMap_assoc, wordsOf_flatMap8 _ (fun c => by
    rw [List.length_flatMap]
    induction (coordSchedule c (chosen.getD c ⟨0, []⟩)) with
    | nil => rfl
    | cons seg L ih => rw [List.map_cons, List.sum_cons, segBytes_length]; omega)]
  apply List.flatMap_congr
  intro c hc7
  have hc7' := List.mem_range.mp hc7
  rw [wordsOf_flatMap8 _ (fun seg => by rw [segBytes_length]; omega), List.flatMap_map]
  apply List.flatMap_congr
  intro seg hseg
  have F := foldFacts c _ (hc c hc7')
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hseg
  have hi5 : i < 5 := by rw [coordSchedule_length] at hi; exact hi
  have hgd : (coordSchedule c (chosen.getD c ⟨0, []⟩)).getD i default =
      (coordSchedule c (chosen.getD c ⟨0, []⟩))[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  have htop := F.top i hi5
  rw [hgd] at htop
  have hlo := coordSchedule_lo c _ (hc c hc7') _ hseg
  refine wordsOf_segBytes chosen proof _ _ htop (by omega) (fun r hr => ?_)
  obtain ⟨hco, hlt⟩ := foldSlot_lt chosen hc hc7' hseg hr
  have hb := slotBase_mono chosen (show c + 1 ≤ 7 by omega)
  have hlt' : foldSlot chosen (coordSchedule c (chosen.getD c ⟨0, []⟩))[i] r < 119 := by omega
  unfold valC
  rw [show slotBase chosen c + (slotPositions (chosen.getD c ⟨0, []⟩)).idxOf
      ((coordSchedule c (chosen.getD c ⟨0, []⟩))[i].sib r) =
      foldSlot chosen (coordSchedule c (chosen.getD c ⟨0, []⟩))[i] r by unfold foldSlot; rw [hco]]
  rw [pfN_lt _ _ hlt']
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hlt').symm

theorem readWords_map (t : RiscvZkvm.Rv64.MachineState) (A : Nat) : ∀ n, t.readWords (BitVec.ofNat 64 A) n =
    (List.range n).map fun k => t.getMem (BitVec.ofNat 64 (A + 8 * k))
  | 0 => rfl
  | n + 1 => by
    rw [readWords_add t A n 1, readWords_one, readWords_map t A n, List.range_succ, List.map_append]
    rfl

/-- **The stream at `fts_done`**: the emitted image of the seven coordinates reads as W's `streamBytes`. -/
theorem stream_readWords (chosen : List Selection) (proof : Fin 119 → Digest) (hc : ChosenOk chosen)
    (h7 : slotBase chosen 7 ≤ 119) (t : RiscvZkvm.Rv64.MachineState) (p : Nat)
    (hS : StreamAt t ⟨emSegs chosen proof 7, [], p⟩) :
    t.readWords (BitVec.ofNat 64 0xC40) 1275 = wordsOf (streamBytes chosen proof) := by
  have hlenW := length_emSegs_words chosen proof hc 7 le_rfl
  have hwB := wordsOf_schedule chosen proof hc h7
  have hsum : ((schedule chosen).map fun s => 8 + 80 * s.a).sum =
      8 * 35 + 80 * ((schedule chosen).map Segment.a).sum := by
    rw [List.sum_map_add, List.map_const', List.sum_replicate, schedule_length, List.sum_map_mul_left]; rfl
  have hlB : ((schedule chosen).flatMap (segBytes chosen proof)).length = 8 * (35 + 10 * slotBase chosen 7) := by
    rw [List.length_flatMap, List.map_congr_left (fun seg _ => segBytes_length chosen proof seg), hsum,
      schedule_folds chosen hc]
    ring
  unfold streamBytes
  rw [List.take_append, List.take_of_length_le (by rw [hlB]; omega), hlB,
    show T3M.zeros 10200 = List.replicate 10200 0 from rfl, List.take_replicate,
    show min (10200 - 8 * (35 + 10 * slotBase chosen 7)) 10200 = 8 * (1275 - (35 + 10 * slotBase chosen 7)) by omega,
    wordsOf_append _ _ (by rw [hlB]; omega), hwB, wordsOf_replicate_zero, readWords_map]
  apply List.ext_getElem (by simp [hlenW]; omega)
  intro k h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hS k (by simpa using h1)]
  simp only [img, List.flatMap_nil, List.append_nil]
  by_cases hk : k < ((emSegs chosen proof 7).flatMap segWords).length
  · rw [List.getElem_append_left hk, List.getD_eq_getElem?_getD, List.getElem?_append_left hk,
      List.getElem?_eq_getElem hk]
    rfl
  · rw [List.getElem_append_right (by omega), List.getElem_replicate, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega)]
    by_cases hk' : k = ((emSegs chosen proof 7).flatMap segWords).length
    · subst hk'; simp
    · rw [List.getElem?_eq_none (by simp only [List.length_singleton]; omega)]; rfl

end SigGolfCandidate.T3M.Expand
