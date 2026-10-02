import SigGolfCandidate.T3M.Witness.Bits
import SigGolfCandidate.T3M.Witness.Basic

/-! # Core's DFS without proof slots (stream W)

`dfsP` is Core's `recoverChildP` with the proof slots replaced by a valuation `val`/`pad` of the empty subtrees'
positions `(level, node)`; `recoverChildP_eq_dfsP` relates them when the slots `used + i` hold the values of the
`i`-th frontier position. `climbV` folds along the root path of one leaf; `dfsP_climb` peels a path whose off-path
siblings are empty, `dfsP_merge` a node with two non-empty children. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## `hasLeaf` -/

theorem hasLeaf_iff (leaves : List Nat) (level node : Nat) :
    hasLeaf leaves level node = true ↔ ∃ leaf ∈ leaves, leaf / 2 ^ level = node := by
  simp only [hasLeaf, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨leaf, hm, hlo, hhi⟩
    exact ⟨leaf, hm, Nat.div_eq_of_lt_le hlo hhi⟩
  · rintro ⟨leaf, hm, rfl⟩
    exact ⟨leaf, hm, Nat.div_mul_le_self leaf _, by
      rw [Nat.add_mul, Nat.one_mul]; have := Nat.lt_div_mul_add (a := leaf) (Nat.two_pow_pos level); omega⟩

theorem hasLeaf_false_iff (leaves : List Nat) (level node : Nat) :
    hasLeaf leaves level node = false ↔ ∀ leaf ∈ leaves, leaf / 2 ^ level ≠ node := by
  rw [← Bool.not_eq_true, hasLeaf_iff]; simp

theorem hasLeaf_self {leaves : List Nat} {g : Nat} (hg : g ∈ leaves) (k : Nat) :
    hasLeaf leaves k (g / 2 ^ k) = true := (hasLeaf_iff _ _ _).mpr ⟨g, hg, rfl⟩

/-- The sibling of `g`'s level-`k` ancestor is empty when no other leaf has its LCA with `g` at level `k + 1`. -/
theorem hasLeaf_sib_false {leaves : List Nat} {g k : Nat}
    (h : ∀ g' ∈ leaves, g' ≠ g → lcaLevel g g' ≠ k + 1) : hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false := by
  rw [hasLeaf_false_iff]
  intro g' hg' he
  by_cases hgg : g' = g
  · subst hgg; exact xor_one_ne _ he.symm
  · exact h g' hg' hgg (lca_of_div_sib he)

/-! ## The slot-free DFS -/

/-- Pad of the node `(level + 1, node)`: the pad of its empty child, zero for a merge. -/
def dfsPad (leaves : List Nat) (pad : Nat × Nat → Digest) (level node : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pad (level, 2 * node)
  else if !hasLeaf leaves level (2 * node + 1) then pad (level, 2 * node + 1) else 0

/-- Core's DFS with the proof slots replaced by the valuation `val` (and `pad`) of the empty positions. -/
def dfsP (index coord : Nat) (leaves : List Nat) (leafH : Nat → M Digest) (val pad : Nat × Nat → Digest) :
    Nat → Nat → M Digest
  | level, node =>
      if !hasLeaf leaves level node then pure (val (level, node))
      else match level with
      | 0 => leafH node
      | level + 1 => do
          let left ← dfsP index coord leaves leafH val pad level (2 * node)
          let right ← dfsP index coord leaves leafH val pad level (2 * node + 1)
          nodeHashP 10 coord index (2 ^ (11 - (level + 1)) + node) left (dfsPad leaves pad level node) right

/-- The leaf hash `recoverChildP` uses (slot `3 coord + j` for the `j`-th selected leaf). -/
def leafHP (index coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads) (node : Nat) : M Digest :=
  ftsLeafP index coord node (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
    (values.getD (leaves.idxOf node) 0)
    (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩)

/-- Slots `used + i` hold the value and pad of the `i`-th position of `ps`. -/
def SlotsMatch (proof : Fin 115 → Digest) (pads : Pads) (val pad : Nat × Nat → Digest) (used : Nat)
    (ps : List (Nat × Nat)) : Prop :=
  ∀ i (hi : i < ps.length) (h : used + i < 115), proof ⟨used + i, h⟩ = val ps[i] ∧ pads.fold ⟨used + i, h⟩ = pad ps[i]

theorem SlotsMatch.left {proof : Fin 115 → Digest} {pads : Pads} {val pad : Nat × Nat → Digest} {used : Nat}
    {l r : List (Nat × Nat)} (h : SlotsMatch proof pads val pad used (l ++ r)) : SlotsMatch proof pads val pad used l := by
  intro i hi hb
  have := h i (by simp; omega) hb
  rwa [List.getElem_append_left hi] at this

theorem SlotsMatch.right {proof : Fin 115 → Digest} {pads : Pads} {val pad : Nat × Nat → Digest} {used : Nat}
    {l r : List (Nat × Nat)} (h : SlotsMatch proof pads val pad used (l ++ r)) :
    SlotsMatch proof pads val pad (used + l.length) r := by
  intro i hi hb
  have := h (l.length + i) (by simp; omega) (by omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  simpa only [Nat.add_assoc] using this

theorem recoverChildP_eq_dfsP (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (pads : Pads) (val pad : Nat × Nat → Digest) :
    ∀ level node used, used + (frontier leaves level node).length ≤ 115 →
      SlotsMatch proof pads val pad used (frontier leaves level node) →
      recoverChildP index coord leaves values proof pads level node used =
        (fun v => some (v, used + (frontier leaves level node).length)) <$>
          dfsP index coord leaves (leafHP index coord leaves values pads) val pad level node := by
  intro level
  induction level with
  | zero =>
      intro node used hfit hm
      by_cases hh : hasLeaf leaves 0 node = true
      · simp only [recoverChildP, dfsP, hh, Bool.not_true, Bool.false_eq_true, ite_false, T3.frontier, ite_true,
          List.length_nil, Nat.add_zero, leafHP, map_eq_bind_pure_comp, Function.comp_def]
      · have hh : hasLeaf leaves 0 node = false := by simpa using hh
        simp only [T3.frontier, hh, Bool.false_eq_true, ite_false, List.length_singleton] at hfit hm ⊢
        have hp := (hm 0 (by simp) (by omega)).1
        simp only [recoverChildP, dfsP, hh, Bool.not_false, ite_true, dif_pos (show used < 115 by omega),
          map_pure]
        simp only [Nat.add_zero] at hp
        rw [hp]; rfl
  | succ level ih =>
      intro node used hfit hm
      by_cases hh : hasLeaf leaves (level + 1) node = true
      · have hsplit : frontier leaves (level + 1) node =
            frontier leaves level (2 * node) ++ frontier leaves level (2 * node + 1) := by
          simp only [T3.frontier, hh, ite_true]
        rw [hsplit, List.length_append] at hfit
        rw [hsplit] at hm
        have hleft := ih (2 * node) used (by omega) hm.left
        have hright := ih (2 * node + 1) (used + (frontier leaves level (2 * node)).length) (by omega) hm.right
        have hpad : foldPad pads leaves level node used (used + (frontier leaves level (2 * node)).length) =
            dfsPad leaves pad level node := by
          unfold foldPad dfsPad
          by_cases hl : hasLeaf leaves level (2 * node) = true
          · by_cases hr : hasLeaf leaves level (2 * node + 1) = true
            · simp [hl, hr]
            · have hr : hasLeaf leaves level (2 * node + 1) = false := by simpa using hr
              have hlen : (frontier leaves level (2 * node + 1)) = [(level, 2 * node + 1)] := by
                cases level <;> simp [T3.frontier, hr]
              have := (hm.right 0 (by simp [hlen]) (by rw [hlen] at hfit; simp at hfit; omega)).2
              simp only [hlen, List.getElem_cons_zero, Nat.add_zero] at this
              simp only [hl, hr, Bool.not_true, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
              rw [← this]; congr 1; ext; simp only [Fin.val_mk]; rw [Nat.mod_eq_of_lt]
              rw [hlen] at hfit; simp at hfit; omega
          · have hl : hasLeaf leaves level (2 * node) = false := by simpa using hl
            have hlen : (frontier leaves level (2 * node)) = [(level, 2 * node)] := by
              cases level <;> simp [T3.frontier, hl]
            have := (hm.left 0 (by simp [hlen]) (by rw [hlen] at hfit; simp at hfit; omega)).2
            simp only [hlen, List.getElem_cons_zero, Nat.add_zero] at this
            simp only [hl, Bool.not_false, ite_true]
            rw [← this]; congr 1; ext; simp only [Fin.val_mk]; rw [Nat.mod_eq_of_lt]
            rw [hlen] at hfit; simp at hfit; omega
        conv_lhs => unfold recoverChildP
        conv_rhs => unfold dfsP
        simp only [hh, Bool.not_true, Bool.false_eq_true, ite_false, hleft, hright, hpad, hsplit,
          List.length_append, bind_map_left, map_bind, Nat.add_assoc]
        rfl
      · have hh : hasLeaf leaves (level + 1) node = false := by simpa using hh
        simp only [T3.frontier, hh, Bool.false_eq_true, ite_false, List.length_singleton] at hfit hm ⊢
        have hp := (hm 0 (by simp) (by omega)).1
        simp only [recoverChildP, dfsP, hh, Bool.not_false, ite_true, dif_pos (show used < 115 by omega),
          map_pure]
        simp only [Nat.add_zero] at hp
        rw [hp]; rfl

/-! ## Climbing a root path -/

/-- One fold on the root path of leaf `g` at level `k`: node `g / 2^k` (a right child iff odd) with its sibling's
value and pad, parent heap `2^(11 - (k+1)) + g / 2^(k+1)`. -/
def climbStep (index coord : Nat) (val pad : Nat × Nat → Digest) (g k : Nat) (v : Digest) : M Digest :=
  if g / 2 ^ k % 2 = 1 then
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) (val (k, g / 2 ^ k ^^^ 1)) (pad (k, g / 2 ^ k ^^^ 1)) v
  else
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) v (pad (k, g / 2 ^ k ^^^ 1)) (val (k, g / 2 ^ k ^^^ 1))

/-- `a` folds on the root path of `g` from level `lo`. -/
def climbV (index coord : Nat) (val pad : Nat × Nat → Digest) (g : Nat) : Nat → Nat → Digest → M Digest
  | _, 0, v => pure v
  | lo, a + 1, v => do
      let v ← climbStep index coord val pad g lo v
      climbV index coord val pad g (lo + 1) a v

section climb
variable (index coord : Nat) (val pad : Nat × Nat → Digest) (g : Nat)

@[simp] theorem climbV_zero (lo : Nat) (v : Digest) : climbV index coord val pad g lo 0 v = pure v := rfl

@[simp] theorem climbV_zero' (lo : Nat) : climbV index coord val pad g lo 0 = pure := rfl

theorem climbV_succ (lo a : Nat) (v : Digest) :
    climbV index coord val pad g lo (a + 1) v =
      climbStep index coord val pad g lo v >>= climbV index coord val pad g (lo + 1) a := rfl

theorem climbV_snoc : ∀ (a lo : Nat) (v : Digest), climbV index coord val pad g lo (a + 1) v =
    climbV index coord val pad g lo a v >>= climbStep index coord val pad g (lo + a) := by
  intro a
  induction a with
  | zero => intro lo v; simp only [climbV_succ, climbV_zero', bind_pure, Nat.add_zero, pure_bind]
  | succ a ih =>
      intro lo v
      rw [climbV_succ, climbV_succ, bind_assoc]
      congr 1; funext x
      rw [ih]; simp only [Nat.add_assoc, Nat.add_comm 1 a]

theorem climbV_add : ∀ (a b lo : Nat) (v : Digest), climbV index coord val pad g lo (a + b) v =
    climbV index coord val pad g lo a v >>= climbV index coord val pad g (lo + a) b := by
  intro a
  induction a with
  | zero => intro b lo v; simp
  | succ a ih =>
      intro b lo v
      rw [show a + 1 + b = (a + b) + 1 by omega, climbV_succ, climbV_succ, bind_assoc]
      congr 1; funext x
      rw [ih]; simp only [Nat.add_assoc, Nat.add_comm 1 a]

end climb

/-! ## Unfolding the DFS -/

section dfs
variable {index coord : Nat} {leaves : List Nat} {leafH : Nat → M Digest} {val pad : Nat × Nat → Digest}

theorem dfsP_empty {level node : Nat} (h : hasLeaf leaves level node = false) :
    dfsP index coord leaves leafH val pad level node = pure (val (level, node)) := by
  cases level <;> simp [dfsP, h]

theorem dfsP_leaf {node : Nat} (h : hasLeaf leaves 0 node = true) :
    dfsP index coord leaves leafH val pad 0 node = leafH node := by
  simp [dfsP, h]

theorem dfsP_node {l node : Nat} (h : hasLeaf leaves (l + 1) node = true) :
    dfsP index coord leaves leafH val pad (l + 1) node = (do
      let left ← dfsP index coord leaves leafH val pad l (2 * node)
      let right ← dfsP index coord leaves leafH val pad l (2 * node + 1)
      nodeHashP 10 coord index (2 ^ (11 - (l + 1)) + node) left (dfsPad leaves pad l node) right) := by
  conv_lhs => unfold dfsP
  simp [h]

theorem hasLeaf_parent {l n : Nat} (h : hasLeaf leaves l n = true) : hasLeaf leaves (l + 1) (n / 2) = true := by
  obtain ⟨leaf, hm, he⟩ := (hasLeaf_iff _ _ _).mp h
  exact (hasLeaf_iff _ _ _).mpr ⟨leaf, hm, by rw [pow_succ, ← Nat.div_div_eq_div_mul, he]⟩

/-- A node with two non-empty children is a merge (zero pad, Core's `nodeHash`). -/
theorem dfsP_merge {l n : Nat} (hl : hasLeaf leaves l (2 * n) = true) (hr : hasLeaf leaves l (2 * n + 1) = true) :
    dfsP index coord leaves leafH val pad (l + 1) n = (do
      let left ← dfsP index coord leaves leafH val pad l (2 * n)
      let right ← dfsP index coord leaves leafH val pad l (2 * n + 1)
      nodeHash 10 coord index (2 ^ (11 - (l + 1)) + n) left right) := by
  have hp : hasLeaf leaves (l + 1) n = true := by
    have := hasLeaf_parent (leaves := leaves) hl; rwa [show 2 * n / 2 = n by omega] at this
  rw [dfsP_node hp]
  have : dfsPad leaves pad l n = 0 := by simp [dfsPad, hl, hr]
  simp only [this, nodeHashP_zero]

/-- **Path lemma.** Above a non-empty node on `g`'s root path, with every off-path sibling empty, the DFS climbs. -/
theorem dfsP_climb {g : Nat} (hg : g ∈ leaves) (lo : Nat) : ∀ d,
    (∀ k, lo ≤ k → k < lo + d → hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false) →
    dfsP index coord leaves leafH val pad (lo + d) (g / 2 ^ (lo + d)) =
      dfsP index coord leaves leafH val pad lo (g / 2 ^ lo) >>= climbV index coord val pad g lo d := by
  intro d
  induction d with
  | zero => intro _; simp only [Nat.add_zero, climbV_zero', bind_pure]
  | succ d ih =>
      intro hsib
      rw [show lo + (d + 1) = (lo + d) + 1 by omega]
      set k := lo + d with hk
      set n := g / 2 ^ k with hn
      have hdiv : g / 2 ^ (k + 1) = n / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
      have hpar : hasLeaf leaves (k + 1) (n / 2) = true := by rw [← hdiv]; exact hasLeaf_self hg _
      have hself : hasLeaf leaves k n = true := hasLeaf_self hg k
      have hsk : hasLeaf leaves k (n ^^^ 1) = false := hsib k (by omega) (by omega)
      have ihk := ih (fun k' h1 h2 => hsib k' h1 (by omega))
      have hrhs : dfsP index coord leaves leafH val pad lo (g / 2 ^ lo) >>= climbV index coord val pad g lo (d + 1) =
          dfsP index coord leaves leafH val pad k n >>= climbStep index coord val pad g k := by
        rw [ihk, bind_assoc]; congr 1; funext v; exact climbV_snoc index coord val pad g d lo v
      rw [hdiv, dfsP_node hpar, hrhs]
      have hx := xor_one_eq n
      rcases Nat.mod_two_eq_zero_or_one n with hpar2 | hpar2
      · have e1 : 2 * (n / 2) = n := by omega
        have e2 : 2 * (n / 2) + 1 = n ^^^ 1 := by omega
        have hpad : dfsPad leaves pad k (n / 2) = pad (k, n ^^^ 1) := by
          unfold dfsPad; rw [e2, e1]; simp [hself, hsk]
        rw [e2, e1, hpad, dfsP_empty hsk]
        congr 1; funext v
        simp [climbStep, ← hn, hpar2]
      · have e1 : 2 * (n / 2) = n ^^^ 1 := by omega
        have e2 : 2 * (n / 2) + 1 = n := by omega
        have hpad : dfsPad leaves pad k (n / 2) = pad (k, n ^^^ 1) := by
          unfold dfsPad; rw [e2, e1]; simp [hsk]
        rw [e2, e1, hpad, dfsP_empty hsk, pure_bind]
        congr 1; funext v
        simp [climbStep, ← hn, hpar2]

end dfs

/-! ## The three leaves of one bucket -/

/-- The canonical coordinate program: Core's post-order DFS of three sorted leaves `g0 < g1 < g2` of one bucket
followed by the four outer folds, as the five climbs of the stream schedule (`coordSchedule`). -/
def coordCanon (index coord : Nat) (leafH : Nat → M Digest) (val pad : Nat × Nat → Digest) (g0 g1 g2 : Nat) :
    M Digest :=
  if lcaLevel g0 g1 < lcaLevel g1 g2 then do
    let v0 ← leafH g0
    let v0 ← climbV index coord val pad g0 0 (lcaLevel g0 g1 - 1) v0
    let v1 ← leafH g1
    let v1 ← climbV index coord val pad g1 0 (lcaLevel g0 g1 - 1) v1
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g0 g1) + g1 / 2 ^ lcaLevel g0 g1) v0 v1
    let m ← climbV index coord val pad g1 (lcaLevel g0 g1) (lcaLevel g1 g2 - 1 - lcaLevel g0 g1) m
    let v2 ← leafH g2
    let v2 ← climbV index coord val pad g2 0 (lcaLevel g1 g2 - 1) v2
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g1 g2) + g2 / 2 ^ lcaLevel g1 g2) m v2
    climbV index coord val pad g2 (lcaLevel g1 g2) (11 - lcaLevel g1 g2) m
  else do
    let v0 ← leafH g0
    let v0 ← climbV index coord val pad g0 0 (lcaLevel g0 g1 - 1) v0
    let v1 ← leafH g1
    let v1 ← climbV index coord val pad g1 0 (lcaLevel g1 g2 - 1) v1
    let v2 ← leafH g2
    let v2 ← climbV index coord val pad g2 0 (lcaLevel g1 g2 - 1) v2
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g1 g2) + g2 / 2 ^ lcaLevel g1 g2) v1 v2
    let m ← climbV index coord val pad g2 (lcaLevel g1 g2) (lcaLevel g0 g1 - 1 - lcaLevel g1 g2) m
    let m ← nodeHash 10 coord index (2 ^ (11 - lcaLevel g0 g1) + g2 / 2 ^ lcaLevel g0 g1) v0 m
    climbV index coord val pad g2 (lcaLevel g0 g1) (11 - lcaLevel g0 g1) m

/-- The children of the LCA node of `g < g'` at level `l + 1`: `g`'s ancestor on the left, `g'`'s on the right. -/
theorem merge_children {g g' l : Nat} (hlt : g < g') (hl : lcaLevel g g' = l + 1) :
    2 * (g' / 2 ^ (l + 1)) = g / 2 ^ l ∧ 2 * (g' / 2 ^ (l + 1)) + 1 = g' / 2 ^ l := by
  have hs := div_sib_of_lca (show g ≠ g' by omega) hl
  have hm := div_pow_mono hlt.le l
  have hx := xor_one_eq (g / 2 ^ l)
  have hd : g' / 2 ^ (l + 1) = g' / 2 ^ l / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hd]
  generalize g / 2 ^ l = u at *
  generalize g' / 2 ^ l = v at *
  subst hs
  omega

section bucket
variable {index coord : Nat} {leafH : Nat → M Digest} {val pad : Nat × Nat → Digest}

/-- **Schedule ≡ DFS (Core side).** The DFS of the bucket subtree of three sorted leaves, followed by the four
outer folds, is the canonical five-climb program. -/
theorem dfsP_bucket {g0 g1 g2 b : Nat} (h01 : g0 < g1) (h12 : g1 < g2)
    (hb0 : g0 / 2 ^ 7 = b) (hb1 : g1 / 2 ^ 7 = b) (hb2 : g2 / 2 ^ 7 = b) :
    dfsP index coord [g0, g1, g2] leafH val pad 7 b >>= climbV index coord val pad g2 7 4 =
      coordCanon index coord leafH val pad g0 g1 g2 := by
  have p01 := lcaLevel_pos g0 g1
  have p12 := lcaLevel_pos g1 g2
  have l01 : lcaLevel g0 g1 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb0, hb1])
  have l12 : lcaLevel g1 g2 ≤ 7 := (div_eq_iff_lca (by omega) 7).mp (by rw [hb1, hb2])
  have l02 : lcaLevel g0 g2 = max (lcaLevel g0 g1) (lcaLevel g1 g2) := lca_outer h01 h12
  have hne : lcaLevel g0 g1 ≠ lcaLevel g1 g2 := lca_ne h01 h12
  have c10 : lcaLevel g1 g0 = lcaLevel g0 g1 := lcaLevel_comm _ _
  have c21 : lcaLevel g2 g1 = lcaLevel g1 g2 := lcaLevel_comm _ _
  have c20 : lcaLevel g2 g0 = lcaLevel g0 g2 := lcaLevel_comm _ _
  -- sibling emptiness from LCA levels (proved before any program equation is in context)
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
  have leafAt : ∀ g, g ∈ [g0, g1, g2] → dfsP index coord [g0, g1, g2] leafH val pad 0 (g / 2 ^ 0) = leafH g := by
    intro g hg; have h := hasLeaf_self hg 0; simp only [pow_zero, Nat.div_one] at h ⊢; exact dfsP_leaf h
  have outer : ∀ (lo : Nat) (v : Digest), lo ≤ 7 →
      climbV index coord val pad g2 lo (7 - lo) v >>= climbV index coord val pad g2 7 4 =
        climbV index coord val pad g2 lo (11 - lo) v := by
    intro lo v hlo
    rw [show 11 - lo = (7 - lo) + 4 by omega, climbV_add, show lo + (7 - lo) = 7 by omega]
  unfold coordCanon
  generalize hd01 : lcaLevel g0 g1 = d01 at *
  generalize hd12 : lcaLevel g1 g2 = d12 at *
  by_cases hA : d01 < d12
  · rw [if_pos hA]
    have top := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d12 (7 - d12) (fun k h1 _ => s2hi k (by omega))
    rw [show d12 + (7 - d12) = 7 by omega, hb2] at top
    obtain ⟨l, hl⟩ : ∃ l, d12 = l + 1 := ⟨d12 - 1, by omega⟩
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = l + 1 by rw [hd12, hl])
    have mid := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := l) (n := g2 / 2 ^ (l + 1)) (by rw [c12a]; exact hasLeaf_self m1 l) (by rw [c12b]; exact hasLeaf_self m2 l)
    rw [c12b, c12a] at mid
    have left := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 d01 (l - d01) (fun k h1 h2 => s1hi k h1 (by omega))
    rw [show d01 + (l - d01) = l by omega] at left
    obtain ⟨m, hm⟩ : ∃ m, d01 = m + 1 := ⟨d01 - 1, by omega⟩
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = m + 1 by rw [hd01, hm])
    have low := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := m) (n := g1 / 2 ^ (m + 1)) (by rw [c01a]; exact hasLeaf_self m0 m) (by rw [c01b]; exact hasLeaf_self m1 m)
    rw [c01b, c01a] at low
    have p0 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m0 0 m (fun k _ h2 => s0 k (by omega))
    have p1 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 0 m (fun k _ h2 => s1lo k (by omega))
    have p2 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 0 l (fun k _ h2 => s2lo k (by omega))
    simp only [Nat.zero_add] at p0 p1 p2
    rw [leafAt g0 m0] at p0; rw [leafAt g1 m1] at p1; rw [leafAt g2 m2] at p2
    rw [top, bind_assoc, hl, mid, ← hl, left, hm, low, ← hm, p0, p1, p2]
    have hout := fun v => outer (l + 1) v (by omega)
    simp only [bind_assoc, hl, hout]
    rw [show d01 - 1 = m by omega, show l + 1 - 1 - d01 = l - d01 by omega, show l + 1 - 1 = l by omega]
  · rw [if_neg hA]
    have hB : d12 < d01 := by omega
    have top := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d01 (7 - d01) (fun k h1 _ => s2hi k (by omega))
    rw [show d01 + (7 - d01) = 7 by omega, hb2] at top
    obtain ⟨l, hl⟩ : ∃ l, d01 = l + 1 := ⟨d01 - 1, by omega⟩
    obtain ⟨c01a, c01b⟩ := merge_children h01 (show lcaLevel g0 g1 = l + 1 by rw [hd01, hl])
    have e21 : g2 / 2 ^ (l + 1) = g1 / 2 ^ (l + 1) := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have e21' : g2 / 2 ^ l = g1 / 2 ^ l := div_eq_of_lca_le (by omega) (by rw [c21]; omega)
    have mid := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := l) (n := g2 / 2 ^ (l + 1)) (by rw [e21, c01a]; exact hasLeaf_self m0 l)
        (by rw [e21, c01b, ← e21']; exact hasLeaf_self m2 l)
    rw [e21, c01b, c01a, ← e21', ← e21] at mid
    have p0 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m0 0 l (fun k _ h2 => s0 k (by omega))
    have right := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 d12 (l - d12) (fun k h1 h2 => s2mid k h1 (by omega))
    rw [show d12 + (l - d12) = l by omega] at right
    obtain ⟨m, hm⟩ : ∃ m, d12 = m + 1 := ⟨d12 - 1, by omega⟩
    obtain ⟨c12a, c12b⟩ := merge_children h12 (show lcaLevel g1 g2 = m + 1 by rw [hd12, hm])
    have low := dfsP_merge (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      (l := m) (n := g2 / 2 ^ (m + 1)) (by rw [c12a]; exact hasLeaf_self m1 m) (by rw [c12b]; exact hasLeaf_self m2 m)
    rw [c12b, c12a] at low
    have p1 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m1 0 m (fun k _ h2 => s1lo k (by omega))
    have p2 := dfsP_climb (index := index) (coord := coord) (leafH := leafH) (val := val) (pad := pad)
      m2 0 m (fun k _ h2 => s2lo k (by omega))
    simp only [Nat.zero_add] at p0 p1 p2
    rw [leafAt g0 m0] at p0; rw [leafAt g1 m1] at p1; rw [leafAt g2 m2] at p2
    rw [top, bind_assoc, hl, mid, ← hl, p0, right, hm, low, ← hm, p1, p2]
    have hout := fun v => outer (l + 1) v (by omega)
    simp only [bind_assoc, hl, hout]
    rw [show d12 - 1 = m by omega, show l + 1 - 1 - d12 = l - d12 by omega, show l + 1 - 1 = l by omega]

end bucket

end SigGolfCandidate.T3M
