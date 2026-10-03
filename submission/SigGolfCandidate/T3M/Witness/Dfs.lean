import SigGolfCandidate.T3M.Witness.Schedule
import SigGolfCandidate.T3M.Witness.Basic

section

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem xor_one_div_two (x : Nat) : (x ^^^ 1) / 2 = x / 2 := by
  rw [Nat.xor_div_two]; simp
theorem xor_one_mod_two (x : Nat) : (x ^^^ 1) % 2 = 1 - x % 2 := by
  have h := @Nat.xor_mod_two_eq_one x 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (x ^^^ 1) with hy | hy <;> simp_all
theorem xor_one_eq (x : Nat) : x ^^^ 1 = 2 * (x / 2) + (1 - x % 2) := by
  have h1 := xor_one_div_two x
  have h2 := xor_one_mod_two x
  have := Nat.div_add_mod (x ^^^ 1) 2
  omega
theorem xor_one_ne (x : Nat) : x ^^^ 1 ≠ x := by
  have := xor_one_eq x; omega
theorem xor_one_xor_one (x : Nat) : x ^^^ 1 ^^^ 1 = x := by
  rw [Nat.xor_assoc]; simp
theorem eq_xor_one_of {x y : Nat} (hdiv : x / 2 = y / 2) (hne : x ≠ y) : y = x ^^^ 1 := by
  have := xor_one_eq x; omega
theorem two_pow_add_xor_one {m u : Nat} (hm : 1 ≤ m) : (2 ^ m + u) ^^^ 1 = 2 ^ m + (u ^^^ 1) := by
  have h2 : 2 ^ m % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]; simp
  rw [xor_one_eq, xor_one_eq u]
  have hd : (2 ^ m + u) / 2 = 2 ^ m / 2 + u / 2 := by omega
  omega
theorem div_eq_iff_lca {x y : Nat} (h : x ≠ y) (ℓ : Nat) : x / 2 ^ ℓ = y / 2 ^ ℓ ↔ lcaLevel x y ≤ ℓ := by
  have hx : x ^^^ y ≠ 0 := Nat.xor_ne_zero_iff.mpr h
  unfold lcaLevel
  constructor
  · intro he
    have h0 : (x ^^^ y) / 2 ^ ℓ = 0 := by rw [Nat.xor_div_two_pow, he, Nat.xor_self]
    have hlt : x ^^^ y < 2 ^ ℓ := by
      by_contra hc
      have := Nat.div_pos (Nat.le_of_not_lt hc) (Nat.two_pow_pos ℓ)
      omega
    have := (Nat.log2_lt hx).mpr hlt
    omega
  · intro hl
    have hlt : x ^^^ y < 2 ^ ℓ := (Nat.log2_lt hx).mp (by omega)
    have h0 : (x ^^^ y) / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hlt
    rw [Nat.xor_div_two_pow] at h0
    exact xor_eq_zero_iff.mp h0
theorem lcaLevel_comm (x y : Nat) : lcaLevel x y = lcaLevel y x := by
  unfold lcaLevel; rw [Nat.xor_comm]
theorem lcaLevel_pos (x y : Nat) : 0 < lcaLevel x y := by unfold lcaLevel; omega
theorem div_ne_of_lt_lca {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : ℓ < lcaLevel x y) :
    x / 2 ^ ℓ ≠ y / 2 ^ ℓ := fun he => by have := (div_eq_iff_lca h ℓ).mp he; omega
theorem div_eq_of_lca_le {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : lcaLevel x y ≤ ℓ) :
    x / 2 ^ ℓ = y / 2 ^ ℓ := (div_eq_iff_lca h ℓ).mpr hl
theorem div_pow_mono {x y : Nat} (h : x ≤ y) (ℓ : Nat) : x / 2 ^ ℓ ≤ y / 2 ^ ℓ := Nat.div_le_div_right h
theorem lca_outer {x0 x1 x2 : Nat} (h01 : x0 < x1) (h12 : x1 < x2) :
    lcaLevel x0 x2 = max (lcaLevel x0 x1) (lcaLevel x1 x2) := by
  have key : ∀ ℓ, x0 / 2 ^ ℓ = x2 / 2 ^ ℓ ↔ x0 / 2 ^ ℓ = x1 / 2 ^ ℓ ∧ x1 / 2 ^ ℓ = x2 / 2 ^ ℓ := by
    intro ℓ
    have a := div_pow_mono h01.le ℓ
    have b := div_pow_mono h12.le ℓ
    constructor
    · intro he; constructor <;> omega
    · rintro ⟨h1, h2⟩; omega
  apply le_antisymm
  · rw [← div_eq_iff_lca (by omega), key]
    exact ⟨div_eq_of_lca_le (by omega) (le_max_left _ _), div_eq_of_lca_le (by omega) (le_max_right _ _)⟩
  · apply max_le
    · rw [← div_eq_iff_lca (by omega)]; exact ((key _).mp (div_eq_of_lca_le (by omega) le_rfl)).1
    · rw [← div_eq_iff_lca (by omega)]; exact ((key _).mp (div_eq_of_lca_le (by omega) le_rfl)).2
theorem lca_ne {x0 x1 x2 : Nat} (h01 : x0 < x1) (h12 : x1 < x2) : lcaLevel x0 x1 ≠ lcaLevel x1 x2 := by
  intro he
  set d := lcaLevel x0 x1 with hd
  have hpos := lcaLevel_pos x0 x1
  have n01 := div_ne_of_lt_lca (show x0 ≠ x1 by omega) (show d - 1 < lcaLevel x0 x1 by omega)
  have n12 := div_ne_of_lt_lca (show x1 ≠ x2 by omega) (show d - 1 < lcaLevel x1 x2 by omega)
  have e01 := div_eq_of_lca_le (show x0 ≠ x1 by omega) (show lcaLevel x0 x1 ≤ d by omega)
  have e12 := div_eq_of_lca_le (show x1 ≠ x2 by omega) (show lcaLevel x1 x2 ≤ d by omega)
  have hp : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at e01 e12
  have a := div_pow_mono h01.le (d - 1)
  have b := div_pow_mono h12.le (d - 1)
  omega
theorem div_sib_of_lca {x y : Nat} (h : x ≠ y) {k : Nat} (hk : lcaLevel x y = k + 1) :
    y / 2 ^ k = x / 2 ^ k ^^^ 1 := by
  apply eq_xor_one_of
  · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    exact div_eq_of_lca_le h (by omega)
  · exact fun he => div_ne_of_lt_lca h (show k < lcaLevel x y by omega) he
theorem lca_of_div_sib {x y : Nat} {k : Nat} (hs : y / 2 ^ k = x / 2 ^ k ^^^ 1) : lcaLevel x y = k + 1 := by
  have hxy : x ≠ y := fun he => by rw [he] at hs; exact xor_one_ne _ hs.symm
  have hne : x / 2 ^ k ≠ y / 2 ^ k := by rw [hs]; exact (xor_one_ne _).symm
  have heq : x / 2 ^ (k + 1) = y / 2 ^ (k + 1) := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hs, xor_one_div_two]
  have h1 := (div_eq_iff_lca hxy (k + 1)).mp heq
  have h2 : ¬ lcaLevel x y ≤ k := fun hc => hne ((div_eq_iff_lca hxy k).mpr hc)
  omega
theorem heap_eq {g ℓ : Nat} (hl : ℓ ≤ 11) : (2048 + g) / 2 ^ ℓ = 2 ^ (11 - ℓ) + g / 2 ^ ℓ := by
  have h2 : 2048 = 2 ^ (11 - ℓ) * 2 ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hl]; norm_num
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos ℓ), Nat.add_comm]
theorem heap_div_two (g k : Nat) : (2048 + g) / 2 ^ k / 2 = (2048 + g) / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]
theorem heap_div_pow (g k a : Nat) : (2048 + g) / 2 ^ k / 2 ^ a = (2048 + g) / 2 ^ (k + a) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
theorem heap_mod_two {g k : Nat} (hk : k < 11) : (2048 + g) / 2 ^ k % 2 = g / 2 ^ k % 2 := by
  rw [heap_eq (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, 11 - k = m + 1 := ⟨10 - k, by omega⟩
  rw [hm, pow_succ]; omega
theorem heap_parent {g k : Nat} (hk : k < 11) :
    (2048 + g) / 2 ^ k / 2 = 2 ^ (11 - (k + 1)) + g / 2 ^ k / 2 := by
  rw [heap_div_two, heap_eq (by omega), Nat.div_div_eq_div_mul, ← pow_succ]
theorem heap_sib {g g' k : Nat} (h : g ≠ g') (hk : k + 1 ≤ 11) (hl : lcaLevel g g' = k + 1) :
    (2048 + g) / 2 ^ k ^^^ 1 = (2048 + g') / 2 ^ k := by
  rw [heap_eq (by omega), heap_eq (by omega), two_pow_add_xor_one (by omega), div_sib_of_lca h hl]
theorem heap_level_of_two_le {g K : Nat} (hg : g < 2048) (h2 : 2 ≤ (2048 + g) / 2 ^ K) : K ≤ 10 := by
  by_contra hc
  have : (2048 + g) / 2 ^ K < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K)]
    have : 2 ^ 11 ≤ 2 ^ K := Nat.pow_le_pow_right (by omega) (by omega)
    have h12 : (2 : Nat) ^ 12 = 2 * 2 ^ 11 := by norm_num
    calc 2048 + g < 4096 := by omega
      _ = 2 * 2 ^ 11 := by norm_num
      _ ≤ 2 * 2 ^ K := by omega
  omega
theorem log2_heap {g K : Nat} (hg : g < 2048) (hK : K ≤ 11) : ((2048 + g) / 2 ^ K).log2 = 11 - K := by
  rw [heap_eq hK]
  have hlt : g / 2 ^ K < 2 ^ (11 - K) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos K), ← pow_add, Nat.sub_add_cancel hK]; norm_num; omega
  rw [Nat.log2_eq_iff (by positivity)]
  generalize g / 2 ^ K = d at *
  constructor
  · omega
  · rw [pow_succ]; omega
theorem log2_xor_one {x : Nat} (hx : 2 ≤ x) : (x ^^^ 1).log2 = x.log2 := by
  have hx1 : x ^^^ 1 ≠ 0 := by have := xor_one_eq x; omega
  have hx0 : x ≠ 0 := by omega
  have e1 := Nat.log2_self_le hx0
  have e2 := Nat.lt_log2_self (n := x)
  have hle : 1 ≤ x.log2 := (Nat.le_log2 hx0).mpr (by omega)
  rw [Nat.log2_eq_iff hx1]
  have hxo := xor_one_eq x
  obtain ⟨m, hm⟩ : ∃ m, x.log2 = m + 1 := ⟨x.log2 - 1, by omega⟩
  rw [hm] at e1 e2 ⊢
  rw [pow_succ] at e1 e2 ⊢
  constructor <;> omega
theorem heap_sib_inv {g g' K K' : Nat} (hg : g < 2048) (hg' : g' < 2048)
    (hs : (2048 + g) / 2 ^ K ^^^ 1 = (2048 + g') / 2 ^ K') (h2 : 2 ≤ (2048 + g') / 2 ^ K') :
    K' ≤ 10 ∧ K = K' ∧ lcaLevel g g' = K + 1 := by
  have hK' := heap_level_of_two_le hg' h2
  have hx2 : 2 ≤ (2048 + g) / 2 ^ K := by
    have := xor_one_eq ((2048 + g) / 2 ^ K); omega
  have hK := heap_level_of_two_le hg hx2
  have hlog := congrArg Nat.log2 hs
  rw [log2_xor_one hx2, log2_heap hg (by omega), log2_heap hg' (by omega)] at hlog
  have hKK : K = K' := by omega
  subst hKK
  refine ⟨hK', rfl, ?_⟩
  rw [heap_eq (by omega), heap_eq (by omega), two_pow_add_xor_one (by omega)] at hs
  exact lca_of_div_sib (by omega)
theorem bucket_leaf_lt {b x : Nat} (hb : b < 16) (hx : x < 128) : b * 128 + x < 2048 := by omega
theorem bucket_div {b x k : Nat} (_hx : x < 128) (hk : k ≤ 7) :
    (b * 128 + x) / 2 ^ k = b * 2 ^ (7 - k) + x / 2 ^ k := by
  have h : b * 128 = b * 2 ^ (7 - k) * 2 ^ k := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hk]; norm_num
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.add_comm]
theorem bucket_div_eight {b x : Nat} (hx : x < 128) : (b * 128 + x) / 2 ^ 7 = b := by
  rw [bucket_div hx le_rfl]; simp only [Nat.sub_self, pow_zero, Nat.mul_one]
  rw [Nat.div_eq_of_lt (by norm_num; omega)]; simp
theorem bucket_div_outer {b x j : Nat} (hx : x < 128) : (b * 128 + x) / 2 ^ (7 + j) = b / 2 ^ j := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, bucket_div_eight hx]
theorem lca_le_eight {b x y : Nat} (hx : x < 128) (hy : y < 128) (hxy : x ≠ y) :
    lcaLevel (b * 128 + x) (b * 128 + y) ≤ 7 :=
  (div_eq_iff_lca (by omega) 7).mp (by rw [bucket_div_eight hx, bucket_div_eight hy])
theorem lca_bucket {b x y : Nat} (hx : x < 128) (hy : y < 128) (hxy : x ≠ y) :
    lcaLevel (b * 128 + x) (b * 128 + y) = lcaLevel x y := by
  have hl := lca_le_eight (b := b) hx hy hxy
  have hl' : lcaLevel x y ≤ 7 :=
    (div_eq_iff_lca hxy 7).mp (by rw [Nat.div_eq_of_lt (by norm_num; omega), Nat.div_eq_of_lt (by norm_num; omega)])
  have key : ∀ ℓ, ℓ ≤ 7 → ((b * 128 + x) / 2 ^ ℓ = (b * 128 + y) / 2 ^ ℓ ↔ x / 2 ^ ℓ = y / 2 ^ ℓ) := by
    intro ℓ hℓ; rw [bucket_div hx hℓ, bucket_div hy hℓ]; omega
  apply le_antisymm
  · rw [← div_eq_iff_lca (by omega), key _ hl']; exact div_eq_of_lca_le hxy le_rfl
  · rw [← div_eq_iff_lca hxy, ← key _ hl]; exact div_eq_of_lca_le (by omega) le_rfl
end SigGolfCandidate.T3M
end

section


namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
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
theorem hasLeaf_sib_false {leaves : List Nat} {g k : Nat}
    (h : ∀ g' ∈ leaves, g' ≠ g → lcaLevel g g' ≠ k + 1) : hasLeaf leaves k (g / 2 ^ k ^^^ 1) = false := by
  rw [hasLeaf_false_iff]
  intro g' hg' he
  by_cases hgg : g' = g
  · subst hgg; exact xor_one_ne _ he.symm
  · exact h g' hg' hgg (lca_of_div_sib he)
def dfsPad (leaves : List Nat) (pad : Nat × Nat → Digest) (level node : Nat) : Digest :=
  if !hasLeaf leaves level (2 * node) then pad (level, 2 * node)
  else if !hasLeaf leaves level (2 * node + 1) then pad (level, 2 * node + 1) else 0
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
def leafHP (index coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads) (node : Nat) : M Digest :=
  ftsLeafP index coord node (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
    (values.getD (leaves.idxOf node) 0)
    (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩)
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
def climbStep (index coord : Nat) (val pad : Nat × Nat → Digest) (g k : Nat) (v : Digest) : M Digest :=
  if g / 2 ^ k % 2 = 1 then
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) (val (k, g / 2 ^ k ^^^ 1)) (pad (k, g / 2 ^ k ^^^ 1)) v
  else
    nodeHashP 10 coord index (2 ^ (11 - (k + 1)) + g / 2 ^ k / 2) v (pad (k, g / 2 ^ k ^^^ 1)) (val (k, g / 2 ^ k ^^^ 1))
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
end
