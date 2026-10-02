import SigGolfCandidate.T3M.Witness.Schedule

/-! # Bit arithmetic of the coordinate trees (stream W)

Lowest-common-ancestor levels (`lcaLevel`), heap indices `(2048 + g) / 2^k` of the ancestors of a global leaf
`g < 2048`, and siblings (`^^^ 1`). Used by the schedule ≡ DFS proofs. -/
namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3

/-! ## XOR with one -/

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

/-- Two numbers with the same half and different values are XOR-1 siblings. -/
theorem eq_xor_one_of {x y : Nat} (hdiv : x / 2 = y / 2) (hne : x ≠ y) : y = x ^^^ 1 := by
  have := xor_one_eq x; omega

theorem two_pow_add_xor_one {m u : Nat} (hm : 1 ≤ m) : (2 ^ m + u) ^^^ 1 = 2 ^ m + (u ^^^ 1) := by
  have h2 : 2 ^ m % 2 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]; simp
  rw [xor_one_eq, xor_one_eq u]
  have hd : (2 ^ m + u) / 2 = 2 ^ m / 2 + u / 2 := by omega
  omega

/-! ## Lowest common ancestors -/

/-- Two distinct leaves have the same ancestor at level `ℓ` iff their LCA level is at most `ℓ`. -/
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

/-- Below the LCA level the ancestors differ. -/
theorem div_ne_of_lt_lca {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : ℓ < lcaLevel x y) :
    x / 2 ^ ℓ ≠ y / 2 ^ ℓ := fun he => by have := (div_eq_iff_lca h ℓ).mp he; omega

/-- From the LCA level on the ancestors agree. -/
theorem div_eq_of_lca_le {x y : Nat} (h : x ≠ y) {ℓ : Nat} (hl : lcaLevel x y ≤ ℓ) :
    x / 2 ^ ℓ = y / 2 ^ ℓ := (div_eq_iff_lca h ℓ).mpr hl

theorem div_pow_mono {x y : Nat} (h : x ≤ y) (ℓ : Nat) : x / 2 ^ ℓ ≤ y / 2 ^ ℓ := Nat.div_le_div_right h

/-- For sorted leaves `x0 < x1 < x2` the outer LCA is the larger of the two adjacent ones. -/
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

/-- Adjacent LCA levels of sorted distinct leaves differ. -/
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

/-- At level `lcaLevel x y - 1` the ancestors are siblings. -/
theorem div_sib_of_lca {x y : Nat} (h : x ≠ y) {k : Nat} (hk : lcaLevel x y = k + 1) :
    y / 2 ^ k = x / 2 ^ k ^^^ 1 := by
  apply eq_xor_one_of
  · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ]
    exact div_eq_of_lca_le h (by omega)
  · exact fun he => div_ne_of_lt_lca h (show k < lcaLevel x y by omega) he

/-- The LCA of siblings' descendants. -/
theorem lca_of_div_sib {x y : Nat} {k : Nat} (hs : y / 2 ^ k = x / 2 ^ k ^^^ 1) : lcaLevel x y = k + 1 := by
  have hxy : x ≠ y := fun he => by rw [he] at hs; exact xor_one_ne _ hs.symm
  have hne : x / 2 ^ k ≠ y / 2 ^ k := by rw [hs]; exact (xor_one_ne _).symm
  have heq : x / 2 ^ (k + 1) = y / 2 ^ (k + 1) := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hs, xor_one_div_two]
  have h1 := (div_eq_iff_lca hxy (k + 1)).mp heq
  have h2 : ¬ lcaLevel x y ≤ k := fun hc => hne ((div_eq_iff_lca hxy k).mpr hc)
  omega

/-! ## Heap indices of a coordinate tree -/

/-- Heap index of the ancestor at level `ℓ ≤ 11` of a leaf `g`. -/
theorem heap_eq {g ℓ : Nat} (hl : ℓ ≤ 11) : (2048 + g) / 2 ^ ℓ = 2 ^ (11 - ℓ) + g / 2 ^ ℓ := by
  have h2 : 2048 = 2 ^ (11 - ℓ) * 2 ^ ℓ := by rw [← pow_add, Nat.sub_add_cancel hl]; norm_num
  rw [h2, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos ℓ), Nat.add_comm]

theorem heap_div_two (g k : Nat) : (2048 + g) / 2 ^ k / 2 = (2048 + g) / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

theorem heap_div_pow (g k a : Nat) : (2048 + g) / 2 ^ k / 2 ^ a = (2048 + g) / 2 ^ (k + a) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- Parity of an ancestor's heap index below the root is its node's parity. -/
theorem heap_mod_two {g k : Nat} (hk : k < 11) : (2048 + g) / 2 ^ k % 2 = g / 2 ^ k % 2 := by
  rw [heap_eq (by omega)]
  obtain ⟨m, hm⟩ : ∃ m, 11 - k = m + 1 := ⟨10 - k, by omega⟩
  rw [hm, pow_succ]; omega

/-- The heap index of a fold's parent: `E / 2 = 2^(11 - (k+1)) + g / 2^(k+1)`. -/
theorem heap_parent {g k : Nat} (hk : k < 11) :
    (2048 + g) / 2 ^ k / 2 = 2 ^ (11 - (k + 1)) + g / 2 ^ k / 2 := by
  rw [heap_div_two, heap_eq (by omega), Nat.div_div_eq_div_mul, ← pow_succ]

/-- Sibling heaps: if `lcaLevel g g' = k + 1` with `k ≤ 10`, the level-`k` ancestors are XOR-1 siblings. -/
theorem heap_sib {g g' k : Nat} (h : g ≠ g') (hk : k + 1 ≤ 11) (hl : lcaLevel g g' = k + 1) :
    (2048 + g) / 2 ^ k ^^^ 1 = (2048 + g') / 2 ^ k := by
  rw [heap_eq (by omega), heap_eq (by omega), two_pow_add_xor_one (by omega), div_sib_of_lca h hl]

/-- A heap index of the form `(2048 + g) / 2^K` with `g < 2048` that is at least 2 sits at level `K ≤ 10`. -/
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

/-- **The `Q` check.** If the sibling of one leaf's ancestor heap is another leaf's ancestor heap and that heap is at
least 2, both ancestors are at the same level `K ≤ 10` and the leaves' LCA is at level `K + 1`. -/
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

/-! ## Leaves of one bucket -/

theorem bucket_leaf_lt {b x : Nat} (hb : b < 8) (hx : x < 256) : b * 256 + x < 2048 := by omega

theorem bucket_div {b x k : Nat} (_hx : x < 256) (hk : k ≤ 8) :
    (b * 256 + x) / 2 ^ k = b * 2 ^ (8 - k) + x / 2 ^ k := by
  have h : b * 256 = b * 2 ^ (8 - k) * 2 ^ k := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hk]; norm_num
  rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.add_comm]

theorem bucket_div_eight {b x : Nat} (hx : x < 256) : (b * 256 + x) / 2 ^ 8 = b := by
  rw [bucket_div hx le_rfl]; simp only [Nat.sub_self, pow_zero, Nat.mul_one]
  rw [Nat.div_eq_of_lt (by norm_num; omega)]; simp

theorem bucket_div_outer {b x j : Nat} (hx : x < 256) : (b * 256 + x) / 2 ^ (8 + j) = b / 2 ^ j := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, bucket_div_eight hx]

/-- Leaves of one bucket have their LCA at level ≤ 8. -/
theorem lca_le_eight {b x y : Nat} (hx : x < 256) (hy : y < 256) (hxy : x ≠ y) :
    lcaLevel (b * 256 + x) (b * 256 + y) ≤ 8 :=
  (div_eq_iff_lca (by omega) 8).mp (by rw [bucket_div_eight hx, bucket_div_eight hy])

/-- The LCA of two leaves of one bucket is the LCA of their local indices. -/
theorem lca_bucket {b x y : Nat} (hx : x < 256) (hy : y < 256) (hxy : x ≠ y) :
    lcaLevel (b * 256 + x) (b * 256 + y) = lcaLevel x y := by
  have hl := lca_le_eight (b := b) hx hy hxy
  have hl' : lcaLevel x y ≤ 8 :=
    (div_eq_iff_lca hxy 8).mp (by rw [Nat.div_eq_of_lt (by norm_num; omega), Nat.div_eq_of_lt (by norm_num; omega)])
  have key : ∀ ℓ, ℓ ≤ 8 → ((b * 256 + x) / 2 ^ ℓ = (b * 256 + y) / 2 ^ ℓ ↔ x / 2 ^ ℓ = y / 2 ^ ℓ) := by
    intro ℓ hℓ; rw [bucket_div hx hℓ, bucket_div hy hℓ]; omega
  apply le_antisymm
  · rw [← div_eq_iff_lca (by omega), key _ hl']; exact div_eq_of_lca_le hxy le_rfl
  · rw [← div_eq_iff_lca hxy, ← key _ hl]; exact div_eq_of_lca_le (by omega) le_rfl

end SigGolfCandidate.T3M
