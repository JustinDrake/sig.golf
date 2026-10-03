import Mathlib.Data.List.Sort
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm
import SigGolfCandidate.SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef

section

namespace SphincsSecurity.Octopus
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1
def xorSum (vs : List Nat) : Nat := (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum
def octH (H : Nat) (vs : List Nat) : Nat := H + 2 + xorSum vs - 2 * vs.length
def octopusSize (vs : List Nat) : Nat :=
  14 + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length
theorem octopusSize_eq (vs : List Nat) : octopusSize vs = octH 14 vs := rfl
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)
def leafOf (N r : Nat) : Nat := N / 2 ^ (34 + 14 * r) % 2 ^ 14
def leavesOf (N : Nat) : List Nat := (List.range 15).map (leafOf N)
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ 118)
def Nadm : Nat := 587603809105224201844661965127195603157454143488
def pstep (K y M : Nat) (T : List Nat) : List Nat :=
  (List.range (K + 1)).map fun j =>
    (2 * y * T.getD j 0 + ((List.range (j + 1)).map fun i => T.getD i 0 * T.getD (j - i) 0).sum) % M
def piter (K y M : Nat) : Nat → List Nat → List Nat
  | 0, T => T
  | k + 1, T => piter K y M k (pstep K y M T)
def pB : Nat := 224
def packedCount : Nat := ((piter 15 (2 ^ pB) (2 ^ (pB * 119)) 14 [0, 1]).getD 15 0) % (2 ^ pB - 1)
theorem packedCount_eq : packedCount = Nadm := by decide +kernel
end SphincsSecurity.Octopus
end

section





namespace SphincsSecurity.Octopus
open Finset Polynomial
theorem testBit_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) (i : ℕ) :
    (z + 2 ^ H).testBit i = (decide (i = H) || z.testBit i) := by
  rw [Nat.add_comm]
  rcases lt_trichotomy i H with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz]; simp
  · have hH : 2 ^ (H + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 2 ^ H + z < 2 ^ i := by rw [pow_succ] at hH; omega
    have h2 : z < 2 ^ i := by rw [pow_succ] at hH; omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [h.ne']
theorem xor_shift_shift {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    (x + 2 ^ H) ^^^ (y + 2 ^ H) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_two_pow hx, testBit_add_two_pow hy]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]
theorem xor_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    x ^^^ (y + 2 ^ H) = (x ^^^ y) + 2 ^ H := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_add_two_pow hy, testBit_add_two_pow (Nat.xor_lt_two_pow hx hy),
    Nat.testBit_xor]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]
theorem bitLen_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) : bitLen (z + 2 ^ H) = H + 1 := by
  unfold bitLen
  have h2 : z + 2 ^ H < 2 ^ (H + 1) := by rw [pow_succ]; omega
  rw [if_neg (by positivity),
    (Nat.log2_eq_iff (n := z + 2 ^ H) (k := H) (by positivity)).2 ⟨by omega, h2⟩]
theorem bitLen_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    bitLen (x ^^^ (y + 2 ^ H)) = H + 1 := by
  rw [xor_cross hx hy, bitLen_add_two_pow (Nat.xor_lt_two_pow hx hy)]
@[simp] theorem xorSum_nil : xorSum [] = 0 := rfl
@[simp] theorem xorSum_single (a : ℕ) : xorSum [a] = 0 := rfl
theorem xorSum_cons_cons (a b : ℕ) (t : List ℕ) :
    xorSum (a :: b :: t) = bitLen (a ^^^ b) + xorSum (b :: t) := by
  simp [xorSum]
theorem xorSum_append (a : List ℕ) (x y : ℕ) (b : List ℕ) :
    xorSum (a ++ x :: y :: b) = xorSum (a ++ [x]) + bitLen (x ^^^ y) + xorSum (y :: b) := by
  induction a with
  | nil => simp [xorSum_cons_cons]
  | cons c a ih =>
    cases a with
    | nil => simp [xorSum_cons_cons]; omega
    | cons d a =>
      simp only [List.cons_append] at ih ⊢
      rw [xorSum_cons_cons, ih, xorSum_cons_cons]; omega
theorem xorSum_map_shift {H : ℕ} : ∀ (l : List ℕ), (∀ z ∈ l, z < 2 ^ H) →
    xorSum (l.map (· + 2 ^ H)) = xorSum l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ih := xorSum_map_shift (b :: t) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons] at ih ⊢
    rw [xorSum_cons_cons, xorSum_cons_cons, ih,
      xor_shift_shift (h a (by simp)) (h b (by simp))]
def glue (H : ℕ) (L R : Finset ℕ) : Finset ℕ := L ∪ R.map (addRightEmbedding (2 ^ H))
def lo (H : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (· < 2 ^ H)
def hi (H : ℕ) (S : Finset ℕ) : Finset ℕ := (S.filter (2 ^ H ≤ ·)).image (· - 2 ^ H)
def Below (H : ℕ) (S : Finset ℕ) : Prop := ∀ x ∈ S, x < 2 ^ H
theorem below_iff (H : ℕ) (S : Finset ℕ) : Below H S ↔ S ∈ (range (2 ^ H)).powerset := by
  simp [Below, subset_iff]
theorem mem_glue {H : ℕ} {L R : Finset ℕ} {x : ℕ} :
    x ∈ glue H L R ↔ x ∈ L ∨ (2 ^ H ≤ x ∧ x - 2 ^ H ∈ R) := by
  simp only [glue, mem_union, mem_map, addRightEmbedding_apply]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by simpa using ha⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, h2, by omega⟩
theorem glue_below {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    Below (H + 1) (glue H L R) := by
  intro x hx
  rw [mem_glue] at hx
  rw [pow_succ]
  rcases hx with h | ⟨h1, h2⟩
  · have := hL x h; omega
  · have := hR _ h2; omega
theorem lo_below (H : ℕ) (S : Finset ℕ) : Below H (lo H S) := by
  intro x hx; simp only [lo, mem_filter] at hx; exact hx.2
theorem hi_below {H : ℕ} {S : Finset ℕ} (hS : Below (H + 1) S) : Below H (hi H S) := by
  intro x hx
  simp only [hi, mem_image, mem_filter] at hx
  obtain ⟨a, ⟨ha, h1⟩, rfl⟩ := hx
  have := hS a ha; rw [pow_succ] at this; omega
theorem glue_lo_hi {H : ℕ} {S : Finset ℕ} : glue H (lo H S) (hi H S) = S := by
  ext x
  rw [mem_glue]
  simp only [lo, hi, mem_filter, mem_image]
  constructor
  · rintro (⟨h, _⟩ | ⟨h1, a, ⟨ha, h2⟩, h3⟩)
    · exact h
    · have : a = x := by omega
      exact this ▸ ha
  · intro h
    by_cases hx : x < 2 ^ H
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨by omega, x, ⟨h, by omega⟩, rfl⟩
theorem lo_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : lo H (glue H L R) = L := by
  ext x
  simp only [lo, mem_filter, mem_glue]
  constructor
  · rintro ⟨h | ⟨h1, _⟩, h2⟩
    · exact h
    · omega
  · intro h; exact ⟨Or.inl h, hL x h⟩
theorem hi_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : hi H (glue H L R) = R := by
  ext x
  simp only [hi, mem_image, mem_filter, mem_glue]
  constructor
  · rintro ⟨a, ⟨h | ⟨h1, h2⟩, h3⟩, rfl⟩
    · have := hL a h; omega
    · exact h2
  · intro h
    exact ⟨x + 2 ^ H, ⟨Or.inr ⟨by omega, by simpa using h⟩, by omega⟩, by omega⟩
theorem card_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).card = L.card + R.card := by
  unfold glue
  rw [card_union_of_disjoint, card_map]
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_map, addRightEmbedding_apply] at hx'
  obtain ⟨a, _, rfl⟩ := hx'
  have := hL _ hx; omega
theorem glue_empty_empty (H : ℕ) : glue H ∅ ∅ = ∅ := by simp [glue]
theorem glue_ne_empty_left {H : ℕ} {L R : Finset ℕ} (h : L ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x ∈ glue H L R := mem_glue.mpr (Or.inl hx)
  rw [h'] at this; simp at this
theorem glue_ne_empty_right {H : ℕ} {L R : Finset ℕ} (h : R ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x + 2 ^ H ∈ glue H L R := mem_glue.mpr (Or.inr ⟨by omega, by simpa using hx⟩)
  rw [h'] at this; simp at this
theorem sort_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).sort = L.sort ++ R.sort.map (· + 2 ^ H) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) (sortedLT_sort _).pairwise
  · rw [List.pairwise_append, List.pairwise_map]
    refine ⟨(sortedLT_sort _).pairwise, (sortedLT_sort _).pairwise.imp (by omega), ?_⟩
    intro a ha b hb
    rw [mem_sort] at ha
    simp only [List.mem_map, mem_sort] at hb
    obtain ⟨c, _, rfl⟩ := hb
    have := hL a ha; omega
  · intro x
    simp only [mem_sort, mem_glue, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x - 2 ^ H, h2, by omega⟩
    · rintro (h | ⟨c, hc, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by simpa using hc⟩
def E (H : ℕ) (S : Finset ℕ) : ℕ := H + 2 + xorSum S.sort
def oc (H : ℕ) (S : Finset ℕ) : ℕ := octH H S.sort
theorem oc_eq (H : ℕ) (S : Finset ℕ) : oc H S = E H S - 2 * S.card := by
  simp [oc, octH, E, length_sort]
theorem E_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) :
    E (H + 1) (glue H L ∅) = E H L + 1 := by
  unfold E
  rw [sort_glue hL]
  simp; omega
theorem E_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) :
    E (H + 1) (glue H ∅ R) = E H R + 1 := by
  unfold E
  rw [sort_glue (by simp [Below])]
  simp only [sort_empty, List.nil_append]
  rw [xorSum_map_shift _ (fun z hz => hR z ((mem_sort _).mp hz))]; omega
theorem E_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : E (H + 1) (glue H L R) = E H L + E H R := by
  unfold E
  rw [sort_glue hL]
  rcases List.eq_nil_or_concat L.sort with h | ⟨a, x, hx⟩
  · exact absurd (by simpa using congrArg List.toFinset h) hL0
  rw [List.concat_eq_append] at hx
  cases hy : R.sort with
  | nil => exact absurd (by simpa using congrArg List.toFinset hy) hR0
  | cons y b =>
    have hxL : x ∈ L := by rw [← mem_sort (r := (· ≤ ·)), hx]; simp
    have hyR : y ∈ R := by rw [← mem_sort (r := (· ≤ ·)), hy]; simp
    have hb : ∀ z ∈ y :: b, z < 2 ^ H := fun z hz => hR z (by rw [← mem_sort (r := (· ≤ ·)), hy]; exact hz)
    rw [hx, List.map_cons, List.append_assoc, List.singleton_append, xorSum_append,
      bitLen_cross (hL x hxL) (hR y hyR)]
    have := xorSum_map_shift (y :: b) hb
    rw [List.map_cons] at this
    rw [this]; omega
theorem below_zero {S : Finset ℕ} (hS : Below 0 S) (h0 : S ≠ ∅) : S = {0} := by
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h0
  ext y
  simp only [mem_singleton]
  constructor
  · intro hy; have := hS y hy; simp at this; exact this
  · rintro rfl; have := hS x hx; simp at this; exact this ▸ hx
theorem two_card_le_E : ∀ (H : ℕ) (S : Finset ℕ), Below H S → S ≠ ∅ → 2 * S.card ≤ E H S
  | 0, S, hS, h0 => by
    rw [below_zero hS h0]; simp [E]
  | H + 1, S, hS, h0 => by
    rw [← glue_lo_hi (H := H) (S := S)] at h0 ⊢
    have hL := lo_below H S
    have hR := hi_below hS
    rw [card_glue hL]
    by_cases hL0 : lo H S = ∅
    · have hR0 : hi H S ≠ ∅ := fun h => h0 (by rw [hL0, h, glue_empty_empty])
      have := two_card_le_E H _ hR hR0
      rw [hL0, E_glue_right hR]; simp; omega
    · by_cases hR0 : hi H S = ∅
      · have := two_card_le_E H _ hL hL0
        rw [hR0, E_glue_left hL]; simp; omega
      · have h1 := two_card_le_E H _ hL hL0
        have h2 := two_card_le_E H _ hR hR0
        rw [E_glue_both hL hR hL0 hR0]; omega
theorem oc_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) (hL0 : L ≠ ∅) :
    oc (H + 1) (glue H L ∅) = oc H L + 1 := by
  have := two_card_le_E H L hL hL0
  rw [oc_eq, oc_eq, E_glue_left hL, card_glue hL]; simp; omega
theorem oc_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) (hR0 : R ≠ ∅) :
    oc (H + 1) (glue H ∅ R) = oc H R + 1 := by
  have := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, E_glue_right hR, card_glue (by simp [Below])]; simp; omega
theorem oc_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : oc (H + 1) (glue H L R) = oc H L + oc H R := by
  have h1 := two_card_le_E H L hL hL0
  have h2 := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, oc_eq, E_glue_both hL hR hL0 hR0, card_glue hL]; omega
theorem sum_powerset_succ {M : Type*} [AddCommMonoid M] (H : ℕ) (f : Finset ℕ → M) :
    ∑ S ∈ (range (2 ^ (H + 1))).powerset, f S =
      ∑ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset, f (glue H L R) := by
  rw [← sum_product']
  refine sum_nbij' (fun S => (lo H S, hi H S)) (fun p => glue H p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [← below_iff] at hS
    rw [mem_product, ← below_iff, ← below_iff]
    exact ⟨lo_below H S, hi_below hS⟩
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    rw [← below_iff]
    exact glue_below h.1 h.2
  · intro S _; exact glue_lo_hi
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    simp only [lo_glue h.1, hi_glue h.1]
  · intro S _; simp only [glue_lo_hi]
noncomputable def mono (y H : ℕ) (S : Finset ℕ) : ℕ[X] :=
  if S = ∅ then 0 else monomial S.card (y ^ oc H S)
noncomputable def Q (y H : ℕ) : ℕ[X] := ∑ S ∈ (range (2 ^ H)).powerset, mono y H S
theorem mono_glue (y : ℕ) {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    mono y (H + 1) (glue H L R) =
      (if R = ∅ then C y * mono y H L else 0) + (if L = ∅ then C y * mono y H R else 0) +
        mono y H L * mono y H R := by
  by_cases hL0 : L = ∅ <;> by_cases hR0 : R = ∅
  · subst hL0; subst hR0; simp [mono, glue_empty_empty]
  · subst hL0
    rw [mono, if_neg (glue_ne_empty_right hR0), card_glue hL, oc_glue_right hR hR0]
    simp only [mono, hR0, if_true, if_false, zero_mul, add_zero, zero_add, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · subst hR0
    rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_left hL hL0]
    simp only [mono, hL0, if_true, if_false, zero_mul, add_zero, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_both hL hR hL0 hR0]
    simp [mono, hL0, hR0, monomial_mul_monomial, pow_add]
theorem Q_succ (y H : ℕ) : Q y (H + 1) = C (2 * y) * Q y H + Q y H * Q y H := by
  unfold Q
  rw [sum_powerset_succ]
  have hmem : ∀ S ∈ (range (2 ^ H)).powerset, Below H S := fun S hS => (below_iff H S).mpr hS
  rw [sum_congr rfl fun L hL => sum_congr rfl fun R hR => mono_glue y (hmem L hL) (hmem R hR)]
  simp only [sum_add_distrib]
  rw [sum_mul_sum]
  congr 1
  have e1 : ∀ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset,
      (if R = ∅ then C y * mono y H L else 0) = C y * mono y H L := by
    intro L _; rw [sum_ite_eq']; simp
  rw [sum_congr rfl e1, sum_comm]
  rw [sum_congr rfl fun R _ => sum_ite_eq' (range (2 ^ H)).powerset ∅ (fun _ => C y * mono y H R)]
  simp only [empty_mem_powerset, if_true]
  rw [← mul_sum, ← two_mul, ← mul_assoc]
  congr 1
  simp [map_mul]
theorem Q_zero (y : ℕ) : Q y 0 = X := by
  unfold Q
  have : (range (2 ^ 0)).powerset = {∅, {0}} := by decide
  rw [this, sum_pair (by decide)]
  simp [mono, oc, octH, xorSum, X]
theorem coeff_Q_succ (y H j : ℕ) : (Q y (H + 1)).coeff j =
    2 * y * (Q y H).coeff j + ∑ i ∈ range (j + 1), (Q y H).coeff i * (Q y H).coeff (j - i) := by
  rw [Q_succ, coeff_add, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
theorem coeff_Q (y H j : ℕ) (hj : j ≠ 0) :
    (Q y H).coeff j = ∑ S ∈ powersetCard j (range (2 ^ H)), y ^ oc H S := by
  unfold Q
  rw [finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  unfold mono
  by_cases h : S = ∅
  · subst h; simp [Ne.symm hj]
  · simp [h, coeff_monomial]
end SphincsSecurity.Octopus
end

section



namespace SphincsSecurity.Octopus
open Finset Polynomial
theorem list_sum_map_range' (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp
theorem getD_pstep (K y M : ℕ) (T : List ℕ) {j : ℕ} (hj : j ≤ K) :
    (pstep K y M T).getD j 0 =
      (2 * y * T.getD j 0 + ∑ i ∈ range (j + 1), T.getD i 0 * T.getD (j - i) 0) % M := by
  unfold pstep
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp [list_sum_map_range']
def Rep (K y M H : ℕ) (T : List ℕ) : Prop := ∀ j ≤ K, T.getD j 0 = (Q y H).coeff j % M
theorem rep_pstep {K y M H : ℕ} {T : List ℕ} (h : Rep K y M H T) :
    Rep K y M (H + 1) (pstep K y M T) := by
  intro j hj
  rw [getD_pstep K y M T hj, coeff_Q_succ]
  show Nat.ModEq M _ _
  apply Nat.ModEq.add
  · exact Nat.ModEq.mul_left _ (by rw [h j hj]; exact Nat.mod_modEq _ _)
  · refine Nat.ModEq.sum fun i hi => ?_
    have hi' : i ≤ K := by rw [mem_range] at hi; omega
    rw [h i hi', h (j - i) (by omega)]
    exact (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)
theorem rep_piter {K y M : ℕ} : ∀ (k H : ℕ) (T : List ℕ), Rep K y M H T →
    Rep K y M (H + k) (piter K y M k T)
  | 0, _, _, h => h
  | k + 1, H, T, h => by
    have := rep_piter k (H + 1) _ (rep_pstep h)
    rwa [show H + 1 + k = H + (k + 1) by omega] at this
theorem rep_zero (K y M : ℕ) (hM : 1 < M) : Rep K y M 0 [0, 1] := by
  intro j _
  rw [Q_zero, coeff_X]
  rcases j with _ | _ | j
  · simp
  · simp [Nat.mod_eq_of_lt hM]
  · simp
theorem mod_pow_sum {y n : ℕ} (hn : 0 < n) (P : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (hP : P.card < y) :
    (∑ S ∈ P, y ^ g S) % y ^ n = ∑ S ∈ P.filter (g · < n), y ^ g S := by
  rw [← sum_filter_add_sum_filter_not P (g · < n)]
  obtain ⟨c, hc⟩ : y ^ n ∣ ∑ S ∈ P.filter (fun S => ¬ g S < n), y ^ g S :=
    dvd_sum fun S hS => pow_dvd_pow y (not_lt.mp (mem_filter.mp hS).2)
  rw [hc, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hy : 1 ≤ y := by omega
  calc ∑ S ∈ P.filter (g · < n), y ^ g S
      ≤ ∑ _S ∈ P.filter (g · < n), y ^ (n - 1) :=
        sum_le_sum fun S hS => Nat.pow_le_pow_right hy (by have := (mem_filter.mp hS).2; omega)
    _ = (P.filter (g · < n)).card * y ^ (n - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ P.card * y ^ (n - 1) := Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ < y * y ^ (n - 1) := Nat.mul_lt_mul_of_pos_right hP (by positivity)
    _ = y ^ n := by rw [← pow_succ']; congr 1; omega
theorem sum_pow_mod_pred {y : ℕ} (hy : 3 ≤ y) (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ) :
    (∑ S ∈ F, y ^ g S) % (y - 1) = F.card % (y - 1) := by
  have hmod : y % (y - 1) = 1 := by
    calc y % (y - 1) = (y - 1 + 1) % (y - 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 1 % (y - 1) := Nat.add_mod_left _ _
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  rw [sum_nat_mod]
  rw [sum_congr rfl fun S _ => by rw [Nat.pow_mod, hmod, one_pow]]
  simp
theorem card_admissibleSets :
    ((powersetCard 15 (range (2 ^ 14))).filter fun S => octH 14 S.sort ≤ 118).card = Nadm := by
  rw [← packedCount_eq]
  unfold packedCount
  have hM : (2 : ℕ) ^ (pB * 119) = (2 ^ pB) ^ 119 := pow_mul 2 pB 119
  have hy3 : 3 ≤ (2 : ℕ) ^ pB := by unfold pB; norm_num
  have hcard : (powersetCard 15 (range (2 ^ 14))).card < 2 ^ pB - 1 := by
    rw [card_powersetCard, card_range]
    exact lt_of_le_of_lt (Nat.choose_le_pow _ _) (by rw [← pow_mul]; unfold pB; norm_num)
  have h15 := rep_piter (K := 15) (y := 2 ^ pB) (M := 2 ^ (pB * 119)) 14 0 [0, 1]
    (rep_zero 15 _ _ (Nat.one_lt_two_pow (by unfold pB; norm_num))) 15 le_rfl
  rw [Nat.zero_add] at h15
  rw [h15, coeff_Q _ _ _ (by norm_num), hM, mod_pow_sum (by norm_num) _ _ (by omega),
    sum_pow_mod_pred hy3, Nat.mod_eq_of_lt (lt_of_le_of_lt (card_filter_le _ _) hcard)]
  exact congrArg card (filter_congr fun S _ => by simp only [oc]; omega)
end SphincsSecurity.Octopus
end

section



namespace SphincsSecurity.Octopus
open Finset
def valList {k n : ℕ} (v : Fin k → Fin n) : List ℕ := List.ofFn fun i => (v i : ℕ)
theorem valList_nodup {k n : ℕ} (v : Fin k → Fin n) :
    (valList v).Nodup ↔ Function.Injective v := by
  unfold valList
  rw [List.nodup_ofFn]
  exact ⟨fun h a b hab => h (by simp [hab]), fun h a b hab => h (Fin.ext hab)⟩
theorem mem_valList {k n : ℕ} (v : Fin k → Fin n) (x : ℕ) :
    x ∈ valList v ↔ ∃ i, (v i : ℕ) = x := by
  simp [valList, List.mem_ofFn]
theorem sortLeaves_eq {l : List ℕ} (hl : l.Nodup) : sortLeaves l = l.toFinset.sort := by
  unfold sortLeaves
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (List.pairwise_insertionSort _ _)
    (pairwise_sort _ _)
  refine (List.perm_insertionSort _ _).trans ?_
  rw [List.perm_ext_iff_of_nodup hl (sort_nodup _ _)]
  intro a; simp
theorem card_fiber (k n : ℕ) (S : Finset ℕ) (hS : S ∈ powersetCard k (range n)) :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ (valList v).toFinset = S).card = k.factorial := by
  rw [mem_powersetCard] at hS
  obtain ⟨hSn, hSk⟩ := hS
  rw [← Fintype.card_subtype]
  have mem : ∀ v : Fin k → Fin n, (valList v).toFinset = S → ∀ i, (v i : ℕ) ∈ S := by
    intro v hv i; rw [← hv, List.mem_toFinset, mem_valList]; exact ⟨i, rfl⟩
  let E : {v : Fin k → Fin n // Function.Injective v ∧ (valList v).toFinset = S} ≃ (Fin k ≃ S) :=
    { toFun := fun v => Equiv.ofBijective (fun i => ⟨(v.1 i : ℕ), mem v.1 v.2.2 i⟩)
        ⟨fun a b hab => v.2.1 (Fin.ext (by simpa using hab)), fun x => by
          have hx : (x : ℕ) ∈ (valList v.1).toFinset := by rw [v.2.2]; exact x.2
          rw [List.mem_toFinset, mem_valList] at hx
          obtain ⟨i, hi⟩ := hx
          exact ⟨i, Subtype.ext hi⟩⟩
      invFun := fun e => ⟨fun i => ⟨(e i : ℕ), mem_range.mp (hSn (e i).2)⟩, fun a b hab => by
          have : (e a : ℕ) = e b := by simpa using congrArg Fin.val hab
          exact e.injective (Subtype.ext this), by
          ext x
          rw [List.mem_toFinset, mem_valList]
          constructor
          · rintro ⟨i, rfl⟩; exact (e i).2
          · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
      left_inv := fun v => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun e => Equiv.ext fun i => Subtype.ext rfl }
  rw [Fintype.card_congr E]
  have e0 : Fin k ≃ S := (S.equivFinOfCardEq hSk).symm
  rw [Fintype.card_equiv e0, Fintype.card_fin]
theorem card_inj_filter (k n : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ P (valList v).toFinset).card =
      k.factorial * ((powersetCard k (range n)).filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := fun v : Fin k → Fin n => (valList v).toFinset)
    (t := (powersetCard k (range n)).filter P)]
  · rw [sum_congr rfl fun S hS => ?_, sum_const, smul_eq_mul, mul_comm]
    rw [mem_filter] at hS
    rw [filter_filter, ← card_fiber k n S hS.1]
    congr 1
    refine filter_congr fun v _ => ?_
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hS.2⟩, h3⟩
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq]
    refine ⟨⟨fun x hx => ?_, ?_⟩, hv.2⟩
    · rw [List.mem_toFinset, mem_valList] at hx
      obtain ⟨i, rfl⟩ := hx
      exact mem_range.mpr (v i).2
    · rw [List.toFinset_card_of_nodup ((valList_nodup v).mpr hv.1)]
      simp [valList]
theorem card_admissibleTuples :
    (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
      Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 118).card =
      Nat.factorial 15 * Nadm := by
  have h := card_inj_filter 15 (2 ^ 14) (fun S => octH 14 S.sort ≤ 118)
  rw [card_admissibleSets] at h
  rw [← h]
  refine congrArg card (filter_congr fun v _ => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)]
def fieldsOf (b : ℕ) : List ℕ := (List.range 15).map fun r => b / 2 ^ (14 * r) % 2 ^ 14
def admB (b : ℕ) : Bool :=
  decide (fieldsOf b).Nodup && decide (octopusSize (sortLeaves (fieldsOf b)) ≤ 118)
theorem leavesOf_eq (N : ℕ) : leavesOf N = fieldsOf (N / 2 ^ 34) := by
  unfold leavesOf fieldsOf leafOf
  refine List.map_congr_left fun r _ => ?_
  rw [Nat.div_div_eq_div_mul, ← pow_add]
theorem admissible_eq (N : ℕ) : admissible N = admB (N / 2 ^ 34) := by
  unfold admissible admB; rw [leavesOf_eq]
theorem fieldsOf_add (c d : ℕ) : fieldsOf (c + 2 ^ 210 * d) = fieldsOf c := by
  unfold fieldsOf
  refine List.map_congr_left fun r hr => ?_
  have hr := List.mem_range.mp hr
  have e : (2 : ℕ) ^ 210 * d = 2 ^ (14 * r) * (2 ^ 14 * (2 ^ (196 - 14 * r) * d)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A B : ℕ) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]
theorem count_low (A B : ℕ) (hA : 0 < A) (p : ℕ → Bool) :
    (∑ k ∈ range (A * B), if p (k / A) then 1 else 0) =
      A * ∑ b ∈ range B, if p b then 1 else 0 := by
  rw [sum_range_mul', mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl fun a ha => by
    rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt (mem_range.mp ha), Nat.zero_add]]
  simp
theorem count_high (A B : ℕ) (p : ℕ → Bool) (hp : ∀ a b, p (a + A * b) = p a) :
    (∑ k ∈ range (A * B), if p k then 1 else 0) = B * ∑ a ∈ range A, if p a then 1 else 0 := by
  rw [sum_range_mul']
  simp [hp]
theorem fieldsOf_equiv (v : Fin 15 → Fin (2 ^ 14)) :
    fieldsOf (finFunctionFinEquiv v : ℕ) = valList v := by
  unfold fieldsOf valList
  apply List.ext_getElem (by simp)
  intro r h1 _
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv v) ⟨r, by simpa using h1⟩
  rw [Equiv.symm_apply_apply] at this
  rw [this, pow_mul]
theorem count_fields :
    (∑ c ∈ range (2 ^ 210), if admB c then 1 else 0) =
      (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
        Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 118).card := by
  have e : (2 : ℕ) ^ 210 = (2 ^ 14) ^ 15 := by rw [← pow_mul]
  rw [e, sum_range (fun c => if admB c then 1 else 0), card_filter]
  rw [← Equiv.sum_comp finFunctionFinEquiv]
  refine sum_congr rfl fun v _ => ?_
  unfold admB
  simp only [fieldsOf_equiv, valList_nodup, Bool.and_eq_true, decide_eq_true_eq]
theorem card_admissibleDigests :
    ((range (2 ^ 256)).filter fun N => admissible N = true).card =
      2 ^ 46 * (Nat.factorial 15 * Nadm) := by
  rw [card_filter]
  have e : (2 : ℕ) ^ 256 = 2 ^ 34 * (2 ^ 210 * 2 ^ 12) := by rw [← pow_add, ← pow_add]
  rw [e, sum_congr rfl fun N _ => by rw [admissible_eq], count_low _ _ (by positivity),
    count_high _ _ _ (fun a b => by unfold admB; rw [fieldsOf_add]), count_fields,
    card_admissibleTuples, ← mul_assoc, ← pow_add]
end SphincsSecurity.Octopus
end

section



namespace SphincsSecurity.Concrete
open Finset
private instance sortRelTotal (leaves : IndexGroup → FtsLeaf) :
    Std.Total (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun a b => le_total _ _⟩
private instance sortRelTrans (leaves : IndexGroup → FtsLeaf) :
    IsTrans IndexGroup (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
theorem sortedLeaves_eq_sortLeaves (leaves : IndexGroup → FtsLeaf) :
    sortedLeaves leaves = Octopus.sortLeaves (Octopus.valList (n := 2 ^ 14) (k := 15) leaves) := by
  unfold sortedLeaves sortedSlots Octopus.sortLeaves Octopus.valList
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  · exact List.pairwise_insertionSort _ _
  · refine ((List.perm_insertionSort _ _).map _).trans ?_
    refine List.Perm.trans ?_ (List.perm_insertionSort _ _).symm
    rw [List.ofFn_eq_map]
    rfl
theorem octopusSize_eq_reference (sorted : List Nat) : octopusSize sorted = Octopus.octopusSize sorted := rfl
theorem card_admissibleLeaves :
    (univ.filter AdmissibleLeaves).card = Nat.factorial 15 * Octopus.Nadm := by
  have hfilter : univ.filter AdmissibleLeaves = univ.filter fun v : IndexGroup → FtsLeaf =>
      Function.Injective v ∧ Octopus.octopusSize (Octopus.sortLeaves (Octopus.valList v)) ≤ 118 := by
    apply filter_congr
    intro leaves _
    unfold AdmissibleLeaves
    rw [sortedLeaves_eq_sortLeaves, octopusSize_eq_reference]
    rfl
  rw [hfilter]
  exact Octopus.card_admissibleTuples
theorem card_leafVectors : Fintype.card (IndexGroup → FtsLeaf) = 2 ^ 210 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl
theorem admissibleLeafCount_bounds :
    2 ^ 210 ≤ 2142 * (Nat.factorial 15 * Octopus.Nadm) ∧ 2141 * (Nat.factorial 15 * Octopus.Nadm) ≤ 2 ^ 210 := by
  unfold Octopus.Nadm
  norm_num [Nat.factorial]
open ENNReal in
noncomputable irreducible_def admissibleProbability : ENNReal :=
  ((univ.filter AdmissibleLeaves).card : ENNReal) / (Fintype.card (IndexGroup → FtsLeaf) : ENNReal)
open ENNReal in
theorem admissibleProbability_ge : (2142 : ENNReal)⁻¹ ≤ admissibleProbability := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), ← ENNReal.div_eq_inv_mul,
    ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h
open ENNReal in
theorem admissibleProbability_le : admissibleProbability ≤ (2141 : ENNReal)⁻¹ := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.2
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProbability_inv_le : admissibleProbability⁻¹ ≤ 2142 :=
  ENNReal.inv_le_iff_inv_le.mpr admissibleProbability_ge
theorem admissibleProbability_pos : admissibleProbability ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by simp) admissibleProbability_ge)
theorem admissibleProbability_ne_top : admissibleProbability ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) admissibleProbability_le
theorem admissibleProbability_le_one : admissibleProbability ≤ 1 :=
  admissibleProbability_le.trans (ENNReal.inv_le_one.mpr (by norm_num))
theorem card_admissibleLeaves_eq_mul :
    ((univ.filter AdmissibleLeaves).card : ENNReal) =
      admissibleProbability * (Fintype.card (IndexGroup → FtsLeaf) : ENNReal) := by
  rw [admissibleProbability_def, ENNReal.div_mul_cancel (by simp) (by simp)]
noncomputable def cachedIndexRate : ENNReal := admissibleProbability * (Fintype.card Index : ENNReal)⁻¹
theorem cachedIndexRate_ne_top : cachedIndexRate ≠ ⊤ :=
  ENNReal.mul_ne_top admissibleProbability_ne_top (by simp)
theorem cachedIndexRate_le_one : cachedIndexRate ≤ 1 :=
  (mul_le_mul' admissibleProbability_le_one (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))).trans_eq
    (one_mul 1)
theorem card_mul_cachedIndexRate : (Fintype.card Index : ENNReal) * cachedIndexRate = admissibleProbability := by
  rw [cachedIndexRate, mul_left_comm, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
end SphincsSecurity.Concrete
end
