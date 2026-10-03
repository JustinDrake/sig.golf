import VCVio.OracleComp.Constructions.SampleableType
import SigGolfCandidate.Budget.Octopus.Tuples
import SigGolfCandidate.Budget.Loops
import Mathlib.Analysis.Complex.ExponentialBounds

section


namespace SigGolfCandidate.Budget.Octopus
open OracleComp Finset ENNReal
theorem card_bitVec_filter' (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]
theorem probEvent_uniform_toNat' (P : ℕ → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter', Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]
theorem admissibleTuples_eq :
    Nat.factorial 15 * Nadm = 768394439706066703645522769421343549971302651574651715584000 := by
  unfold Nadm; norm_num [Nat.factorial]
theorem admissibleTuples_bounds :
    2 ^ 210 ≤ 2142 * (Nat.factorial 15 * Nadm) ∧ 2141 * (Nat.factorial 15 * Nadm) ≤ 2 ^ 210 ∧
      2 ^ 198 ≤ Nat.factorial 15 * Nadm := by
  rw [admissibleTuples_eq]; norm_num
theorem probEvent_admissibleDigest :
    Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [probEvent_uniform_toNat' (fun N => admissible N = true), card_admissibleDigests]
  have e : (2 : ℝ≥0∞) ^ 256 = 2 ^ 46 * 2 ^ 210 := by rw [← pow_add]
  rw [e, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]
theorem probEvent_not_admissibleDigest :
    Pr[fun u : BitVec 256 => ¬ admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => admissible u.toNat = true)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_admissibleDigest]
theorem admissibleProb_ge :
    (1 : ℝ≥0∞) / 2142 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_div,
    ← ENNReal.div_eq_inv_mul]
  apply ENNReal.div_le_of_le_mul
  have h := admissibleTuples_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProb_le :
    ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 ≤ (1 : ℝ≥0∞) / 2141 := by
  rw [ENNReal.div_le_iff (by simp) (by simp), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleTuples_bounds.2.1
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProb_ge_two_pow :
    (1 : ℝ≥0∞) / 2 ^ 12 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 :=
  le_trans (ENNReal.div_le_div_left (by norm_num) 1) admissibleProb_ge
theorem probEvent_admissibleDigest_ge :
    (1 : ℝ≥0∞) / 2 ^ 12 ≤ Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  rw [probEvent_admissibleDigest]; exact admissibleProb_ge_two_pow
end SigGolfCandidate.Budget.Octopus
end

section


namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp Finset ENNReal
theorem sum_range_mul {M : Type} [AddCommMonoid M] (f : Nat → M) (A B : Nat) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]
theorem card_bitVec_filter (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]
theorem probEvent_uniform_toNat (P : Nat → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter, Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]
theorem card_filter_range (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    ((range n).filter P).card = ∑ k ∈ range n, if P k then 1 else 0 :=
  Finset.card_filter _ _
theorem admissible_eq_octopus : Ref.admissible = Octopus.admissible := rfl
theorem probEvent_not_admissible :
    Pr[fun u : BitVec 256 => ¬ admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - ((Nat.factorial 15 * Octopus.Nadm : Nat) : ℝ≥0∞) / 2 ^ 210 := by
  rw [admissible_eq_octopus]
  exact Octopus.probEvent_not_admissibleDigest
theorem leBytes_add (a b v : Nat) :
    leBytes (a + b) v = leBytes a v ++ leBytes b (v / 256 ^ a) := by
  unfold leBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.pow_add, Nat.div_div_eq_div_mul]
theorem answerBytes_eq (k : Nat) (u : BitVec 256) (hk : k ≤ 32) :
    answerBytes k u = leBytes k u.toNat := by
  unfold answerBytes leBytes
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have := extractByte_ofNat 256 u.toNat i (by omega)
  simpa using this
theorem leNat_answerBytes16 (u : BitVec 256) : leNat (answerBytes 16 u) = u.toNat % 2 ^ 128 := by
  rw [answerBytes_eq 16 u (by omega), leNat_leBytes]; norm_num
theorem count_mod_eq_le (A B r : Nat) :
    (∑ k ∈ range (A * B), if k % A = r then 1 else 0) ≤ B := by
  rw [sum_range_mul]
  calc (∑ b ∈ range B, ∑ a ∈ range A, if (a + A * b) % A = r then 1 else 0)
      ≤ ∑ _b ∈ range B, 1 := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Finset.sum_congr rfl fun a ha => by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp ha)]]
        rw [Finset.sum_ite_eq' (range A) r (fun _ => 1)]
        split <;> simp
    _ = B := by simp
theorem probEvent_answerBytes_mem_le (R : Finset Val) :
    Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
      (R.card : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniformSample]
  have hsub : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R) ⊆
      R.biUnion fun ρ => univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨_, hu, by rw [leNat_answerBytes16]⟩
  have hone : ∀ r : Nat,
      (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = r).card ≤ 2 ^ 128 := by
    intro r
    rw [card_bitVec_filter 256 (fun k => k % 2 ^ 128 = r), card_filter_range,
      show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
    exact count_mod_eq_le _ _ r
  have hcard : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card ≤ R.card * 2 ^ 128 :=
    (card_le_card hsub).trans (card_biUnion_le.trans (by
      calc ∑ ρ ∈ R, (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ).card
          ≤ ∑ _ρ ∈ R, 2 ^ 128 := Finset.sum_le_sum fun ρ _ => hone _
        _ = R.card * 2 ^ 128 := by simp))
  have hc : (Fintype.card (BitVec 256) : ℝ≥0∞) = 2 ^ 128 * 2 ^ 128 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  rw [hc]
  calc ((univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128)
      ≤ ((R.card * 2 ^ 128 : Nat) : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128) := by
        gcongr
    _ = (R.card : ℝ≥0∞) / 2 ^ 128 := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
def ds (n a : Nat) : Nat := ∑ r ∈ range n, a / 8 ^ r % 8
theorem list_sum_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ r ∈ range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
theorem sum_digitsOfWord (d : Nat) : (digitsOfWord d).sum = ds 21 d := by
  unfold digitsOfWord ds
  exact list_sum_map_range _ 21
theorem ds_succ (n d b : Nat) (hd : d < 8) : ds (n + 1) (d + 8 * b) = d + ds n b := by
  unfold ds
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one]
  rw [show (d + 8 * b) % 8 = d by omega, Nat.add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (d + 8 * b) / 8 = b by omega]
theorem ds_le (n a : Nat) : ds n a ≤ 7 * n := by
  unfold ds
  calc ∑ r ∈ range n, a / 8 ^ r % 8 ≤ ∑ _r ∈ range n, 7 :=
        Finset.sum_le_sum fun r _ => Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    _ = 7 * n := by simp [Nat.mul_comm]
def gfDigit (X : Nat) : Nat := ∑ d ∈ range 8, X ^ d
theorem gf_ds (X n : Nat) : ∑ a ∈ range (8 ^ n), X ^ ds n a = gfDigit X ^ n := by
  induction n with
  | zero => simp [ds]
  | succ n ih =>
    rw [pow_succ', sum_range_mul, pow_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gfDigit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [ds_succ n d b (mem_range.mp hd), pow_add, Nat.mul_comm]
def npair (n s : Nat) : Nat :=
  ∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), if ds n a0 + ds n a1 = s then 1 else 0
theorem gf_pairs (X n : Nat) :
    ∑ s ∈ range (14 * n + 1), npair n s * X ^ s = gfDigit X ^ (2 * n) := by
  have hr : gfDigit X ^ (2 * n) =
      ∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), X ^ (ds n a0 + ds n a1) := by
    rw [Nat.two_mul, pow_add, ← gf_ds, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a0 _ => ?_
    rw [pow_add]
  rw [hr]
  unfold npair
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_ite_eq (range (14 * n + 1)) (ds n a0 + ds n a1) (fun s => X ^ s), if_pos]
  have := ds_le n a0; have := ds_le n a1
  rw [mem_range]; omega
theorem npair_le (n s : Nat) : npair n s ≤ 8 ^ n * 8 ^ n := by
  unfold npair
  calc (∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), if ds n a0 + ds n a1 = s then 1 else 0)
      ≤ ∑ _a1 ∈ range (8 ^ n), ∑ _a0 ∈ range (8 ^ n), 1 :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => by split <;> simp
    _ = 8 ^ n * 8 ^ n := by simp
theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)
theorem npair_coeff (n s X : Nat) (hX : 8 ^ n * 8 ^ n < X) (hs : s < 14 * n + 1) :
    npair n s = gfDigit X ^ (2 * n) / X ^ s % X := by
  rw [← gf_pairs]
  exact (digit_of_sum X (by omega) (npair n) (fun s => (npair_le n s).trans_lt hX) _ s hs).symm
def codeCount : Nat := 166377570312823648881394061712938016
theorem gfDigit_eq (X : Nat) : gfDigit X = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 := by
  simp [gfDigit, Finset.sum_range_succ]
theorem npair_target : npair 21 targetSum = codeCount := by
  rw [npair_coeff 21 targetSum (2 ^ 128) (by norm_num) (by simp [targetSum]), gfDigit_eq]
  simp only [targetSum]
  decide
def Dok (k : Nat) : Prop :=
  k % 2 ^ 64 < 2 ^ 63 ∧ k / 2 ^ 64 % 2 ^ 64 < 2 ^ 63 ∧
    ds 21 (k % 2 ^ 64) + ds 21 (k / 2 ^ 64 % 2 ^ 64) = targetSum
instance : DecidablePred Dok := fun k => by unfold Dok; infer_instance
theorem Dok_high (a b : Nat) : Dok (a + 2 ^ 128 * b) ↔ Dok a := by
  have e : 2 ^ 128 * b = 2 ^ 64 * (2 ^ 64 * b) := by rw [← Nat.mul_assoc, ← pow_add]
  have h1 : (a + 2 ^ 128 * b) % 2 ^ 64 = a % 2 ^ 64 := by rw [e, Nat.add_mul_mod_self_left]
  have h2 : (a + 2 ^ 128 * b) / 2 ^ 64 % 2 ^ 64 = a / 2 ^ 64 % 2 ^ 64 := by
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  unfold Dok; rw [h1, h2]
theorem Dok_split (a0 a1 : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) :
    Dok (a0 + 2 ^ 64 * a1) ↔ (a0 < 2 ^ 63 ∧ a1 < 2 ^ 63 ∧ ds 21 a0 + ds 21 a1 = targetSum) := by
  have e1 : (a0 + 2 ^ 64 * a1) % 2 ^ 64 = a0 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have e2 : (a0 + 2 ^ 64 * a1) / 2 ^ 64 % 2 ^ 64 = a1 := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add,
      Nat.mod_eq_of_lt h1]
  unfold Dok; rw [e1, e2]
theorem sum_half (M : Nat) (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P] :
    (∑ x ∈ range (M + M), if x < M ∧ P x then f x else 0) = ∑ x ∈ range M, if P x then f x else 0 := by
  rw [Finset.sum_range_add]
  have : ∀ x ∈ range M, (if M + x < M ∧ P (M + x) then f (M + x) else 0) = 0 := by
    intro x _; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, Nat.add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := mem_range.mp hx
  by_cases hp : P x <;> simp [hp, this]
theorem Dok_split' (M a0 a1 : Nat) (hM : M = 2 ^ 63) (h0 : a0 < M + M) (h1 : a1 < M + M) :
    Dok (a0 + (M + M) * a1) ↔ (a0 < M ∧ a1 < M ∧ ds 21 a0 + ds 21 a1 = targetSum) := by
  have hMM : M + M = 2 ^ 64 := by subst hM; norm_num
  rw [hMM] at h0 h1 ⊢
  rw [Dok_split a0 a1 h0 h1, hM]
theorem count_Dok_low (M : Nat) (hM : M = 2 ^ 63) :
    (∑ a ∈ range ((M + M) * (M + M)), if Dok a then 1 else 0) =
      ∑ a1 ∈ range M, ∑ a0 ∈ range M, if ds 21 a0 + ds 21 a1 = targetSum then 1 else 0 := by
  rw [sum_range_mul]
  have step : ∀ a1 ∈ range (M + M),
      (∑ a0 ∈ range (M + M), if Dok (a0 + (M + M) * a1) then 1 else 0)
      = if a1 < M then ∑ a0 ∈ range M, (if ds 21 a0 + ds 21 a1 = targetSum then 1 else 0) else 0 := by
    intro a1 ha1
    rw [Finset.sum_congr rfl fun a0 ha0 => by
      rw [if_congr (Dok_split' M a0 a1 hM (mem_range.mp ha0) (mem_range.mp ha1)) rfl rfl]]
    by_cases h : a1 < M
    · rw [if_pos h]
      have := sum_half M (fun _ => 1) (fun a0 => ds 21 a0 + ds 21 a1 = targetSum)
      rw [← this]
      refine Finset.sum_congr rfl fun a0 _ => ?_
      by_cases h' : a0 < M <;> simp [h, h']
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun a0 _ => by simp [h]
  rw [Finset.sum_congr rfl step]
  have := sum_half M (fun a1 => ∑ a0 ∈ range M, if ds 21 a0 + ds 21 a1 = targetSum then 1 else 0)
    (fun _ => True)
  simp only [and_true, if_true] at this
  exact this
theorem count_Dok (W T : Nat) (hW : W = 2 ^ 128) :
    (∑ k ∈ range (W * T), if Dok k then 1 else 0) = T * ∑ a ∈ range W, if Dok a then 1 else 0 := by
  rw [sum_range_mul]
  have : ∀ b ∈ range T, (∑ a ∈ range W, if Dok (a + W * b) then 1 else 0) =
      ∑ a ∈ range W, if Dok a then 1 else 0 := fun b _ =>
    Finset.sum_congr rfl fun a _ => by rw [hW]; exact if_congr (Dok_high a _) rfl rfl
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, smul_eq_mul]
theorem count_Dok_256 :
    ((range (2 ^ 256)).filter Dok).card = 2 ^ 128 * codeCount := by
  have h1 := count_Dok ((2 ^ 63 + 2 ^ 63) * (2 ^ 63 + 2 ^ 63)) (2 ^ 128) (by norm_num)
  have h2 := count_Dok_low (2 ^ 63) rfl
  have h3 : npair 21 targetSum = ∑ a1 ∈ range (2 ^ 63), ∑ a0 ∈ range (2 ^ 63),
      if ds 21 a0 + ds 21 a1 = targetSum then 1 else 0 := by
    unfold npair; rw [show (8 : Nat) ^ 21 = 2 ^ 63 by norm_num]
  have e : (2 : Nat) ^ 256 = (2 ^ 63 + 2 ^ 63) * (2 ^ 63 + 2 ^ 63) * 2 ^ 128 := by norm_num
  rw [card_filter_range, e, h1, h2, ← h3, npair_target]
theorem slice_leBytes16 (v : Nat) :
    slice (leBytes 16 v) 0 8 = leBytes 8 v ∧ slice (leBytes 16 v) 8 8 = leBytes 8 (v / 256 ^ 8) := by
  rw [show 16 = 8 + 8 from rfl, leBytes_add]
  unfold slice
  constructor
  · simp
  · simp
theorem decode_none_iff (u : BitVec 256) :
    decodeDigits (answerBytes 16 u) = none ↔ ¬ Dok u.toNat := by
  rw [answerBytes_eq 16 u (by omega)]
  obtain ⟨h1, h2⟩ := slice_leBytes16 u.toNat
  unfold decodeDigits
  simp only [h1, h2, leNat_leBytes, List.sum_append, sum_digitsOfWord]
  have e1 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [e1]
  unfold Dok
  split_ifs with ha hb <;> simp_all
theorem probEvent_decode_none :
    Pr[fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - (2 ^ 128 * codeCount : Nat) / (2 ^ 256 : ℝ≥0∞) := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => Dok u.toNat)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  have hcongr : (fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none) =
      fun u => ¬ Dok u.toNat := funext fun u => propext (decode_none_iff u)
  rw [hcongr, ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_uniform_toNat Dok, count_Dok_256]
end SigGolfCandidate.Budget
end

section

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist
theorem hash16_bind_eq {β : Type} (x : List Byte) (f : Val → OracleComp HashSpec β) :
    Ref.hash16 x >>= f = qry (fmt x) >>= fun a => f (answerBytes 16 a) := by
  simp only [Ref.hash16, Ref.H, bind_assoc, pure_bind]
theorem digest_bind_eq {β : Type} (rho m : List Byte) (f : Nat → OracleComp HashSpec β) :
    digest rho m >>= f = qry (fmt (digestInput rho m)) >>= fun a => f a.toNat := by
  simp only [digest, Ref.H, bind_assoc, pure_bind]
theorem ev_ite_le (P : BitVec 256 → Prop) [DecidablePred P] (x y : ℝ≥0∞)
    (g : BitVec 256 → ℝ≥0∞) (hg : ∀ u, g u ≤ if P u then x else y) :
    expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) g ≤
      Pr[P | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * x +
        Pr[fun u => ¬ P u | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * y := by
  calc expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) g
      ≤ expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          (fun u => (if P u then 1 else 0) * x + (if ¬ P u then 1 else 0) * y) :=
        expectedValue_mono _ fun u => (hg u).trans (by by_cases h : P u <;> simp [h])
    _ = _ := by
        rw [expectedValue_add, expectedValue_mul_const, expectedValue_mul_const,
          expectedValue_ite_one, expectedValue_ite_one]
theorem probEvent_not_uniform (P : BitVec 256 → Prop) [DecidablePred P] :
    Pr[fun u => ¬ P u | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - Pr[P | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256)) P
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc)
theorem fmt_encInput (lay tau e : Nat) (M : Val) (c : Nat) :
    fmt (encInput lay tau e M c) = pad64 (encInput lay tau e M c) :=
  fmt_eq_pad64 _ _ _ _ _ _ (by decide)
theorem fmt_rndInput (S m : List Byte) (a : Nat) : fmt (rndInput S m a) = pad64 (rndInput S m a) :=
  by simp [fmt, IsChainFmt, IsNodeFmt, IsDigestFmt, rndInput, byte]
theorem enc_inj (lay tau e : Nat) (M : Val) {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : fmt (encInput lay tau e M c) = fmt (encInput lay tau e M c')) : c = c' := by
  rw [fmt_encInput, fmt_encInput] at h
  have h2 := pad64_inj (by simp [encInput]) h
  simp only [encInput, thInput, List.append_assoc, List.append_cancel_left_eq] at h2
  exact le32_inj hc hc' h2
noncomputable def rhoC : ℝ≥0∞ :=
  Pr[fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none |
    ($ᵗ BitVec 256 : ProbComp (BitVec 256))]
theorem V_searchCounter (z b : ℝ≥0∞) (hz : 1 ≤ z) (hb : 1 ≤ b)
    (hstep : z * (rhoC * b + (1 - rhoC)) ≤ b)
    (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) :
    ∀ fuel c (cache : RCache), c + fuel ≤ 2 ^ 32 →
      (∀ c', c ≤ c' → c' < 2 ^ 32 → cache (fmt (encInput lay tau e M c')) = none) →
      V z (searchCounter lay tau e M c fuel) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro c cache _ _; simp [searchCounter, hb]
  | succ n ih =>
    intro c cache hbound hfresh
    unfold searchCounter
    rw [hash16_bind_eq, V_query,
      expectedValue_ro_fresh _ _ (hfresh c le_rfl (by omega))]
    have hbl : (fmt (encInput lay tau e M c)).blocks ≤ 1 :=
      blocksFmt_le _ 1 (by simp [encInput]; omega) le_rfl
    have hz1 : z ^ (fmt (encInput lay tau e M c)).blocks ≤ z := by
      calc z ^ (fmt (encInput lay tau e M c)).blocks ≤ z ^ 1 := pow_le_pow_right₀ hz hbl
        _ = z := pow_one z
    refine le_trans (mul_le_mul' hz1 (ev_ite_le
      (fun u => decodeDigits (answerBytes 16 u) = none) b 1 _ fun u => ?_)) ?_
    · dsimp only
      cases hd : decodeDigits (answerBytes 16 u) with
      | some x => simp
      | none =>
        simp only [if_true]
        refine ih (c + 1) _ (by omega) fun c' hc' hc'b => ?_
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh c' (by omega) hc'b
        · intro heq
          have := enc_inj lay tau e M hc'b (by omega) heq
          omega
    · rw [probEvent_not_uniform, mul_one]
      exact hstep
theorem rnd_inj (S m : List Byte) {a a' : Nat} (ha : a < 2 ^ 32) (ha' : a' < 2 ^ 32)
    (h : fmt (rndInput S m a) = fmt (rndInput S m a')) : a = a' := by
  rw [fmt_rndInput, fmt_rndInput] at h
  have h2 := pad64_inj (by simp [rndInput]) h
  have h3 : le32 a = le32 a' := by
    simpa only [rndInput, List.append_assoc, List.append_cancel_left_eq] using h2
  exact le32_inj ha ha' h3
theorem rnd_ne_dig (S m rho m' : List Byte) (a : Nat) :
    fmt (rndInput S m a) ≠ fmt (digestInput rho m') := by
  intro h
  have h7 : qbyte (fmt (rndInput S m a)) 1 = 7 := by
    rw [qbyte_fmt _ _ (by decide)]
    simp [rndInput, byte_toNat]
  have h12 : qbyte (fmt (digestInput rho m')) 1 = 12 := by
    unfold digestInput
    rw [qbyte_tag]
  have := congrArg (fun q => qbyte q 1) h
  omega
theorem dig_inj (m : List Byte) (hm : m.length = 32) {rho rho' : List Byte} (hr : rho.length = 16)
    (hr' : rho'.length = 16)
    (h : fmt (digestInput rho m) = fmt (digestInput rho' m)) : rho = rho' := by
  rw [Ref.fmt_digestInput rho m hr hm, Ref.fmt_digestInput rho' m hr' hm] at h
  have h1 := congrArg (fun q : Query => toList q.2) h
  dsimp only at h1
  rw [toList_ofList _ _ (by simp [hr, hm]), toList_ofList _ _ (by simp [hr', hm])] at h1
  simp only [List.append_assoc, List.append_cancel_left_eq] at h1
  exact List.append_inj_left' h1 rfl
noncomputable def rhoD : ℝ≥0∞ :=
  Pr[fun u : BitVec 256 => ¬ admissible u.toNat = true |
    ($ᵗ BitVec 256 : ProbComp (BitVec 256))]
noncomputable def epsD : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 20 / 2 ^ 128
theorem V_searchDigest (z b : ℝ≥0∞) (hz : 1 ≤ z) (hb : 1 ≤ b)
    (hstep : z ^ 2 * ((epsD + rhoD) * b + (1 - rhoD)) ≤ b)
    (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a (cache : RCache) (R : Finset Val), a + fuel ≤ 2 ^ 20 → R.card ≤ a →
      (∀ a', a ≤ a' → a' < 2 ^ 32 → cache (fmt (rndInput S m a')) = none) →
      (∀ rho, rho.length = 16 → rho ∉ R → cache (fmt (digestInput rho m)) = none) →
      V z (searchDigest S m a fuel) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro a cache R _ _ _ _; simp [searchDigest, hb]
  | succ n ih =>
    intro a cache R hbound hcard hrnd hdig
    unfold searchDigest
    rw [hash16_bind_eq, V_query, expectedValue_ro_fresh _ _ (hrnd a le_rfl (by omega))]
    obtain ⟨-, hb1⟩ := rnd_ok S m hS hm a
    have hz1 : ∀ q : Query, q.blocks ≤ 1 → z ^ q.blocks ≤ z := fun q hq =>
      (pow_le_pow_right₀ hz hq).trans_eq (pow_one z)
    have hcont : ∀ u : BitVec 256,
        V z (digest (answerBytes 16 u) m >>= fun N =>
            if admissible N = true then pure (some (answerBytes 16 u, N))
            else searchDigest S m (a + 1) n)
          ((cache.cacheQuery (fmt (rndInput S m a)) u)) ≤
        if answerBytes 16 u ∈ R then z * b else z * (rhoD * b + (1 - rhoD)) := by
      intro u
      set rho := answerBytes 16 u with hrho_def
      have hrho : rho.length = 16 := by simp [rho]
      have hc1rnd : ∀ a', a + 1 ≤ a' → a' < 2 ^ 32 → (cache.cacheQuery (fmt (rndInput S m a)) u) (fmt (rndInput S m a')) = none := by
        intro a' ha' ha'b
        rw [QueryCache.cacheQuery_of_ne]
        · exact hrnd a' (by omega) ha'b
        · intro h; have := rnd_inj S m ha'b (by omega) h; omega
      have hc1dig : ∀ rho', (cache.cacheQuery (fmt (rndInput S m a)) u) (fmt (digestInput rho' m)) = cache (fmt (digestInput rho' m)) :=
        fun rho' => QueryCache.cacheQuery_of_ne _ _ fun h => rnd_ne_dig S m rho' m a h.symm
      obtain ⟨-, hb2⟩ := dig_ok rho m hrho hm
      rw [digest_bind_eq, V_query]
      have hk : ∀ (R' : Finset Val) (c2 : RCache), R'.card ≤ a + 1 →
          (∀ a', a + 1 ≤ a' → a' < 2 ^ 32 → c2 (fmt (rndInput S m a')) = none) →
          (∀ rho', rho'.length = 16 → rho' ∉ R' → c2 (fmt (digestInput rho' m)) = none) →
          ∀ v : BitVec 256,
          V z (if admissible v.toNat = true then
              pure (some (rho, v.toNat)) else searchDigest S m (a + 1) n) c2 ≤
            if admissible v.toNat = true then 1 else b := by
        intro R' c2 hR' h1 h2 v
        split
        · simp
        · exact ih (a + 1) c2 R' (by omega) hR' h1 h2
      by_cases hmem : rho ∈ R
      · rw [if_pos hmem]
        refine mul_le_mul' (hz1 _ hb2) ?_
        refine expectedValue_le_of_support fun y hy => ?_
        refine (hk R y.2 (by omega) ?_ ?_ y.1).trans (by split <;> simp [hb])
        · rcases mem_support_ro _ _ y hy with ⟨_, h⟩ | ⟨_, h⟩
          · rw [h]; exact hc1rnd
          · rw [h]; intro a' ha' ha'b
            try dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => rnd_ne_dig S m rho m a' h')]
            exact hc1rnd a' ha' ha'b
        · rcases mem_support_ro _ _ y hy with ⟨_, h⟩ | ⟨_, h⟩
          · rw [h]; intro rho' hl hn; rw [hc1dig]; exact hdig rho' hl hn
          · rw [h]; intro rho' hl hn
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => hn (dig_inj m hm hl hrho h' ▸ hmem)),
              hc1dig]
            exact hdig rho' hl hn
      · rw [if_neg hmem]
        have hfresh : (cache.cacheQuery (fmt (rndInput S m a)) u) (fmt (digestInput rho m)) = none := by
          rw [hc1dig]; exact hdig rho hrho hmem
        rw [expectedValue_ro_fresh _ _ hfresh]
        refine mul_le_mul' (hz1 _ hb2) ?_
        refine (ev_ite_le (fun v : BitVec 256 => ¬ admissible v.toNat = true) b 1 _
          fun v => ?_).trans ?_
        · refine (hk (insert rho R) _ ((Finset.card_insert_le _ _).trans (by omega)) ?_ ?_ v).trans
            (by split <;> simp_all)
          · intro a' ha' ha'b
            try dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => rnd_ne_dig S m rho m a' h')]
            exact hc1rnd a' ha' ha'b
          · intro rho' hl hn
            rw [Finset.mem_insert, not_or] at hn
            dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => hn.1 (dig_inj m hm hl hrho h')), hc1dig]
            exact hdig rho' hl hn.2
        · rw [probEvent_not_uniform (fun v : BitVec 256 => ¬ admissible v.toNat = true),
            mul_one]
          exact le_rfl
    refine le_trans (mul_le_mul' (hz1 _ hb1) (ev_ite_le (fun u => answerBytes 16 u ∈ R) _ _ _
      hcont)) ?_
    have hcoll : Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R |
        ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ epsD := by
      refine (probEvent_answerBytes_mem_le R).trans ?_
      unfold epsD
      gcongr
      exact_mod_cast (show R.card ≤ 2 ^ 20 by omega)
    calc z * (Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R |
            ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * (z * b) +
          Pr[fun u : BitVec 256 => ¬ answerBytes 16 u ∈ R |
            ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * (z * (rhoD * b + (1 - rhoD))))
        ≤ z * (epsD * (z * b) + 1 * (z * (rhoD * b + (1 - rhoD)))) := by
          gcongr; exact probEvent_le_one
      _ = z ^ 2 * ((epsD + rhoD) * b + (1 - rhoD)) := by ring
      _ ≤ b := hstep
end SigGolfCandidate.Budget
end

section

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist Finset
def layerCost (n : Nat) : Nat := ∑ l ∈ Finset.range n, treeCost (height (l + 1))
theorem layerCost_succ (n : Nat) : layerCost (n + 1) = layerCost n + treeCost (height (n + 1)) := by
  simp [layerCost, Finset.sum_range_succ]
theorem layerCost_4 : layerCost 4 = 73244 := by decide
def InvL (n : Nat) (q : Query) : Prop := qbyte q 1 = 4 → n ≤ qbyte q 2
def Inv0 (q : Query) : Prop := qbyte q 1 ≠ 4 ∧ qbyte q 1 ≠ 7 ∧ qbyte q 1 ≠ 12
theorem sum_getD (x : List Nat) : ∑ i ∈ range x.length, x.getD i 0 = x.sum := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    omega
theorem spec_chainTo (lay tau e i x : Nat) (v : Val) (hv : v.length ≤ 16) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) x (chainTo lay tau e i x v) := by
  unfold chainTo
  refine Spec.foldlM_range'_le (P := fun _ => True) 1 x _ (fun _ (w : Val) => w.length ≤ 16)
    (fun _ => 1) v hv (fun i' _ w hw => ?_) (fun _ h => h) (by simp)
  exact spec_hash16_bind (chainInput lay tau e i (1 + i') w) trivial
    (blocksFmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl
theorem sum_pairs (f : Nat → Nat) (n : Nat) :
    ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) = ∑ i ∈ range (2 * n), f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_assoc]
theorem spec_topPath (S cache : List Byte) (hS : S.length = 32) (e : Nat) :
    Spec (fun _ => True) (fun _ => True) 11 (topPath S cache e) := by
  unfold topPath
  rw [topH_eq]
  refine Spec.foldlM_range_le (P := fun _ => True) 11 _ (fun _ (_ : List Val) => True)
    (fun _ => 1) [] trivial (fun l _ acc _ => ?_) (fun _ _ => trivial) (by simp)
  exact spec_hash16_bind _ trivial (mask_ok S hS l _).2 (fun _ _ => Spec.pure _ 0 trivial) le_rfl
def topCost : Nat := 21 + 181 + 11
theorem V_signTop (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) (M : Val) (c : RCache) (hM : M.length ≤ 16) (hinv : CacheInv (InvL 1) c) :
    V z (signTop S cache idx M) c ≤ bC * z ^ topCost := by
  unfold signTop
  rcases hr : route idx 0 with ⟨e, tau⟩
  dsimp only
  have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 → c (fmt (encInput 0 tau e M c')) = none := by
    intro c' _ _
    cases hq : c (fmt (encInput 0 tau e M c')) with
    | none => rfl
    | some u =>
      exfalso
      have h := hinv _ u hq (by unfold encInput; rw [qbyte_tag])
      unfold encInput at h; rw [qbyte_lay] at h; omega
  refine (V_bind_le z _ _ c (z ^ topCost) fun x hx => ?_).trans
    (mul_le_mul' (V_searchCounter z bC hz hbC hstepC 0 tau e M hM cMax 0 c (by simp [cMax])
      hfresh) le_rfl)
  have hx' := (spec_searchCounter 0 tau e M hM (by omega) cMax 0).support
    (I := fun _ => True) (fun _ _ => trivial) c (fun _ _ _ => trivial) x hx
  obtain ⟨o, c1⟩ := x
  rcases o with _ | ⟨cnt, xs⟩
  · simpa using one_le_pow₀ hz
  · dsimp only
    obtain ⟨hlen, hsum⟩ := hx'.1 cnt xs rfl
    refine Spec.V_le (P := fun _ => True) (Post := fun _ => True) ?_ hz c1
    refine Spec.bind' (l := 11) (Spec.foldlM_range (P := fun _ => True) (nChains / 2) _
      (fun _ (_ : List Val) => True) (fun k => 1 + (xs.getD (2 * k) 0 + xs.getD (2 * k + 1) 0))
      [] trivial (fun k _ acc _ => ?_)) (fun vals _ => ?_) ?_
    · obtain ⟨h1, h2⟩ := prf_ok S hS 0 tau e k
      refine spec_prf2 _ trivial h2 (l := xs.getD (2 * k) 0 + xs.getD (2 * k + 1) 0)
        (fun sp hs0 hs1 => ?_) le_rfl
      obtain ⟨s0, s1⟩ := sp
      dsimp only at hs0 hs1 ⊢
      refine (spec_chainTo 0 tau e (2 * k) _ s0 hs0).bind' (fun v0 _ => ?_) le_rfl
      exact (spec_chainTo 0 tau e (2 * k + 1) _ s1 hs1).bind' (l := 0)
        (fun _ _ => Spec.pure _ 0 trivial) (by omega)
    · exact (spec_topPath S cache hS e).bind' (l := 0) (fun _ _ => Spec.pure _ 0 trivial) le_rfl
    · have h42 : 2 * (nChains / 2) = xs.length := by rw [hlen]; rfl
      rw [Finset.sum_add_distrib, sum_pairs (fun i => xs.getD i 0), h42, sum_getD, hsum]
      simp [topCost, targetSum, nChains]
theorem V_signLayers (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) :
    ∀ lay (M : Val) (c : RCache), lay ≤ 4 → M.length ≤ 16 → CacheInv (InvL (lay + 1)) c →
      V z (signLayers S cache idx lay M) c ≤ bC ^ (lay + 1) * z ^ (layerCost lay + topCost) := by
  intro lay
  induction lay with
  | zero =>
    intro M c _ hM hinv
    simp only [signLayers, layerCost, Finset.range_zero, Finset.sum_empty, Nat.zero_add, pow_one]
    exact V_signTop z bC hz hbC hstepC S cache hS idx M c hM hinv
  | succ lay ih =>
    intro M cache' hlay hM hinv
    unfold signLayers
    rcases hr : route idx (lay + 1) with ⟨e, tau⟩
    dsimp only
    have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 →
        cache' (fmt (encInput (lay + 1) tau e M c')) = none := by
      intro c' _ _
      cases hq : cache' (fmt (encInput (lay + 1) tau e M c')) with
      | none => rfl
      | some u =>
        exfalso
        have h := hinv _ u hq (by unfold encInput; rw [qbyte_tag])
        unfold encInput at h; rw [qbyte_lay] at h; omega
    refine (V_bind_le z _ _ cache' (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) fun x hx => ?_).trans ?_
    · have hx' := (spec_searchCounter (lay + 1) tau e M hM (by omega) cMax 0).support
        (I := InvL (lay + 1)) (fun q hq h => by rw [hq.2]) cache'
        (hinv.mono fun q h h4 => by have := h h4; omega) x hx
      obtain ⟨o, c1⟩ := x
      have hbig : 1 ≤ bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)) := one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz)
      rcases o with _ | ⟨cnt, xs⟩
      · simpa using hbig
      · dsimp only
        refine (V_bind_le z _ _ c1 (bC ^ (lay + 1) * z ^ (layerCost lay + topCost))
          fun y hy => ?_).trans ?_
        · have hy' := (spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs).support
            (I := InvL (lay + 1)) (fun q hq h => by unfold PT at hq; omega) c1 hx'.2 y hy
          obtain ⟨⟨root, vals, path⟩, c2⟩ := y
          dsimp only
          refine (V_bind_le z _ _ c2 1 fun w _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := w
            rcases r with _ | rest <;> simp
          · rw [mul_one]; exact ih root c2 (by omega) hy'.1 hy'.2
        · rw [pow_add z (treeCost (height (lay + 1))) (layerCost lay + topCost)]
          calc V z (buildTree S (lay + 1) tau (height (lay + 1)) e xs) c1 *
                (bC ^ (lay + 1) * z ^ (layerCost lay + topCost))
              ≤ z ^ treeCost (height (lay + 1)) * (bC ^ (lay + 1) * z ^ (layerCost lay + topCost)) :=
                mul_le_mul' ((spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs).V_le hz c1)
                  le_rfl
            _ = bC ^ (lay + 1) * (z ^ treeCost (height (lay + 1)) *
                  z ^ (layerCost lay + topCost)) := by ring
    · rw [layerCost_succ]
      calc V z (searchCounter (lay + 1) tau e M 0 cMax) cache' * (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)))
          ≤ bC * (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) :=
            mul_le_mul' (V_searchCounter z bC hz hbC hstepC (lay + 1) tau e M hM cMax 0 cache'
              (by simp [cMax]) hfresh) le_rfl
        _ = bC ^ (lay + 1 + 1) * z ^ (layerCost lay + treeCost (height (lay + 1)) + topCost) := by
            rw [show layerCost lay + treeCost (height (lay + 1)) + topCost =
              treeCost (height (lay + 1)) + (layerCost lay + topCost) by omega]
            ring
theorem spec_H {P : Query → Prop} (x : List Byte) (k : Nat) (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ k) : Spec P (fun _ => True) k (Ref.H x) := by
  rw [← bind_pure (Ref.H x)]
  exact Spec.qry_bind hP (fun u => Spec.pure _ 0 trivial) (by omega)
theorem mac_ok (S cache : List Byte) (hS : S.length = 32) :
    qbyte (fmt (macInput S (cacheRegion cache))) 1 = 14 ∧
      (fmt (macInput S (cacheRegion cache))).blocks ≤ 1025 := by
  refine ⟨by unfold macInput; rw [qbyte_tag], blocksFmt_le _ 1025 ?_ (by omega)⟩
  have : (cacheRegion cache).length ≤ 65504 := by
    unfold cacheRegion slice; rw [List.length_take, ← regionBytes_eq]; omega
  simp only [macInput, length_thInput, length_tweak, List.length_append, hS]; omega
noncomputable abbrev signBound (z bD bC : ℝ≥0∞) : ℝ≥0∞ :=
  bD * (z ^ 40959 * (bC ^ 5 * z ^ (73244 + 213)))
set_option maxRecDepth 100000 in
theorem V_signBody (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 2 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (do
      match ← searchDigest S m 0 aMax with
      | none => pure none
      | some (rho, N) =>
        let (levels, secrets) ← buildPorsTree S (idxOf N)
        let M := (levels.getD porsH []).getD 0 []
        let fts := porsOpening (sortLeaves (leavesOf N)) levels secrets
        match ← signLayers S cache (idxOf N) (nLayers - 1) M with
        | none => pure none
        | some lays => pure (some (serialize rho fts lays))) c ≤ signBound z bD bC := by
  have hbig : 1 ≤ z ^ 40959 * (bC ^ 5 * z ^ (73244 + 213)) :=
    one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz))
  refine (V_bind_le z _ _ c _ fun x hx => ?_).trans (mul_le_mul' ?_ le_rfl)
  · have hx' := (spec_searchDigest S m hS hm aMax 0).support
      (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PD at hq; omega) c
      (hinv.mono fun q h => h.1) x hx
    obtain ⟨o, c1⟩ := x
    rcases o with _ | ⟨rho, N⟩
    · simpa using hbig
    · dsimp only
      refine (V_bind_le z _ _ c1 (bC ^ 5 * z ^ (73244 + 213)) fun y hy => ?_).trans ?_
      · have hy' := (spec_buildPorsTree S hS (idxOf N)).support (I := fun q => qbyte q 1 ≠ 4)
          (fun q hq => by unfold PP at hq; omega) c1 hx'.2 y hy
        obtain ⟨⟨levels, secrets⟩, c2⟩ := y
        dsimp only
        refine (V_bind_le z _ _ c2 1 fun r _ => ?_).trans ?_
        · obtain ⟨r, _⟩ := r
          rcases r with _ | lays <;> simp
        · rw [mul_one, ← layerCost_4, show (213 : Nat) = topCost from rfl]
          refine V_signLayers z bC hz hbC hstepC S cache hS (idxOf N) (nLayers - 1) _ c2
            (by decide) hy'.1 ?_
          exact hy'.2.mono fun q h h4 => absurd h4 h
      · refine mul_le_mul' ?_ le_rfl
        rw [← porsCost_eq]
        exact (spec_buildPorsTree S hS (idxOf N)).V_le hz c1
  · refine V_searchDigest z bD hz hbD hstepD S m hS hm aMax 0 c ∅ (by simp [aMax]) (by simp)
      (fun a' _ _ => ?_) (fun rho _ _ => ?_)
    · cases hq : c (fmt (rndInput S m a')) with
      | none => rfl
      | some u =>
        exfalso
        have h7 : qbyte (fmt (rndInput S m a')) 1 = 7 := by
          rw [qbyte_fmt _ _ (by decide)]
          simp [rndInput, byte_toNat]
        exact (hinv _ u hq).2.1 h7
    · cases hq : c (fmt (digestInput rho m)) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.2; unfold digestInput at this; rw [qbyte_tag] at this
        exact this rfl
theorem V_signList (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 2 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (signList S cache m) c ≤ z ^ 1025 * signBound z bD bC := by
  unfold signList
  obtain ⟨h1, h2⟩ := mac_ok S cache hS
  have hspec := spec_H (P := fun q => qbyte q 1 = 14) (macInput S (cacheRegion cache)) 1025 h1 h2
  refine (V_bind_le z _ _ c _ fun x hx => ?_).trans (mul_le_mul' (hspec.V_le hz c) le_rfl)
  have hx' := hspec.support (I := Inv0) (fun q hq => by unfold Inv0; omega) c hinv x hx
  dsimp only
  split
  · exact V_signBody z bD bC hz hbD hbC hstepD hstepC S cache m hS hm x.2 hx'.2
  · simp only [V_pure]
    exact one_le_mul hbD (one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_pow₀ hbC)
      (one_le_pow₀ hz)))
theorem V_signRef (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 2 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache) (hinv : CacheInv Inv0 c) :
    V z (signRef sk cache m) c ≤ z ^ 1025 * signBound z bD bC := by
  unfold signRef
  refine (V_bind_le z _ _ c 1 fun _ _ => by simp).trans ?_
  rw [mul_one]
  exact V_signList z bD bC hz hbD hbC hstepD hstepC _ _ _ (length_toList sk) (length_toList m)
    c hinv
end SigGolfCandidate.Budget
end

section


namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp ENNReal
noncomputable def zOf (B : Nat) : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (1 / (B : ℝ)))
theorem zOf_pow (B n : Nat) :
    zOf B ^ n = ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) / (B : ℝ))) := by
  unfold zOf
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf
theorem one_le_zOf (B : Nat) : 1 ≤ zOf B := by
  unfold zOf
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.one_le_rpow (by norm_num) (by positivity)
theorem rpow_two_inv_le (B : Nat) (hB : 1 ≤ B) :
    (2 : ℝ) ^ (1 / (B : ℝ)) ≤ 1 / (1 - 0.6931471808 / (B : ℝ)) := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hx0 : 0 < Real.log 2 * (1 / (B : ℝ)) := by positivity
  have hx1 : Real.log 2 * (1 / (B : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  refine (Real.exp_bound_div_one_sub_of_interval' hx0 hx1).le.trans ?_
  have h1 : Real.log 2 * (1 / (B : ℝ)) ≤ 0.6931471808 / (B : ℝ) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hl.le (by linarith)
  have h2 : 0.6931471808 / (B : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  apply one_div_le_one_div_of_le (by linarith)
  linarith
theorem rpow_two_ge (y : ℝ) (hy : 0 ≤ y) :
    1 + 0.6931471803 * y + (0.6931471803 * y) ^ 2 / 2 ≤ (2 : ℝ) ^ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl := Real.log_two_gt_d9
  have hx : 0.6931471803 * y ≤ Real.log 2 * y := mul_le_mul_of_nonneg_right hl.le hy
  have hx0 : 0 ≤ 0.6931471803 * y := by positivity
  have h := Real.quadratic_le_exp_of_nonneg (hx0.trans hx)
  nlinarith
theorem natCast_div_eq_ofReal (a b : Nat) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / (b : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]
theorem one_sub_ofReal (x : ℝ) (hx : 0 ≤ x) :
    1 - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub _ hx, ENNReal.ofReal_one]
def admTuples : Nat := 768394439706066703645522769421343549971302651574651715584000
theorem rhoD_eq : rhoD = ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210) := by
  unfold rhoD
  rw [probEvent_not_admissible, Octopus.admissibleTuples_eq,
    show (2 : ℝ≥0∞) ^ 210 = ((2 ^ 210 : Nat) : ℝ≥0∞) by rw [Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
  unfold admTuples
  norm_num
theorem rhoC_eq : rhoC = ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) := by
  unfold rhoC
  rw [probEvent_decode_none,
    show (2 : ℝ≥0∞) ^ 256 = ((2 ^ 256 : Nat) : ℝ≥0∞) by rw [Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
  congr 2
  push_cast
  field_simp
  ring
theorem epsD_eq : epsD = ENNReal.ofReal (1 / 2 ^ 108) := by
  unfold epsD
  rw [show (2 : ℝ≥0∞) ^ 20 / 2 ^ 128 = ((2 ^ 20 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity)]
  norm_num
noncomputable def bD : ℝ≥0∞ := ENNReal.ofReal 1.0232
noncomputable def bC : ℝ≥0∞ := ENNReal.ofReal 1.011
theorem zS_le : zOf (2 ^ 17) ≤ ENNReal.ofReal (1 / (1 - 0.6931471808 / 131072)) := by
  unfold zOf
  refine ENNReal.ofReal_le_ofReal ?_
  have := rpow_two_inv_le (2 ^ 17) (by norm_num)
  simpa using this
theorem stepD : zOf (2 ^ 17) ^ 2 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD := by
  have hp0 : 0 ≤ (admTuples : ℝ) / 2 ^ 210 := by positivity
  have hp1 : (admTuples : ℝ) / 2 ^ 210 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold admTuples; norm_num
  rw [rhoD_eq, epsD_eq, one_sub_ofReal _ (by linarith), bD]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) ^ 2 * ((ENNReal.ofReal (1 / 2 ^ 108) +
        ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210)) * ENNReal.ofReal 1.0232 +
        ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210)))
      ≤ ENNReal.ofReal zb ^ 2 * ((ENNReal.ofReal (1 / 2 ^ 108) +
        ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210)) * ENNReal.ofReal 1.0232 +
        ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb ^ 2 * ((1 / 2 ^ 108 + (1 - (admTuples : ℝ) / 2 ^ 210)) * 1.0232 +
          (1 - (1 - (admTuples : ℝ) / 2 ^ 210)))) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by linarith),
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_pow (by norm_num [zb]), ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.0232 := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold admTuples
        norm_num [zb]
theorem stepC : zOf (2 ^ 17) * (rhoC * bC + (1 - rhoC)) ≤ bC := by
  have hc0 : 0 ≤ (codeCount : ℝ) / 2 ^ 128 := by positivity
  have hc : (codeCount : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold codeCount; norm_num
  rw [rhoC_eq, one_sub_ofReal _ (by linarith), bC]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) * ENNReal.ofReal 1.011 +
        ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))
      ≤ ENNReal.ofReal zb * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) *
        ENNReal.ofReal 1.011 + ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb * ((1 - (codeCount : ℝ) / 2 ^ 128) * 1.011 +
          (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.011 := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold codeCount
        norm_num [zb]
theorem final_sign :
    zOf (2 ^ 17) ^ 1025 * signBound (zOf (2 ^ 17)) bD bC ≤ 2 := by
  have e : zOf (2 ^ 17) ^ 1025 * signBound (zOf (2 ^ 17)) bD bC =
      bD * bC ^ 5 * zOf (2 ^ 17) ^ 115441 := by
    rw [show 115441 = 1025 + (40959 + (73244 + 213)) by norm_num, pow_add, pow_add]
    simp only [signBound]; ring
  rw [e, zOf_pow, bD, bC, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : (2 : ℝ) ^ (((115441 : Nat) : ℝ) / ((2 ^ 17 : Nat) : ℝ)) =
      2 / (2 : ℝ) ^ ((15631 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  rw [hsplit]
  have hlow := rpow_two_ge (15631 / 131072) (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ ((15631 : ℝ) / 131072) := Real.rpow_pos_of_pos (by norm_num) _
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith
theorem V_signRef_le_two (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache)
    (hinv : CacheInv Inv0 c) : V (zOf (2 ^ 17)) (signRef sk cache m) c ≤ 2 := by
  have h1 : 1 ≤ bD := by rw [bD, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : 1 ≤ bC := by rw [bC, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact (V_signRef _ bD bC (one_le_zOf _) h1 h2 stepD stepC sk cache m c hinv).trans final_sign
theorem V_keygenRef_le_two (sk : Bytes 32) (cache : RCache) :
    V (zOf (2 ^ 20)) (keygenRef sk) cache ≤ 2 := by
  refine ((spec_keygenRef sk).V_le (one_le_zOf _) cache).trans ?_
  rw [keygenCost_eq]
  rw [zOf_pow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ) ^ ((674814 : Nat) / ((2 ^ 20 : Nat) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2
end SigGolfCandidate.Budget
end
