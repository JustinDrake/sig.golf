import SigGolfCandidate.Budget.Sign
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Budget: the numbers

With `z = 2 ^ (1 / 2^17)`, the paired cap117 digest search uses `bD = 1.0279`.
The five target sums are `[185,185,186,186,186]`; exact selected acceptance
is `(63/32) * codeCount lay / 2^128`. Counter moment bounds are `1.01078` and `1.01290`.
The cache MAC is arithmetic (three key derivations) and the top path is read from the cache, so the
deterministic compression work is 114423.
The resulting certified moment is
`2 ^ (114423 / 2^17) * 1.0279 * 1.01078^2 * 1.01290^3 ≈ 1.99874 ≤ 2`.
Keygen: `z_K ^ 673792 ≤ 2` with
`z_K = 2 ^ (1 / 2^20)` (`V_keygenRef_le_two`).

Real bounds used: `log 2 < 0.6931471808`, `log 2 > 0.6931471803`, `exp x < 1 / (1 - x)` and
`1 + x + x^2/2 ≤ exp x` (x ≥ 0).
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp ENNReal

/-- `2 ^ (1 / B)` as an extended real. -/
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

/-- `2 ^ (1/B) ≤ 1 / (1 - 0.6931471808 / B)`. -/
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

/-- `2 ^ y ≥ 1 + x + x^2/2` with `x = 0.6931471803 y`, for `y ≥ 0`. -/
theorem rpow_two_ge (y : ℝ) (hy : 0 ≤ y) :
    1 + 0.6931471803 * y + (0.6931471803 * y) ^ 2 / 2 ≤ (2 : ℝ) ^ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl := Real.log_two_gt_d9
  have hx : 0.6931471803 * y ≤ Real.log 2 * y := mul_le_mul_of_nonneg_right hl.le hy
  have hx0 : 0 ≤ 0.6931471803 * y := by positivity
  have h := Real.quadratic_le_exp_of_nonneg (hx0.trans hx)
  nlinarith

/-! ## The per-trial probabilities as reals -/

theorem natCast_div_eq_ofReal (a b : Nat) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / (b : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

theorem one_sub_ofReal (x : ℝ) (hx : 0 ≤ x) :
    1 - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub _ hx, ENNReal.ofReal_one]

/-- `15! * Nadm`, the number of admissible 15-tuples of leaf indices. -/
def admTuples : Nat := 482553903788731839004032501852250937641274733772928974848000

theorem rhoD_eq : rhoD = ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210) := by
  unfold rhoD
  rw [probEvent_not_admissible, Octopus.admissibleTuples_eq,
    show (2 : ℝ≥0∞) ^ 210 = ((2 ^ 210 : Nat) : ℝ≥0∞) by rw [Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
  unfold admTuples
  norm_num

theorem rhoC_eq (lay : Nat) : rhoC lay = ENNReal.ofReal (1 - (63 * codeCount lay : ℝ) / 2 ^ 133) := by
  unfold rhoC
  rw [probEvent_selected_decode_none,
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

/-! ## The step conditions -/

/-- The paired one-block digest-search bound (also valid for cap117). -/
noncomputable def bD : ℝ≥0∞ := ENNReal.ofReal 1.0279
/-- The counter-search bound. -/
noncomputable def bC (lay : Nat) : ℝ≥0∞ := ENNReal.ofReal (if 2 ≤ lay then 1.01290 else 1.01078)

theorem zS_le : zOf (2 ^ 17) ≤ ENNReal.ofReal (1 / (1 - 0.6931471808 / 131072)) := by
  unfold zOf
  refine ENNReal.ofReal_le_ofReal ?_
  have := rpow_two_inv_le (2 ^ 17) (by norm_num)
  simpa using this

theorem epsP_eq : epsP = ENNReal.ofReal (1 / 2 ^ 107) := by
  unfold epsP
  rw [show (2 : ℝ≥0∞) ^ 21 / 2 ^ 128 = ((2 ^ 21 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity)]
  norm_num

theorem stepD : zOf (2 ^ 17) ^ 2 * (1 - rhoD) +
    zOf (2 ^ 17) ^ 3 * rhoD * (1 - rhoD) +
    zOf (2 ^ 17) ^ 3 * (rhoD ^ 2 + 2 * epsP) * bD ≤ bD := by
  have hp0 : 0 ≤ (admTuples : ℝ) / 2 ^ 210 := by positivity
  have hp1 : (admTuples : ℝ) / 2 ^ 210 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold admTuples; norm_num
  rw [rhoD_eq, epsP_eq, one_sub_ofReal _ (by linarith), bD]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  have hzb : 0 ≤ zb := by norm_num [zb]
  have hr : 0 ≤ 1 - (admTuples : ℝ) / 2 ^ 210 := by linarith
  have hp : 0 ≤ 1 - (1 - (admTuples : ℝ) / 2 ^ 210) := by linarith
  calc _ ≤ ENNReal.ofReal zb ^ 2 * ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210)) +
      ENNReal.ofReal zb ^ 3 * ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210) *
        ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210)) +
      ENNReal.ofReal zb ^ 3 * (ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210) ^ 2 +
        2 * ENNReal.ofReal (1 / 2 ^ 107)) * ENNReal.ofReal 1.0279 := by
          gcongr <;> exact zS_le
    _ ≤ ENNReal.ofReal 1.0279 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      simp only [← ENNReal.ofReal_pow hzb, ← ENNReal.ofReal_pow hr]
      repeat' first
        | rw [← ENNReal.ofReal_mul (by norm_num [zb, admTuples])]
        | rw [← ENNReal.ofReal_add (by norm_num [zb, admTuples]) (by norm_num [zb, admTuples])]
      apply ENNReal.ofReal_le_ofReal
      norm_num [zb, admTuples]

theorem stepC_low (lay : Nat) (hlay : ¬ 2 ≤ lay) : zOf (2 ^ 17) * (rhoC lay * bC lay + (1 - rhoC lay)) ≤ bC lay := by
  have hc0 : 0 ≤ (63 * codeCount lay : ℝ) / 2 ^ 133 := by positivity
  have hc : (63 * codeCount lay : ℝ) / 2 ^ 133 ≤ 1 := by
    rw [div_le_one (by positivity)]; simp [codeCount, hlay]; norm_num
  rw [rhoC_eq, one_sub_ofReal _ (by linarith), bC, if_neg hlay]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) * (ENNReal.ofReal (1 - (63 * codeCount lay : ℝ) / 2 ^ 133) * ENNReal.ofReal 1.01078 +
        ENNReal.ofReal (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133)))
      ≤ ENNReal.ofReal zb * (ENNReal.ofReal (1 - (63 * codeCount lay : ℝ) / 2 ^ 133) *
        ENNReal.ofReal 1.01078 + ENNReal.ofReal (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb * ((1 - (63 * codeCount lay : ℝ) / 2 ^ 133) * 1.01078 +
          (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.01078 := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [codeCount, if_neg hlay]
        norm_num [zb]

theorem stepC_high (lay : Nat) (hlay : 2 ≤ lay) : zOf (2 ^ 17) * (rhoC lay * bC lay + (1 - rhoC lay)) ≤ bC lay := by
  have hc0 : 0 ≤ (63 * codeCount lay : ℝ) / 2 ^ 133 := by positivity
  have hc : (63 * codeCount lay : ℝ) / 2 ^ 133 ≤ 1 := by
    rw [div_le_one (by positivity)]; simp [codeCount, hlay]; norm_num
  rw [rhoC_eq, one_sub_ofReal _ (by linarith), bC, if_pos hlay]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) * (ENNReal.ofReal (1 - (63 * codeCount lay : ℝ) / 2 ^ 133) * ENNReal.ofReal 1.01290 +
        ENNReal.ofReal (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133)))
      ≤ ENNReal.ofReal zb * (ENNReal.ofReal (1 - (63 * codeCount lay : ℝ) / 2 ^ 133) *
        ENNReal.ofReal 1.01290 + ENNReal.ofReal (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb * ((1 - (63 * codeCount lay : ℝ) / 2 ^ 133) * 1.01290 +
          (1 - (1 - (63 * codeCount lay : ℝ) / 2 ^ 133)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.01290 := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [codeCount, if_pos hlay]
        norm_num [zb]

theorem stepC (lay : Nat) : zOf (2 ^ 17) * (rhoC lay * bC lay + (1 - rhoC lay)) ≤ bC lay := by
  by_cases h : 2 ≤ lay
  · exact stepC_high lay h
  · exact stepC_low lay h

/-! ## The final bounds -/

theorem final_sign :
    zOf (2 ^ 17) ^ 3 * signBound (zOf (2 ^ 17)) bD bC ≤ 2 := by
  have e : zOf (2 ^ 17) ^ 3 * signBound (zOf (2 ^ 17)) bD bC =
      bD * (ENNReal.ofReal 1.01078) ^ 2 * (ENNReal.ofReal 1.01290) ^ 3 * zOf (2 ^ 17) ^ 114423 := by
    rw [show 114423 = 3 + (40959 + (73244 + 217)) by norm_num, pow_add, pow_add]
    norm_num [signBound, counterProduct, Finset.prod_range_succ, bC]
    ring
  rw [e, zOf_pow, bD, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : (2 : ℝ) ^ (((114423 : Nat) : ℝ) / ((2 ^ 17 : Nat) : ℝ)) =
      2 / (2 : ℝ) ^ ((16649 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  rw [hsplit]
  have hlow := rpow_two_ge (16649 / 131072) (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ ((16649 : ℝ) / 131072) := Real.rpow_pos_of_pos (by norm_num) _
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem V_signRef_le_two (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache)
    (hinv : CacheInv Inv0 c) : V (zOf (2 ^ 17)) (signRef sk cache m) c ≤ 2 := by
  have h1 : 1 ≤ bD := by rw [bD, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : ∀ lay, 1 ≤ bC lay := by
    intro lay
    rw [bC, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    split_ifs <;> norm_num
  exact (V_signRef _ bD bC (one_le_zOf _) h1 h2 stepD stepC sk cache m c hinv).trans final_sign

theorem V_keygenRef_le_two (sk : Bytes 32) (cache : RCache) :
    V (zOf (2 ^ 20)) (keygenRef sk) cache ≤ 2 := by
  refine ((spec_keygenRef sk).V_le (one_le_zOf _) cache).trans ?_
  rw [keygenCost_eq]
  rw [zOf_pow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ) ^ ((673792 : Nat) / ((2 ^ 20 : Nat) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

end SigGolfCandidate.Budget
