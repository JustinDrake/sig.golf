import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude

namespace SphincsSecurity.Security

open ENNReal
set_option exponentiation.threshold 1024

private theorem smallReserve (x : ℝ)
    (hlow : 606208 / 2 ^ 128 ≤ x) (hhigh : x ≤ 3 / 16384) :
    7 / 4 * x + 254 * 1 / 2 ^ 16 * x + 1 / 2 ^ 700 + x ^ 2 * 2 +
      16384 / 16381 * x * (1241 * x + 15 * (254 * x / 2 ^ 25) + 15 / 2 ^ 700) +
      x / 2 ^ 72 ≤ 2 * x - 2 / 2 ^ 128 := by
  have hn : 0 ≤ x := le_trans (by positivity) hlow
  have hsq : x * x ≤ x * (3 / 16384) := mul_le_mul_of_nonneg_left hhigh hn
  have htail : (1 : ℝ) / 2 ^ 700 ≤ x / 2 ^ 572 := by
    calc
      (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by norm_num
      _ ≤ x / 2 ^ 572 := div_le_div_of_nonneg_right (le_trans (by norm_num) hlow) (by positivity)
  have hsmall : (2 : ℝ) / 2 ^ 128 ≤ x / 303104 := by
    calc
      (2 : ℝ) / 2 ^ 128 = (606208 / 2 ^ 128) / 303104 := by norm_num
      _ ≤ x / 303104 := div_le_div_of_nonneg_right hlow (by positivity)
  norm_num at hsq htail hsmall ⊢
  nlinarith [hsq, htail, hn, hlow, hhigh, hsmall]

private theorem largeReserve (x : ℝ) (hx : 3 / 16384 ≤ x) :
    2 * x - x ^ 2 + (1 / 65536) * x + (x / 2 ^ 25 + 1 / 2 ^ 700) +
      x / 2 ^ 72 ≤ 2 * x := by
  have hn : 0 ≤ x := le_trans (by norm_num) hx
  have hs := mul_nonneg (sub_nonneg.mpr hx) hn
  have he : (1 : ℝ) / 2 ^ 700 ≤ 1 / 1099511627776 := by
    calc
      _ ≤ 1 / (2 : ℝ) ^ 40 := one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by decide : 40 ≤ 700))
      _ = _ := by norm_num
  calc
    _ ≤ 2 * x - x ^ 2 + (1 / 65536) * x +
        (x / 2 ^ 25 + 1 / 1099511627776) + x / 2 ^ 72 := by
          gcongr
    _ ≤ 2 * x := by
      norm_num at hx hs ⊢
      nlinarith

theorem seedLoss_le_reserve (r : Nat) :
    (r : ENNReal) / 2 ^ 207 ≤ (r : ENNReal) / 2 ^ 200 := by
  apply ENNReal.div_le_div le_rfl
  norm_num

theorem macLoss_le_oneQuery :
    (2 ^ 32 : ENNReal) / 2 ^ 256 ≤ (1 : ENNReal) / 2 ^ 127 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem oneQueryGap (q : Nat) (hq : 1 ≤ q) :
    ((q - 1 : Nat) : ENNReal) / 2 ^ 127 + (1 : ENNReal) / 2 ^ 127 =
      (q : ENNReal) / 2 ^ 127 := by
  rw [← ENNReal.add_div]
  have h : q - 1 + 1 = q := Nat.sub_add_cancel hq
  calc
    _ = (((q - 1 + 1 : Nat) : ENNReal)) / 2 ^ 127 := by norm_num [Nat.cast_add]
    _ = _ := by rw [h]

theorem transferReserveArithmetic (q : Nat) (hq : 1 ≤ q) (x : ENNReal)
    (hx : x + ((q - 1 : Nat) : ENNReal) / 2 ^ 200 ≤
      ((q - 1 : Nat) : ENNReal) / 2 ^ 127) :
    x + (2 ^ 32 : ENNReal) / 2 ^ 256 +
      ((q - 1 : Nat) : ENNReal) / 2 ^ 207 ≤ (q : ENNReal) / 2 ^ 127 := by
  calc
    _ = (x + ((q - 1 : Nat) : ENNReal) / 2 ^ 207) +
        (2 ^ 32 : ENNReal) / 2 ^ 256 := by ac_rfl
    _ ≤ (x + ((q - 1 : Nat) : ENNReal) / 2 ^ 200) +
        (2 ^ 32 : ENNReal) / 2 ^ 256 :=
      add_le_add (add_le_add le_rfl (seedLoss_le_reserve _)) le_rfl
    _ ≤ ((q - 1 : Nat) : ENNReal) / 2 ^ 127 + (1 : ENNReal) / 2 ^ 127 :=
      add_le_add hx macLoss_le_oneQuery
    _ = _ := oneQueryGap q hq

end SphincsSecurity.Security
