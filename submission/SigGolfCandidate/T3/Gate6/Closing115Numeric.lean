import SigGolfCandidate.T3.Gate6.MomentNumeric
import SigGolfCandidate.T3.Gate6.SourceBudget
namespace SigGolfResearch.Gate3Closing115
open ENNReal SigGolfResearch.Gate6.Moments.Numeric
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Exact gate3 mean at the current fixed proposal horizon. -/
theorem mean_bound :
    (2:ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234≤37/64 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]

theorem variance_excess : (18400/100000000:ℚ)*(8/13)≤11324/100000000 := by norm_num

theorem reuse_bound : SigGolfResearch.Gate6.Budget.p0≤(1/64:ℚ) := by
  norm_num [SigGolfResearch.Gate6.Budget.p0]

theorem prefix_rate :
    ((3/2:ℚ)+4/8192+2/(8192^2))*(8192/8191)+4/8192*(8192/8191)^2+
      2*57/8192*(8192/8191)≤181/100 := by norm_num

theorem encoding_rate : (1:ℚ)+2*3306/8192*(8192/8191)≤181/100 := by norm_num

theorem small_excess_rate : (201:ℚ)*(11324/100000000)≤1/40 := by norm_num

theorem near_rate : (8192/8191:ℚ)*(404+21*201/2^25)≤405 := by norm_num

theorem small_first_rate : (181/100:ℚ)+1/40+1/1000≤37/20 := by norm_num

theorem pointwise_excess (v m : ℝ) (hm : m≤37/64) :
    (13/8)*max 0 (v-63/64)+2*m*v≤v^2+m^2 := by
  rcases le_total v (63/64) with hv|hv
  · rw [max_eq_left (sub_nonpos.mpr hv)];nlinarith [sq_nonneg (v-m)]
  · rw [max_eq_right (sub_nonneg.mpr hv)]
    nlinarith [sq_nonneg (v-m-13/16)]

theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 1 / 2 ^ 13) :
    37 / 20 * y + 512 * y ^ 2 + 1 / 2 ^ 132 + (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : 512 * y ^ 2 ≤ y / 16 := by
    have h := mul_le_mul_of_nonneg_left hhigh hn
    have h2 : y ^ 2 = y * y := by ring
    rw [h2]
    have : (512 : ℝ) * (y * (1 / 2 ^ 13)) = y / 16 := by ring
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 16 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 128) / 16 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by norm_num)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 128) / 2 ^ 24 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy18 : y / 2 ^ 18 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy572 : y / 2 ^ 572 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy24 : y / 2 ^ 24 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  linarith

theorem large_closing_real (y : ℝ) (hlow : 1 / 2 ^ 13 ≤ y) :
    (2 * y - y ^ 2) + y * (11324 / 100000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 20) + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : y * (1 / 2 ^ 13) ≤ y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlow hn
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 2 ^ 119 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 13) / 2 ^ 119 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 687 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 13) / 2 ^ 687 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 139 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 13) / 2 ^ 139 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy118 : y / 2 ^ 119 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy686 : y / 2 ^ 687 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy138 : y / 2 ^ 139 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  norm_num at hsq hy118 hy686 hy138 hy128 ⊢
  nlinarith

end SigGolfResearch.Gate3Closing115
#print axioms SigGolfResearch.Gate3Closing115.mean_bound
#print axioms SigGolfResearch.Gate3Closing115.variance_excess
#print axioms SigGolfResearch.Gate3Closing115.reuse_bound
#print axioms SigGolfResearch.Gate3Closing115.prefix_rate
#print axioms SigGolfResearch.Gate3Closing115.encoding_rate
#print axioms SigGolfResearch.Gate3Closing115.small_excess_rate
#print axioms SigGolfResearch.Gate3Closing115.near_rate
#print axioms SigGolfResearch.Gate3Closing115.small_first_rate
#print axioms SigGolfResearch.Gate3Closing115.pointwise_excess
#print axioms SigGolfResearch.Gate3Closing115.small_closing_real
#print axioms SigGolfResearch.Gate3Closing115.large_closing_real
