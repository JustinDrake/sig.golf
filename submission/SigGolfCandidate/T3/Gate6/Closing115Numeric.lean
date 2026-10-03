import SigGolfCandidate.T3.Gate6.MomentNumeric
import SigGolfCandidate.T3.Gate6.SourceBudget
namespace SigGolfResearch.Gate3Closing115
open ENNReal SigGolfResearch.Gate6.Moments.Numeric
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Exact gate3 mean at the current fixed proposal horizon, with the gate 135/1024
(reference-gate envelope times 135/128). -/
theorem mean_bound :
    (2:ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234*(135/128)≤4995/8192 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]

theorem variance_excess : (16767/81920000:ℚ)*(2048/3189)≤13145/100000000 := by norm_num

theorem reuse_bound : SigGolfResearch.Gate6.Budget.p0≤(1/1024:ℚ) := by
  norm_num [SigGolfResearch.Gate6.Budget.p0]

theorem prefix_rate :
    ((3/2:ℚ)+4*(143/2^20)+2*(143/2^20)^2)*(1048576/1048433)+4*(143/2^20)*(1048576/1048433)^2+
      2*57*(143/2^20)*(1048576/1048433)≤1903/1000 := by norm_num

theorem encoding_rate : (1:ℚ)+2*3306*(143/2^20)*(1048576/1048433)≤1903/1000 := by norm_num

theorem small_excess_rate : (201:ℚ)*(13145/100000000)≤27/1000 := by norm_num

theorem near_rate : (1048576/1048433:ℚ)*(872505/2048+1/16+21*201/2^25)≤427 := by norm_num

theorem small_first_rate : (1903/1000:ℚ)+27/1000+1/1000≤1931/1000 := by norm_num

theorem pointwise_excess (v m : ℝ) (hm : m≤4995/8192) :
    (3189/2048)*max 0 (v-1023/1024)+2*m*v≤v^2+m^2 := by
  rcases le_total v (1023/1024) with hv|hv
  · rw [max_eq_left (sub_nonpos.mpr hv)];nlinarith [sq_nonneg (v-m)]
  · rw [max_eq_right (sub_nonneg.mpr hv)]
    nlinarith [sq_nonneg (v-m-3189/4096)]

theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 143 / 2 ^ 20) :
    1931 / 1000 * y + 430 * y ^ 2 + 1 / 2 ^ 132 + (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hprod : 0 ≤ (y - 1/2^128) * (143/2^20 - y) := mul_nonneg (sub_nonneg.2 hlow) (sub_nonneg.2 hhigh)
  have hsq : y^2 ≤ (1/2^128 + 143/2^20) * y - 1/2^128 * (143/2^20) := by nlinarith
  linarith

theorem large_closing_real (y : ℝ) (hlow : 143 / 2 ^ 20 ≤ y) :
    (2 * y - y ^ 2) + y * (13145 / 100000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 20) + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have h13 : (1 : ℝ) / 2 ^ 13 ≤ y := le_trans (by norm_num) hlow
  have hsq : y * (143 / 2 ^ 20) ≤ y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlow hn
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 2 ^ 119 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 13) / 2 ^ 119 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right h13 (by positivity)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 687 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 13) / 2 ^ 687 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right h13 (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 139 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 13) / 2 ^ 139 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right h13 (by positivity)
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
