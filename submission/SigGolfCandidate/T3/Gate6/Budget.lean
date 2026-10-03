import SigGolfCandidate.T3.Gate6.FreshProbability
import SigGolfCandidate.Budget.Numeric
namespace SigGolfResearch.Gate6.Budget
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def p0 : ℚ := 940126139045457411061189575/2535301200456458802993406410752
def zU : ℚ := 1/(1-6931471808/(10000000000*131072))
def b0 : ℚ := 202893524443/200000000000

theorem digest_geometric_step : zU*((1-p0)*b0+p0)≤b0 := by norm_num [zU,p0,b0]
theorem probability_floor : 1/3300≤p0 ∧ p0≤1/16 := by norm_num [p0]
theorem probability_matches : (SigGolfResearch.Gate6.acceptance).toReal=(p0 : ℝ) := by
  norm_num [SigGolfResearch.Gate6.acceptance,p0,ENNReal.toReal_div]

/-- Retuned four WOTS geometric bounds, linked to actual decoder counts in EncodingCounting. -/
noncomputable def wotsProduct : ℝ := (1009892452433/1000000000000)*(1008345227909/1000000000000)^3
noncomputable def bProduct : ℝ := (b0 : ℝ)*wotsProduct

/-- Conservative T3 fixed signing allowance satisfies the full exponential envelope
at the unchanged exact digest probability and retuned WOTS geometric factors. -/
theorem signing_envelope : (2 : ℝ)^((121761 : ℝ)/131072)*bProduct≤2 := by
  have hsplit : (2 : ℝ)^((121761 : ℝ)/131072)=2/(2 : ℝ)^((9311 : ℝ)/131072) := by
    rw [_root_.eq_div_iff (by positivity),←Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (9311/131072) (by norm_num)
  have hn : bProduct≤1+0.6931471803*(9311/131072)+(0.6931471803*(9311/131072))^2/2 := by
    norm_num [bProduct,b0,wotsProduct]
  rw [hsplit,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  nlinarith

theorem physical_bank_work : 7*(1024+2048+2047)+2=35835 := by decide
theorem fixed_signing_work : 2+2+35835+85922=121761 := by decide
theorem signature_layout_bytes : 16*(1+21+87+28+183+31)=5616 := by decide

end SigGolfResearch.Gate6.Budget
