import SigGolfCandidate.T3.Gate6.FreshProbability
import SigGolfCandidate.Budget.Numeric
namespace SigGolfResearch.Gate6.Budget
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def p0 : ℚ := 18602366037442415965022913/39614081257132168796771975168
def zU : ℚ := 1/(1-6931471808/(10000000000*131072))
def b0 : ℚ := 1011389784313 / 1000000000000

theorem digest_geometric_step : zU*((1-p0)*b0+p0)≤b0 := by norm_num [zU,p0,b0]
theorem probability_floor : 1/3300≤p0 ∧ p0≤1/16 := by norm_num [p0]
theorem probability_matches : (SigGolfResearch.Gate6.acceptance).toReal=(p0 : ℝ) := by
  norm_num [SigGolfResearch.Gate6.acceptance,p0,ENNReal.toReal_div]

/-- Existing four WOTS geometric bounds; their source refinements are inherited unchanged. -/
noncomputable def wotsProduct : ℝ := (252581068277 / 250000000000)*(503409673483/500000000000)^3
noncomputable def bProduct : ℝ := (b0 : ℝ)*wotsProduct

/-- Conservative T3 fixed signing allowance satisfies the full exponential envelope
at the new exact digest probability and unchanged WOTS geometric factors. -/
theorem signing_envelope : (2 : ℝ)^((123036 : ℝ)/131072)*bProduct≤2 := by
  have hsplit : (2 : ℝ)^((123036 : ℝ)/131072)=2/(2 : ℝ)^((8036 : ℝ)/131072) := by
    rw [_root_.eq_div_iff (by positivity),←Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (8036/131072) (by norm_num)
  have hn : bProduct≤1+0.6931471803*(8036/131072)+(0.6931471803*(8036/131072))^2/2 := by
    norm_num [bProduct,b0,wotsProduct]
  rw [hsplit,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  nlinarith

theorem physical_bank_work : 7*(1024+2048+2047)+2=35835 := by decide
theorem fixed_signing_work : 513+2+35835+86686=123036 := by decide
theorem signature_layout_bytes : 16*(1+21+89+28+187+31)=5712 := by decide

end SigGolfResearch.Gate6.Budget
