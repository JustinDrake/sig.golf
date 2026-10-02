import SigGolfCandidate.T3.Gate6.Budget

namespace SigGolfCandidate.T3.BaseAudit
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def zU : ℚ := 1/(1-6931471808/(10000000000*131072))
def p0 : ℚ := (18602366037442415965022913 / 39614081257132168796771975168)
def b0 : ℚ := (1011389784313 / 1000000000000)
theorem step_0 : zU*((1-p0)*b0+p0) ≤ b0 := by norm_num [zU,p0,b0]
def p1 : ℚ := (5503086055698106792572791280776033 / 10633823966279326983230456482242756608)
def b1 : ℚ := (252581068277 / 250000000000)
theorem step_1 : zU*((1-p1)*b1+p1) ≤ b1 := by norm_num [zU,p1,b1]
def p2 : ℚ := (33210373316701753609053794695642145 / 42535295865117307932921825928971026432)
def b2 : ℚ := (503409673483 / 500000000000)
theorem step_2 : zU*((1-p2)*b2+p2) ≤ b2 := by norm_num [zU,p2,b2]
def p3 : ℚ := (33210373316701753609053794695642145 / 42535295865117307932921825928971026432)
def b3 : ℚ := (503409673483 / 500000000000)
theorem step_3 : zU*((1-p3)*b3+p3) ≤ b3 := by norm_num [zU,p3,b3]
def p4 : ℚ := (33210373316701753609053794695642145 / 42535295865117307932921825928971026432)
def b4 : ℚ := (503409673483 / 500000000000)
theorem step_4 : zU*((1-p4)*b4+p4) ≤ b4 := by norm_num [zU,p4,b4]

theorem signing_envelope :
    (2 : ℝ)^((123036 : ℝ)/131072) * ((1011389784313 / 1000000000000) * (252581068277 / 250000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000)) ≤ 2 := by
  have hsplit : (2 : ℝ)^((123036 : ℝ)/131072) = 2/(2 : ℝ)^((8036 : ℝ)/131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (8036/131072) (by norm_num)
  have hn : ((1011389784313 / 1000000000000) * (252581068277 / 250000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000) : ℝ) ≤
      1+0.6931471803*(8036/131072)+(0.6931471803*(8036/131072))^2/2 := by norm_num
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith


/-- The actual source and search model share the updated fixed compression allowance. -/
theorem source_signing_envelope :
    (2 : ℝ)^((123036 : ℝ)/131072) * ((1011389784313 / 1000000000000) * (252581068277 / 250000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000) * (503409673483 / 500000000000)) ≤ 2 := by
  exact signing_envelope

end SigGolfCandidate.T3.BaseAudit
