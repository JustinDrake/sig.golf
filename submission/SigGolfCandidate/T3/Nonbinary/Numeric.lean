import SigGolfCandidate.Budget.Numeric
namespace SigGolfResearch.NonbinaryTop
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def zU : ℚ := 1/(1-6931471808/(10000000000*131072))
def p0 : ℚ := 6963897326262647489342145/19807040628566084398385987584
def b0 : ℚ := 507635451307/500000000000
theorem geometric0 : zU*((1-p0)*b0+p0)≤b0 := by norm_num [zU,p0,b0]
def p1 : ℚ := 45926795543361359114465905709789119/85070591730234615865843651857942052864
def b1 : ℚ := 1009892452433/1000000000000
theorem geometric1 : zU*((1-p1)*b1+p1)≤b1 := by norm_num [zU,p1,b1]
def p2 : ℚ := 27179160510794301985010390415765999/42535295865117307932921825928971026432
def b2 : ℚ := 1008345227909/1000000000000
theorem geometric2 : zU*((1-p2)*b2+p2)≤b2 := by norm_num [zU,p2,b2]
def p3 : ℚ := 27179160510794301985010390415765999/42535295865117307932921825928971026432
def b3 : ℚ := 1008345227909/1000000000000
theorem geometric3 : zU*((1-p3)*b3+p3)≤b3 := by norm_num [zU,p3,b3]
def p4 : ℚ := 33210373316701753609053794695642145/42535295865117307932921825928971026432
def b4 : ℚ := 503409673483/500000000000
theorem geometric4 : zU*((1-p4)*b4+p4)≤b4 := by norm_num [zU,p4,b4]
theorem top_floor : (1:ℚ)/4096≤p1 := by norm_num [p1]
noncomputable def product : ℝ := (b0:ℝ)*(b1:ℝ)*(b2:ℝ)*(b3:ℝ)*(b4:ℝ)
theorem signing_envelope : (2:ℝ)^((121762:ℝ)/131072)*product≤2 := by
  have hsplit : (2:ℝ)^((121762:ℝ)/131072)=2/(2:ℝ)^((9310:ℝ)/131072) := by
    rw [_root_.eq_div_iff (by positivity),←Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (9310/131072) (by norm_num)
  have hn : product≤1+0.6931471803*(9310/131072)+(0.6931471803*(9310/131072))^2/2 := by
    norm_num [product,b0,b1,b2,b3,b4]
  rw [hsplit,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  nlinarith
theorem keygen : (213+27+14+2)*4096=1048576 := by decide
theorem signature_size : 5728-7*16=5616 := by decide
end SigGolfResearch.NonbinaryTop
#print axioms SigGolfResearch.NonbinaryTop.geometric0
#print axioms SigGolfResearch.NonbinaryTop.geometric1
#print axioms SigGolfResearch.NonbinaryTop.geometric2
#print axioms SigGolfResearch.NonbinaryTop.geometric3
#print axioms SigGolfResearch.NonbinaryTop.geometric4
#print axioms SigGolfResearch.NonbinaryTop.top_floor
#print axioms SigGolfResearch.NonbinaryTop.signing_envelope
#print axioms SigGolfResearch.NonbinaryTop.keygen
#print axioms SigGolfResearch.NonbinaryTop.signature_size
