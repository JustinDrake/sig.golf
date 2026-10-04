import SigGolfCandidate.T3.Gate6.SourceBudget
import SigGolfCandidate.Budget.Numeric

namespace ClaudeWCT.W9.T3.BaseAudit
open SigGolfCandidate.T3.BaseAudit (zU b1 b2 b3 b4 step_1 step_2 step_3 step_4)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def p0 : ℚ := 16016 ^ 9 / 2 ^ 138
def b0 : ℚ := 10273002 / 10000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by
  norm_num [zU, p0, b0]
theorem probability_floor : 1 / 5026 ≤ p0 ∧ p0 ≤ 1 / 5025 := by
  norm_num [p0]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0]
theorem signing_envelope :
    (2 : ℝ) ^ ((118176 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hsplit : (2 : ℝ) ^ ((118176 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((12896 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (12896 / 131072) (by norm_num)
  have hn : (b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) ≤
      1 + 0.6931471803 * (12896 / 131072) + (0.6931471803 * (12896 / 131072)) ^ 2 / 2 := by
    norm_num [b0, SigGolfCandidate.T3.BaseAudit.b1, SigGolfCandidate.T3.BaseAudit.b2,
      SigGolfCandidate.T3.BaseAudit.b3, SigGolfCandidate.T3.BaseAudit.b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
def lowerCount194 : ℕ := 265682986533614028872430357565137160
def lowerCount195 : ℕ := 217433284086354415880083123326127992
def lowerCount196 : ℕ := 177063161351702039889196043868193572
def lowerCount197 : ℕ := 143468572474466315422327516384120300
def topCount126 : ℕ := 183707182173445436457863622839156476
namespace V2b
def p0 : ℚ := 5 * 16016 ^ 9 / 2 ^ 140
def b0 : ℚ := 1021721556316 / 1000000000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by norm_num [zU, p0, b0]
theorem probability_floor : 1 / 4021 ≤ p0 ∧ p0 ≤ 1 / 4020 := by norm_num [p0]
theorem p0_ge_5026 : 1 / 5026 ≤ p0 := by norm_num [p0]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0]
def p1 : ℚ := topCount126 / 2 ^ 128
def b1 : ℚ := 1009892452433 / 1000000000000
theorem step_1 : zU * ((1 - p1) * b1 + p1) ≤ b1 := by norm_num [zU, p1, b1, topCount126]
def p2 : ℚ := lowerCount197 / 2 ^ 128
def b2 : ℚ := 1012702229908 / 1000000000000
theorem step_2 : zU * ((1 - p2) * b2 + p2) ≤ b2 := by norm_num [zU, p2, b2, lowerCount197]
def p3 : ℚ := lowerCount197 / 2 ^ 128
def b3 : ℚ := 1012702229908 / 1000000000000
theorem step_3 : zU * ((1 - p3) * b3 + p3) ≤ b3 := by norm_num [zU, p3, b3, lowerCount197]
def p4 : ℚ := lowerCount196 / 2 ^ 128
def b4 : ℚ := 1010267462656 / 1000000000000
theorem step_4 : zU * ((1 - p4) * b4 + p4) ≤ b4 := by norm_num [zU, p4, b4, lowerCount196]
theorem signing_envelope :
    (2 : ℝ) ^ ((118176 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hsplit : (2 : ℝ) ^ ((118176 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((12896 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (12896 / 131072) (by norm_num)
  have hn : (b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) ≤
      1 + 0.6931471803 * (12896 / 131072) + (0.6931471803 * (12896 / 131072)) ^ 2 / 2 := by
    norm_num [b0, b1, b2, b3, b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
end V2b
namespace V2r
def p1 : ℚ := topCount126 / 2 ^ 128
def b1 : ℚ := 1009892452433 / 1000000000000
theorem step_1 : zU * ((1 - p1) * b1 + p1) ≤ b1 := by norm_num [zU, p1, b1, topCount126]
def p2 : ℚ := lowerCount196 / 2 ^ 128
def b2 : ℚ := 1010267462656 / 1000000000000
theorem step_2 : zU * ((1 - p2) * b2 + p2) ≤ b2 := by norm_num [zU, p2, b2, lowerCount196]
def p3 : ℚ := lowerCount196 / 2 ^ 128
def b3 : ℚ := 1010267462656 / 1000000000000
theorem step_3 : zU * ((1 - p3) * b3 + p3) ≤ b3 := by norm_num [zU, p3, b3, lowerCount196]
def p4 : ℚ := lowerCount196 / 2 ^ 128
def b4 : ℚ := 1010267462656 / 1000000000000
theorem step_4 : zU * ((1 - p4) * b4 + p4) ≤ b4 := by norm_num [zU, p4, b4, lowerCount196]
theorem signing_envelope :
    (2 : ℝ) ^ ((118176 : ℝ) / 131072) *
      ((ClaudeWCT.W9.T3.BaseAudit.b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hsplit : (2 : ℝ) ^ ((118176 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((12896 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (12896 / 131072) (by norm_num)
  have hn : (ClaudeWCT.W9.T3.BaseAudit.b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) ≤
      1 + 0.6931471803 * (12896 / 131072) + (0.6931471803 * (12896 / 131072)) ^ 2 / 2 := by
    norm_num [ClaudeWCT.W9.T3.BaseAudit.b0, b1, b2, b3, b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
end V2r
namespace V3
def ftsSign : ℕ := 32243
theorem ftsSign_eq : ftsSign = 9 * (128 * (4 + 21 + 2) + 126) + 5 := by norm_num [ftsSign]
def fixedSign : ℕ := 118169
theorem fixedSign_eq : fixedSign = 2 + 2 + ftsSign + 85922 := by norm_num [fixedSign, ftsSign]
theorem fixedSign_add_seven : fixedSign + 7 = 118176 := by norm_num [fixedSign]
theorem signing_envelope_le :
    (2 : ℝ) ^ ((118169 : ℝ) / 131072) *
      ((V2b.b0 : ℝ) * (V2b.b1 : ℝ) * (V2b.b2 : ℝ) * (V2b.b3 : ℝ) * (V2b.b4 : ℝ)) ≤ 19973 / 10000 := by
  have hsplit : (2 : ℝ) ^ ((118169 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((12903 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (12903 / 131072) (by norm_num)
  have hn : 2 * ((V2b.b0 : ℝ) * (V2b.b1 : ℝ) * (V2b.b2 : ℝ) * (V2b.b3 : ℝ) * (V2b.b4 : ℝ)) ≤
      19973 / 10000 *
        (1 + 0.6931471803 * (12903 / 131072) + (0.6931471803 * (12903 / 131072)) ^ 2 / 2) := by
    norm_num [V2b.b0, V2b.b1, V2b.b2, V2b.b3, V2b.b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact hn.trans (mul_le_mul_of_nonneg_left hlo (by norm_num))
theorem signing_envelope :
    (2 : ℝ) ^ ((118169 : ℝ) / 131072) *
      ((V2b.b0 : ℝ) * (V2b.b1 : ℝ) * (V2b.b2 : ℝ) * (V2b.b3 : ℝ) * (V2b.b4 : ℝ)) ≤ 2 :=
  signing_envelope_le.trans (by norm_num)
theorem completeness_union :
    (2 : ℝ) ^ 256 * (1 / 2 ^ 450) + 2 ^ 301 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 193 := by
  set_option exponentiation.threshold 2048 in norm_num
def expandFixed : ℕ := 606
theorem expandFixed_eq : expandFixed = 9 * (6 + 2 + 6) + 5 + (478 - 3) := by norm_num [expandFixed]
theorem expandFixed_le : expandFixed ≤ 622 := by norm_num [expandFixed]
end V3
end ClaudeWCT.W9.T3.BaseAudit
