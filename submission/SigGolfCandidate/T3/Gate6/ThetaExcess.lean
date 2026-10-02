import SigGolfCandidate.T3.Gate6.BPORSPrefix

/-!
# Stream CC: the BPORS excess above `theta = 15 / 16`

`E_{W uniform, |W| = proposalLength}[(fullPrice W − 15 / 16)_+] ≤ 18400/10^8`, from SEC's mean bound
(`fullPrice_mean_bound`, ≤ 5 / 8) and second-moment bound (`fullPrice_secondMoment_bound`, variance ≤ 2·18400/10^8):
pointwise `2(v − 15 / 16)_+ + 2mv ≤ v² + m²` for `m ≤ 5 / 8` (since `4(15 / 16 − m) ≥ 2`), hence `2·E ≤ 2e`.
The threshold `15 / 16 < 1` leaves `1 / 8` of each digest unit for the cache-reuse exception (rate `p0 ≤ 1/16`).
-/

namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 5 / 8) :
    1 * (value - 15 / 16) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 5 / 8 := by
    have h := (ENNReal.toReal_le_toReal hm (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ value.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 15 / 16
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 15 / 16 ≤ value := le_of_not_ge hsmall
    have hlr : 15 / 16 ≤ value.toReal := by
      have h := (ENNReal.toReal_le_toReal (by finiteness) hvalue).mpr hlarge
      simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 2 * (15 / 16 - mean.toReal)),
      mul_nonneg (sub_nonneg.mpr hlr) (show (0 : ℝ) ≤ 4 * (15 / 16 - mean.toReal) - 1 by linarith)]

/-- **The excess above `15 / 16`** of the complete uniform proposal word. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - (15 / 16)) ≤
      18400 / 100000000 := by
  let mean := uniformWordAverage BPORS.Numeric.proposalLength BPORS.History.fullPrice
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) BPORS.History.fullPrice_mean_bound
  have hquarter : mean ≤ 5 / 8 := BPORS.History.fullPrice_mean_bound.trans (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div])
  have h := SphincsSecurity.Concrete.uniformWordAverage_mono BPORS.Numeric.proposalLength (fun word =>
    theta_excess_le_square (BPORS.History.fullPrice word) mean (BPORS.History.fullPrice_ne_top word) hquarter)
  rw [SphincsSecurity.Concrete.uniformWordAverage_add, SphincsSecurity.Concrete.uniformWordAverage_add,
    SphincsSecurity.Concrete.uniformWordAverage_mul_left, SphincsSecurity.Concrete.uniformWordAverage_mul_left,
    BPORS.History.uniformWordAverage_constant] at h
  have hcancel : (1 : ENNReal) *
      uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - (15 / 16)) ≤
      1 * (18400 / 100000000) := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (1 : ENNReal) *
            uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - 15 / 16) +
          2 * mean * uniformWordAverage BPORS.Numeric.proposalLength BPORS.History.fullPrice := by
        change _ = _ + 2 * mean * mean
        ring
      _ ≤ uniformWordAverage BPORS.Numeric.proposalLength (fun word => BPORS.History.fullPrice word ^ 2) +
          mean ^ 2 := h
      _ ≤ (mean ^ 2 + 1 * (18400 / 100000000)) + mean ^ 2 :=
        add_le_add BPORS.History.fullPrice_secondMoment_bound le_rfl
      _ = _ := by ring
  have hhalf : (1 / 1 : ENNReal) * (1) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1 / 1 : ENNReal) * ((1) *
        uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - (15 / 16))) := by
      rw [← mul_assoc, hhalf, one_mul]
    _ ≤ (1 / 1 : ENNReal) * (1 * (18400 / 100000000)) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

end SigGolfCandidate.T3.BPORS.History

#print axioms SigGolfCandidate.T3.BPORS.History.theta_excess_le_square
#print axioms SigGolfCandidate.T3.BPORS.History.excess_three_quarters
