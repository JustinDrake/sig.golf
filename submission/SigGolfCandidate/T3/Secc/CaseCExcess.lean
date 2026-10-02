import SigGolfCandidate.T3.Secc.CaseCForecast

/-!
# Stream CC: the BPORS excess above `theta = 3/4`

`E_{W uniform, |W| = proposalLength}[(fullPrice W − 3/4)_+] ≤ 987/10^8`, from SEC's mean bound
(`fullPrice_mean_bound`, ≤ 0.119) and second-moment bound (`fullPrice_secondMoment_bound`, variance ≤ 2·987/10^8):
pointwise `(5/2)(v − 3/4)_+ + 2mv ≤ v² + m²` for `m ≤ 1/8` (since `4(3/4 − m) ≥ 5/2`), hence `(5/2)·E ≤ 2e`.
The threshold `3/4 < 1` leaves `1/4` of each digest unit for the cache-reuse exception (rate `p0 ≤ 1/16`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 1 / 8) :
    5 / 2 * (value - 3 / 4) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 1 / 8 := by
    have h := (ENNReal.toReal_le_toReal hm (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ value.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 3 / 4
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 3 / 4 ≤ value := le_of_not_ge hsmall
    have hlr : 3 / 4 ≤ value.toReal := by
      have h := (ENNReal.toReal_le_toReal (by finiteness) hvalue).mpr hlarge
      simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 2 * (3 / 4 - mean.toReal)),
      mul_nonneg (sub_nonneg.mpr hlr) (show (0 : ℝ) ≤ 4 * (3 / 4 - mean.toReal) - 5 / 2 by linarith)]

/-- **The excess above `3/4`** of the complete uniform proposal word. -/
theorem excess_three_quarters :
    uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      987 / 100000000 := by
  let mean := uniformWordAverage BPORS.Numeric.proposalLength BPORS.History.fullPrice
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) BPORS.History.fullPrice_mean_bound
  have heighth : mean ≤ 1 / 8 := BPORS.History.fullPrice_mean_bound.trans (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div])
  have h := SphincsSecurity.Concrete.uniformWordAverage_mono BPORS.Numeric.proposalLength (fun word =>
    theta_excess_le_square (BPORS.History.fullPrice word) mean (BPORS.History.fullPrice_ne_top word) heighth)
  rw [SphincsSecurity.Concrete.uniformWordAverage_add, SphincsSecurity.Concrete.uniformWordAverage_add,
    SphincsSecurity.Concrete.uniformWordAverage_mul_left, SphincsSecurity.Concrete.uniformWordAverage_mul_left,
    BPORS.History.uniformWordAverage_constant] at h
  have hcancel : (5 / 2 : ENNReal) *
      uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta) ≤
      2 * (987 / 100000000) := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (5 / 2 : ENNReal) *
            uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - 3 / 4) +
          2 * mean * uniformWordAverage BPORS.Numeric.proposalLength BPORS.History.fullPrice := by
        change _ = _ + 2 * mean * mean
        unfold theta
        ring
      _ ≤ uniformWordAverage BPORS.Numeric.proposalLength (fun word => BPORS.History.fullPrice word ^ 2) +
          mean ^ 2 := h
      _ ≤ (mean ^ 2 + 2 * (987 / 100000000)) + mean ^ 2 :=
        add_le_add BPORS.History.fullPrice_secondMoment_bound le_rfl
      _ = _ := by ring
  have hfive : (2 / 5 : ENNReal) * (5 / 2) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (2 / 5 : ENNReal) * ((5 / 2) *
        uniformWordAverage BPORS.Numeric.proposalLength (fun W => BPORS.History.fullPrice W - theta)) := by
      rw [← mul_assoc, hfive, one_mul]
    _ ≤ (2 / 5 : ENNReal) * (2 * (987 / 100000000)) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

end SigGolfCandidate.T3.Security.CaseC
