import SigGolfCandidate.ClaudeWCT.Numerics.WCTEnvelope
import SigGolfCandidate.ClaudeWCT.Numerics.PoissonReflect
import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
import SigGolfCandidate.T3.Gate6.ExcessSquare

namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Kernel ClaudeWCT.Numerics.WCTEnvelope ClaudeWCT.Numerics.PoissonReflect
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage uniformWordAverage_mono
  uniformWordAverage_mul_left uniformWordAverage_sum uniformWordAverage_add)
open SigGolfCandidate.T3.BPORS.History (atIndex uniformWordAverage_constant)
open ClaudeWCT.Bank.WCT (WProposal price ExcessBound wctSpec')
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem mean_summand_le_one (r : ℕ) :
    ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) ≤ 1 :=
  (wctEnv_moment r).symm.le.trans (wctEnv_moment_le_one r)
section Window
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem wct_price_mean_bound_tight_window : uniformWordAverage T price ≤ 1 / 8 := by
  rw [price_mean]
  have h := mean_tight_bound_W (fun r => ((xNum r ^ 9 : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal))
    hT1 hT2 (fun r _ => (meanPay_eq r).ge) (fun r _ => mean_summand_le_one r)
  calc
    _ ≤ (5 / 4 : ENNReal) * (1 / 10) := mul_le_mul' le_rfl h
    _ = 1 / 8 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
theorem wct_price_mean_bound_window : uniformWordAverage T price ≤ 37 / 64 := by
  refine (wct_price_mean_bound_tight_window hT1 hT2).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
theorem wct_price_second_bound_window :
    uniformWordAverage T (fun W => price W ^ 2) ≤ uniformWordAverage T price ^ 2 + 28750 / 100000000 := by
  refine (price_secondMoment_le T).trans (add_le_add le_rfl ?_)
  have h := diag_bound_W (fun r => ((yNum r ^ 9 : ℕ) : ENNReal) / (((Kc * Nn ^ 2) ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal))
    hT1 hT2 (fun r _ => (diagPay_eq r).ge)
    (fun r _ => (wctEnv_sq_moment r).symm.le.trans (wctEnv_sq_moment_le_one r))
  calc
    _ ≤ (25 / 16 : ENNReal) * (18400 / 100000000) := mul_le_mul' le_rfl h
    _ = 28750 / 100000000 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
end Window
theorem price_ne_top (W : List WProposal) : price W ≠ ⊤ := by
  rw [price_eq]
  exact ENNReal.mul_ne_top (by finiteness)
    (ENNReal.sum_ne_top.mpr fun index _ => ne_top_of_le_ne_top ENNReal.one_ne_top (wctEnv_le_one _))
theorem theta_eq : SigGolfCandidate.T3.Security.CaseC.theta = 63 / 64 := rfl
theorem theta_excess_le_square (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 37 / 64) :
    (13 / 8) * (value - 63 / 64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 :=
  SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean
theorem theta_excess_le_square_relaxed (value mean : ENNReal) (hvalue : value ≠ ⊤) (hmean : mean ≤ 1 / 8) :
    (55 / 16) * (value - 63 / 64) + 2 * mean * value ≤ value ^ 2 + mean ^ 2 := by
  have hmf : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have hmr : mean.toReal ≤ 1 / 8 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hmean
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hm0 : 0 ≤ mean.toReal := ENNReal.toReal_nonneg
  by_cases hsmall : value ≤ 63 / 64
  · rw [tsub_eq_zero_of_le hsmall, mul_zero, zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add,
      ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal)]
  · have hlarge : 63 / 64 ≤ value := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hvalue, ENNReal.toReal_div, ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (value.toReal - mean.toReal - 55 / 32)]
section Window2
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem wct_price_excess_of_pointwise (threshold : ENNReal)
    (hpointwise : ∀ value mean : ENNReal, value ≠ ⊤ → mean ≤ 1 / 8 →
      (55 / 16) * (value - threshold) + 2 * mean * value ≤ value ^ 2 + mean ^ 2) :
    uniformWordAverage T (fun word => price word - threshold) ≤ 11324 / 100000000 := by
  have hmean := wct_price_mean_bound_tight_window hT1 hT2
  have hsecond := wct_price_second_bound_window hT1 hT2
  let mean := uniformWordAverage T price
  have hm : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
  have h := uniformWordAverage_mono T (fun word : List WProposal =>
    hpointwise (price word) mean (price_ne_top word) hmean)
  rw [uniformWordAverage_add, uniformWordAverage_add, uniformWordAverage_mul_left,
    uniformWordAverage_mul_left, uniformWordAverage_constant] at h
  have hcancel : (55 / 16 : ENNReal) * uniformWordAverage T (fun word => price word - threshold) ≤
      28750 / 100000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (by finiteness)
    calc
      _ = (55 / 16 : ENNReal) * uniformWordAverage T (fun word => price word - threshold) +
          2 * mean * uniformWordAverage T price := by
        change _ = _ + 2 * mean * mean
        ring
      _ ≤ uniformWordAverage T (fun word => price word ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 28750 / 100000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (16 / 55 : ENNReal) * (55 / 16) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (16 / 55 : ENNReal) * ((55 / 16) * uniformWordAverage T (fun word => price word - threshold)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (16 / 55 : ENNReal) * (28750 / 100000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
theorem wct_price_excess_bound_window :
    uniformWordAverage T (fun W => price W - 63 / 64) ≤ 11324 / 100000000 :=
  wct_price_excess_of_pointwise hT1 hT2 (63 / 64) theta_excess_le_square_relaxed
end Window2
abbrev wctHorizon : ℕ := SigGolfCandidate.T3.BPORS.Numeric.proposalLength
theorem wctHorizon_eq : wctHorizon = 2 ^ 32 + 2 ^ 23 := by
  unfold wctHorizon SigGolfCandidate.T3.BPORS.Numeric.proposalLength
  norm_num
theorem wctHorizon_ge : 2 ^ 32 ≤ wctHorizon := by rw [wctHorizon_eq]; omega
theorem wctHorizon_le : wctHorizon ≤ 2 ^ 32 + 2 ^ 23 := wctHorizon_eq.le
section Fibre
theorem wct_price_mean_bound : uniformWordAverage wctHorizon price ≤ 37 / 64 :=
  wct_price_mean_bound_window wctHorizon_ge wctHorizon_le
theorem wct_price_mean_bound_tight : uniformWordAverage wctHorizon price ≤ 1 / 8 :=
  wct_price_mean_bound_tight_window wctHorizon_ge wctHorizon_le
theorem wct_price_second_bound :
    uniformWordAverage wctHorizon (fun W => price W ^ 2) ≤ uniformWordAverage wctHorizon price ^ 2 + 28750 / 100000000 :=
  wct_price_second_bound_window wctHorizon_ge wctHorizon_le
theorem wct_price_excess_bound :
    uniformWordAverage wctHorizon (fun W => price W - 63 / 64) ≤ 11324 / 100000000 :=
  wct_price_excess_bound_window wctHorizon_ge wctHorizon_le
theorem wct_excessBound_window {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23) :
    ExcessBound T (11324 / 100000000) := by
  unfold ExcessBound
  rw [theta_eq]
  exact wct_price_excess_bound_window hT1 hT2
theorem wct_excessBound_forall :
    ∀ T : ℕ, 2 ^ 32 ≤ T → T ≤ 2 ^ 32 + 2 ^ 23 → ExcessBound T (11324 / 100000000) :=
  fun _ h1 h2 => wct_excessBound_window h1 h2
theorem wct_excessBound : ExcessBound wctHorizon (11324 / 100000000) :=
  wct_excessBound_window wctHorizon_ge wctHorizon_le
theorem wct_excessBound_2_32 : ExcessBound (2 ^ 32) (11324 / 100000000) :=
  wct_excessBound_window le_rfl (by norm_num)
theorem wct_price_mean_bound_2_32 : uniformWordAverage (2 ^ 32) price ≤ 37 / 64 :=
  wct_price_mean_bound_window le_rfl (by norm_num)
theorem wct_price_mean_bound_tight_2_32 : uniformWordAverage (2 ^ 32) price ≤ 1 / 8 :=
  wct_price_mean_bound_tight_window le_rfl (by norm_num)
theorem wct_price_second_bound_2_32 :
    uniformWordAverage (2 ^ 32) (fun W => price W ^ 2) ≤
      uniformWordAverage (2 ^ 32) price ^ 2 + 28750 / 100000000 :=
  wct_price_second_bound_window le_rfl (by norm_num)
theorem wct_price_excess_bound_2_32 :
    uniformWordAverage (2 ^ 32) (fun W => price W - 63 / 64) ≤ 11324 / 100000000 :=
  wct_price_excess_bound_window le_rfl (by norm_num)
end Fibre
noncomputable def wctSpecFinal : ClaudeWCT.Bank.FtsBankSpec WProposal :=
  wctSpec' wctHorizon (11324 / 100000000) (wct_excessBound)
theorem wctSpecFinal_horizon : (wctSpecFinal).horizon = wctHorizon := rfl
theorem wctSpecFinal_excessRate :
    (wctSpecFinal).excessRate = 11324 / 100000000 := rfl
theorem wctSpecFinal_price : (wctSpecFinal).price = price := rfl
noncomputable def wctSpecFinal32 : ClaudeWCT.Bank.FtsBankSpec WProposal :=
  wctSpec' (2 ^ 32) (11324 / 100000000) (wct_excessBound_2_32)
theorem wctSpecFinal32_horizon : (wctSpecFinal32).horizon = 2 ^ 32 := rfl
theorem wctSpecFinal32_excessRate :
    (wctSpecFinal32).excessRate = 11324 / 100000000 := rfl
theorem wctSpecFinal32_price : (wctSpecFinal32).price = price := rfl
end ClaudeWCT.Numerics.WCTPrice
