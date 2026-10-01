import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
namespace SphincsSecurity.Concrete

open ENNReal

theorem stirlingPowerMoment_ne_top (rate : ENNReal) (hrate : rate ≠ ⊤) (degree : Nat) :
    stirlingPowerMoment rate degree ≠ ⊤ := by
  unfold stirlingPowerMoment
  apply ENNReal.sum_ne_top.mpr
  intro order _
  exact ENNReal.mul_ne_top (by finiteness) (ENNReal.pow_ne_top hrate)

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_full_mean_le :
    (2 ^ 34 : ENNReal) * ((15 ^ 15 : ENNReal) / 2 ^ 116) * stirlingPowerMoment (19 / 50) 15 ≤ 1 / 2 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 15
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 20000000 in
theorem stirlingPowerMoment_full_variance_le :
    (2 ^ 34 : ENNReal) * ((15 ^ 15 : ENNReal) / 2 ^ 116) ^ 2 * stirlingPowerMoment (19 / 50) 30 ≤ 1 / 40000 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 30
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

end SphincsSecurity.Concrete

/-! Numerical prerequisites for the alternate four-layer radix-four/FORS design.
These inequalities do not transfer the production security theorem to that design.
The new forest and proposal game still need their own refinement and reduction.
-/
namespace SigGolfCandidate.Base4Candidate

open ENNReal SphincsSecurity.Concrete

set_option maxHeartbeats 10000000 in
theorem forest_mean :
    (2 ^ 33 : ENNReal) * (2 ^ 70 : ENNReal)⁻¹ *
      stirlingPowerMoment (19 / 25) 17 ≤ 1 / 10 := by
  have hm := stirlingPowerMoment_ne_top (19 / 25) (by finiteness) 17
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 40000000 in
theorem forest_variance :
    (2 ^ 33 : ENNReal) * ((2 ^ 70 : ENNReal)⁻¹) ^ 2 *
      stirlingPowerMoment (19 / 25) 34 ≤ 1 / 100000 := by
  have hm := stirlingPowerMoment_ne_top (19 / 25) (by finiteness) 34
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

set_option maxHeartbeats 10000000 in
theorem forest_near_price :
    17 * (2 ^ 28 : ENNReal)⁻¹ * stirlingPowerMoment (19 / 25) 16 ≤ 106 := by
  have hm := stirlingPowerMoment_ne_top (19 / 25) (by finiteness) 16
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

end SigGolfCandidate.Base4Candidate
