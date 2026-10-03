import Mathlib

namespace SigGolfResearch.Gate6.Excess
open ENNReal
theorem theta_excess_le_square (v m : ENNReal) (hv : v ≠ ⊤) (hm : m ≤ 37/64) :
    (13/8)*(v-63/64)+2*m*v ≤ v^2+m^2 := by
  have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hm
  have hmr : m.toReal ≤ 37/64 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hm
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h
  by_cases hsmall : v ≤ 63/64
  · rw [tsub_eq_zero_of_le hsmall,mul_zero,zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_add,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal)]
  · have hlarge : 63/64 ≤ v := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hv,ENNReal.toReal_div,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal-13/16)]
end SigGolfResearch.Gate6.Excess
