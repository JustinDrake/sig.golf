import Mathlib
namespace SigGolfResearch.Gate6.Excess
open ENNReal
/-- Pointwise excess at threshold `1023/1024` for a mean at most `4995/8192`
(the gate 135/1024 mean cap); `3189/2048 = 4·(1023/1024 - 4995/8192)`. -/
theorem theta_excess_le_square (v m : ENNReal) (hv : v ≠ ⊤) (hm : m ≤ 4995/8192) :
    (3189/2048)*(v-1023/1024)+2*m*v ≤ v^2+m^2 := by
  have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hm
  have hmr : m.toReal ≤ 4995/8192 := by
    have h := (ENNReal.toReal_le_toReal hmf (by finiteness)).mpr hm
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat] using h
  by_cases hsmall : v ≤ 1023/1024
  · rw [tsub_eq_zero_of_le hsmall,mul_zero,zero_add]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_add,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal)]
  · have hlarge : 1023/1024 ≤ v := le_of_not_ge hsmall
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hlarge hv,ENNReal.toReal_div,ENNReal.toReal_ofNat]
    nlinarith [sq_nonneg (v.toReal-m.toReal-3189/4096)]

end SigGolfResearch.Gate6.Excess
