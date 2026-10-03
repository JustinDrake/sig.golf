import Mathlib

namespace SigGolfCandidate.T3M.Verify
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar7_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 63) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0x8e38e38e38e38e38 := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat ≤ 0x0e38e38e38e38e38 := by
    have hb' : b.toNat % 2 ^ 63 = b.toNat := Nat.mod_eq_of_lt hb
    have he := Nat.and_mod_two_pow (a := b.toNat) (b := (~~~M).toNat) (n := 63)
    rw [hb', Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left hb)] at he
    rw [BitVec.toNat_and, he]
    simpa [hM] using (Nat.and_le_right : b.toNat &&& ((~~~M).toNat % 2 ^ 63) ≤ (~~~M).toNat % 2 ^ 63)
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
theorem swar2_period : ∀ i : Fin 62,
    (0x3333333333333333#64).getLsbD i.val = !(0x3333333333333333#64).getLsbD (i.val + 2) := by
  decide
theorem swar2_shift (x : BitVec 64) :
    (x >>> 2) &&& 0x3333333333333333#64 = (x &&& ~~~0x3333333333333333#64) >>> 2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 62
  · have hp := swar2_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 2 + i = i + 2 by omega]
    simp [show i + 2 < 64 by omega]
  · have hx : x.getLsbD (2 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]
theorem swar2_low (x : BitVec 64) : (x &&& ~~~0x3333333333333333#64).toNat % 4 = 0 := by
  have h7 : (x &&& ~~~0x3333333333333333#64) &&& 3#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 2
    · have : (0x3333333333333333#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      simp [this]
    · have : (3#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 3 < 2 ^ 2 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (3#64).toNat = 2 ^ 2 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this
theorem swar2_eq (a b : BitVec 64) (hb : b.toNat < 2 ^ 34) :
    ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64)) +
      (((a + b) - ((a &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64))) >>> 2) =
    ((a >>> 2) &&& 0x3333333333333333#64) + (a &&& 0x3333333333333333#64) +
      ((b >>> 2) &&& 0x3333333333333333#64) + (b &&& 0x3333333333333333#64) := by
  rw [swar2_shift a, swar2_shift b]
  set M : BitVec 64 := 0x3333333333333333#64 with hM
  have la := swar2_low a
  have lb := swar2_low b
  rw [← hM] at la lb
  have loa : (a &&& ~~~M).toNat ≤ 0xcccccccccccccccc := by
    rw [BitVec.toNat_and]; simpa [hM] using (Nat.and_le_right : a.toNat &&& (~~~M).toNat ≤ (~~~M).toNat)
  have lob : (b &&& ~~~M).toNat < 2 ^ 34 := by
    rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_left hb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.sub_eq_iff_eq_add.mpr
    calc a + b = ((a &&& M) + (a &&& ~~~M)) + ((b &&& M) + (b &&& ~~~M)) := by
           rw [swar7_split a M, swar7_split b M]
         _ = ((a &&& ~~~M) + (b &&& ~~~M)) + ((a &&& M) + (b &&& M)) := by ac_rfl
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 2 = ((a &&& ~~~M) >>> 2) + ((b &&& ~~~M) >>> 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl
end SigGolfCandidate.T3M.Verify
