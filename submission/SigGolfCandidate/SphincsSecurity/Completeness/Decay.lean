import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# A search that beats its own odds

The signer's searches are long: `2 ^ 20` randomizer trials accepted with probability at least `2 ^ -10`
each, and `2 ^ 20` counter trials accepted with probability at least `1/2397` each.
What that buys is stated here, in the elementary form the bound needs. A trial rejected with
probability at most `1 - 1/m` leaves at most `1/2` after `m` trials, because `(1-a)(1+a) ≤ 1` caps
the product while Bernoulli's inequality puts `(1+a)^m` above `1 + m a = 2`.

Repeating the halving is what turns a per-trial edge into the exponentially small failure the
specification's `2 ^ -256` needs.
-/

namespace SphincsSecurity.Completeness

/-- `m` trials, each rejected with probability at most `1 - 1/m`, all reject with probability at most `1/2`. -/
theorem pow_le_half (m : Nat) (hm : 0 < m) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 - (m : ℝ)⁻¹) :
    x ^ m ≤ 1 / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ha0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have ha1 : (m : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast hm
  set a := (m : ℝ)⁻¹ with hadef
  have hmono : x ^ m ≤ (1 - a) ^ m := by
    apply pow_le_pow_left₀ hx0 hx
  refine le_trans hmono ?_
  set X := (1 - a) ^ m with hXdef
  set Y := (1 + a) ^ m with hYdef
  have hnonneg : (0 : ℝ) ≤ X := by
    rw [hXdef]
    apply pow_nonneg
    linarith
  have hprod : X * Y ≤ 1 := by
    rw [hXdef, hYdef, ← mul_pow]
    have hle : (1 - a) * (1 + a) ≤ 1 := by nlinarith
    have hnn : (0 : ℝ) ≤ (1 - a) * (1 + a) := by nlinarith
    exact pow_le_one₀ hnn hle
  have h2 : (2 : ℝ) ≤ Y := by
    have hbern : 1 + (m : ℝ) * a ≤ (1 + a) ^ m := one_add_mul_le_pow (by linarith) m
    have hma : (m : ℝ) * a = 1 := by
      rw [hadef]
      field_simp
    rw [hma] at hbern
    rw [hYdef]
    linarith
  have hstep : X * 2 ≤ X * Y := mul_le_mul_of_nonneg_left h2 hnonneg
  have hhalf : X * 2 ≤ 1 := le_trans hstep hprod
  linarith

/-- The same statement for probabilities: a rejection share with room for `1/m` leaves at most `1/2` after `m` trials. -/
theorem pow_le_half_ennreal (m : Nat) (hm : 0 < m) (x : ENNReal)
    (hx : x + (m : ENNReal)⁻¹ ≤ 1) : x ^ m ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hminv : (m : ENNReal)⁻¹ ≠ ⊤ := by
    simpa using (Nat.pos_iff_ne_zero.mp hm)
  have hreal : x.toReal ≤ 1 - (m : ℝ)⁻¹ := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop hminv, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_one] at h
    linarith
  have hhalf := pow_le_half m hm x.toReal ENNReal.toReal_nonneg hreal
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc ENNReal.ofReal (x.toReal ^ m) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hhalf
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-- A sharper block length for the rarer 118-node frontier. -/
theorem pow_le_half_2143_1500 (x : ENNReal)
    (hx : x + (2143 : ENNReal)⁻¹ ≤ 1) : x ^ 1500 ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (2142 : ℝ) / 2143 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  have hrat : ((2142 : ℝ) / 2143) ^ 1500 ≤ 1 / 2 := by
    have hnat : 100 * (2142 : Nat) ^ 250 ≤ 89 * (2143 : Nat) ^ 250 := by decide
    have hreal : (100 : ℝ) * (2142 : ℝ) ^ 250 ≤ 89 * (2143 : ℝ) ^ 250 := by
      exact_mod_cast hnat
    have hblock : ((2142 : ℝ) / 2143) ^ 250 ≤ 89 / 100 := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    calc
      _ = (((2142 : ℝ) / 2143) ^ 250) ^ 6 := by rw [← pow_mul]
      _ ≤ ((89 : ℝ) / 100) ^ 6 := pow_le_pow_left₀ (by positivity) hblock 6
      _ ≤ 1 / 2 := by norm_num
  have hpow : x.toReal ^ 1500 ≤ 1 / 2 :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 1500).trans hrat
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc
    ENNReal.ofReal (x.toReal ^ 1500) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hpow
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

set_option exponentiation.threshold 512 in
/-- A sharper counter block: 1680 trials halve rejection with acceptance at least 1/2397. -/
theorem pow_le_half_2397_1680 (x : ENNReal)
    (hx : x + (2397 : ENNReal)⁻¹ ≤ 1) : x ^ 1680 ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (2396 : ℝ) / 2397 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  have hrat : ((2396 : ℝ) / 2397) ^ 1680 ≤ 1 / 2 := by
    have hnat : 100 * (2396 : Nat) ^ 280 ≤ 89 * (2397 : Nat) ^ 280 := by decide
    have hreal : (100 : ℝ) * (2396 : ℝ) ^ 280 ≤ 89 * (2397 : ℝ) ^ 280 := by
      exact_mod_cast hnat
    have hblock : ((2396 : ℝ) / 2397) ^ 280 ≤ 89 / 100 := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    calc
      _ = (((2396 : ℝ) / 2397) ^ 280) ^ 6 := by rw [← pow_mul]
      _ ≤ ((89 : ℝ) / 100) ^ 6 := pow_le_pow_left₀ (by positivity) hblock 6
      _ ≤ 1 / 2 := by norm_num
  have hpow : x.toReal ^ 1680 ≤ 1 / 2 :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 1680).trans hrat
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc
    ENNReal.ofReal (x.toReal ^ 1680) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hpow
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

set_option exponentiation.threshold 512 in
/-- A sharper counter block: 1980 trials halve rejection with acceptance at least 1/2822. -/
theorem pow_le_half_2822_1980 (x : ENNReal)
    (hx : x + (2822 : ENNReal)⁻¹ ≤ 1) : x ^ 1980 ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (2821 : ℝ) / 2822 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  have hrat : ((2821 : ℝ) / 2822) ^ 1980 ≤ 1 / 2 := by
    have hnat : 100 * (2821 : Nat) ^ 330 ≤ 89 * (2822 : Nat) ^ 330 := by decide
    have hreal : (100 : ℝ) * (2821 : ℝ) ^ 330 ≤ 89 * (2822 : ℝ) ^ 330 := by
      exact_mod_cast hnat
    have hblock : ((2821 : ℝ) / 2822) ^ 330 ≤ 89 / 100 := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    calc
      _ = (((2821 : ℝ) / 2822) ^ 330) ^ 6 := by rw [← pow_mul]
      _ ≤ ((89 : ℝ) / 100) ^ 6 := pow_le_pow_left₀ (by positivity) hblock 6
      _ ≤ 1 / 2 := by norm_num
  have hpow : x.toReal ^ 1980 ≤ 1 / 2 :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 1980).trans hrat
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc
    ENNReal.ofReal (x.toReal ^ 1980) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hpow
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

set_option exponentiation.threshold 512 in
/-- A sharper counter block: 1434 trials halve rejection with acceptance at least 1/2046. -/
theorem pow_le_half_2046_1434 (x : ENNReal)
    (hx : x + (2046 : ENNReal)⁻¹ ≤ 1) : x ^ 1434 ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hreal : x.toReal ≤ (2045 : ℝ) / 2046 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop (by simp), ENNReal.toReal_inv,
      ENNReal.toReal_ofNat, ENNReal.toReal_one] at h
    norm_num at h ⊢
    linarith
  have hrat : ((2045 : ℝ) / 2046) ^ 1434 ≤ 1 / 2 := by
    have hnat : 100 * (2045 : Nat) ^ 239 ≤ 89 * (2046 : Nat) ^ 239 := by decide
    have hreal : (100 : ℝ) * (2045 : ℝ) ^ 239 ≤ 89 * (2046 : ℝ) ^ 239 := by
      exact_mod_cast hnat
    have hblock : ((2045 : ℝ) / 2046) ^ 239 ≤ 89 / 100 := by
      rw [div_pow]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    calc
      _ = (((2045 : ℝ) / 2046) ^ 239) ^ 6 := by rw [← pow_mul]
      _ ≤ ((89 : ℝ) / 100) ^ 6 := pow_le_pow_left₀ (by positivity) hblock 6
      _ ≤ 1 / 2 := by norm_num
  have hpow : x.toReal ^ 1434 ≤ 1 / 2 :=
    (pow_le_pow_left₀ ENNReal.toReal_nonneg hreal 1434).trans hrat
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc
    ENNReal.ofReal (x.toReal ^ 1434) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hpow
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-! ## The closing numbers

Every quantity below is a power of `2⁻¹`, so the comparisons are monotonicity in the exponent and the
identity `2⁻¹ + 2⁻¹ = 1`, never an evaluation of `2 ^ (2 ^ 21)`. -/

theorem inv_two_pow_succ_add (k : Nat) :
    (2⁻¹ : ENNReal) ^ (k + 1) + (2⁻¹ : ENNReal) ^ (k + 1) = (2⁻¹ : ENNReal) ^ k := by
  rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

theorem inv_two_pow_anti {j k : Nat} (h : j ≤ k) :
    (2⁻¹ : ENNReal) ^ k ≤ (2⁻¹ : ENNReal) ^ j :=
  pow_le_pow_right_of_le_one' (by norm_num) h

theorem two_pow_div_two_pow (j k : Nat) :
    (2 : ENNReal) ^ j / (2 : ENNReal) ^ (j + k) = (2⁻¹ : ENNReal) ^ k := by
  rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    mul_comm ((2 : ENNReal) ^ j)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one,
    ENNReal.inv_pow]

/-- `1/2143 + 1/(2142 * 2143) = 1/2142`. -/
theorem inv_2143_add : (2143 : ENNReal)⁻¹ + (4590306 : ENNReal)⁻¹ = (2142 : ENNReal)⁻¹ := by
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- The collision share is smaller than the gap between `1/2142` and `1/2143`. -/
theorem digest_room (x : ENNReal) (hx : x + (2142 : ENNReal)⁻¹ ≤ 1) :
    x + (2 : ENNReal) ^ 20 / (2 : ENNReal) ^ 128 + ((2143 : Nat) : ENNReal)⁻¹ ≤ 1 := by
  have hcoll : (2 : ENNReal) ^ 20 / (2 : ENNReal) ^ 128 = (2⁻¹ : ENNReal) ^ 108 := by
    rw [show (128 : Nat) = 20 + 108 from rfl, two_pow_div_two_pow]
  have hsmall : (2⁻¹ : ENNReal) ^ 108 ≤ (4590306 : ENNReal)⁻¹ := by
    rw [← ENNReal.inv_pow]
    refine ENNReal.inv_le_inv.mpr ?_
    calc (4590306 : ENNReal) ≤ ((2 ^ 108 : Nat) : ENNReal) := by exact_mod_cast (by norm_num)
      _ = 2 ^ 108 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  calc x + (2 : ENNReal) ^ 20 / (2 : ENNReal) ^ 128 + ((2143 : Nat) : ENNReal)⁻¹
      ≤ x + ((4590306 : ENNReal)⁻¹ + (2143 : ENNReal)⁻¹) := by
        rw [hcoll, Nat.cast_ofNat, add_assoc]
        exact add_le_add le_rfl (add_le_add hsmall le_rfl)
    _ = x + (2142 : ENNReal)⁻¹ := by rw [add_comm (4590306 : ENNReal)⁻¹, inv_2143_add]
    _ ≤ 1 := hx

/-- After a union bound over all `2²⁵⁶` messages, the digest search (`2⁻⁶⁹⁹`) and the five counter
searches (`2⁻⁵²⁹` each) stay below `2⁻²⁵⁶`. -/
theorem closing_sum :
    (2 : ENNReal) ^ 256 *
      ((2⁻¹ : ENNReal) ^ 699 + 5 * (2⁻¹ : ENNReal) ^ 529)
      ≤ ((2 ^ 256 : Nat) : ENNReal)⁻¹ := by
  have hcast : ((2 ^ 256 : Nat) : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 256 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  have ha : (2⁻¹ : ENNReal) ^ 699 ≤ (2⁻¹ : ENNReal) ^ 513 := inv_two_pow_anti (by norm_num)
  have hb : 5 * (2⁻¹ : ENNReal) ^ 529 ≤ (2⁻¹ : ENNReal) ^ 513 := by
    have hy : (2⁻¹ : ENNReal) ^ 529 ≤ (2⁻¹ : ENNReal) ^ 516 := inv_two_pow_anti (by norm_num)
    have h1 := inv_two_pow_succ_add 515
    have h2 := inv_two_pow_succ_add 514
    have h3 := inv_two_pow_succ_add 513
    calc 5 * (2⁻¹ : ENNReal) ^ 529 ≤ 8 * (2⁻¹ : ENNReal) ^ 516 :=
          mul_le_mul' (by norm_num) hy
      _ = (((2⁻¹ : ENNReal) ^ 516 + (2⁻¹ : ENNReal) ^ 516)
            + ((2⁻¹ : ENNReal) ^ 516 + (2⁻¹ : ENNReal) ^ 516))
          + (((2⁻¹ : ENNReal) ^ 516 + (2⁻¹ : ENNReal) ^ 516)
            + ((2⁻¹ : ENNReal) ^ 516 + (2⁻¹ : ENNReal) ^ 516)) := by ring
      _ = (2⁻¹ : ENNReal) ^ 513 := by rw [h1, h2, h3]
  have hsum : (2⁻¹ : ENNReal) ^ 699 + 5 * (2⁻¹ : ENNReal) ^ 529 ≤ (2⁻¹ : ENNReal) ^ 512 :=
    (add_le_add ha hb).trans_eq (inv_two_pow_succ_add 512)
  rw [hcast]
  calc
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 699 + 5 * (2⁻¹ : ENNReal) ^ 529)
        ≤ (2 : ENNReal) ^ 256 * (2⁻¹ : ENNReal) ^ 512 := mul_le_mul_right hsum _
    _ = (2⁻¹ : ENNReal) ^ 256 := by
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (512 : Nat) = 256 + 256 by norm_num, two_pow_div_two_pow]

/-- Low-target counter cap used by the partial twelve-byte serializer. -/
theorem counter_cap_low_pow (x : ENNReal) (hx : x + (2046 : ENNReal)⁻¹ ≤ 1) :
    x ^ 557056 ≤ (2⁻¹ : ENNReal) ^ 388 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  calc x ^ 557056 ≤ x ^ (1434 * 388) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 1434) ^ 388 := by rw [← pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 388 :=
      pow_le_pow_left₀ (by positivity) (pow_le_half_2046_1434 x hx) _

/-- High-target counter cap used by the partial twelve-byte serializer. -/
theorem counter_cap_high_pow (x : ENNReal) (hx : x + (2822 : ENNReal)⁻¹ ≤ 1) :
    x ^ 786432 ≤ (2⁻¹ : ENNReal) ^ 397 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  calc x ^ 786432 ≤ x ^ (1980 * 397) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 1980) ^ 397 := by rw [← pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 397 :=
      pow_le_pow_left₀ (by positivity) (pow_le_half_2822_1980 x hx) _

/-- The cap-abort experiment's numerical union bound over all messages.
This lemma does not replace the stronger existing completeness theorem: the partial
serializer must separately prove that these are its actual failure probabilities. -/
theorem closing_sum_caps :
    (2 : ENNReal) ^ 256 *
      ((2⁻¹ : ENNReal) ^ 699 + 4 * (2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 397)
      ≤ ((2 ^ 128 : Nat) : ENNReal)⁻¹ := by
  have ha : (2⁻¹ : ENNReal) ^ 699 ≤ (2⁻¹ : ENNReal) ^ 388 := inv_two_pow_anti (by decide)
  have hb : (2⁻¹ : ENNReal) ^ 397 ≤ (2⁻¹ : ENNReal) ^ 388 := inv_two_pow_anti (by decide)
  have hsum : (2⁻¹ : ENNReal) ^ 699 + 4 * (2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 397
      ≤ (2⁻¹ : ENNReal) ^ 384 := by
    have h1 := inv_two_pow_succ_add 387
    have h2 := inv_two_pow_succ_add 386
    have h3 := inv_two_pow_succ_add 385
    calc
      _ ≤ (2⁻¹ : ENNReal) ^ 388 + 4 * (2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388 :=
        add_le_add (add_le_add ha le_rfl) hb
      _ = 6 * (2⁻¹ : ENNReal) ^ 388 := by ring
      _ ≤ 8 * (2⁻¹ : ENNReal) ^ 388 := mul_le_mul' (by norm_num) le_rfl
      _ = (((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)
            + ((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388))
          + (((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)
            + ((2⁻¹ : ENNReal) ^ 388 + (2⁻¹ : ENNReal) ^ 388)) := by ring
      _ = (2⁻¹ : ENNReal) ^ 385 := by rw [h1, h2, h3]
      _ ≤ (2⁻¹ : ENNReal) ^ 384 := inv_two_pow_anti (by decide)
  have hcast : ((2 ^ 128 : Nat) : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 128 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  rw [hcast]
  calc
    _ ≤ (2 : ENNReal) ^ 256 * (2⁻¹ : ENNReal) ^ 384 := mul_le_mul_right hsum _
    _ = (2⁻¹ : ENNReal) ^ 128 := by
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (384 : Nat) = 256 + 128 by norm_num, two_pow_div_two_pow]

end SphincsSecurity.Completeness
