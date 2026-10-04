import SigGolfCandidate.T3.Core

namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
theorem split3 (n M : Nat) : n &&& (64 * M + 7) = 64 * ((n / 64) &&& M) + n % 8 :=
  land_split n M 3 6 (by decide)
theorem split6 (n M : Nat) : n &&& (4096 * M + 63) = 4096 * ((n / 4096) &&& M) + n % 64 :=
  land_split n M 6 12 (by decide)
theorem split2 (n M : Nat) : n &&& (16 * M + 3) = 16 * ((n / 16) &&& M) + n % 4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256 * M + 15) = 256 * ((n / 256) &&& M) + n % 16 :=
  land_split n M 4 8 (by decide)
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
theorem and3 (n : Nat) : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2
def mask3 : Nat := 8198552921648689607
def mask6 : Nat := 17311559823019733055
def mask2 : Nat := 3689348814741910323
def mask4 : Nat := 1085102592571150095
theorem landM1 (n : Nat) : n &&& mask3 =
    64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 % 8) + n / 64 / 64 % 8) + n / 64 % 8) + n % 8 := by
  rw [show mask3 = 64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * 7 + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7 by
    norm_num [mask3]]
  simp only [split3, and7]
theorem landM2 (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 4096 / 4096 / 4096 / 4096 / 4096 % 16)
    + n / 4096 / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 % 64)
    + n / 4096 % 64) + n % 64 := by
  rw [show mask6 = 4096 * (4096 * (4096 * (4096 * (4096 * 15 + 63) + 63) + 63) + 63) + 63 by norm_num [mask6]]
  simp only [split6, and15]
def sw1 (a b : Nat) : Nat :=
  ((((a / 8 &&& mask3) + (a &&& mask3)) % 18446744073709551616 + (b / 8 &&& mask3)) % 18446744073709551616 +
    (b &&& mask3)) % 18446744073709551616
def lowSwar (a b : Nat) : Nat := ((sw1 a b + sw1 a b / 64) % 18446744073709551616 &&& mask6) % 4095
theorem hdiv64 (c R : Nat) (h : c < 64) : (c + 64 * R) / 64 = R := by omega
theorem hmod64 (c R : Nat) (h : c < 64) : (c + 64 * R) % 64 = c := by omega
theorem landM2' (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 16)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 / 64 / 64 / 64 / 64 % 64)
    + n / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 % 64) + n % 64 := by
  rw [landM2]; simp only [Nat.div_div_eq_div_mul]
theorem fold_mod4095 (a b c d e f : Nat) :
    (a + 4096 * (b + 4096 * (c + 4096 * (d + 4096 * (e + 4096 * f))))) % 4095 =
      (a + b + c + d + e + f) % 4095 := by
  omega
theorem swarLanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 : Nat) (h0 : L0 ≤ 28) (h1 : L1 ≤ 28) (h2 : L2 ≤ 28)
    (h3 : L3 ≤ 28) (h4 : L4 ≤ 28) (h5 : L5 ≤ 28) (h6 : L6 ≤ 28) (h7 : L7 ≤ 28) (h8 : L8 ≤ 28) (h9 : L9 ≤ 28)
    (h10 : L10 ≤ 15) (X : Nat)
    (hX : X = L0 + 64 * (L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))))) :
    ((X + X / 64) % 18446744073709551616 &&& mask6) % 4095 =
      L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 := by
  have e1 : X / 64 = L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))) := by rw [hX]; exact hdiv64 _ _ (by omega)
  have e2 : X + X / 64 = (L0 + L1) + 64 * ((L1 + L2) + 64 * ((L2 + L3) + 64 * ((L3 + L4) + 64 * ((L4 + L5) +
      64 * ((L5 + L6) + 64 * ((L6 + L7) + 64 * ((L7 + L8) + 64 * ((L8 + L9) + 64 * ((L9 + L10) +
      64 * L10))))))))) := by
    omega
  have e3 : X + X / 64 < 18446744073709551616 := by rw [e2]; omega
  have e4 : (X + X / 64) % 18446744073709551616 &&& mask6 = (L0 + L1) + 4096 * ((L2 + L3) + 4096 * ((L4 + L5) +
      4096 * ((L6 + L7) + 4096 * ((L8 + L9) + 4096 * L10)))) := by
    rw [Nat.mod_eq_of_lt e3, e2, landM2']
    simp (disch := omega) only [hdiv64, hmod64]
    rw [Nat.mod_eq_of_lt (show L10 < 16 by omega)]
    omega
  rw [e4]
  clear e1 e2 e3 e4 hX
  have hlt : L0 + L1 + (L2 + L3) + (L4 + L5) + (L6 + L7) + (L8 + L9) + L10 < 4095 := by omega
  rw [fold_mod4095, Nat.mod_eq_of_lt hlt]
  ac_rfl
def dsum21 (a : Nat) : Nat :=
  a % 8 + a / 8 % 8 + a / 64 % 8 + a / 512 % 8 + a / 4096 % 8 + a / 32768 % 8 + a / 262144 % 8 +
    a / 2097152 % 8 + a / 16777216 % 8 + a / 134217728 % 8 + a / 1073741824 % 8 +
    a / 8589934592 % 8 + a / 68719476736 % 8 + a / 549755813888 % 8 + a / 4398046511104 % 8 +
    a / 35184372088832 % 8 + a / 281474976710656 % 8 + a / 2251799813685248 % 8 +
    a / 18014398509481984 % 8 + a / 144115188075855872 % 8 + a / 1152921504606846976 % 8
theorem dsum21_eq (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 8 ^ i % 8).sum := by
  simp only [dsum21, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem lowSwar_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 63) :
    lowSwar a b = dsum21 a + a / 2 ^ 63 + dsum21 b := by
  have hat : a / 9223372036854775808 ≤ 1 := by omega
  have ha' : a / 9223372036854775808 % 8 = a / 9223372036854775808 := Nat.mod_eq_of_lt (by omega)
  have hb' : b / 9223372036854775808 = 0 := Nat.div_eq_of_lt hb
  unfold lowSwar dsum21
  generalize hX : sw1 a b = X
  unfold sw1 at hX
  simp only [landM1, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  rw [ha'] at hX
  simp only [hb', Nat.zero_mod, Nat.mul_zero] at hX
  norm_num
  clear ha'
  generalize a / 9223372036854775808 = a21 at *
  have ha0 : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a % 8 = a0 at *
  have ha1 : a / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8 % 8 = a1 at *
  have ha2 : a / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 8 = a2 at *
  have ha3 : a / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 512 % 8 = a3 at *
  have ha4 : a / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 8 = a4 at *
  have ha5 : a / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 32768 % 8 = a5 at *
  have ha6 : a / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 8 = a6 at *
  have ha7 : a / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2097152 % 8 = a7 at *
  have ha8 : a / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 8 = a8 at *
  have ha9 : a / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 134217728 % 8 = a9 at *
  have ha10 : a / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 8 = a10 at *
  have ha11 : a / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8589934592 % 8 = a11 at *
  have ha12 : a / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 8 = a12 at *
  have ha13 : a / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 549755813888 % 8 = a13 at *
  have ha14 : a / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 8 = a14 at *
  have ha15 : a / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 35184372088832 % 8 = a15 at *
  have ha16 : a / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 8 = a16 at *
  have ha17 : a / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2251799813685248 % 8 = a17 at *
  have ha18 : a / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 8 = a18 at *
  have ha19 : a / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 144115188075855872 % 8 = a19 at *
  have ha20 : a / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 8 = a20 at *
  have hb0 : b % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b % 8 = b0 at *
  have hb1 : b / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8 % 8 = b1 at *
  have hb2 : b / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 8 = b2 at *
  have hb3 : b / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 512 % 8 = b3 at *
  have hb4 : b / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 8 = b4 at *
  have hb5 : b / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 32768 % 8 = b5 at *
  have hb6 : b / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 8 = b6 at *
  have hb7 : b / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2097152 % 8 = b7 at *
  have hb8 : b / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 8 = b8 at *
  have hb9 : b / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 134217728 % 8 = b9 at *
  have hb10 : b / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 8 = b10 at *
  have hb11 : b / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8589934592 % 8 = b11 at *
  have hb12 : b / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 8 = b12 at *
  have hb13 : b / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 549755813888 % 8 = b13 at *
  have hb14 : b / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 8 = b14 at *
  have hb15 : b / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 35184372088832 % 8 = b15 at *
  have hb16 : b / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 8 = b16 at *
  have hb17 : b / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2251799813685248 % 8 = b17 at *
  have hb18 : b / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 8 = b18 at *
  have hb19 : b / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 144115188075855872 % 8 = b19 at *
  have hb20 : b / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 8 = b20 at *
  clear ha hb hb'
  rw [swarLanes (a0 + a1 + b0 + b1) (a2 + a3 + b2 + b3) (a4 + a5 + b4 + b5) (a6 + a7 + b6 + b7)
    (a8 + a9 + b8 + b9) (a10 + a11 + b10 + b11) (a12 + a13 + b12 + b13) (a14 + a15 + b14 + b15)
    (a16 + a17 + b16 + b17) (a18 + a19 + b18 + b19) (a20 + a21 + b20) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) X (by
    rw [← hX]
    clear hX
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  clear hX
  ac_rfl
theorem div_mod_add_pow (x y k m w : Nat) (h : k + w ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ w * (2 ^ (m - k - w) * y)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]
theorem div_add_pow (x y k m : Nat) (h : k ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k = x / 2 ^ k + 2 ^ (m - k) * y := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ (m - k) * y) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
theorem dig_carry (b c j : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) (hj : 0 < j) :
    (b + c) / 2 ^ (3 * j) % 8 = b / 2 ^ (3 * j) % 8 := by
  have e : (b + c) / 2 = b / 2 := by omega
  have p : 2 ^ (3 * j) = 2 * 2 ^ (3 * j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [p, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]
theorem dig_carry0 (b c : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) : (b + c) % 8 = b % 8 + c := by omega
theorem sum_range_add (f : Nat → Nat) (m n : Nat) :
    ((List.range (m + n)).map f).sum = ((List.range m).map f).sum + ((List.range n).map fun j => f (m + j)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl
theorem sum_range_succ' (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map fun j => f (j + 1)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl
theorem sum_congr_range (f g : Nat → Nat) (n : Nat) (h : ∀ i < n, f i = g i) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)
theorem dsum21_pow (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 2 ^ (3 * i) % 2 ^ 3).sum := by
  rw [dsum21_eq]
  apply sum_congr_range
  intro i _
  rw [Nat.pow_mul]; rfl
theorem lowDigits_sum (v0 v1 : Nat) (h0 : v0 < 2 ^ 64) :
    ((List.range 42).map fun i => (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3).sum =
      dsum21 v0 + v0 / 2 ^ 63 + dsum21 (2 * v1) := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3 = v0 / 2 ^ (3 * i) % 2 ^ 3 :=
    fun i hi => div_mod_add_pow _ _ _ _ _ (by omega)
  rw [sum_congr_range _ _ 21 hlow]
  have hc : v0 / 2 ^ 63 ≤ 1 := by
    have : v0 / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by rw [show 2 ^ 63 * 2 = 2 ^ 64 by norm_num]; exact h0)
    omega
  have hW : ∀ j, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * (21 + j)) % 2 ^ 3 = (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8 := by
    intro j
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (by omega)]
    norm_num
    rw [Nat.add_comm]
  simp only [hW]
  have e1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
      v0 / 2 ^ 63 + ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum := by
    have s1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
        (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * 0) % 8 +
          ((List.range 20).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8).sum :=
      sum_range_succ' (fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8) 20
    have s2 : ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum =
        2 * v1 / 2 ^ (3 * 0) % 2 ^ 3 + ((List.range 20).map fun j => 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3).sum :=
      sum_range_succ' (fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3) 20
    have hj : ∀ j < 20, (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8 = 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3 :=
      fun j _ => dig_carry _ _ _ (by omega) hc (by omega)
    rw [s1, s2, sum_congr_range _ _ 20 hj]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [dig_carry0 _ _ (by omega) hc]
    norm_num
    omega
  rw [e1]
  omega
theorem landM4 (n : Nat) : n &&& mask2 =
    16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 % 4) + n / 16 / 16 % 4) + n / 16 % 4) + n % 4 := by
  rw [show mask2 = 16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3 by norm_num [mask2]]
  simp only [split2, and3]
theorem landM8' (n : Nat) : n &&& mask4 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 % 16) + n / 256 / 256 % 16) + n / 256 % 16) + n % 16 := by
  rw [show mask4 = 256 * (256 * (256 * (256 * (256 * (256 * (256 * (15) + 15) + 15) + 15) + 15) + 15) + 15) + 15 by norm_num [mask4]]
  simp only [split4, and15]
theorem landM8 (n : Nat) : n &&& mask4 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 % 16) + n % 16 := by
  rw [landM8']; simp only [Nat.div_div_eq_div_mul]
theorem hdiv16 (c R : Nat) (h : c < 16) : (c + 16 * R) / 16 = R := by omega
theorem hmod16 (c R : Nat) (h : c < 16) : (c + 16 * R) % 16 = c := by omega
theorem fold_mod255 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) :
    (x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * (x7)))))))) % 255 =
      (x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7) % 255 := by
  omega
theorem lanes4 (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 : Nat) (h0 : q0 ≤ 12) (h1 : q1 ≤ 12) (h2 : q2 ≤ 12) (h3 : q3 ≤ 12) (h4 : q4 ≤ 12) (h5 : q5 ≤ 12) (h6 : q6 ≤ 12) (h7 : q7 ≤ 12) (h8 : q8 ≤ 12) (h9 : q9 ≤ 12) (h10 : q10 ≤ 12) (h11 : q11 ≤ 12) (h12 : q12 ≤ 12) (h13 : q13 ≤ 12) (h14 : q14 ≤ 12) (h15 : q15 ≤ 12) (L : Nat)
    (hL : L = q0 + 16 * (q1 + 16 * (q2 + 16 * (q3 + 16 * (q4 + 16 * (q5 + 16 * (q6 + 16 * (q7 + 16 * (q8 + 16 * (q9 + 16 * (q10 + 16 * (q11 + 16 * (q12 + 16 * (q13 + 16 * (q14 + 16 * (q15)))))))))))))))) :
    ((L / 16 &&& mask4) + (L &&& mask4)) % 18446744073709551616 % 255 = q0 + q1 + q2 + q3 + q4 + q5 + q6 + q7 + q8 + q9 + q10 + q11 + q12 + q13 + q14 + q15 := by
  have e : (L / 16 &&& mask4) + (L &&& mask4) = (q1 + q0) + 256 * ((q3 + q2) + 256 * ((q5 + q4) + 256 * ((q7 + q6) + 256 * ((q9 + q8) + 256 * ((q11 + q10) + 256 * ((q13 + q12) + 256 * ((q15 + q14)))))))) := by
    rw [landM8, landM8, hL]
    simp (disch := omega) only [hdiv16, hmod16, Nat.mod_eq_of_lt]
    ring
  rw [e]
  clear e hL
  have hlt : (q1 + q0) + 256 * ((q3 + q2) + 256 * ((q5 + q4) + 256 * ((q7 + q6) + 256 * ((q9 + q8) + 256 * ((q11 + q10) + 256 * ((q13 + q12) + 256 * ((q15 + q14)))))))) < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt, fold_mod255]
  have hlt2 : (q1 + q0) + (q3 + q2) + (q5 + q4) + (q7 + q6) + (q9 + q8) + (q11 + q10) + (q13 + q12) + (q15 + q14) < 255 := by omega
  rw [Nat.mod_eq_of_lt hlt2]
  ring
def qsum32 (a : Nat) : Nat :=
  a % 4 + a / 4 % 4 + a / 16 % 4 + a / 64 % 4 + a / 256 % 4 + a / 1024 % 4 + a / 4096 % 4 + a / 16384 % 4 + a / 65536 % 4 + a / 262144 % 4 + a / 1048576 % 4 + a / 4194304 % 4 + a / 16777216 % 4 + a / 67108864 % 4 + a / 268435456 % 4 + a / 1073741824 % 4 + a / 4294967296 % 4 + a / 17179869184 % 4 + a / 68719476736 % 4 + a / 274877906944 % 4 + a / 1099511627776 % 4 + a / 4398046511104 % 4 + a / 17592186044416 % 4 + a / 70368744177664 % 4 + a / 281474976710656 % 4 + a / 1125899906842624 % 4 + a / 4503599627370496 % 4 + a / 18014398509481984 % 4 + a / 72057594037927936 % 4 + a / 288230376151711744 % 4 + a / 1152921504606846976 % 4 + a / 4611686018427387904 % 4
def qsum17 (c : Nat) : Nat :=
  c % 4 + c / 4 % 4 + c / 16 % 4 + c / 64 % 4 + c / 256 % 4 + c / 1024 % 4 + c / 4096 % 4 + c / 16384 % 4 + c / 65536 % 4 + c / 262144 % 4 + c / 1048576 % 4 + c / 4194304 % 4 + c / 16777216 % 4 + c / 67108864 % 4 + c / 268435456 % 4 + c / 1073741824 % 4 + c / 4294967296 % 4
def dsum9 (g : Nat) : Nat :=
  g % 8 + g / 8 % 8 + g / 64 % 8 + g / 512 % 8 + g / 4096 % 8 + g / 32768 % 8 + g / 262144 % 8 + g / 2097152 % 8 + g / 16777216 % 8
def topL (a c : Nat) : Nat :=
  (((a / 4 &&& mask2) + (a &&& mask2)) % 18446744073709551616 +
    ((c / 4 &&& mask2) + (c &&& mask2)) % 18446744073709551616) % 18446744073709551616
def topSwar2 (a c : Nat) : Nat :=
  ((topL a c / 16 &&& mask4) + (topL a c &&& mask4)) % 18446744073709551616 % 255
theorem topSwar2_eq (a c : Nat) (hc : c < 2 ^ 34) :
    topSwar2 a c = qsum32 a + qsum17 c := by
  have hc17 : c / 17179869184 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc18 : c / 68719476736 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc19 : c / 274877906944 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc20 : c / 1099511627776 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc21 : c / 4398046511104 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc22 : c / 17592186044416 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc23 : c / 70368744177664 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc24 : c / 281474976710656 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc25 : c / 1125899906842624 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc26 : c / 4503599627370496 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc27 : c / 18014398509481984 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc28 : c / 72057594037927936 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc29 : c / 288230376151711744 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc30 : c / 1152921504606846976 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hc31 : c / 4611686018427387904 % 4 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  unfold topSwar2 qsum32 qsum17
  generalize hL : topL a c = L
  unfold topL at hL
  simp only [landM4, Nat.div_div_eq_div_mul] at hL
  norm_num at hL
  simp only [hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hL
  clear hc17
  clear hc18
  clear hc19
  clear hc20
  clear hc21
  clear hc22
  clear hc23
  clear hc24
  clear hc25
  clear hc26
  clear hc27
  clear hc28
  clear hc29
  clear hc30
  clear hc31
  have ha0 : a % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a % 4 = a0 at *
  have ha1 : a / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4 % 4 = a1 at *
  have ha2 : a / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16 % 4 = a2 at *
  have ha3 : a / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 4 = a3 at *
  have ha4 : a / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 256 % 4 = a4 at *
  have ha5 : a / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1024 % 4 = a5 at *
  have ha6 : a / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 4 = a6 at *
  have ha7 : a / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16384 % 4 = a7 at *
  have ha8 : a / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 65536 % 4 = a8 at *
  have ha9 : a / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 4 = a9 at *
  have ha10 : a / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1048576 % 4 = a10 at *
  have ha11 : a / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4194304 % 4 = a11 at *
  have ha12 : a / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 4 = a12 at *
  have ha13 : a / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 67108864 % 4 = a13 at *
  have ha14 : a / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 268435456 % 4 = a14 at *
  have ha15 : a / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 4 = a15 at *
  have ha16 : a / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4294967296 % 4 = a16 at *
  have ha17 : a / 17179869184 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17179869184 % 4 = a17 at *
  have ha18 : a / 68719476736 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 4 = a18 at *
  have ha19 : a / 274877906944 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 274877906944 % 4 = a19 at *
  have ha20 : a / 1099511627776 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1099511627776 % 4 = a20 at *
  have ha21 : a / 4398046511104 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 4 = a21 at *
  have ha22 : a / 17592186044416 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 17592186044416 % 4 = a22 at *
  have ha23 : a / 70368744177664 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 70368744177664 % 4 = a23 at *
  have ha24 : a / 281474976710656 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 4 = a24 at *
  have ha25 : a / 1125899906842624 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1125899906842624 % 4 = a25 at *
  have ha26 : a / 4503599627370496 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4503599627370496 % 4 = a26 at *
  have ha27 : a / 18014398509481984 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 4 = a27 at *
  have ha28 : a / 72057594037927936 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 72057594037927936 % 4 = a28 at *
  have ha29 : a / 288230376151711744 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 288230376151711744 % 4 = a29 at *
  have ha30 : a / 1152921504606846976 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 4 = a30 at *
  have ha31 : a / 4611686018427387904 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize a / 4611686018427387904 % 4 = a31 at *
  have hc0 : c % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c % 4 = c0 at *
  have hc1 : c / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4 % 4 = c1 at *
  have hc2 : c / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16 % 4 = c2 at *
  have hc3 : c / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 64 % 4 = c3 at *
  have hc4 : c / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 256 % 4 = c4 at *
  have hc5 : c / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1024 % 4 = c5 at *
  have hc6 : c / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4096 % 4 = c6 at *
  have hc7 : c / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16384 % 4 = c7 at *
  have hc8 : c / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 65536 % 4 = c8 at *
  have hc9 : c / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 262144 % 4 = c9 at *
  have hc10 : c / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1048576 % 4 = c10 at *
  have hc11 : c / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4194304 % 4 = c11 at *
  have hc12 : c / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 16777216 % 4 = c12 at *
  have hc13 : c / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 67108864 % 4 = c13 at *
  have hc14 : c / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 268435456 % 4 = c14 at *
  have hc15 : c / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 1073741824 % 4 = c15 at *
  have hc16 : c / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize c / 4294967296 % 4 = c16 at *
  clear hc
  rw [lanes4 (a1 + a0 + c1 + c0) (a3 + a2 + c3 + c2) (a5 + a4 + c5 + c4) (a7 + a6 + c7 + c6) (a9 + a8 + c9 + c8) (a11 + a10 + c11 + c10) (a13 + a12 + c13 + c12) (a15 + a14 + c15 + c14) (a17 + a16 + c16) (a19 + a18) (a21 + a20) (a23 + a22) (a25 + a24) (a27 + a26) (a29 + a28) (a31 + a30) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) (by clear hL; omega) L (by
    rw [← hL]
    clear hL
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    ring)]
  clear hL
  ring
def topSwar3 (g : Nat) : Nat :=
  ((((g / 8 &&& mask3) + (g &&& mask3)) % 18446744073709551616 +
    ((g / 8 &&& mask3) + (g &&& mask3)) % 18446744073709551616 / 64) % 18446744073709551616 &&& mask6) % 4095
theorem topSwar3_eq (g : Nat) (hg : g < 2 ^ 27) : topSwar3 g = dsum9 g := by
  have e : topSwar3 g = lowSwar g 0 := by
    unfold topSwar3 lowSwar sw1
    simp only [Nat.zero_div, Nat.zero_and, Nat.add_zero, Nat.mod_mod]
  rw [e, lowSwar_eq _ _ (by omega) (by norm_num)]
  have h63 : g / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
  rw [h63]
  unfold dsum21 dsum9
  have hg9 : g / 134217728 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg10 : g / 1073741824 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg11 : g / 8589934592 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg12 : g / 68719476736 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg13 : g / 549755813888 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg14 : g / 4398046511104 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg15 : g / 35184372088832 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg16 : g / 281474976710656 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg17 : g / 2251799813685248 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg18 : g / 18014398509481984 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg19 : g / 144115188075855872 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  have hg20 : g / 1152921504606846976 % 8 = 0 := by rw [Nat.div_eq_of_lt (by omega)]
  simp only [hg9, hg10, hg11, hg12, hg13, hg14, hg15, hg16, hg17, hg18, hg19, hg20, Nat.zero_div, Nat.zero_mod, Nat.add_zero]
theorem qsum32_eq (a : Nat) : qsum32 a = ((List.range 32).map fun i => a / 2 ^ (2 * i) % 2 ^ 2).sum := by
  simp only [qsum32, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem qsum17_eq (c : Nat) : qsum17 c = ((List.range 17).map fun i => c / 2 ^ (2 * i) % 2 ^ 2).sum := by
  simp only [qsum17, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem dsum9_eq (g : Nat) : dsum9 g = ((List.range 9).map fun j => g / 2 ^ (3 * j) % 2 ^ 3).sum := by
  simp only [dsum9, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem dataDigits_lower (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    dataDigits lay value = (List.range 42).map fun i => value.toNat / 2 ^ (3 * i) % 2 ^ 3 := by
  have h42 : dataCount lay = 42 := by simp [dataCount, hlay]
  unfold dataDigits
  rw [h42]
  apply List.map_congr_left
  intro i _
  simp [hlay, coreDigit]
def lowSum (V : Nat) : Nat := lowSwar (V % 2 ^ 64) (2 * (V / 2 ^ 64))
theorem lowSum_lt (V : Nat) : lowSum V < 4095 := Nat.mod_lt _ (by norm_num)
theorem lowSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 62) :
    lowSum V = ((List.range 42).map fun i => V / 2 ^ (3 * i) % 2 ^ 3).sum := by
  unfold lowSum
  rw [lowSwar_eq _ _ (Nat.mod_lt _ (by norm_num)) (by omega)]
  have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
  have := lowDigits_sum (V % 2 ^ 64) (V / 2 ^ 64) (Nat.mod_lt _ (by norm_num))
  rw [← hV] at this
  exact this.symm
theorem target_le (lay : Layer) : target lay ≤ 197 := by
  fin_cases lay <;> decide
theorem decode_lower (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    decode lay value =
      if value.toNat / 2 ^ 64 / 2 ^ 62 ≠ 0 then none
      else if (target lay + 2 ^ 64 - lowSum value.toNat) % 2 ^ 64 < 8 then
        some (((List.range 42).map fun i => value.toNat / 2 ^ (3 * i) % 2 ^ 3) ++
          [(target lay + 2 ^ 64 - lowSum value.toNat) % 2 ^ 64])
      else none := by
  have ht := target_le lay
  have hS := lowSum_lt value.toNat
  have hb : encodedBits lay = 126 := by simp [encodedBits, hlay]
  unfold decode
  rw [hb, dataDigits_lower lay hlay]
  simp only [if_neg hlay]
  by_cases h : value.toNat / 2 ^ 64 / 2 ^ 62 ≠ 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), ← lowSum_eq _ (by omega)]
    by_cases hc : lowSum value.toNat ≤ target lay ∧ target lay - lowSum value.toNat < 8
    · rw [if_pos hc, if_pos (by omega)]
      congr 3
      omega
    · rw [if_neg hc, if_neg (by omega)]
def topSum (V : Nat) : Nat := topSwar2 (V % 2 ^ 64) (V / 2 ^ 64 % 2 ^ 34) + topSwar3 (V / 2 ^ 64 / 2 ^ 34)
theorem topSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 61) :
    topSum V = ((List.range 49).map fun i => V / 2 ^ (2 * i) % 2 ^ 2).sum +
      ((List.range 9).map fun j => V / 2 ^ (98 + 3 * j) % 2 ^ 3).sum := by
  unfold topSum
  rw [topSwar2_eq _ _ (Nat.mod_lt _ (by norm_num)),
    topSwar3_eq _ (by omega), qsum32_eq, qsum17_eq, dsum9_eq, show 49 = 32 + 17 from rfl, sum_range_add]
  have hV : ∀ i < 32, V / 2 ^ (2 * i) % 2 ^ 2 = V % 2 ^ 64 / 2 ^ (2 * i) % 2 ^ 2 := by
    intro i hi
    have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
    conv_lhs => rw [hV]
    exact div_mod_add_pow _ _ _ _ _ (by omega)
  have hW : ∀ j < 17, V / 2 ^ (2 * (32 + j)) % 2 ^ 2 = V / 2 ^ 64 % 2 ^ 34 / 2 ^ (2 * j) % 2 ^ 2 := by
    intro j hj
    have hU : V / 2 ^ 64 = V / 2 ^ 64 % 2 ^ 34 + 2 ^ 34 * (V / 2 ^ 64 / 2 ^ 34) :=
      (Nat.mod_add_div _ (2 ^ 34)).symm
    rw [show 2 * (32 + j) = 64 + 2 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    conv_lhs => rw [hU]
    exact div_mod_add_pow _ _ _ _ _ (by omega)
  have hG : ∀ j < 9, V / 2 ^ (98 + 3 * j) % 2 ^ 3 = V / 2 ^ 64 / 2 ^ 34 / 2 ^ (3 * j) % 2 ^ 3 := by
    intro j _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.pow_add,
      show 64 + (34 + 3 * j) = 98 + 3 * j by omega]
  rw [sum_congr_range _ _ 32 hV, sum_congr_range _ _ 17 hW, sum_congr_range _ _ 9 hG]
end SigGolfCandidate.T3M
