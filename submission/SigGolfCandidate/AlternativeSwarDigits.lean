import SigGolfCandidate.AlternativeMachineBasics

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal


namespace SigGolfCandidate.Base4Candidate.SwarProof
open SigGolfCandidate.Verify (land_split)
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem split2 (n M : Nat) : n &&& (16*M+3) = 16*((n/16) &&& M)+n%4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256*M+15) = 256*((n/256) &&& M)+n%16 :=
  land_split n M 4 8 (by decide)
theorem and3 (n : Nat) : n &&& 3 = n%4 := Nat.and_two_pow_sub_one_eq_mod n 2
theorem and15 (n : Nat) : n &&& 15 = n%16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem mask2 (n : Nat) : n &&& 3689348814741910323 =
    16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 / 16 % 4) + n / 16 / 16 / 16 % 4) + n / 16 / 16 % 4) + n / 16 % 4) + n % 4 := by
  rw [show (3689348814741910323 : Nat) = 16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (16 * (3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3) + 3 by norm_num]
  simp only [split2, and3]

theorem mask4 (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 256 / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 / 256 % 16) + n / 256 / 256 / 256 % 16) + n / 256 / 256 % 16) + n / 256 % 16) + n % 16 := by
  rw [show (1085102592571150095 : Nat) = 256 * (256 * (256 * (256 * (256 * (256 * (256 * (15) + 15) + 15) + 15) + 15) + 15) + 15) + 15 by norm_num]
  simp only [split4, and15]

theorem mask4_nibbles (n : Nat) : n &&& 1085102592571150095 =
    256 * (256 * (256 * (256 * (256 * (256 * (256 * (n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 / 16 / 16 % 16) + n / 16 / 16 % 16) + n % 16 := by
  rw [mask4]
  simp only [Nat.div_div_eq_div_mul]

theorem hdiv16 (c R : Nat) (h : c < 16) : (c+16*R)/16 = R := by omega
theorem hmod16 (c R : Nat) (h : c < 16) : (c+16*R)%16 = c := by omega

theorem byteChecksum (P0 P1 P2 P3 P4 P5 P6 P7 : Nat) (h0 : P0 ≤ 24) (h1 : P1 ≤ 24) (h2 : P2 ≤ 24) (h3 : P3 ≤ 24) (h4 : P4 ≤ 24) (h5 : P5 ≤ 24) (h6 : P6 ≤ 24) (h7 : P7 ≤ 24) :
    ((P0) + 256 * ((P1) + 256 * ((P2) + 256 * ((P3) + 256 * ((P4) + 256 * ((P5) + 256 * ((P6) + 256 * (P7)))))))) % 255 = P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7 := by
  calc
    _ = (P0 + (P1 + (P2 + (P3 + (P4 + (P5 + (P6 + (P7)))))))) % 255 := by simp [Nat.add_mod,Nat.mul_mod]
    _ = _ := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega

def tail (X : Nat) : Nat := (((X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095)) % 18446744073709551616) % 255

theorem lanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 : Nat) (h0 : L0 ≤ 12) (h1 : L1 ≤ 12) (h2 : L2 ≤ 12) (h3 : L3 ≤ 12) (h4 : L4 ≤ 12) (h5 : L5 ≤ 12) (h6 : L6 ≤ 12) (h7 : L7 ≤ 12) (h8 : L8 ≤ 12) (h9 : L9 ≤ 12) (h10 : L10 ≤ 12) (h11 : L11 ≤ 12) (h12 : L12 ≤ 12) (h13 : L13 ≤ 12) (h14 : L14 ≤ 12) (h15 : L15 ≤ 12)
    (X : Nat) (hX : X = (L0) + 16 * ((L1) + 16 * ((L2) + 16 * ((L3) + 16 * ((L4) + 16 * ((L5) + 16 * ((L6) + 16 * ((L7) + 16 * ((L8) + 16 * ((L9) + 16 * ((L10) + 16 * ((L11) + 16 * ((L12) + 16 * ((L13) + 16 * ((L14) + 16 * (L15)))))))))))))))) : tail X = L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 + L11 + L12 + L13 + L14 + L15 := by
  have hM : (X &&& 1085102592571150095) + (X/16 &&& 1085102592571150095) = (L0+L1) + 256 * ((L2+L3) + 256 * ((L4+L5) + 256 * ((L6+L7) + 256 * ((L8+L9) + 256 * ((L10+L11) + 256 * ((L12+L13) + 256 * (L14+L15))))))) := by
    rw [hX, mask4_nibbles, mask4_nibbles]
    simp (disch := omega) only [hdiv16, hmod16, Nat.mod_eq_of_lt]
    omega
  have hbound : (X &&& 1085102592571150095) +
      (X/16 &&& 1085102592571150095) < 18446744073709551616 := by
    rw [hM]
    omega
  unfold tail
  rw [Nat.mod_eq_of_lt hbound, hM]
  have h := byteChecksum (L0+L1) (L2+L3) (L4+L5) (L6+L7) (L8+L9) (L10+L11) (L12+L13) (L14+L15) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  omega

def first (a b : Nat) : Nat :=
  (((a &&& 3689348814741910323)+(a/4 &&& 3689348814741910323)) % 18446744073709551616 +
    ((b &&& 3689348814741910323)+(b/4 &&& 3689348814741910323)) % 18446744073709551616) % 18446744073709551616

/-- Bound the four masked words before expanding their individual digits.
This avoids modular elimination over all 64 digit variables. -/
theorem first_no_wrap (a b : Nat) :
    first a b = (a &&& 3689348814741910323)+(a/4 &&& 3689348814741910323)+
      ((b &&& 3689348814741910323)+(b/4 &&& 3689348814741910323)) := by
  have h0 : a &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h1 : a/4 &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h2 : b &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  have h3 : b/4 &&& 3689348814741910323 ≤ 3689348814741910323 := Nat.and_le_right
  unfold first
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]

def digitSum (a : Nat) : Nat := ((List.range 32).map fun i => a/4^i%4).sum

theorem digitSum_expanded (a : Nat) : digitSum a =
    a % 4 + a / 4 % 4 + a / 16 % 4 + a / 64 % 4 + a / 256 % 4 + a / 1024 % 4 + a / 4096 % 4 + a / 16384 % 4 + a / 65536 % 4 + a / 262144 % 4 + a / 1048576 % 4 + a / 4194304 % 4 + a / 16777216 % 4 + a / 67108864 % 4 + a / 268435456 % 4 + a / 1073741824 % 4 + a / 4294967296 % 4 + a / 17179869184 % 4 + a / 68719476736 % 4 + a / 274877906944 % 4 + a / 1099511627776 % 4 + a / 4398046511104 % 4 + a / 17592186044416 % 4 + a / 70368744177664 % 4 + a / 281474976710656 % 4 + a / 1125899906842624 % 4 + a / 4503599627370496 % 4 + a / 18014398509481984 % 4 + a / 72057594037927936 % 4 + a / 288230376151711744 % 4 + a / 1152921504606846976 % 4 + a / 4611686018427387904 % 4 := by
  simp only [digitSum, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num
  omega

/-- All 64 digits are summed exactly. The decoder separately zeros the upper
four bits, so the final two digits contribute zero for valid encodings. -/
theorem sum_exact (a b : Nat) : tail (first a b) = digitSum a+digitSum b := by
  generalize hX : first a b = X
  rw [first_no_wrap] at hX
  rw [digitSum_expanded, digitSum_expanded]
  simp only [mask2, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
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
  have hb0 : b % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b % 4 = b0 at *
  have hb1 : b / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4 % 4 = b1 at *
  have hb2 : b / 16 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16 % 4 = b2 at *
  have hb3 : b / 64 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 4 = b3 at *
  have hb4 : b / 256 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 256 % 4 = b4 at *
  have hb5 : b / 1024 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1024 % 4 = b5 at *
  have hb6 : b / 4096 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 4 = b6 at *
  have hb7 : b / 16384 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16384 % 4 = b7 at *
  have hb8 : b / 65536 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 65536 % 4 = b8 at *
  have hb9 : b / 262144 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 4 = b9 at *
  have hb10 : b / 1048576 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1048576 % 4 = b10 at *
  have hb11 : b / 4194304 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4194304 % 4 = b11 at *
  have hb12 : b / 16777216 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 4 = b12 at *
  have hb13 : b / 67108864 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 67108864 % 4 = b13 at *
  have hb14 : b / 268435456 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 268435456 % 4 = b14 at *
  have hb15 : b / 1073741824 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 4 = b15 at *
  have hb16 : b / 4294967296 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4294967296 % 4 = b16 at *
  have hb17 : b / 17179869184 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 17179869184 % 4 = b17 at *
  have hb18 : b / 68719476736 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 4 = b18 at *
  have hb19 : b / 274877906944 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 274877906944 % 4 = b19 at *
  have hb20 : b / 1099511627776 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1099511627776 % 4 = b20 at *
  have hb21 : b / 4398046511104 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 4 = b21 at *
  have hb22 : b / 17592186044416 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 17592186044416 % 4 = b22 at *
  have hb23 : b / 70368744177664 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 70368744177664 % 4 = b23 at *
  have hb24 : b / 281474976710656 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 4 = b24 at *
  have hb25 : b / 1125899906842624 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1125899906842624 % 4 = b25 at *
  have hb26 : b / 4503599627370496 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4503599627370496 % 4 = b26 at *
  have hb27 : b / 18014398509481984 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 4 = b27 at *
  have hb28 : b / 72057594037927936 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 72057594037927936 % 4 = b28 at *
  have hb29 : b / 288230376151711744 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 288230376151711744 % 4 = b29 at *
  have hb30 : b / 1152921504606846976 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 4 = b30 at *
  have hb31 : b / 4611686018427387904 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize b / 4611686018427387904 % 4 = b31 at *
  rw [lanes (a0+a1+b0+b1) (a2+a3+b2+b3) (a4+a5+b4+b5) (a6+a7+b6+b7) (a8+a9+b8+b9) (a10+a11+b10+b11) (a12+a13+b12+b13) (a14+a15+b14+b15) (a16+a17+b16+b17) (a18+a19+b18+b19) (a20+a21+b20+b21) (a22+a23+b22+b23) (a24+a25+b24+b25) (a26+a27+b26+b27) (a28+a29+b28+b29) (a30+a31+b30+b31) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) X (by
    rw [← hX]
    ring)]
  omega

end SigGolfCandidate.Base4Candidate.SwarProof


namespace SigGolfCandidate.Base4Candidate.SwarProof
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- A mask whose set bits stay in the low machine word ignores higher bits,
even when it is applied after the fixed two-bit shift. -/
theorem mask_low_word (n shift mask : Nat) (hs : shift ≤ 64)
    (hm : mask < 2^(64-shift)) :
    (n%2^64/2^shift &&& mask) = (n/2^shift &&& mask) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i+shift < 64
  · simp [hi]
  · have hp : 2^(64-shift) ≤ (2:Nat)^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hz := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hp)
    simp [hi,hz]

theorem first_low_word (a b : Nat) : first (a%2^64) b = first a b := by
  have h0 := mask_low_word a 0 3689348814741910323 (by decide) (by decide)
  have h2 := mask_low_word a 2 3689348814741910323 (by decide) (by decide)
  norm_num only [Nat.reduceSub, Nat.reducePow, Nat.div_one] at h0 h2
  unfold first
  norm_num only [Nat.reducePow]
  rw [h0,h2]

theorem digit_value (d : BitVec 128) (i : Base4Candidate.Index) :
    (Base4Candidate.digits d i).val = d.toNat/4^i.val%4 := by
  simp [Base4Candidate.digits, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, pow_mul]

/-- The two high radix-four digits are zero exactly where the concrete decoder
requires four high padding bits to be clear. -/
theorem decoded_weight (d : BitVec 128) (hd : d.toNat < 2^124) :
    Base4Candidate.weight (Base4Candidate.digits d) =
      digitSum d.toNat + digitSum (d.toNat/2^64) := by
  have h62 : d.toNat/2^124 = 0 := Nat.div_eq_of_lt hd
  have h63 : d.toNat/2^126 = 0 := Nat.div_eq_of_lt (lt_trans hd (by norm_num))
  simp only [Base4Candidate.weight, digit_value, Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [digitSum_expanded, digitSum_expanded]
  simp only [Nat.div_div_eq_div_mul]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.reducePow,
    Nat.reduceMul, Nat.div_one] at h62 h63 ⊢
  rw [h62,h63]
  simp only [Nat.zero_mod, Nat.zero_add, Nat.add_zero]
  ac_rfl

/-- Exact natural arithmetic performed by the verifier's packed digit check.
The remaining machine proof must connect register operations to these terms. -/
theorem decoder_sum (d : BitVec 128) (hd : d.toNat < 2^124) :
    tail (first (d.toNat%2^64) (d.toNat/2^64)) =
      Base4Candidate.weight (Base4Candidate.digits d) := by
  rw [first_low_word, sum_exact, ← decoded_weight d hd]

end SigGolfCandidate.Base4Candidate.SwarProof
