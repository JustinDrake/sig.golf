import SigGolfCandidate.T3M.Search.Arith

/-!
# `counter_search`: the decode arithmetic (stream E)

The answer value `v` (low 16 bytes of the HASH output) sits in two doublewords `lo = v[0,64)`,
`hi = v[64,128)` (`t1`, `t2`). `counter_search` reads the digits with unrolled shift/mask code
(lower layers: 42 radix-8 digits, one crossing the doubleword boundary; top layer: 49 radix-4 and
9 radix-8 digits) and sums them. Here: the shift/mask terms as `ofNat` digit values, Core's
`dataDigits` as explicit lists (`lowDigits`, `topDigits`) and their sums term by term, and Core's
`decode` restated with them.
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)

/-! ## Digit terms -/

theorem ext_shr_mask (v : BitVec 128) (base sh w : Nat) (h : sh + w ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& BitVec.ofNat 64 (2 ^ w - 1) =
      BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 2 ^ w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, hi,
    decide_true, Bool.true_and]
  by_cases hw : i < w
  · simp only [hw, decide_true, Bool.and_true, Bool.true_and, show sh + i < 64 by omega, BitVec.testBit_toNat]
    congr 1; omega
  · simp [hw]

@[simp] theorem ext_shr_and7 (v : BitVec 128) (base sh : Nat) (h : sh + 3 ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& 7#64 = BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 8) :=
  ext_shr_mask v base sh 3 h

@[simp] theorem ext_and7 (v : BitVec 128) (base : Nat) :
    v.extractLsb' base 64 &&& 7#64 = BitVec.ofNat 64 (v.toNat / 2 ^ base % 8) := by
  simpa using ext_shr_mask v base 0 3 (by omega)

@[simp] theorem ext_shr_and3 (v : BitVec 128) (base sh : Nat) (h : sh + 2 ≤ 64) :
    (v.extractLsb' base 64 >>> sh) &&& 3#64 = BitVec.ofNat 64 (v.toNat / 2 ^ (base + sh) % 4) :=
  ext_shr_mask v base sh 2 h

@[simp] theorem ext_and3 (v : BitVec 128) (base : Nat) :
    v.extractLsb' base 64 &&& 3#64 = BitVec.ofNat 64 (v.toNat / 2 ^ base % 4) := by
  simpa using ext_shr_mask v base 0 2 (by omega)

/-- The lower-layer digit 21 (bits 63..65) across the two doublewords. -/
theorem cross_low (v : BitVec 128) :
    (v.extractLsb' 0 64 >>> 63 ||| v.extractLsb' 64 64 <<< 1 &&& 7#64) =
      BitVec.ofNat 64 (v.toNat / 2 ^ 63 % 8) := by
  rw [show (8 : Nat) = 2 ^ 3 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h7 : (7#64).getLsbD i = decide (i < 3) := by
    rw [BitVec.getLsbD_ofNat, show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, h7, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, BitVec.testBit_toNat]
  rcases i with _ | _ | _ | i
  · simp
  · simp
  · simp
  · simp only [show ¬ (i + 1 + 1 + 1 < 3) from by omega, decide_false, Bool.and_false, Bool.false_and,
      show ¬ (63 + (i + 1 + 1 + 1) < 64) from by omega, Bool.or_false]

/-! ## Core's digits -/

/-- The 42 radix-8 data digits of a lower layer. -/
def lowDigits (v : Digest) : List Nat := (List.range 42).map fun i => v.toNat / 2 ^ (3 * i) % 8

/-- The 49 radix-4 and 9 radix-8 data digits of the top layer. -/
def topDigits (v : Digest) : List Nat := (List.range 58).map fun i =>
  if i < 49 then v.toNat / 2 ^ (2 * i) % 4 else v.toNat / 2 ^ (98 + 3 * (i - 49)) % 8

theorem dataDigits_low (lay : Layer) (h : lay ≠ 0) (v : Digest) : T3.dataDigits lay v = lowDigits v := by
  unfold T3.dataDigits lowDigits
  simp only [T3.dataCount, T3.width, h, if_false, false_and]
  rfl

theorem dataDigits_top (v : Digest) : T3.dataDigits 0 v = topDigits v := by
  unfold T3.dataDigits topDigits
  simp only [T3.dataCount, T3.width, if_true, true_and]
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 49 <;> simp [hi]

theorem lowDigits_length (v : Digest) : (lowDigits v).length = 42 := by simp [lowDigits]
theorem topDigits_length (v : Digest) : (topDigits v).length = 58 := by simp [topDigits]

/-- The lower-layer digit sum, term by term (`s9` of `counter_search`). -/
theorem lowDigits_sum (v : Digest) : (lowDigits v).sum =
      v.toNat / 1 % 8 +
      v.toNat / 8 % 8 +
      v.toNat / 64 % 8 +
      v.toNat / 512 % 8 +
      v.toNat / 4096 % 8 +
      v.toNat / 32768 % 8 +
      v.toNat / 262144 % 8 +
      v.toNat / 2097152 % 8 +
      v.toNat / 16777216 % 8 +
      v.toNat / 134217728 % 8 +
      v.toNat / 1073741824 % 8 +
      v.toNat / 8589934592 % 8 +
      v.toNat / 68719476736 % 8 +
      v.toNat / 549755813888 % 8 +
      v.toNat / 4398046511104 % 8 +
      v.toNat / 35184372088832 % 8 +
      v.toNat / 281474976710656 % 8 +
      v.toNat / 2251799813685248 % 8 +
      v.toNat / 18014398509481984 % 8 +
      v.toNat / 144115188075855872 % 8 +
      v.toNat / 1152921504606846976 % 8 +
      v.toNat / 9223372036854775808 % 8 +
      v.toNat / 73786976294838206464 % 8 +
      v.toNat / 590295810358705651712 % 8 +
      v.toNat / 4722366482869645213696 % 8 +
      v.toNat / 37778931862957161709568 % 8 +
      v.toNat / 302231454903657293676544 % 8 +
      v.toNat / 2417851639229258349412352 % 8 +
      v.toNat / 19342813113834066795298816 % 8 +
      v.toNat / 154742504910672534362390528 % 8 +
      v.toNat / 1237940039285380274899124224 % 8 +
      v.toNat / 9903520314283042199192993792 % 8 +
      v.toNat / 79228162514264337593543950336 % 8 +
      v.toNat / 633825300114114700748351602688 % 8 +
      v.toNat / 5070602400912917605986812821504 % 8 +
      v.toNat / 40564819207303340847894502572032 % 8 +
      v.toNat / 324518553658426726783156020576256 % 8 +
      v.toNat / 2596148429267413814265248164610048 % 8 +
      v.toNat / 20769187434139310514121985316880384 % 8 +
      v.toNat / 166153499473114484112975882535043072 % 8 +
      v.toNat / 1329227995784915872903807060280344576 % 8 +
      v.toNat / 10633823966279326983230456482242756608 % 8 := by
  simp only [lowDigits, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num

/-- The top-layer digit sum, term by term. -/
theorem topDigits_sum (v : Digest) : (topDigits v).sum =
      v.toNat / 1 % 4 +
      v.toNat / 4 % 4 +
      v.toNat / 16 % 4 +
      v.toNat / 64 % 4 +
      v.toNat / 256 % 4 +
      v.toNat / 1024 % 4 +
      v.toNat / 4096 % 4 +
      v.toNat / 16384 % 4 +
      v.toNat / 65536 % 4 +
      v.toNat / 262144 % 4 +
      v.toNat / 1048576 % 4 +
      v.toNat / 4194304 % 4 +
      v.toNat / 16777216 % 4 +
      v.toNat / 67108864 % 4 +
      v.toNat / 268435456 % 4 +
      v.toNat / 1073741824 % 4 +
      v.toNat / 4294967296 % 4 +
      v.toNat / 17179869184 % 4 +
      v.toNat / 68719476736 % 4 +
      v.toNat / 274877906944 % 4 +
      v.toNat / 1099511627776 % 4 +
      v.toNat / 4398046511104 % 4 +
      v.toNat / 17592186044416 % 4 +
      v.toNat / 70368744177664 % 4 +
      v.toNat / 281474976710656 % 4 +
      v.toNat / 1125899906842624 % 4 +
      v.toNat / 4503599627370496 % 4 +
      v.toNat / 18014398509481984 % 4 +
      v.toNat / 72057594037927936 % 4 +
      v.toNat / 288230376151711744 % 4 +
      v.toNat / 1152921504606846976 % 4 +
      v.toNat / 4611686018427387904 % 4 +
      v.toNat / 18446744073709551616 % 4 +
      v.toNat / 73786976294838206464 % 4 +
      v.toNat / 295147905179352825856 % 4 +
      v.toNat / 1180591620717411303424 % 4 +
      v.toNat / 4722366482869645213696 % 4 +
      v.toNat / 18889465931478580854784 % 4 +
      v.toNat / 75557863725914323419136 % 4 +
      v.toNat / 302231454903657293676544 % 4 +
      v.toNat / 1208925819614629174706176 % 4 +
      v.toNat / 4835703278458516698824704 % 4 +
      v.toNat / 19342813113834066795298816 % 4 +
      v.toNat / 77371252455336267181195264 % 4 +
      v.toNat / 309485009821345068724781056 % 4 +
      v.toNat / 1237940039285380274899124224 % 4 +
      v.toNat / 4951760157141521099596496896 % 4 +
      v.toNat / 19807040628566084398385987584 % 4 +
      v.toNat / 79228162514264337593543950336 % 4 +
      v.toNat / 316912650057057350374175801344 % 8 +
      v.toNat / 2535301200456458802993406410752 % 8 +
      v.toNat / 20282409603651670423947251286016 % 8 +
      v.toNat / 162259276829213363391578010288128 % 8 +
      v.toNat / 1298074214633706907132624082305024 % 8 +
      v.toNat / 10384593717069655257060992658440192 % 8 +
      v.toNat / 83076749736557242056487941267521536 % 8 +
      v.toNat / 664613997892457936451903530140172288 % 8 +
      v.toNat / 5316911983139663491615228241121378304 % 8 := by
  simp only [topDigits, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num

/-! ## `decode` -/

/-- `decode` of a lower layer: range `v < 2^126`, digit sum `S ≤ target`, `target - S < 8`; the
checksum digit `target - S` is appended. -/
theorem decode_low (lay : Layer) (h : lay ≠ 0) (v : Digest) :
    T3.decode lay v =
      if v.toNat < 2 ^ 126 ∧ (lowDigits v).sum ≤ T3.target lay ∧ T3.target lay - (lowDigits v).sum < 8
      then some (lowDigits v ++ [T3.target lay - (lowDigits v).sum]) else none := by
  unfold T3.decode
  simp only [T3.encodedBits, h, if_false, dataDigits_low lay h]
  by_cases h1 : v.toNat < 2 ^ 126
  · simp only [show ¬ (v.toNat ≥ 2 ^ 126) from by omega, if_false, h1, true_and]
  · simp only [show v.toNat ≥ 2 ^ 126 from by omega, if_true, h1, false_and, if_false]

/-- `decode` of the top layer: range `v < 2^125`, digit sum exactly 126. -/
theorem decode_top (v : Digest) :
    T3.decode 0 v = if v.toNat < 2 ^ 125 ∧ (topDigits v).sum = 126 then some (topDigits v) else none := by
  unfold T3.decode
  simp only [T3.encodedBits, if_true, dataDigits_top, T3.target]
  by_cases h1 : v.toNat < 2 ^ 125
  · simp only [show ¬ (v.toNat ≥ 2 ^ 125) from by omega, if_false, h1, true_and]
    rfl
  · simp only [show v.toNat ≥ 2 ^ 125 from by omega, if_true, h1, false_and, if_false]

end SigGolfCandidate.T3M.Search
