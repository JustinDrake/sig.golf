import SigGolfCandidate.T3M.Search.Arith

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
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
def lowDigits (v : Digest) : List Nat := (List.range 42).map fun i => v.toNat / 2 ^ (3 * i) % 8
def topDigits (v : Digest) : List Nat := (List.range 54).map (T3.coreDigit 0 v)
theorem dataDigits_low (lay : Layer) (h : lay ≠ 0) (v : Digest) : T3.dataDigits lay v = lowDigits v := by
  simp only [T3.dataDigits, T3.dataCount, h, if_false, lowDigits]
  congr 1
  funext i
  simp [T3.coreDigit, h]
theorem dataDigits_top (v : Digest) : T3.dataDigits 0 v = topDigits v := rfl
theorem lowDigits_length (v : Digest) : (lowDigits v).length = 42 := by simp [lowDigits]
theorem topDigits_length (v : Digest) : (topDigits v).length = 54 := by simp [topDigits]
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
theorem topDigits_sum (v : Digest) : (topDigits v).sum =
      (v.toNat / 1 % 128) / 1 % 5 +
      (v.toNat / 1 % 128) / 5 % 5 +
      (v.toNat / 1 % 128) / 25 % 5 +
      (v.toNat / 128 % 128) / 1 % 5 +
      (v.toNat / 128 % 128) / 5 % 5 +
      (v.toNat / 128 % 128) / 25 % 5 +
      (v.toNat / 16384 % 128) / 1 % 5 +
      (v.toNat / 16384 % 128) / 5 % 5 +
      (v.toNat / 16384 % 128) / 25 % 5 +
      (v.toNat / 2097152 % 128) / 1 % 5 +
      (v.toNat / 2097152 % 128) / 5 % 5 +
      (v.toNat / 2097152 % 128) / 25 % 5 +
      (v.toNat / 268435456 % 128) / 1 % 5 +
      (v.toNat / 268435456 % 128) / 5 % 5 +
      (v.toNat / 268435456 % 128) / 25 % 5 +
      (v.toNat / 34359738368 % 128) / 1 % 5 +
      (v.toNat / 34359738368 % 128) / 5 % 5 +
      (v.toNat / 34359738368 % 128) / 25 % 5 +
      (v.toNat / 4398046511104 % 128) / 1 % 5 +
      (v.toNat / 4398046511104 % 128) / 5 % 5 +
      (v.toNat / 4398046511104 % 128) / 25 % 5 +
      (v.toNat / 562949953421312 % 128) / 1 % 5 +
      (v.toNat / 562949953421312 % 128) / 5 % 5 +
      (v.toNat / 562949953421312 % 128) / 25 % 5 +
      (v.toNat / 72057594037927936 % 128) / 1 % 5 +
      (v.toNat / 72057594037927936 % 128) / 5 % 5 +
      (v.toNat / 72057594037927936 % 128) / 25 % 5 +
      (v.toNat / 9223372036854775808 % 128) / 1 % 5 +
      (v.toNat / 9223372036854775808 % 128) / 5 % 5 +
      (v.toNat / 9223372036854775808 % 128) / 25 % 5 +
      (v.toNat / 1180591620717411303424 % 128) / 1 % 5 +
      (v.toNat / 1180591620717411303424 % 128) / 5 % 5 +
      (v.toNat / 1180591620717411303424 % 128) / 25 % 5 +
      (v.toNat / 151115727451828646838272 % 128) / 1 % 5 +
      (v.toNat / 151115727451828646838272 % 128) / 5 % 5 +
      (v.toNat / 151115727451828646838272 % 128) / 25 % 5 +
      (v.toNat / 19342813113834066795298816 % 128) / 1 % 5 +
      (v.toNat / 19342813113834066795298816 % 128) / 5 % 5 +
      (v.toNat / 19342813113834066795298816 % 128) / 25 % 5 +
      (v.toNat / 2475880078570760549798248448 % 128) / 1 % 5 +
      (v.toNat / 2475880078570760549798248448 % 128) / 5 % 5 +
      (v.toNat / 2475880078570760549798248448 % 128) / 25 % 5 +
      (v.toNat / 316912650057057350374175801344 % 128) / 1 % 5 +
      (v.toNat / 316912650057057350374175801344 % 128) / 5 % 5 +
      (v.toNat / 316912650057057350374175801344 % 128) / 25 % 5 +
      (v.toNat / 40564819207303340847894502572032 % 128) / 1 % 5 +
      (v.toNat / 40564819207303340847894502572032 % 128) / 5 % 5 +
      (v.toNat / 40564819207303340847894502572032 % 128) / 25 % 5 +
      (v.toNat / 5192296858534827628530496329220096 % 128) / 1 % 5 +
      (v.toNat / 5192296858534827628530496329220096 % 128) / 5 % 5 +
      (v.toNat / 5192296858534827628530496329220096 % 128) / 25 % 5 +
      v.toNat / 664613997892457936451903530140172288 % 4 +
      v.toNat / 2658455991569831745807614120560689152 % 4 +
      v.toNat / 10633823966279326983230456482242756608 % 4 := by
  simp only [topDigits, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num [T3.coreDigit]
theorem decode_low (lay : Layer) (h : lay ≠ 0) (v : Digest) :
    T3.decode lay v =
      if v.toNat < 2 ^ 126 ∧ (lowDigits v).sum ≤ T3.target lay ∧ T3.target lay - (lowDigits v).sum < 8
      then some (lowDigits v ++ [T3.target lay - (lowDigits v).sum]) else none := by
  unfold T3.decode
  simp only [T3.encodedBits, h, if_false, dataDigits_low lay h]
  by_cases h1 : v.toNat < 2 ^ 126
  · simp only [show ¬ (v.toNat ≥ 2 ^ 126) from by omega, if_false, h1, true_and]
  · simp only [show v.toNat ≥ 2 ^ 126 from by omega, if_true, h1, false_and, if_false]
theorem decode_top (v : Digest) :
    T3.decode 0 v = if v.toNat < 2 ^ 125 ∧ T3.topRanksValid v = true ∧ (topDigits v).sum = 126
      then some (topDigits v) else none := by
  unfold T3.decode
  simp only [T3.encodedBits, if_true, dataDigits_top, T3.target, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> simp_all <;> omega
end SigGolfCandidate.T3M.Search
