import SigGolfCandidate.AlternativeMachineBasics

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal


namespace SigGolfCandidate.Base4Candidate.SwarProof
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

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
  ac_rfl

end SigGolfCandidate.Base4Candidate.SwarProof

