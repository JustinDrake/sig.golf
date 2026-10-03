import SigGolfCandidate.T3.Core
import SigGolfCandidate.T3.Nonbinary.Codec

namespace SigGolfCandidate.T3.Nonbinary
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem coreDigit_le (lay : Layer) (value : Digest) (i : Nat) :
    coreDigit lay value i ≤  maxDigit lay i := by
  unfold coreDigit maxDigit
  split_ifs
  all_goals have h := Nat.mod_lt (value.toNat / 2 ^ (3*i)) (by decide : 0<8)
  all_goals first | exact Nat.le_pred_of_lt (Nat.mod_lt _ (by decide)) | omega

theorem maxDigit_lt_pow_width (lay : Layer) (i : Nat) : maxDigit lay i<2^width lay i := by
  by_cases hl : lay=0
  · subst lay
    by_cases hi : i<51
    · simp [maxDigit,width,hi,show ¬51 ≤ i by omega]
    · simp [maxDigit,width,hi,show 51 ≤ i by omega]
  · simp [maxDigit,width,hl]

theorem dataDigits_getD (lay : Layer) (value : Digest) (i : Nat) (hi : i<dataCount lay) :
    (dataDigits lay value).getD i 0=coreDigit lay value i := by
  simp [dataDigits,List.getD_eq_getElem,hi]

theorem top_rank_lt (v : Digest) (h : topRanksValid v=true) (j : Nat) (hj : j<17) :
    v.toNat/2^(7*j)%128<125 := by
  have hh := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  exact of_decide_eq_true hh

theorem top_core_triple (v : Digest) (j k : Nat) (hj : j<17) (hk : k<3) :
    coreDigit 0 v (3*j+k)=(v.toNat/2^(7*j)%128)/5^k%5 := by
  have hi : 3*j+k<51 := by omega
  have hd : (3*j+k)/3=j := by omega
  have hm : (3*j+k)%3=k := by omega
  simp [coreDigit,hi,hd,hm]

theorem top_rank_eq {a b : Digest} (h : dataDigits 0 a=dataDigits 0 b)
    (ha : topRanksValid a=true) (hb : topRanksValid b=true) (j : Nat) (hj : j<17) :
    a.toNat/2^(7*j)%128=b.toNat/2^(7*j)%128 := by
  have hpos (k : Nat) (hk : k<3) :
      (a.toNat/2^(7*j)%128)/5^k%5=(b.toNat/2^(7*j)%128)/5^k%5 := by
    have hi : 3*j+k<dataCount 0 := by change 3*j+k<54;omega
    have hh := congrArg (fun xs : List Nat => xs.getD (3*j+k) 0) h
    simpa only [dataDigits_getD 0 a _ hi,dataDigits_getD 0 b _ hi,
      top_core_triple _ _ _ hj hk] using hh
  have h0 := hpos 0 (by decide)
  have h1 := hpos 1 (by decide)
  have h2 := hpos 2 (by decide)
  have hla := top_rank_lt a ha j hj
  have hlb := top_rank_lt b hb j hj
  norm_num only [Nat.reducePow,Nat.div_one] at h0 h1 h2
  omega

theorem top_digest_injective {a b : Digest} (h : dataDigits 0 a=dataDigits 0 b)
    (ha : topRanksValid a=true) (hb : topRanksValid b=true)
    (hla : a.toNat<2^125) (hlb : b.toNat<2^125) : a=b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit _
  by_cases hbit : bit<125
  · by_cases hfirst : bit<119
    · have hj : bit/7<17 := by omega
      have he : a.extractLsb' (7*(bit/7)) 7=b.extractLsb' (7*(bit/7)) 7 := by
        apply BitVec.eq_of_toNat_eq
        simpa only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,
          show (2:Nat)^7=128 by decide] using top_rank_eq h ha hb (bit/7) hj
      have hh := congrArg (fun d : BitVec 7 => d.getLsbD (bit%7)) he
      simpa only [BitVec.getLsbD_extractLsb',show bit%7<7 by omega,decide_true,
        Bool.true_and,show 7*(bit/7)+bit%7=bit by omega] using hh
    · have hi : 51+(bit-119)/2<dataCount 0 := by change _<54;omega
      have he := congrArg (fun xs : List Nat => xs.getD (51+(bit-119)/2) 0) h
      rw [dataDigits_getD 0 a _ hi,dataDigits_getD 0 b _ hi] at he
      have hex : a.extractLsb' (119+2*((bit-119)/2)) 2=
          b.extractLsb' (119+2*((bit-119)/2)) 2 := by
        apply BitVec.eq_of_toNat_eq
        simpa [coreDigit,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow] using he
      have hh := congrArg (fun d : BitVec 2 => d.getLsbD ((bit-119)%2)) hex
      simpa only [BitVec.getLsbD_extractLsb',show (bit-119)%2<2 by omega,decide_true,
        Bool.true_and,show 119+2*((bit-119)/2)+(bit-119)%2=bit by omega] using hh
  · have hla' := (BitVec.toNat_lt_iff_getLsbD_eq_false 125 (by decide : 125<128)).mp hla
    have hlb' := (BitVec.toNat_lt_iff_getLsbD_eq_false 125 (by decide : 125<128)).mp hlb
    have he : 125+(bit-125)=bit := by omega
    simpa only [he] using (hla' (bit-125)).trans (hlb' (bit-125)).symm

end SigGolfCandidate.T3.Nonbinary
