import SigGolfCandidate.Sign.CounterPackLayout
import SigGolfCandidate.Keygen.State

namespace SigGolfCandidate.Sign.CounterMixWords
open SigGolfCandidate.Ref
abbrev W := BitVec 64

def rankW (a b c d e : W) : W :=
  ((((e >>> 18) * 17 + (d >>> 15)) * 17 + (c >>> 15)) * 17 + (b >>> 15)) * 17 + (a >>> 15)
def lowW (a b c d e : W) : W :=
  ((((a &&& 32767) + ((b &&& 32767) <<< 15)) + ((c &&& 32767) <<< 30)) +
    ((d &&& 32767) <<< 45)) + ((e &&& 262143) <<< 60)
def highW (a b c d e : W) : W :=
  (rankW a b c d e <<< 14) + ((e &&& 262143) >>> 4)
def okW (a b c d e : W) : W :=
  ((((if a.toNat < 557056 then 1 else 0) &&& (if b.toNat < 557056 then 1 else 0)) &&&
    (if c.toNat < 557056 then 1 else 0)) &&& (if d.toNat < 557056 then 1 else 0)) &&&
    (if e.toNat < 786432 then 1 else 0)
def outLow (a b c d e : W) : W := lowW a b c d e ||| (okW a b c d e - 1)
def outHigh (a b c d e : W) : W :=
  (highW a b c d e ||| (okW a b c d e - 1)) <<< 32 >>> 32

theorem andMask (a k : Nat) (hk : k ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2^k-1) = BitVec.ofNat 64 (a % 2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hm : 2^k-1 < 2^64 := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
    omega
  rw [Nat.mod_eq_of_lt hm, Nat.and_two_pow_sub_one_eq_mod]
  have hd : 2^k ∣ 2^64 := Nat.pow_dvd_pow 2 hk
  rw [Nat.mod_mod_of_dvd _ hd]
  exact (Nat.mod_eq_of_lt ((Nat.mod_lt _ (by positivity)).trans_le
    (Nat.pow_le_pow_right (by decide) hk))).symm

theorem rankW_eq (a b c d e : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (hd : d < 2^64) (he : e < 2^64) :
    rankW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) = BitVec.ofNat 64 (CounterMix.rank a b c d e) := by
  unfold rankW
  rw [Keygen.ofNat_shr _ _ ha, Keygen.ofNat_shr _ _ hb, Keygen.ofNat_shr _ _ hc,
    Keygen.ofNat_shr _ _ hd, Keygen.ofNat_shr _ _ he]
  change ((((BitVec.ofNat 64 (e / 2^18) * BitVec.ofNat 64 17 + BitVec.ofNat 64 (d / 2^15)) *
    BitVec.ofNat 64 17 + BitVec.ofNat 64 (c / 2^15)) * BitVec.ofNat 64 17 + BitVec.ofNat 64 (b / 2^15)) *
    BitVec.ofNat 64 17 + BitVec.ofNat 64 (a / 2^15)) = _
  simp only [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  simp only [CounterMix.rank, CounterMix.join]
  ring

theorem lowW_eq (a b c d e : Nat) :
    lowW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) = BitVec.ofNat 64 (CounterMix.low a b c d e) := by
  unfold lowW
  change ((((BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2^15-1)) +
    ((BitVec.ofNat 64 b &&& BitVec.ofNat 64 (2^15-1)) <<< 15)) +
    ((BitVec.ofNat 64 c &&& BitVec.ofNat 64 (2^15-1)) <<< 30)) +
    ((BitVec.ofNat 64 d &&& BitVec.ofNat 64 (2^15-1)) <<< 45)) +
    ((BitVec.ofNat 64 e &&& BitVec.ofNat 64 (2^18-1)) <<< 60) = _
  simp only [andMask _ 15 (by decide), andMask _ 18 (by decide), Keygen.ofNat_shl,
    ← BitVec.ofNat_add]
  congr 1
  simp only [CounterMix.low, CounterMix.join]
  ring

theorem raw_div64 (a b c d e : Nat) :
    CounterMix.raw a b c d e / 2^64 =
      16384 * CounterMix.rank a b c d e + (e % 262144) / 16 := by
  unfold CounterMix.raw CounterMix.low CounterMix.join
  omega

theorem raw_mod64 (a b c d e : Nat) :
    CounterMix.raw a b c d e % 2^64 = CounterMix.low a b c d e % 2^64 := by
  unfold CounterMix.raw
  omega

theorem highW_eq (a b c d e : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (hd : d < 2^64) (he : e < 2^64) :
    highW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) = BitVec.ofNat 64 (CounterMix.raw a b c d e / 2^64) := by
  unfold highW
  rw [rankW_eq a b c d e ha hb hc hd he]
  change _ + ((BitVec.ofNat 64 e &&& BitVec.ofNat 64 (2^18-1)) >>> 4) = _
  rw [andMask _ 18 (by decide), Keygen.ofNat_shr _ _ (by omega), Keygen.ofNat_shl,
    ← BitVec.ofNat_add, raw_div64]
  congr 1
  norm_num
  omega

theorem flag_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) : W) &&& (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

theorem okW_eq (a b c d e : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (hd : d < 2^64) (he : e < 2^64) :
    okW (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) =
      if CounterPack.Fits [a,b,c,d,e] then 1 else 0 := by
  simp only [okW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he, flag_and]
  simp [CounterPack.Fits, and_assoc]

theorem outLow_eq (a b c d e : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (hd : d < 2^64) (he : e < 2^64) :
    outLow (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) = CounterPackLayout.lowWord a b c d e := by
  rw [outLow, okW_eq a b c d e ha hb hc hd he, lowW_eq]
  unfold CounterPackLayout.lowWord CounterPack.packDigits
  split
  next h =>
    simp only [BitVec.sub_self, BitVec.or_zero]
    simp only [List.getD_cons_zero, List.getD_cons_succ, raw_mod64]
    apply BitVec.eq_of_toNat_eq
    simp
  next h =>
    change _ ||| BitVec.allOnes 64 = BitVec.ofNat 64 (CounterMix.reserved % 2^64)
    rw [BitVec.or_allOnes]
    decide

theorem outHigh_eq (a b c d e : Nat)
    (ha : a < 2^64) (hb : b < 2^64) (hc : c < 2^64) (hd : d < 2^64) (he : e < 2^64) :
    outHigh (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c)
      (BitVec.ofNat 64 d) (BitVec.ofNat 64 e) = CounterPackLayout.highWord a b c d e := by
  rw [outHigh, okW_eq a b c d e ha hb hc hd he, highW_eq a b c d e ha hb hc hd he]
  unfold CounterPackLayout.highWord CounterPack.packDigits
  split
  next h =>
    simp only [BitVec.sub_self, BitVec.or_zero, List.getD_cons_zero, List.getD_cons_succ]
    have hf : CounterPack.Fits [a,b,c,d,e] := h
    simp only [CounterPack.Fits, List.length_cons, List.length_nil, List.getD_cons_zero,
      List.getD_cons_succ] at hf
    have hv := CounterMix.raw_lt a b c d e hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2
    have hw : CounterMix.raw a b c d e / 2^64 < 2^32 := by
      have := CounterMix.capacity_lt
      omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    omega
  next h =>
    change (_ ||| BitVec.allOnes 64) <<< 32 >>> 32 =
      BitVec.ofNat 64 ((CounterMix.reserved / 2^64) % 2^64)
    rw [BitVec.or_allOnes]
    decide

end SigGolfCandidate.Sign.CounterMixWords
