import SigGolfCandidate.AlternativeCodecAlgorithms

set_option profiler true
set_option profiler.threshold 1000
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace SigGolfCandidate.Base4Candidate.Reference
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal
open SigGolfCandidate.Ref (Val zeros byte le32 slice answerBytes)

theorem witness_charge : (19200 + 255) / 256 = 75 := by decide
theorem witness_end : 2048 + 19200 = 21248 := by decide
theorem layout_room : 21248 ≤ 32768 ∧ 32768 + 131072 ≤ 196608 ∧
    196608 + 7232 < 2 ^ 24 := by decide

/-- The full non-root top-tree cache exactly fills the cache allowance. -/
theorem full_cache_bytes : 32 + 8190*16 = 131072 := by decide
theorem full_cache_mac : (32+32+131040+63)/64 = 2049 := by decide
theorem full_cache_keygen : 4096*234-1+8190+2049 = 968702 := by decide
theorem full_cache_keygen_room : 968702 < 2^20 := by decide
theorem full_cache_sign : 3*(128*234-1)+17*1279+5+2049+31+110+12 = 113803 := by decide

/-! The acceptance condition reads twelve bits disjoint from the 33 instance
bits and the 153 forest-index bits. This counts a fresh uniform output only;
adaptive freshness and finite-search failures require separate proofs. -/
def checkField (u : BitVec 256) : BitVec 12 :=
  (u.extractLsb' 186 70).extractLsb' 0 12

theorem checkField_toNat (u : BitVec 256) :
    (checkField u).toNat = u.toNat / 2 ^ 186 % 4096 := by
  have hi : u.toNat / 2 ^ 186 < 2 ^ 70 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [← Nat.pow_add] using u.isLt
  simp [checkField, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hi]

theorem digestOK_checkField (u : BitVec 256) :
    digestOK u.toNat = true ↔ checkField u = 0 := by
  simp only [digestOK, decide_eq_true_eq]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    change (checkField u).toNat = 0
    rw [checkField_toNat]
    exact h
  · intro h
    have he := congrArg BitVec.toNat h
    change (checkField u).toNat = 0 at he
    rwa [checkField_toNat] at he

theorem checkField_card :
    (Finset.univ.filter fun u : BitVec 256 => checkField u = 0).card = 2 ^ 244 := by
  change (Finset.univ.filter fun u : BitVec 256 =>
    (fun v : BitVec (256-186) => v.extractLsb' 0 12 = 0) (u.extractLsb' 186 (256-186))).card = _
  rw [SphincsSecurity.Completeness.card_filter_high (n := 256) (w := 186) (by decide)
    (fun v => v.extractLsb' 0 12 = 0),
    SphincsSecurity.Completeness.card_filter_low (n := 70) (w := 12) (by decide) (fun v => v = 0)]
  have hz : (Finset.univ.filter fun d : BitVec 12 => d = 0).card = 1 := by simp
  rw [hz]
  norm_num

theorem fresh_digest_share :
    Pr[fun u : BitVec 256 => checkField u = 0 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = (4096 : ENNReal)⁻¹ := by
  rw [probEvent_uniformSample, checkField_card, Fintype.card_bitVec]
  norm_num

/-! These are search-tail arithmetic lemmas. The adaptive random-oracle proof
must supply their rejection-share premises; independence is not assumed here. -/
theorem digest_tail_arithmetic (x : ENNReal)
    (hx : x + (4097 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 21) ≤ (2⁻¹ : ENNReal) ^ 511 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 4097 (by decide) x hx
  calc
    x ^ (2 ^ 21) ≤ x ^ (4097 * 511) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 4097) ^ 511 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 511 := pow_le_pow_left' hh _

theorem counter_tail_arithmetic (x : ENNReal)
    (hx : x + (2268 : ENNReal)⁻¹ ≤ 1) :
    x ^ (2 ^ 22) ≤ (2⁻¹ : ENNReal) ^ 1024 := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hh := SphincsSecurity.Completeness.pow_le_half_ennreal 2268 (by decide) x hx
  calc
    x ^ (2 ^ 22) ≤ x ^ (2268 * 1024) :=
      pow_le_pow_right_of_le_one' hx1 (by decide)
    _ = (x ^ 2268) ^ 1024 := by rw [pow_mul]
    _ ≤ (2⁻¹ : ENNReal) ^ 1024 := pow_le_pow_left' hh _

/-- The proposed finite searches leave room for a union over every message. -/
theorem all_message_tail_arithmetic :
    (2 : ENNReal) ^ 256 * ((2⁻¹ : ENNReal) ^ 511 +
      4 * (2⁻¹ : ENNReal) ^ 1024) ≤ ((2 : ENNReal) ^ 128)⁻¹ := by
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow]
  norm_num


end SigGolfCandidate.Base4Candidate.Reference
