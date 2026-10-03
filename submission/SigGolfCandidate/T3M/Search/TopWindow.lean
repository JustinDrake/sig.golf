import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
def topWindow (v : Digest) (j : Nat) : Word :=
  if j < 9 then v.extractLsb' 0 64 >>> (7 * j)
  else v.extractLsb' 63 64 >>> (7 * (j - 9))
theorem topWindow_rank (v : Digest) (j : Nat) (hj : j < 17) :
    topWindow v j &&& 127#64 = BitVec.ofNat 64 (topRank v j) := by
  unfold topWindow topRank
  split_ifs with h
  · simpa using ext_shr_mask v 0 (7 * j) 7 (by omega)
  · have he := ext_shr_mask v 63 (7 * (j - 9)) 7 (by omega)
    rw [show 63 + 7 * (j - 9) = 7 * j by omega] at he
    exact he
theorem topWindow_cross (v : Digest) :
    v.extractLsb' 64 64 <<< 1 ||| v.extractLsb' 0 64 >>> 63 = v.extractLsb' 63 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb']
  by_cases h : i = 0
  · subst h; simp
  · have ha : ¬ 63 + i < 64 := by omega
    have hb : ¬ i < 1 := by omega
    simp only [ha, hb, decide_false, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false]
    have hc : 64 + (i - 1) = 63 + i := by omega
    simp only [hc, hi, show i - 1 < 64 by omega, decide_true, Bool.true_and]
theorem topWindow_shift (v : Digest) (j : Nat) (hj : j < 17) (hcross : j ≠ 8) :
    topWindow v j >>> 7 = topWindow v (j + 1) := by
  unfold topWindow
  by_cases h : j < 8
  · rw [if_pos (by omega), if_pos (by omega), ← BitVec.shiftRight_add]
    congr 1 <;> omega
  · rw [if_neg (by omega), if_neg (by omega), ← BitVec.shiftRight_add]
    congr 1 <;> omega
theorem topRank_lt (v : Digest) (j : Nat) : topRank v j < 128 := by unfold topRank; omega
theorem topRank_ptr (v : Digest) (j : Nat) (hj : j < 17) :
    (topWindow v j &&& 127#64) + BitVec.ofNat 64 TOP_DATA = BitVec.ofNat 64 (TOP_DATA + topRank v j) := by
  rw [topWindow_rank v j hj, ofNat_add_ofNat]
  congr 1
  omega
end SigGolfCandidate.T3M.Search
