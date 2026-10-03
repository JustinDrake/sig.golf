import SigGolfCandidate.T3M.Verify.Nonbinary.PairAlgebra
import SigGolfCandidate.T3M.Search.TopWindow

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option Elab.async false

def pairRank (v : Digest) (q : Nat) : Nat := v.toNat / 2 ^ (7 * q) % 16384

theorem pairRank_lt (v : Digest) (q : Nat) : pairRank v q < 16384 := by unfold pairRank; omega

theorem pairRank_components (v : Digest) (q : Nat) :
    pairRank v q = topRank v q + 128 * topRank v (q+1) := by
  unfold pairRank topRank
  rw [show 7 * (q + 1) = 7 * q + 7 by omega, Nat.pow_add]
  norm_num
  rw [← Nat.div_div_eq_div_mul, show 16384 = 128 * 128 by rfl, Nat.mod_mul]

theorem pairWindow_rank (v : Digest) (q : Nat) (hq : q < 8 ∨ (9 ≤ q ∧ q < 16)) :
    topWindow v q &&& 16383#64 = BitVec.ofNat 64 (pairRank v q) := by
  unfold topWindow pairRank
  split_ifs with h
  · simpa using ext_shr_mask v 0 (7 * q) 14 (by omega)
  · have he := ext_shr_mask v 63 (7 * (q - 9)) 14 (by omega)
    rw [show 63 + 7 * (q - 9) = 7 * q by omega] at he
    exact he

theorem pairWindow_shift (v : Digest) (q : Nat) (hq : q < 7 ∨ 9 ≤ q) :
    topWindow v q >>> 14 = topWindow v (q + 2) := by
  unfold topWindow
  by_cases h : q < 7
  · rw [if_pos (by omega),if_pos (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega
  · rw [if_neg (by omega),if_neg (by omega),← BitVec.shiftRight_add]
    congr 1 <;> omega

theorem pairLookup_pairRank (v : Digest) (q : Nat) :
    pairLookup (pairRank v q) = pairWeight (topRank v q) (topRank v (q+1)) := by
  rw [pairRank_components,pairLookup_components _ _ (topRank_lt v q)]

end SigGolfCandidate.T3M.Verify.Nonbinary
