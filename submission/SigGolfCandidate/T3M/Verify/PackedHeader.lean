import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Witness.VerifyP
import SigGolfCandidate.T3.PackedChain

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def packedHi (lay : Layer) (tree leaf : Nat) : Nat :=
  (tree * 2 ^ height lay + leaf) % 2 ^ 32 + lay.val * 2 ^ 32 + 193 * 2 ^ 40
def packedPrefix (lay : Layer) (tree leaf : Nat) : Nat := 128 + 2 ^ 16 * packedHi lay tree leaf
theorem packedHi_lt (lay : Layer) (tree leaf : Nat) : packedHi lay tree leaf < 2 ^ 48 := by
  have hr := Nat.mod_lt (tree * 2 ^ height lay + leaf) (by norm_num : 0 < 2 ^ 32)
  have hl := lay.isLt
  unfold packedHi
  omega
theorem packedWord_lt (lay : Layer) (tree leaf i m : Nat) (hi : i < 128) (hm : m < 256) :
    i + 256 * m + packedPrefix lay tree leaf < 2 ^ 64 := by
  have hh := packedHi_lt lay tree leaf
  unfold packedPrefix
  omega
theorem extract64_of_eq (x : BitVec 128) (n : Nat) (h : x = BitVec.ofNat 128 n) :
    x.extractLsb' 0 64 = BitVec.ofNat 64 n := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_zero, Nat.div_one]
  exact Nat.mod_mod_of_dvd _ (by norm_num)
theorem chainHeader_low_bounded (lay : Layer) (tree leaf i m : Nat) (hi : i < 64) (hm : m < 8)
    (ht : tree < 2 ^ (31 - height lay)) (hl : leaf < 2 ^ height lay) :
    (chainHeader lay tree leaf i m).extractLsb' 0 64 =
      BitVec.ofNat 64 (i + 256 * m + packedPrefix lay tree leaf) := by
  have hr : tree * 2 ^ height lay + leaf < 2 ^ 31 := by
    fin_cases lay <;> norm_num [height] at ht hl ⊢ <;> omega
  apply extract64_of_eq
  exact (chainHeader_actual lay tree leaf i m hr hl hi hm).trans
    (congrArg (BitVec.ofNat 128) (by
      unfold packedPrefix packedHi
      rw [Nat.mod_eq_of_lt (show tree * 2 ^ height lay + leaf < 2 ^ 32 by omega)]
      ring))
theorem wordsOf_chainInputP (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest)
    (headerPad : Word) (v : Digest) :
    wordsOf (chainInputP lay tree leaf i step p0 p1 headerPad v) =
      [p0.extractLsb' 0 64, p0.extractLsb' 64 64,
        (chainHeader lay tree leaf i step).extractLsb' 0 64, headerPad,
        p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInputP
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  have hlo : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 0 64 =
      (chainHeader lay tree leaf i step).extractLsb' 0 64 := BitVec.extractLsb'_append_eq_right
  have hhi : (chainHeaderP lay tree leaf i step headerPad).extractLsb' 64 64 = headerPad :=
    BitVec.extractLsb'_append_eq_left
  rw [hlo, hhi]
  rfl
theorem chainInputP_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 : Digest)
    (headerPad : Word) (v : Digest) :
    (chainInputP lay tree leaf i step p0 p1 headerPad v).length = 64 * (0 + 1) := by
  simp only [chainInputP, List.length_append, SphincsSecurity.bytesLE_length]
end SigGolfCandidate.T3M
