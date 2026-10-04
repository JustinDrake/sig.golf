import SigGolfCandidate.T3M.Bytes

namespace SigGolfCandidate.T3M.Keygen.Packed
open SigGolfCandidate.T3 (Layer Digest height chainHeader chainInput zero16 pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem wordsOf_chainInput (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (chainInput lay tree leaf i step v) =
      [0, 0, (chainHeader lay tree leaf i step).extractLsb' 0 64,
        (chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [zero16]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl
theorem query_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  have hl : (chainInput lay tree leaf i step v).length = 64 := by
    simp [chainInput, bytesLE_length, zero16]
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; omega, by rw [hl]⟩, hl]
end SigGolfCandidate.T3M.Keygen.Packed
