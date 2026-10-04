import SigGolfCandidate.W9Machine.WctV3Source
import SigGolfCandidate.T3M.Verify.PackedHeader

set_option autoImplicit false
namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv SigGolfCandidate.T3
open SphincsSecurity (bytesLE)
theorem wordsOf_bytesLE8 (x : BitVec 64) : wordsOf (bytesLE 8 x) = [x] := by
  simpa using wordsOf_bytesLE 1 x
theorem chainInput_length (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) : (V3.chainInput index coord child chain step a b c value).length = 64 := by
  simp [V3.chainInput, SphincsSecurity.bytesLE_length]
theorem wordsOf_chainInput (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) : wordsOf (V3.chainInput index coord child chain step a b c value) =
      [a.extractLsb' 0 64, a.extractLsb' 64 64,
       BitVec.ofNat 64 (V3.chainLow index coord child chain step), b,
       c.extractLsb' 0 64, c.extractLsb' 64 64,
       value.extractLsb' 0 64, value.extractLsb' 64 64] := by
  unfold V3.chainInput
  rw [wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [List.length_append, SphincsSecurity.bytesLE_length])]
  rw [wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE8, wordsOf_bytesLE8]
  rfl
end W9Machine
