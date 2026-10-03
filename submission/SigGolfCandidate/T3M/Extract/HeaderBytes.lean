import SigGolfCandidate.T3M.Extract.Normalize

namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false

/-- Serialization of the two header doublewords, low word first. -/
theorem bytesLE_header_words (high low : BitVec 64) :
    bytesLE 16 (high ++ low) = bytesLE 8 low ++ bytesLE 8 high := by
  apply readLE_inj (by simp [bytesLE_length])
  rw [readLE_bytesLE, readLE_append, readLE_bytesLE, readLE_bytesLE, bytesLE_length]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]
  omega

theorem bytesLE8_marker (low : BitVec 64) :
    ((bytesLE 8 low).getD 0 0).toNat = low.toNat % 256 := by
  simp [bytesLE, List.getD_eq_getElem?_getD, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem bytesLE16_marker (hdr : BitVec 128) :
    ((bytesLE 16 hdr).getD 0 0).toNat = hdr.toNat % 256 := by
  simp [bytesLE, List.getD_eq_getElem?_getD, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem canonicalHeader_words (high low : BitVec 64)
    (hm : 128 ≤ low.toNat % 256) :
    canonicalHeader (bytesLE 16 (high ++ low)) = bytesLE 8 low ++ List.replicate 8 0 := by
  rw [bytesLE_header_words]
  apply canonicalHeader_marked _ _ (bytesLE_length _ _)
  simpa only [bytesLE8_marker] using hm

theorem canonicalHeader_high_irrelevant (high high' low : BitVec 64)
    (hm : 128 ≤ low.toNat % 256) :
    canonicalHeader (bytesLE 16 (high ++ low)) =
      canonicalHeader (bytesLE 16 (high' ++ low)) := by
  rw [canonicalHeader_words high low hm, canonicalHeader_words high' low hm]

theorem canonicalHeader_high_zero (hdr : BitVec 128) (hz : hdr.extractLsb' 64 64 = 0) :
    canonicalHeader (bytesLE 16 hdr) = bytesLE 16 hdr := by
  have he : hdr = (0#64 ++ hdr.extractLsb' 0 64) := by
    have h := (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
    rw [hz] at h
    exact h
  rw [he, bytesLE_header_words]
  have hzero : bytesLE 8 (0#64) = List.replicate 8 0 := by decide +kernel
  rw [hzero]
  exact canonicalHeader_zero_pad _ (bytesLE_length _ _)

theorem canonicalHeader_marker_ne (hdr : BitVec 128)
    (hm : hdr.toNat % 256 < 128) :
    canonicalHeader (bytesLE 16 hdr) = bytesLE 16 hdr := by
  apply canonicalHeader_unmarked
  rw [bytesLE16_marker]
  omega

end SigGolfCandidate.T3M.Extract
