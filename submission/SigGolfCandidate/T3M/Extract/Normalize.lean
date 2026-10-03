import SigGolfCandidate.T3M.Bytes

/-! Reference-key normalization, never a normalization of the HASH query itself.
Only a chain's first-byte discriminator permits the upper header doubleword to be ignored. -/
namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3

/-- A role-specific reference key. The first header byte is input byte16. -/
def canonicalHeader (hdr : HashInput) : HashInput :=
  if 128 ≤ (hdr.getD 0 0).toNat then hdr.take 8 ++ List.replicate 8 0 else hdr

@[simp] theorem canonicalHeader_unmarked (hdr : HashInput) (h : ¬128 ≤ (hdr.getD 0 0).toNat) :
    canonicalHeader hdr = hdr := by
  unfold canonicalHeader
  rw [if_neg h]

/-- Arbitrary high header bytes are ignored for references, not removed from queries. -/
theorem canonicalHeader_marked (low pad : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = low ++ List.replicate 8 0 := by
  have hm : 128 ≤ ((low ++ pad).getD 0 0).toNat := by
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hmark
  unfold canonicalHeader
  rw [if_pos hm]
  simp [List.take_append, hlen]

theorem canonicalHeader_pad_irrelevant (low pad pad' : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = canonicalHeader (low ++ pad') := by
  rw [canonicalHeader_marked low pad hlen hmark, canonicalHeader_marked low pad' hlen hmark]

/-- Canonicalization leaves an already-zero chain header pad unchanged. -/
theorem canonicalHeader_zero_pad (low : HashInput) (hlen : low.length = 8) :
    canonicalHeader (low ++ List.replicate 8 0) = low ++ List.replicate 8 0 := by
  by_cases hm : 128 ≤ (low.getD 0 0).toNat
  · exact canonicalHeader_marked low _ hlen hm
  · apply canonicalHeader_unmarked
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hm

end SigGolfCandidate.T3M.Extract
