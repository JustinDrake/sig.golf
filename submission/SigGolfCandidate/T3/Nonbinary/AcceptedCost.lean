import SigGolfCandidate.T3.Nonbinary.SourceEncoding
import SigGolfCandidate.T3.Nonbinary.Cost

namespace SigGolfCandidate.T3.Nonbinary
open SigGolfResearch.NonbinaryTop

/-- An actually accepted top word has a canonical mixed-radix representation
and at least eleven digits eligible for the terminal-store saving. -/
theorem decode_top_credit {value : Digest} {digits : List Nat}
    (h : T3.decode 0 value = some digits) :
    ∃ w : Codec.Word, Decoder.decodeBV value = some w ∧ digits = wordDigits w ∧
      Counting.weight w = 126 ∧ 11 ≤ Cost.credit w := by
  rw [decode_top_eq_map] at h
  cases hw : Decoder.decodeBV value with
  | none => simp [hw] at h
  | some w =>
    have hd : wordDigits w = digits := by simpa only [hw,Option.map_some,Option.some.injEq] using h
    have hs := (Decoder.decode_some_iff value.toFin w).mp hw
    exact ⟨w, rfl, hd.symm, hs.2, Cost.accepted_credit_ge_eleven w hs.2⟩

end SigGolfCandidate.T3.Nonbinary
#print axioms SigGolfCandidate.T3.Nonbinary.decode_top_credit
