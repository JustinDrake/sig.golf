import SigGolfCandidate.Ref.CounterPack

/-!
# Expansion of the canonical counter tail

The witness still stores five aligned LE32 counters at `0x20b8 + 4*i`.
The unchanged verifier image reads those words. The expander copies the five
aligned bodies and unpacks the 12-byte tail before returning the witness.
-/

namespace SigGolfCandidate.Expand.CounterUnpackLayout
open SigGolfCandidate.Ref SigGolfCandidate.Legacy

def tailSource : Nat := 0x3300 + CounterPack.tailOffset
def counterDest (lay : Nat) : Nat := 0x20b8 + 4 * lay

/-- `(compact body source, unchanged witness body destination, 4-byte word count)`. -/
def bodyCopies : List (Nat × Nat × Nat) :=
  [(0x3b60, 0x1178, 212), (0x3eb0, 0x14c8, 192),
   (0x41b0, 0x17c8, 192), (0x44b0, 0x1ac8, 192),
   (0x47b0, 0x1dc8, 188)]

/-- Existing copy-loop code can be reused at five aligned body pairs. -/
def bodySetupPCs : List Nat := [171, 182, 193, 204, 215]
def bodyLoopPCs : List Nat := [176, 187, 198, 209, 220]
def tailDecodePC : Nat := 226

/-- The fifth loop already leaves its source and destination registers exactly
at the packed tail and the witness's LE32 counter area. -/
theorem lastBodyPointers :
    0x47b0 + 4 * 188 = tailSource ∧
    0x1dc8 + 4 * 188 = counterDest 0 := by decide

theorem bodyCopies_disjoint :
    bodyCopies.all (fun (src, dst, words) =>
      decide (src % 4 = 0 ∧ dst % 4 = 0 ∧ src + 4 * words ≤ 0x1000000 ∧
        dst + 4 * words ≤ 0x1000000 ∧ dst + 4 * words ≤ src)) = true := by decide

theorem tailSource_eq : tailSource = 0x4aa0 := by decide
theorem counterDest_eq : (List.range nLayers).map counterDest =
    [0x20b8, 0x20bc, 0x20c0, 0x20c4, 0x20c8] := by decide


/-- Machine extracts, including the mixed-radix quotient rank. -/
def unpackWords (lo hi : Nat) : List Nat :=
  [lo % 32768 + 32768 * (hi / 16384 % 17),
   lo / 32768 % 32768 + 32768 * (hi / 16384 / 17 % 17),
   lo / 1073741824 % 32768 + 32768 * (hi / 16384 / 17 / 17 % 17),
   lo / 35184372088832 % 32768 + 32768 * (hi / 16384 / 17 / 17 / 17 % 17),
   lo / 1152921504606846976 + 16 * (hi % 16384) +
     262144 * (hi / 16384 / 17 / 17 / 17 / 17 % 3)]

def canonicalHigh (hi : Nat) : Bool := hi / 16384 < 250563

theorem unpackWords_value (v : Nat) :
    unpackWords (v % 2 ^ 64) (v / 2 ^ 64) = CounterPack.unpackDigits v nLayers := by
  norm_num [unpackWords, CounterPack.unpackDigits, CounterMix.decode, CounterMix.join, nLayers, List.range_succ, List.map_append]
  omega

theorem canonicalHigh_iff (v : Nat) :
    canonicalHigh (v / 2 ^ 64) = true ↔ v < CounterMix.capacity := by
  simp [canonicalHigh, CounterMix.capacity]
  omega

theorem canonicalTail_iff_highHalfword (tail : List Byte)
    (hlen : tail.length = CounterPack.tailBytes) :
    CounterPack.canonicalTail tail = true ↔
      canonicalHigh (CounterPack.tailValue tail / 2^64) = true := by
  rw [CounterPack.canonicalTail_iff, canonicalHigh_iff]
  exact and_iff_right hlen

end SigGolfCandidate.Expand.CounterUnpackLayout
