import SigGolfCandidate.Ref.CounterPack

/-!
# Expansion of the canonical counter tail

The witness still stores five aligned LE32 counters at `0x20b8 + 4*i`.
The unchanged verifier image reads those words. The expander copies the five
aligned bodies and unpacks the 13-byte tail before returning the witness.
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

/-- Decode the five counters from an aligned 64-bit low word and a 40-bit high word. -/
def unpackWords (lo hi : Nat) : List Nat :=
  [lo % 2 ^ 20,
   lo / 2 ^ 20 % 2 ^ 20,
   lo / 2 ^ 40 % 2 ^ 20,
   (lo / 2 ^ 60 + (hi % 2 ^ 16) * 2 ^ 4) % 2 ^ 20,
   hi / 2 ^ 16 % 2 ^ 20]

/-- The four unused bits of the final halfword must be zero. -/
def canonicalHigh (hi : Nat) : Bool := hi < 2 ^ 36

/-- The decoder's three register extracts are the five base-`2^20` digits of
the original 104-bit tail value. The statement permits noncanonical high bits;
the separate branch check rejects them. -/
theorem unpackWords_value (v : Nat) :
    unpackWords (v % 2 ^ 64) (v / 2 ^ 64) = CounterPack.unpackDigits v nLayers := by
  norm_num [unpackWords, CounterPack.unpackDigits, CounterPack.radix,
    CounterPack.counterBits, nLayers]
  omega

/-- The high-half comparison is exactly the 100-bit canonicality bound. -/
theorem canonicalHigh_iff (v : Nat) :
    canonicalHigh (v / 2 ^ 64) = true ↔ v < 2 ^ 100 := by
  simp [canonicalHigh]
  omega

/-- The final byte has four unused high bits. -/
theorem canonicalTail_iff_highHalfword (tail : List Byte)
    (hlen : tail.length = CounterPack.tailBytes) :
    CounterPack.canonicalTail tail = true ↔
      (tail.getD 12 0).toNat / 2 ^ 4 = 0 := by
  rw [CounterPack.canonicalTail_iff]
  norm_num
  omega

end SigGolfCandidate.Expand.CounterUnpackLayout
