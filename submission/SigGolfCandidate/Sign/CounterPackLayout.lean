import SigGolfCandidate.Ref.CounterPack

set_option maxRecDepth 8192

/-!
# Aligned signer packing plan

The old pack mixed each 4-byte counter into a layer. The compact 13-byte-tail
format lets the existing staged layer bodies move directly by aligned dwords.
The signer writes the five counters only after these 488 body dwords.
-/

namespace SigGolfCandidate.Sign.CounterPackLayout
open SigGolfCandidate.Ref

def stageCounterOffset (lay : Nat) : Nat := 0x900 + 856 * lay
def stageBodyOffset (lay : Nat) : Nat := stageCounterOffset lay + 8
def signatureBodyOffset (lay : Nat) : Nat := 0x3300 + CounterPack.bodyOffset lay
def signatureTailOffset : Nat := 0x3300 + CounterPack.tailOffset

/-- Each table entry is `(kind=0, aligned stage source, unused)`. -/
def bodyPackTable : List (Nat × Nat × Nat) :=
  (List.range nLayers).flatMap fun lay =>
    (List.range (CounterPack.bodyBytes lay / 8)).map fun j =>
      (0, stageBodyOffset lay + 8 * j, 0)

theorem bodyPackTable_length : bodyPackTable.length = 488 := by decide
theorem signatureTailOffset_eq : signatureTailOffset = 0x4aa0 := by decide
theorem stageBodyOffsets :
    (List.range nLayers).map stageBodyOffset = [0x908, 0xc60, 0xfb8, 0x1310, 0x1668] := by decide
theorem signatureBodyOffsets :
    (List.range nLayers).map signatureBodyOffset =
      [0x3b60, 0x3eb0, 0x41b0, 0x44b0, 0x47b0] := by decide

/-- The low 64 bits of the five 20-bit counters. -/
def lowWord (c0 c1 c2 c3 : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (c0 + 2 ^ 20 * c1 + 2 ^ 40 * c2 + 2 ^ 60 * c3)

/-- Bits 64..99; its upper 28 bits are zero for accepted counters. -/
def highWord (c2 c3 c4 : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (c3 / 2 ^ 4 + 2 ^ 16 * c4)

theorem highWord_value_lt (c2 c3 c4 : Nat)
    (h2 : c2 < CounterPack.radix)
    (h3 : c3 < CounterPack.radix)
    (h4 : c4 < CounterPack.radix) :
    c3 / 2 ^ 4 + 2 ^ 16 * c4 < 2 ^ 36 := by
  norm_num [CounterPack.radix, CounterPack.counterBits] at h2 h3 h4 ⊢
  omega

/-- The two aligned stores in the signer tail split the five-digit value at
bit 64. The top 28 bits of the second store are zero by `highWord_value_lt`. -/
theorem packDigits_five_low (c0 c1 c2 c3 c4 : Nat) :
    CounterPack.packDigits [c0, c1, c2, c3, c4] % 2 ^ 64 =
      (c0 + 2 ^ 20 * c1 + 2 ^ 40 * c2 + 2 ^ 60 * c3) % 2 ^ 64 := by
  norm_num [CounterPack.packDigits, CounterPack.radix, CounterPack.counterBits]
  omega

theorem packDigits_five_high (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < CounterPack.radix)
    (h1 : c1 < CounterPack.radix)
    (h2 : c2 < CounterPack.radix) :
    CounterPack.packDigits [c0, c1, c2, c3, c4] / 2 ^ 64 =
      c3 / 2 ^ 4 + 2 ^ 16 * c4 := by
  norm_num [CounterPack.packDigits, CounterPack.radix, CounterPack.counterBits] at h0 h1 h2 ⊢
  omega

/-- The value written by the first aligned store is the low machine word of
the canonical five-digit encoding. -/
theorem lowWord_eq_packDigits (c0 c1 c2 c3 c4 : Nat) :
    lowWord c0 c1 c2 c3 =
      BitVec.ofNat 64 (CounterPack.packDigits [c0, c1, c2, c3, c4] % 2 ^ 64) := by
  rw [packDigits_five_low]
  apply BitVec.eq_of_toNat_eq
  simp only [lowWord, BitVec.toNat_ofNat, Nat.mod_mod]

/-- Accepted counter bounds make the second store the upper machine word of
the same five-digit encoding. -/
theorem highWord_eq_packDigits (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < CounterPack.radix)
    (h1 : c1 < CounterPack.radix)
    (h2 : c2 < CounterPack.radix) :
    highWord c2 c3 c4 =
      BitVec.ofNat 64
        ((CounterPack.packDigits [c0, c1, c2, c3, c4] / 2 ^ 64) % 2 ^ 64) := by
  rw [packDigits_five_high c0 c1 c2 c3 c4 h0 h1 h2]
  apply BitVec.eq_of_toNat_eq
  simp only [highWord, BitVec.toNat_ofNat, Nat.mod_mod]

end SigGolfCandidate.Sign.CounterPackLayout
