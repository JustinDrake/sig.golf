import SigGolfCandidate.Ref.CounterPack

set_option maxRecDepth 8192

/-!
# Aligned signer packing plan

The old pack mixed each 4-byte counter into a layer. The compact 12-byte-tail
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


def lowWord (c0 c1 c2 c3 c4 : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (CounterPack.packDigits [c0,c1,c2,c3,c4] % 2^64)

def highWord (c0 c1 c2 c3 c4 : Nat) : BitVec 64 :=
  BitVec.ofNat 64 ((CounterPack.packDigits [c0,c1,c2,c3,c4] / 2^64) % 2^64)

theorem lowWord_eq_packDigits (c0 c1 c2 c3 c4 : Nat) :
    lowWord c0 c1 c2 c3 c4 =
      BitVec.ofNat 64 (CounterPack.packDigits [c0,c1,c2,c3,c4] % 2^64) := rfl

theorem highWord_eq_packDigits (c0 c1 c2 c3 c4 : Nat) :
    highWord c0 c1 c2 c3 c4 =
      BitVec.ofNat 64 ((CounterPack.packDigits [c0,c1,c2,c3,c4] / 2^64) % 2^64) := rfl

end SigGolfCandidate.Sign.CounterPackLayout
