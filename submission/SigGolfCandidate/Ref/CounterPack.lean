import SigGolfCandidate.Ref.CounterMix

/-! # A canonical twelve-byte counter tail

The witness retains five 32-bit counters. Compact signatures admit counter caps
557056 on layers 0–3 and 786432 on layer 4. The checked mixed-radix codec uses 96 bits.
Out-of-range tuples map to the reserved all-one tail, which expansion rejects.
-/

namespace SigGolfCandidate.Ref.CounterPack
open SigGolfCandidate.Ref
open SigGolfCandidate.Legacy

/-- Exact per-layer range admitted by the compact mixed-radix representation. -/
def counterCap (lay : Nat) : Nat := if 4 ≤ lay then 786432 else 557056

def counterBits : Nat := 20
def radix : Nat := 2 ^ counterBits
def tailBytes : Nat := 12

/-- Bytes occupied by one layer's chain values and authentication path. -/
def bodyBytes (lay : Nat) : Nat := 16 * nChains + 16 * height lay

/-- The bodies stay naturally aligned; the packed counter tail follows them. -/
def bodyOffset (lay : Nat) : Nat :=
  16 + 16 * (porsK + porsM) + ((List.range lay).map bodyBytes).sum

def tailOffset : Nat := bodyOffset nLayers
def packedSigBytes : Nat := tailOffset + tailBytes

theorem bodyOffsets :
    (List.range nLayers).map bodyOffset = [2144, 2992, 3760, 4528, 5296] := by decide
theorem bodyLengths :
    (List.range nLayers).map bodyBytes = [848, 768, 768, 768, 752] := by decide
theorem tailOffset_eq : tailOffset = 6048 := by decide
theorem packedSigBytes_eq : packedSigBytes = 6060 := by decide

/-- Exactly five counters in the per-layer ranges of the compact codec. -/
def Fits (cs : List Nat) : Prop :=
  cs.length = 5 ∧ cs.getD 0 0 < 557056 ∧ cs.getD 1 0 < 557056 ∧
    cs.getD 2 0 < 557056 ∧ cs.getD 3 0 < 557056 ∧ cs.getD 4 0 < 786432

instance fitsDecidable (cs : List Nat) : Decidable (Fits cs) :=
  inferInstanceAs (Decidable (cs.length = 5 ∧ cs.getD 0 0 < 557056 ∧ cs.getD 1 0 < 557056 ∧
    cs.getD 2 0 < 557056 ∧ cs.getD 3 0 < 557056 ∧ cs.getD 4 0 < 786432))

theorem fits_iff (cs : List Nat) : Fits cs ↔
    cs.length = nLayers ∧ ∀ i, i < nLayers → cs.getD i 0 < counterCap i := by
  constructor
  · rintro ⟨hlen, h0, h1, h2, h3, h4⟩
    refine ⟨hlen, ?_⟩
    intro i hi
    change i < 5 at hi
    interval_cases i <;> simp [counterCap] <;> assumption
  · rintro ⟨hlen, h⟩
    exact ⟨hlen, h 0 (by decide), h 1 (by decide), h 2 (by decide),
      h 3 (by decide), h 4 (by decide)⟩

/-- Total encoding: an unrepresentable tuple receives the explicitly rejected tail. -/
def packDigits (cs : List Nat) : Nat :=
  if Fits cs then CounterMix.raw (cs.getD 0 0) (cs.getD 1 0) (cs.getD 2 0) (cs.getD 3 0) (cs.getD 4 0)
  else CounterMix.reserved

/-- Decode only the requested finite prefix; indices beyond the fifth decode to zero. -/
def unpackDigits (v n : Nat) : List Nat := (List.range n).map (CounterMix.decode v)

def packTail (counters : List Nat) : List Byte :=
  toList (n := 12) (BitVec.ofNat (8 * 12) (packDigits counters))

def tailValue (tail : List Byte) : Nat := leNat tail
def unpackTail (tail : List Byte) : List Nat := unpackDigits (tailValue tail) nLayers
def unpackCounter (tail : List Byte) (lay : Nat) : Nat := (unpackTail tail).getD lay 0

/-- Reserved high ranks, including the all-one marker, are rejected. -/
def canonicalTail (tail : List Byte) : Bool :=
  (tail.length == tailBytes) && (tailValue tail < CounterMix.capacity)

theorem canonicalTail_iff (tail : List Byte) :
    canonicalTail tail = true ↔ tail.length = tailBytes ∧ tailValue tail < CounterMix.capacity := by
  simp [canonicalTail]

theorem length_packTail (cs : List Nat) : (packTail cs).length = tailBytes := by
  simp [packTail, tailBytes, toList, SigGolfCandidate.Legacy.bytes]

theorem packDigits_lt (cs : List Nat) : packDigits cs < 2 ^ 96 := by
  unfold packDigits
  split
  next h =>
    exact (CounterMix.raw_lt _ _ _ _ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2).trans
      CounterMix.capacity_lt
  next h => decide

theorem packDigits_lt_capacity (cs : List Nat) (h : Fits cs) :
    packDigits cs < CounterMix.capacity := by
  rw [packDigits, if_pos h]
  exact CounterMix.raw_lt _ _ _ _ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

theorem length_unpackDigits (v n : Nat) : (unpackDigits v n).length = n := by
  simp [unpackDigits]

theorem length_unpackTail (tail : List Byte) : (unpackTail tail).length = nLayers :=
  length_unpackDigits _ _

theorem unpackDigits_fits (v : Nat) : Fits (unpackDigits v nLayers) := by
  change 5 = 5 ∧ CounterMix.decode v 0 < 557056 ∧ CounterMix.decode v 1 < 557056 ∧
    CounterMix.decode v 2 < 557056 ∧ CounterMix.decode v 3 < 557056 ∧ CounterMix.decode v 4 < 786432
  exact ⟨rfl, CounterMix.decode_lt v 0 (by decide), CounterMix.decode_lt v 1 (by decide),
    CounterMix.decode_lt v 2 (by decide), CounterMix.decode_lt v 3 (by decide),
    CounterMix.decode_lt v 4 (by decide)⟩

theorem unpackCounter_lt_cap (tail : List Byte) (lay : Nat) (hlay : lay < nLayers) :
    unpackCounter tail lay < counterCap lay :=
  ((fits_iff _).mp (unpackDigits_fits (tailValue tail))).2 lay hlay

theorem unpackCounter_lt (tail : List Byte) (lay : Nat) (hlay : lay < nLayers) :
    unpackCounter tail lay < radix := by
  have h := unpackCounter_lt_cap tail lay hlay
  unfold counterCap at h
  split at h <;> exact h.trans (by decide)

theorem packDigits_unpackDigits (v : Nat) :
    packDigits (unpackDigits v nLayers) = v % CounterMix.capacity := by
  rw [packDigits, if_pos (unpackDigits_fits v)]
  exact CounterMix.raw_decode v

theorem packDigits_unpackTail (tail : List Byte) :
    packDigits (unpackTail tail) = tailValue tail % CounterMix.capacity :=
  packDigits_unpackDigits _

theorem unpackDigits_pack (cs : List Nat) (h : Fits cs) :
    unpackDigits (packDigits cs) nLayers = cs := by
  rw [packDigits, if_pos h]
  have hc := CounterMix.decode_raw _ _ _ _ _ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  apply List.ext_getElem (by rw [length_unpackDigits]; exact h.1.symm)
  intro i h1 h2
  have hi : i < 5 := by simpa [unpackDigits, nLayers] using h1
  unfold unpackDigits at h1 ⊢
  rw [List.getElem_map, List.getElem_range]
  rw [List.getElem_eq_getD (l := cs) (i := i) (h := h2) 0]
  interval_cases i <;> simp_all only [and_self]

end SigGolfCandidate.Ref.CounterPack
