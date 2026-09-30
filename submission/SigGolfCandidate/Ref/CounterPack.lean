import SigGolfCandidate.Ref.Basic

/-!
# Canonical 14-byte counter tail

The five WOTS counters remain 32-bit values in the witness. Only their compact
signature representation changes. Each accepted counter is below `2^22`; the
tail is the little-endian encoding of `c₀ + 2^22 c₁ + ⋯ + 2^88 c₄`.
The top two bits of byte 13 must be zero on every accepted compact signature.
-/

namespace SigGolfCandidate.Ref.CounterPack
open SigGolfCandidate.Ref
open SigGolfCandidate.Legacy

def counterBits : Nat := 22
def radix : Nat := 2 ^ counterBits
def tailBytes : Nat := 14

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
theorem packedSigBytes_eq : packedSigBytes = 6062 := by decide

/-- Base-`2^22` digits, least significant counter first. -/
def packDigits : List Nat → Nat
  | [] => 0
  | c :: cs => c + radix * packDigits cs

/-- Decode exactly `n` counter digits, least significant first. -/
def unpackDigits (v : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => v % radix :: unpackDigits (v / radix) n

/-- The compact tail has a fixed length even if a caller supplies fewer layers. -/
def packTail (counters : List Nat) : List Byte :=
  toList (n := 14) (BitVec.ofNat (8 * 14) (packDigits counters))

def tailValue (tail : List Byte) : Nat := leNat tail
def unpackTail (tail : List Byte) : List Nat := unpackDigits (tailValue tail) nLayers
def unpackCounter (tail : List Byte) (lay : Nat) : Nat := (unpackTail tail).getD lay 0

/-- An accepted tail uses exactly 110 bits; the unused two bits are checked. -/
def canonicalTail (tail : List Byte) : Bool :=
  (tail.length == tailBytes) && ((tail.getD 13 0).toNat < 64)

theorem canonicalTail_iff (tail : List Byte) :
    canonicalTail tail = true ↔
      tail.length = tailBytes ∧ (tail.getD 13 0).toNat < 64 := by
  simp [canonicalTail]

theorem length_packTail (cs : List Nat) : (packTail cs).length = tailBytes := by
  simp [packTail, tailBytes, toList, SigGolfCandidate.Legacy.bytes]

theorem packDigits_cons_mod (c : Nat) (cs : List Nat) (hc : c < radix) :
    packDigits (c :: cs) % radix = c := by
  change (c + radix * packDigits cs) % radix = c
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt hc

theorem packDigits_cons_div (c : Nat) (cs : List Nat) (hc : c < radix) :
    packDigits (c :: cs) / radix = packDigits cs := by
  change (c + radix * packDigits cs) / radix = packDigits cs
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hc]
  simp

theorem packDigits_lt_pow (cs : List Nat) (hcs : ∀ c ∈ cs, c < radix) :
    packDigits cs < radix ^ cs.length := by
  induction cs with
  | nil => simp [packDigits]
  | cons c cs ih =>
    have hc : c < radix := hcs c (by simp)
    have hrest : ∀ x ∈ cs, x < radix := by
      intro x hx
      exact hcs x (by simp [hx])
    have hb := ih hrest
    simp only [packDigits, List.length_cons, Nat.pow_succ]
    norm_num [radix, counterBits] at hc hb ⊢
    omega

/-- Peeling five bounded radix digits recovers the original counters. -/
theorem unpackDigits_pack : ∀ (cs : List Nat),
    (∀ c ∈ cs, c < radix) → unpackDigits (packDigits cs) cs.length = cs := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hc : c < radix := h c (by simp)
    have hcs : ∀ x ∈ cs, x < radix := by
      intro x hx
      exact h x (by simp [hx])
    change packDigits (c :: cs) % radix ::
      unpackDigits (packDigits (c :: cs) / radix) cs.length = c :: cs
    rw [packDigits_cons_mod c cs hc, packDigits_cons_div c cs hc, ih hcs]

theorem length_unpackDigits (v n : Nat) : (unpackDigits v n).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [unpackDigits, ih]

theorem unpackDigits_entries_lt (v n : Nat) :
    ∀ c ∈ unpackDigits v n, c < radix := by
  induction n generalizing v with
  | zero =>
    intro c hc
    cases hc
  | succ n ih =>
    intro c hc
    simp only [unpackDigits, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Nat.mod_lt _ (by decide)
    · exact ih (v / radix) c hc

theorem length_unpackTail (tail : List Byte) : (unpackTail tail).length = nLayers := by
  exact length_unpackDigits _ _

theorem unpackCounter_lt (tail : List Byte) (lay : Nat) (hlay : lay < nLayers) :
    unpackCounter tail lay < radix := by
  unfold unpackCounter
  have hlen := length_unpackTail tail
  have hidx : lay < (unpackTail tail).length := by rw [hlen]; exact hlay
  rw [← List.getElem_eq_getD (l := unpackTail tail) (i := lay) (h := hidx) 0]
  exact unpackDigits_entries_lt _ _ _ (List.getElem_mem hidx)

/-- Decoding `n` base-`radix` digits and packing them recovers the low `n`
digits. The proof works for every width and needs no large numeral expansion. -/
theorem packDigits_unpackDigits (v n : Nat) :
    packDigits (unpackDigits v n) = v % radix ^ n := by
  induction n generalizing v with
  | zero => simp [unpackDigits, packDigits, Nat.mod_one]
  | succ n ih =>
    change v % radix + radix * packDigits (unpackDigits (v / radix) n) =
      v % radix ^ (n + 1)
    rw [ih (v / radix), Nat.pow_succ, Nat.mul_comm (radix ^ n) radix,
      Nat.mod_mul]

/-- Five radix digits reassemble to the low 110 bits of the original tail value. -/
theorem packDigits_unpackTail (tail : List Byte) :
    packDigits (unpackTail tail) = tailValue tail % radix ^ nLayers := by
  exact packDigits_unpackDigits (tailValue tail) nLayers

end SigGolfCandidate.Ref.CounterPack
