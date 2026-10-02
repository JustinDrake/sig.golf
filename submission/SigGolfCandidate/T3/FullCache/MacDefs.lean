import SigGolfCandidate.T3.FullCache.Primitives
import Mathlib

namespace SiggolfT3Mac4
open SphincsSecurity
set_option autoImplicit false

abbrev MacTag := Fin 4 → BitVec 64
abbrev MacKey := Fin 2 → HashOutput

def macKeyWord (key : MacKey) (j : Fin 4) : Nat :=
  ((key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2)) 61).toNat

def macPadWord (key : MacKey) (j : Fin 4) : BitVec 64 :=
  (key ⟨j.val / 2, by omega⟩).extractLsb' (128 * (j.val % 2) + 64) 64

def macTag (key : MacKey) (data : HashInput) : MacTag :=
  fun j => BitVec.ofNat 64 (polyMac (macKeyWord key j) (chunks32 data)) + macPadWord key j


/-- Canonical little-endian encoding of the four MAC words. -/
def encodeTag (tag : MacTag) : HashOutput :=
  answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)

def decodeTag (tag : HashOutput) : MacTag :=
  fun i => tag.extractLsb' (64*i.val) 64

end SiggolfT3Mac4
