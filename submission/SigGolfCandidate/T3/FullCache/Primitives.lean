import SigGolfCandidate.SphincsSecurity.Scheme

/-! Generic polynomial primitives rebased from the arithmetic-MAC predecessor.
No predecessor scheme parameters or cache types are imported. -/
namespace SphincsSecurity

/-- The MAC modulus, the Mersenne prime `2^61 - 1`. -/
def macPrime : Nat := 2 ^ 61 - 1

/-- The polynomial hash of a chunk list at the key `k`: `acc ↦ (acc + c) * k mod (2^61 - 1)`, from `0`.
The final multiplication leaves no constant term, so shifting the last chunk is no forgery. -/
def polyMac (k : Nat) (chunks : List Nat) : Nat :=
  chunks.foldl (fun acc c => (acc + c) * k % macPrime) 0

/-- The little-endian 32-bit chunks of a byte string (a trailing partial chunk is dropped; the region's
length is divisible by four). -/
def chunks32 : HashInput → List Nat
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat) :: chunks32 rest
  | _ => []


/-- Four little-endian 64-bit words as one complete answer. -/
def answerOfWords (w0 w1 w2 w3 : BitVec 64) : HashOutput :=
  BitVec.ofNat 256 (w0.toNat + 2^64*w1.toNat + 2^128*w2.toNat + 2^192*w3.toNat)

end SphincsSecurity
