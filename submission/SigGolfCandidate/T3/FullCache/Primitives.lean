import SigGolfCandidate.SphincsSecurity.Scheme

namespace SphincsSecurity
def macPrime : Nat := 2 ^ 61 - 1
def polyMac (k : Nat) (chunks : List Nat) : Nat :=
  chunks.foldl (fun acc c => (acc + c) * k % macPrime) 0
def chunks32 : HashInput → List Nat
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat) :: chunks32 rest
  | _ => []
def answerOfWords (w0 w1 w2 w3 : BitVec 64) : HashOutput :=
  BitVec.ofNat 256 (w0.toNat + 2^64*w1.toNat + 2^128*w2.toNat + 2^192*w3.toNat)
end SphincsSecurity
