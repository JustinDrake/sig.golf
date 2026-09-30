import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6048` bytes, `W = 6348` bytes, `K = 131072` bytes (cache), `C = 11518` cycles (verify bound
`11493` plus the witness charge `⌈6348 / 256⌉ = 25`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 13056, witness 2048.

The five WOTS+C counters are not in the signature: `expand` recomputes each layer's least valid
counter (the signer's own search from 0), running the record verifier's PORS root and layer checks
on the partial witness to obtain each layer's message, and writes the counters into the witness.
The witness format is unchanged.

The promoted parameter set is retained: WOTS target sum 181 and the one-block private
randomizer input, together with its existing security and signing-budget proofs.

The verifier ports the OTS modular checksum and constant-reuse optimizations: each layer
uses an exact remainder modulo 4095, and the rebased address register doubles as the
modulus. The verify image is regenerated without the padding that kept the old addresses,
chains 0..6 store their index byte from registers that already hold 0..6, and each digit pair
dispatches once: the table of the pair's first chain jumps into a copy of the pair's code
specialized to the second digit, so the second chain has neither a table nor a `jalr`. Each
Merkle path jumps once per leaf-index chunk into straight-line level code for that chunk value
(no per-level branch), the two heap indices below each root are stored from registers that
hold them, and each block of the last chunk carries its own copy of the next layer's transition. The PORS
segment dispatch uses 8-word table slots with the entry code inlined, and the fold limit is
checked once through the stream pointer instead of a per-segment counter. The startup reuses
the address base and the digest's known input length, saving four more instructions on
accepting runs. These verifier changes preserve the promoted scheme's hash queries and formats.

The certificate is `SigGolfCandidate.certificateNew`. It is transferred from
`SigGolfCandidate.Final.certificate`, a certificate for the same images under the previous
organizer contract (70ba436, kept verbatim as `SigGolfCandidate.Legacy`): `SigGolfCandidate.Transfer`
proves that both contracts' machines and runs agree on admissible images and transfers each statement.
In the legacy certificate the four RISC-V images are proved to refine a byte-level reference
(`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+ scheme with PORS+FP
(`SphincsSecurity`) up to the oracle input format; the abstract scheme's 127-bit event-form
security, per-seed completeness and correctness are transported to the organizer's game through
`SigGolfCandidate.Bridge`.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6048 := rfl

theorem witness_bytes : submission.sizes.witness = 6348 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 13056, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11518 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
