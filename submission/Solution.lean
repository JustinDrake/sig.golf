import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6048` bytes, `W = 16384` bytes, `K = 131072` bytes (cache), `C = 10962` cycles (verify bound
`10898` plus the witness charge `⌈16384 / 256⌉ = 64`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 150272, witness 2048.

The five WOTS+C counters are not in the signature: `expand` recomputes each layer's least valid
counter (the signer's own search from 0), running the record verifier's PORS root and layer checks
on the partial witness to obtain each layer's message, and writes the counters into the witness.

The witness has the W1a in-place chain layout: after the PORS part and the Merkle paths, each WOTS
chain gets a 64-byte block `[tweak slot 16 | pad 32 | value 16]`, and verify hashes the chains in
place (it writes each step's tweak into the slot and the step's output over the value), so a nonzero
pad is hashed as it stands; the abstract game accounts for this through the padded chain queries
(`verifyP`, `Bridge.padDec`). Verify dispatches three chains per table jump. The counters `c0 .. c3`
sit in the tweak slot of layer 0's first block, `c4` after the PORS stream.

The promoted parameter set is retained: WOTS target sum 181 and the one-block private
randomizer input, together with its existing security and signing-budget proofs.

The verifier keeps the exact remainder checksum modulo 4095, triple-chain dispatch, and
chunk-selected Merkle paths of the accepted in-place construction. The PORS segment dispatch
uses 8-word table slots with inlined entry code. Its root tail now compares E directly with the
known constant-one register, reuses the known hash input length 64, and forms the chain tweak
constant by shifting that same constant-one register. These three instruction savings preserve
the root-tail output registers and all hash queries, while the branch layout preserves subsequent
instruction addresses. The root-tail rejection paths remain covered by the arbitrary-input bound.

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

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10962 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
