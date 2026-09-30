import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6062` bytes, `W = 6348` bytes, `K = 131072` bytes (cache), `C = 11664` cycles (verify bound
`11639` plus the witness charge `⌈6348 / 256⌉ = 25`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 13056, witness 2048.

The verifier reuses the initially zero PORS fold counter and the hash length already held
in `a1` at the PORS root tail. This removes two redundant register initializations on every
accepting run while preserving all later code addresses. The other three program images
and the reference scheme are unchanged.

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

theorem signature_bytes : submission.sizes.signature = 6062 := rfl

theorem witness_bytes : submission.sizes.witness = 6348 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 13056, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11664 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
