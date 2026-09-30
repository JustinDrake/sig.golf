import SigGolf
import SigGolfCandidate.Transport.SecurityFinal
import SigGolfCandidate.Final.Discharge

/-!
# sig.golf solution: a SPHINCS+ variant

`S = W = 6404` bytes, `K = 131072` bytes (cache), `C = 11572` cycles. Layout (bytes): message 64, secret key 128,
public key 160, cache 17568, signature 9808, witness 2048.

The original certificate is `SigGolfCandidate.Final.certificate`: the four RISC-V images are proved to refine
a byte-level reference (`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+
scheme (`SigGolfCandidate.SphincsSecurity`) up to zero-padding of oracle inputs; the abstract
scheme's 127-bit event-form security, per-seed completeness and correctness are transported to the
organizer's game through `SigGolfCandidate.Bridge`.
`SigGolfCandidate.Transport` proves that this certificate satisfies the current vendored contract,
including its oracle-level hash counter and finite-computation adversary interface.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission :=
  SigGolfCandidate.Transport.submission SigGolfCandidate.submission

theorem signature_bytes : submission.sizes.signature = 6404 := rfl

theorem witness_bytes : submission.sizes.witness = 6404 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11572 := by
  have old := SigGolfCandidate.Final.certificate
  exact {
    admission := SigGolfCandidate.Transport.admission _ old.admissible
    completeness := SigGolfCandidate.Transport.completeness _ old.admissible old.completeness
    compressionBudgets := SigGolfCandidate.Transport.compressionBudgets _ old.admissible old.compressionBounds
    verificationCycles := SigGolfCandidate.Transport.verificationCycles _ old.admissible _ old.verificationBound
    security := SigGolfCandidate.Transport.security _ old.admissible old.security
    termination := SigGolfCandidate.Transport.termination _ old.admissible old.termination
  }

end SigGolf.Challenge
