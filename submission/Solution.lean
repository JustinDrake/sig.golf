import SigGolf
import SigGolfCandidate.T3M.CanonicalFinal.Conditional
import SigGolfCandidate.T3M.Final.CanonicalSecurityGame
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
The T3 construction with a digest-derived FTS verifier. The native verifier
dispatches to 42 public geometry schedules instead of interpreting witness
segment headers and a dynamic tree stack. A repeated digest query, checked in
all 256 bits, supports normalization against arbitrary oracle response streams.

The universal accepting native bound is 8495 cycles. The unchanged 25240-byte
witness adds 99 cycles, giving charged C=8594. Signature and cache sizes remain
5616 and 131072 bytes. Key generation, signing, expansion, and the lower WOTS
and Merkle construction retain the checked T3 source.

CanonicalSecurityGame proves security for adaptive adversaries with both
witness and signature forgeries. It transfers each terminal event at arbitrary
initial random-oracle caches, preserves the signing log and its freshness and
lifetime checks, and compares charged hash calls on every winning path. Honest
expansions supply canonical schedules; completeness follows from the existing
source construction under every fixed hash function and lazy-oracle transfer.

CanonicalRun proves exact machine refinement, all-input termination, and the
8495 accepting bound for the frozen fixture. CanonicalFinal assembles all six
organizer certificate fields and transfers from the legacy machine contract.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.CanonicalFinal.submissionNew

theorem signature_bytes : submission.sizes.signature=5616 := rfl
theorem witness_bytes : submission.sizes.witness=25240 := rfl
theorem cache_bytes : submission.sizes.cache=131072 := rfl
theorem layout_offsets : submission.layout=
    { message:=64,secretKey:=128,publicKey:=160,cache:=524288,signature:=28672,witness:=2048 } := rfl

theorem certificate : SigGolf.Certificate submission 8594 :=
  SigGolfCandidate.T3M.CanonicalFinal.certificate_of_security
    (SigGolfCandidate.T3M.CanonicalSource.securityC_of_old SigGolfCandidate.T3.Secc.t3_securityP)

end SigGolf.Challenge
