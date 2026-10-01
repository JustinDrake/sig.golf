import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with PORS and padded in-place WOTS chains

The declared sizes are S = 6048 signature bytes, W = 16384 witness bytes, and
K = 131072 cache bytes. The certified verification claim is C = 10628:
10564 accepting verifier cycles plus the 64-cycle witness charge. The five
WOTS digit-sum targets, in layer order 0 through 4, are [182, 182, 182, 182, 183].
The paired private-randomizer sampler, per-seed signing compression envelope,
completeness, and security proofs cover these exact targets.

This candidate composes two three-cycle reductions onto the accepted erickeigen
frontier a8b1751a21cc230145270e9dbb2ec7401cdcf7a3. Balancing the targets around
the common checksum constant 182 removes three checksum corrections while
preserving the aggregate target sum. The chain-base reduction follows Gopi's
promoted submission 4528ff23136b01e342c77eedaf2f6d74ad961d15: the root initializes
x28 to 2688, and each of the four lower layers derives its chain base from the
retained preceding base using one SUB instead of LUI plus ADDI. The shared
initializer costs one cycle, yielding three net cycles from those four cuts.
Register-frame and layer-transition proofs establish the retained base invariant.

The inherited machine uses a shared three-chain dispatch table, 64-byte padded
witness chain blocks, and chunk-selected Merkle paths. Its abstract verifier
accounts for arbitrary witness pads; the address-format oracle relabeling and
127-bit event security bound remain part of the certificate. A structural PORS
bound provides the final one-cycle tightening from the generic bound 10565.
These are certified upper bounds, with no accepting-run instruction or HASH
profile asserted in this file.

`SigGolfCandidate.certificateNew` transfers all six obligations to the pinned
organizer contract: admission, universal termination, per-seed completeness,
compression budgets, security, and verification cycles. The source proofs refine
the exact four RISC-V images to the byte-level reference and then to the abstract
scheme; no benchmark rule or trusted verifier source is changed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6048 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10628 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
