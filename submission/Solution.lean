import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with narrow gated overlapping-window encoding

S=6032 signature bytes, W=15872 witness bytes, K=131072 cache bytes.
The claim C=10412 is accepting verifier bound10350 plus witness charge62.
PORS has height14,15 openings and authentication cap117. Every WOTS checksum target is185.

For oracle words A,B,C,D, select AB when B's top bit is clear and A's top bit is clear;
select BC when B's top bit is clear and A's top bit is set. When B's top bit is set,
select CD exactly when A's top nine bits are at least125; otherwise retain the invalid AB
pair. The selected-pair multiplicity is1923/1024 relative to a uniform pair. The complete
selector, completeness, and encoding-risk proofs use this same gate.

PORS uses bit-reversed heap headers and the physical leaf-header lookup table. The final
route remains in its physical register, the root checksum reuses x29=185, and the root tag
is loaded from the protected word at0xFDFFD0. The root transition takes12 instructions, including the shared x25=125 threshold initialization.
The gate compares x14 directly against preserved x25; selector/checksum scratch uses x14.
Each worst-case layer path saves one instruction, for a net four-cycle improvement.
A32-byte data prefix duplicates the masks and root tag. Preserving the initial stack
pointer through PORS lets the root load these words directly, eliminating its mask-base
LUI. The original leaf-table physical addresses and all original data bytes are unchanged.
The external witness omits the two internal cache words; the unchanged internal verifier
semantics are connected by the proved witness transport. Lower-layer authentication paths
occupy consumed tweak slots of the next layer verified, so the input starts at0xa00 and
the witness charge is62. All costs are formal bounds.

The bit-reversed PORS implementation is from patternrecognition9-del's public
673f281905f0907c60cdad02ca0fbbdc221ae2d7. Earlier public construction sources include
47ecb4bca5558562f3576fd6bfe687e9f2a8ab2f by patternrecognition9-del,
Gopi's4528ff23136b01e342c77eedaf2f6d74ad961d15, and
0ba3dc24993dd3491a0a6a064c7cd9fbb9aa6439. Compact-witness attribution is retained
in the accompanying public submission note.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 15872 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2560 } := rfl

theorem certificate : SigGolf.Certificate submission 10412 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
