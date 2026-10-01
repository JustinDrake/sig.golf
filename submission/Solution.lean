import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with gated overlapping-window encoding

S=6032 signature bytes, W=16384 witness bytes, K=131072 cache bytes.
The claim C=10473 is accepting verifier bound10409 plus witness charge64.
PORS has height14,15 openings and authentication cap117. The five WOTS
checksum targets are[184,185,185,185,185]. The fixed AB/BC/CD selector has
15/8 acceptance multiplier and is shared by the signer, expander, verifier
and the reference scheme.

Three descriptor bits check the PORS path modulo8 and specialize up to two
nonfinal folds. The verifier copies nonroot fold suffixes to remove their
join jump. The root retains its checked continuation. A finite kernel-checked
tree certificate, connected to every accepting reference witness, bounds the
segment cost by2406 including one reserved root cycle. Signature bytes and
honest oracle queries remain unchanged.

The proven signing envelope is
2^(115257/131072)*1.0279*1.00951*1.01132^4 <= 2.
The joint security proof uses primitive coefficient253/128 and split65*2^106.
The certificate covers all four images, universal termination, per-seed
completeness, honest compression budgets,127-bit security and accepting
verifier cycles under the pinned contract. No measured profile is claimed.

Inherited public optimizations include promoted234b1bd3 root-data and final-layer
x30 reuse,47ecb4bca5558562f3576fd6bfe687e9f2a8ab2f by patternrecognition9-del,
Gopi's4528ff23136b01e342c77eedaf2f6d74ad961d15, and
0ba3dc24993dd3491a0a6a064c7cd9fbb9aa6439. The previous checked two-padding-bit
selector and layer-specific target proofs supply the construction baseline.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10473 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
