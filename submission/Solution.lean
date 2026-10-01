import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with gated overlapping-window encoding

S=6032 signature bytes, W=16384 witness bytes, K=131072 cache bytes.
The claim C=10498 is accepting verifier bound10434 plus witness charge64.
PORS has height14,15 openings and authentication cap117. The five WOTS
checksum targets are[184,185,185,185,185].

For oracle words A,B,C,D, select AB when B's top bit is clear and A's top
bit is clear; select BC when B's top bit is clear and A's top bit is set.
When B's top bit is set, select CD only if either of A's top two bits is
set; otherwise retain the invalid AB pair. Every padding-clear output has
exactly15*2^125 preimages, giving acceptance multiplier15/8. Sign, expand,
reference and verify all implement this fixed selector.

The verifier carries forward the promoted234b1bd3 root-data and final-layer
x30 optimizations. It now uses the descriptor's three high bits to check the
current PORS path modulo8 and specialize up to two nonfinal folds. The
expander emits these canonical path bits. All signature bytes and honest
oracle queries stay unchanged; malformed witnesses face the stronger guard.
The existing constant6 initializer moves from root entry to digest setup,
so the new prefixes require no net initializer charge. Their aggregate
credit is at least22 cycles below the generic bound, versus the prior
one-cycle structural credit, giving a net21-cycle improvement from C10519.

The proven signing envelope is
2^(115257/131072)*1.0279*1.00951*1.01132^4 <= 2.
The joint security proof uses primitive coefficient253/128 and split65*2^106;
all primitive, residual and certificate remainder terms are rechecked.
The verifier selector takes at most seven instructions, with separately
proved shorter AB paths. Shared target185 needs one correction at layer0.
Compared with the previous7/4 mixed construction, two target increments
remove eighteen chain cycles and the selector adds at most five cycles.

The signer and expander share a straight-line selector in existing padding.
Including the call jump it executes16 instructions and22 cycles. Counter
search termination accounts for64 cycles per trial. Their oracle-query
sequences match the byte reference; no extra hash queries are introduced.

Inherited machine improvements include four lower-layer SUB base updates,
startup stack-pointer reuse, five retained-header instruction reductions,
and the universal positive-segment PORS structural bound.

Prior public construction sources include47ecb4bca5558562f3576fd6bfe687e9f2a8ab2f
by patternrecognition9-del, Gopi's4528ff23136b01e342c77eedaf2f6d74ad961d15,
and0ba3dc24993dd3491a0a6a064c7cd9fbb9aa6439. This source extends the previously
certified two-padding-bit selector and layer-specific target proofs.

The certificate covers all four images, universal termination, per-seed
completeness, honest compression budgets,127-bit security and accepting
verifier cycles under the pinned contract. No measured profile is claimed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10498 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
