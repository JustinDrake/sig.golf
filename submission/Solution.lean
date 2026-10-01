import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with gated overlapping-window encoding

S=6032 signature bytes, W=15872 witness bytes, K=131072 cache bytes.
The claim C=10380 is accepting verifier bound10318 plus witness charge62.
PORS has height14,15 openings and authentication cap117. The five WOTS
checksum targets are[185,185,185,185,186].

For oracle words A,B,C,D, select AB when B's top bit is clear and A's top
bit is clear; select BC when B's top bit is clear and A's top bit is set.
When B's top bit is set, select CD only if one of A's top four bits is
set; otherwise retain the invalid AB pair. Every padding-clear output has
exactly63*2^123 preimages, giving acceptance multiplier63/32. Sign, expand,
reference and verify all implement this fixed selector.

The proven signing envelope is
2^(115258/131072)*1.0279*1.01078^4*1.01290 <= 2.
The joint security proof uses primitive coefficient253/128 and split65*2^106;
all primitive, residual and certificate remainder terms are rechecked.
The verifier selector takes at most seven instructions, with separately
proved shorter AB paths. Shared target185 retains a zero correction at layer0; layer4 uses186.
Compared with the f3569 construction, two target increments remove eighteen
chain cycles without increasing selector instruction cost. The security envelope
combines fine and coarse first-contact bounds with weights1/16 and15/16.

PORS node headers are relabelled: the tag-10 tweak field carries efield(H),
the 32-bit bit reversal of the heap index H. The verifier keeps
sext32(efield(H)), so one slliw yields the parent field and its sign bit
is the direction; each leaf loads its relabelled header from a data table
of 2^14+1 words. Sign and expand compute the header with a rev16 network.

The signer and expander share a straight-line selector in existing padding.
Including the call jump it executes16 instructions and22 cycles. Counter
search termination accounts for64 cycles per trial. Their oracle-query
sequences match the byte reference; no extra hash queries are introduced.

Lower authentication paths occupy future tweak slots; the external witness begins at0xa00
and has15872 bytes, reducing its charge to62 without adding verifier instructions.

Layers0..3 sign the two children(L,R) of the root of the tree below instead of
that root: the encoding input is tweak||L||R||counter, with L in the slot that
held the zero parameter; the bottom layer still signs(0,PORS root), the same
bytes as before. The verifier folds each lower tree only to the node under its
root, copies the top sibling of the path next to it and hashes no lower root:
14 cycles fewer per lower layer and4 more per upper transition,40 fewer in all.
Only the top tree's root is hashed and compared with the public key. The signer
and the expander still hash every root, so their oracle-query counts are unchanged.

Inherited machine improvements include four lower-layer SUB base updates,
startup stack-pointer reuse, five retained-header instruction reductions,
and the universal one-cycle PORS accepting-bound refinement.

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

theorem witness_bytes : submission.sizes.witness = 15872 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2560 } := rfl

theorem certificate : SigGolf.Certificate submission 10380 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
