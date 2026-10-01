import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with gated overlapping-window encoding

S=6032 signature bytes, W=15872 witness bytes, K=131072 cache bytes.
The claim C=10378 is accepting verifier bound10316 plus witness charge62.
PORS has height14,15 openings and authentication cap117. The five WOTS
checksum targets are[185,185,185,185,186].

For oracle words A,B,C,D, select AB when B's top bit is clear and A's top
bit is clear; select BC when B's top bit is clear and A's top bit is set.
When B's top bit is set, select CD only if any of A's top four bits is
set; otherwise retain the invalid AB pair. Every padding-clear output has
exactly63*2^123 preimages, giving acceptance multiplier63/32. Sign, expand,
reference and verify implement this fixed selector.

The proven signing envelope is
2^(115258/131072)*1.0279*1.01078^4*1.01290 <= 2.
The joint security proof retains coefficient253/128 and split65*2^106.
The primitive bound combines a1/16 fine estimate with a15/16 coarse
contact-union estimate. All primitive, residual and remainder terms are
rechecked for the new selector and target counts. The common target185 needs no bottom-layer correction; the top layer
uses186 loaded once in the PORS root tail.

PORS node headers are relabelled: the tag-10 tweak field carries efield(H),
the32-bit bit reversal of the heap index H. The verifier keeps
sext32(efield(H)), so one slliw yields the parent field and its sign bit
is the direction. Each leaf loads its relabelled header from a data table
of2^14+1 words. Sign and expand compute the header with a rev16 network.

Leaf indices in the verifier's PIND table are stored as eight times the raw
index. Each selected index is already the offset into the node-header table,
eliminating one instruction at all fifteen leaf heads. The tag-9 address
field is rotated left by three bits through an injective global query
permutation; on admitted leaf indices this is multiplication by eight.
Raw secret-PRF addresses, abstract leaf selection and sorting are unchanged.

PORS segments with at least three folds carry three natural heap path bits.
Their table entries compare a static reversed three-bit constant against the
relabelled heap field, then take two known directions without branch tests.
Nonroot entries use copied suffixes without a join; the root retains its join.
Short segments retain parity-only guards and normalize ignored lookahead in
the abstract signature. The compressed-tree certificate bounds all decoded
segment costs by2322, including the exact final/root segment exception.

The signer and expander share a straight-line selector in existing padding.
Their oracle-query sequences match the byte reference; no extra hash queries
are introduced. Inherited machine improvements include lower-layer SUB base
updates, startup stack-pointer reuse, retained-header reductions, scaled
PIND addressing, and specialized conditional-prefix PORS continuations.
The heaviest independent machine-proof branches are ordered by imports to
avoid overlapping their kernel reductions during the official build.

Construction sources include accepted patternrecognition9-del commit
498bae017836d99872f43642766f828109fcfa49 for the63/32 selector, mixed targets,
and security mixture, and its earlier673f281905f0907c60cdad02ca0fbbdc221ae2d7.
Our conditional-prefix and scaled-address implementation is preserved from
c216d85858f8a7dcd68a2782cc27cfd057d45b67. Earlier public sources include
47ecb4bca5558562f3576fd6bfe687e9f2a8ab2f, Gopi's
4528ff23136b01e342c77eedaf2f6d74ad961d15, and
0ba3dc24993dd3491a0a6a064c7cd9fbb9aa6439.

The compact witness transport follows Frodan's accepted source
bb9996d3f64b407f4fa74ee4963727246c747211. External witness bytes start at0xA00;
a512-byte zero prefix restores the internal0x800-based view. Lower paths
occupy consumed tweak slots, giving witness charge62.

An additional global native-query involution exchanges the two128-bit payload
halves at byte offsets32 and48 only for one-block queries with low16header
bits1025 (encoding tag4). The padding function and raw encoding input stay
unchanged. All other headers and multi-block queries are fixed. The verifier
keeps the message at304, the counter at288 and the preserved zero at296;
one zero store disappears in each of five layers. Sign and expand issue the
same permuted query sequence. This lowers the raw accepting bound from10326
to10321 without changing the construction or its security estimate.

The next global native-query involution exchanges low16 header classes513
and1025 only for exactly11-block inputs. The verifier stores its existing
tag4 header directly for the WOTS leaf hash, removing one arithmetic
instruction per layer and lowering the raw accepting bound to10316. All
four images use this leaf representation; malformed query classes are
covered by the same total permutation and inverse.

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

theorem certificate : SigGolf.Certificate submission 10378 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
