import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with gated overlapping-window encoding

S=6032 signature bytes, W=14080 witness bytes, K=131072 cache bytes.
The claim C=10280 is accepting verifier bound10225 plus witness charge55.
The PORS node/leaf instance header rotates bytes3..7 through a total query involution,
so setup builds its two headers with a shift and add, saving four instructions.
The witness-counter range check masks the merged counters with a constant mask word kept in the
verifier data's padding word, replacing a shift/or/shift fold with one load and one and.
This candidate retains the accepted ordered root-children message construction and adds
length-separated leaf header reuse, a preserved selector threshold, a reversible
top heap address reflection, carried upper-layer leaf headers, and rotated encoding
payload lanes. The encoding header remains in memory and only its layer byte is updated,
removing four header subtractions and one unused register initializer.
Sparse temporary PORS cells share consumed chain-tweak slots. The certificate checks the concrete programs and query map.
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
rechecked for the new selector and target counts. Shared target185 now
needs one correction at the bottom layer; the top correction disappears.

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

The high word of leaf header0 holds0xFFF: the prologue loads x18 with one
`lwu x18, 52(sp)`, its x18-relative offsets are unrebased, the PORS leaf head
no longer restores x18, and the header loads read the low word with `lw`.

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

The external witness omits its internal zero prefix. Temporary PORS cells share consumed
chain tweak slots, and authentication paths use contiguous 16-byte cells. The external
witness begins at 0x1100 and has 14080 bytes, with charge 55.

The certificate covers all four images, universal termination, per-seed
completeness, honest compression budgets,127-bit security and accepting
verifier cycles under the pinned contract. No measured profile is claimed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 14080 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 32, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 4352 } := rfl

theorem certificate : SigGolf.Certificate submission 10280 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
