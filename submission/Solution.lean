import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless PORS+FP signature with inline conditional-half WOTS encoding

The proposed bounds are S=6032 signature bytes, W=16384 witness bytes, K=131072 cache
bytes and C=10598 charged verification cycles. The tight raw bound is10534; the unchanged
witness charge is64. The exported certificate proves these claims under the pinned contract.

The five-layer construction retains the M117 PORS cap (height14,15 opened leaves),42 base-eight
WOTS chains per layer, and deterministic counter reconstruction in expansion. A single256-bit
encoding answer supplies a selected128-bit digest: use the upper half iff bit63 of the lower
half is1. Both padding checks and uniform target183 remain required. The accepted-codeword
mass gains an exact factor3/2. The proof carries this bias into encoding-contact and neighbor
bounds; it does not change ordinary structural-hash truncation. The signing envelope uses
D=115256, paired digest factor1.0279 and five counter factors1.011, denominator131072.

The public cache authenticates2046 masked internal top-tree nodes with a full256-bit tag.
Signing reconstructs the omitted level-zero sibling. No compact internal-row cache is included.
The witness preserves in-place address-labelled chain hashing and shared leaf/node buffers.
The address-query permutation transports the abstract security statement to those images.

This composition retains protected root constants, the initial/preserved stack-pointer
invariants, encoding-biased layer headers and the universal structural PORS cycle credit.
Root tails take11 instructions, and the accepting prologue takes24. The selector is inlined
at all227 post-HASH transition copies, removing a call and a return at each of five layers.
Its six instructions produce exactly the same selected words as the inherited helper.
The local code relocations, validity obligations, branch displacements and return-PC tables
are covered by the symbolic block proofs. The generic raw bound is10535; a separately proved
structural credit yields10534. The aggregate layer cost is7632.

All four exact images refine the byte-level reference and abstract scheme. Admission,
per-seed completeness, three exponential compression budgets, classical security for the
organizer interfaces, honest verification cycles and all-input termination remain required.
The legacy certificate is transported through the existing contract-equivalence proof to
SigGolfCandidate.certificateNew. Development checks and public notes do not change the score.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10598 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
