import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# Stateless SPHINCS+ with two-padding-bit conditional-half encoding

Declared sizes: S = 6032 signature bytes, W = 16384 witness bytes, and K = 131072
cache bytes. The claim C = 10559 is the certified accepting verifier bound 10495
plus the 64-cycle witness charge. The PORS authentication cap is 117; all five
WOTS digit-sum targets are 184.

The extra one-cycle credit follows a universal structural fact about the PORS
authentication stream: an accepting path either has fewer than 117 folds or
contains a zero-fold segment. The executable images and data layouts are unchanged
from the promoted two-padding-bit construction.

The encoding selects the upper 128 bits of a 256-bit oracle answer when either
bit 63 or bit 127 of its lower half is set, otherwise selecting the lower half.
Every padding-clear word has exactly seven quarter-digest spaces of preimages:
2^128 + 3 * 2^126. Thus valid-word acceptance has the exact multiplier 7/4.
Signer, expander, reference and verifier use this same fixed selection rule.
The rounded signing envelope is 2^(115257/131072) * 1.0279 * 1.011^5 <= 2.

The verifier selector uses six instructions on either branch. All 227 copies
are checked for both selector branches and both rejection conditions. Compared
with the original eight-instruction selector, ten instructions are removed
across the five layers. Uniform target184 removes forty-five chain cycles.

The carried witness-chain base replaces four lower-layer LUI/ADDI pairs with
SUB instructions. The existing obsolete x28 root initializer becomes x28=2688,
so no extra initializer is required. Register-frame proofs preserve x22 and
x28 across each leaf and Merkle fold.

The predecessor conditional-half construction is public source
47ecb4bca5558562f3576fd6bfe687e9f2a8ab2f by patternrecognition9-del. Base reuse
follows Gopi's promoted 4528ff23136b01e342c77eedaf2f6d74ad961d15.
The four-image certificate covers image admission, universal termination,
per-seed completeness, compression budgets, 127-bit event security and verifier
cycles under the pinned contract. No measured instruction or HASH profile is claimed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10559 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
