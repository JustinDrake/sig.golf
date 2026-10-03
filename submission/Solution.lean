import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf: cached four-layer BPORS with reversed FTS labels and checked side bits

The signature has 5616 bytes; the expanded witness has 25240 bytes and the
fully authenticated cache has 131072 bytes. The claimed verification charge is
8702 =8603 accepting machine cycles +99 witness cycles.

The source uses a height 12/7/6/6 hypertree and seven BPORS banks. Each bank
selects three leaves from one of 16 buckets of 128 leaves; the authentication cap
is 115 folds. Digest bits 206 through 208 are zero. The 54-chain top code uses
51 radix-five and three radix-four digits, total 126. Lower target sums are
195/195/194. The cache stores 8190 top-tree nodes below the root, protected by
paired masks and a two-key polynomial MAC.

FTS tag 9 and tag 10 addresses use the public bit-reversal encoding introduced
by patternrecognition9-del (601149e7c5aaeb297f7454cf75bba411ccbe84c3).
The source proof includes the concrete address injectivity and domain separation.
Each segment header carries its fold count, merge flag and three direction bits;
only live bits are checked. The first two nonfinal folds and the final fold cost
13 cycles, with 14 cycles for later nonfinal folds. The actual canonical stream
bound is 361 +2100 =2461, including seven initial constant loads.
The source-support proof applies it to every accepting witness and oracle.

The 64KiB verifier data combines the bit-reversal table, erickeigen's lower-layer
public WOTS header table (68a6a216a98cc0e329f517431d568e0e21e88619), and the
paired top-rank sum table. Gopikannappan 745a58d5 supplies digit-specific
table-slot lower chain heads that jump straight to each first ecall. Five constants survive the forest and are reused in
the lower verifier, extending the register-carry approach of cryptogakusei and
znan2. The full-cache, mixed-radix top and earlier suffix optimizations retain
contributions from pratikgx, Frodan, i34-9, jungjipdo and newjordan.

The certificate transfers the four exact RV64 images from the preserved legacy
contract to the pinned organizer contract. It combines all-input termination,
source refinement, accepting cycle accounting, per-key completeness, signing
and expansion compression moments, hash-only computation and padded-game security.
The concrete security theorem is T3.Secc.t3_securityP. All six organizer fields
are assembled by Final.certificate_of_security.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5616 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 8702 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
