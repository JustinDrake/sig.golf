import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6048` bytes, `W = 16384` bytes, `K = 131072` bytes (cache), `C = 10917` cycles (verify bound
`10853` plus the witness charge `⌈16384 / 256⌉ = 64`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 150272, witness 2048.

The five WOTS+C counters are not in the signature: `expand` recomputes each layer's least valid
counter (the signer's own search from 0), running the record verifier's PORS root and layer checks
on the partial witness to obtain each layer's message, and writes the counters into the witness.

The witness has the W1a in-place chain layout: after the PORS part and the Merkle paths, each WOTS
chain gets a 64-byte block `[tweak slot 16 | pad 32 | value 16]`, and verify hashes the chains in
place (it writes each step's tweak into the slot and the step's output over the value), so a nonzero
pad is hashed as it stands; the abstract game accounts for this through the padded chain queries
(`verifyP`, `Bridge.padDec`). Verify dispatches three chains per table jump. The counters `c0 .. c3`
sit in the tweak slot of layer 0's first block, `c4` after the PORS stream.

WOTS layers zero through two use target sum 181, layer three uses 182, and layer four uses 183. The counter
search limit remains 2^22. Layer-indexed encoding, security, completeness and signing-budget
proofs cover these targets; the one-block private randomizer input is unchanged.
Layer four removes its redundant HASH-length load and corrects the digit checksum
by two in the freed instruction slot. Layer three inserts a one-step correction and shifts
its local header, leaf, and rejection stub into one padding word.

The cache stores only masked internal nodes, authenticated together with a single MAC.
Signing rebuilds the missing leaf sibling from the seed; replay and erasure lemmas preserve
the security bound. The smaller MAC costs 513 compressions instead of 1025, while rebuilding
the sibling adds 325, saving 187 deterministic signing compressions.

The verifier uses an exact remainder modulo 4095 for the digit checksum and dispatches three
chains per shared table row. Each WOTS chain hashes directly in its padded witness block;
the security bridge carries arbitrary adversarial pads into the abstract padded verifier.
Merkle paths use chunk-selected straight-line blocks, and PORS retains its inlined segment
entries and stream-pointer fold limit. The final root comparison uses the last-word XOR as
its HALT result. PORS setup installs its empty-stack sentinel with one upper-word store and
reuses known constants. Root equality branches skip rejection jumps on success, and repeated
mask seeds shorten the three alternative root tails without moving later code addresses.
The root tails form `2^40` by shifting the known value one and preserve the already-known
HASH input length of 64, removing two additional instructions on every accepting run.
The digest and PORS domain constants are each formed with one addition from the known
4095, shortening the prologue and setup by one instruction each. The first leaf and all
later table/code addresses remain fixed.
The two zero-shift triple dispatches in each layer mask their source register directly.
This removes an unnecessary register copy in each dispatch while preserving all table
addresses and JALR destinations, reducing the total chain overhead by ten cycles.

The certificate is `SigGolfCandidate.certificateNew`. It is transferred from
`SigGolfCandidate.Final.certificate`, a certificate for the same images under the previous
organizer contract (70ba436, kept verbatim as `SigGolfCandidate.Legacy`): `SigGolfCandidate.Transfer`
proves that both contracts' machines and runs agree on admissible images and transfers each statement.
In the legacy certificate the four RISC-V images are proved to refine a byte-level reference
(`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+ scheme with PORS+FP
(`SphincsSecurity`) up to the oracle input format; the abstract scheme's 127-bit event-form
security, per-seed completeness and correctness are transported to the organizer's game through
`SigGolfCandidate.Bridge`.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.submissionNew

theorem signature_bytes : submission.sizes.signature = 6048 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10917 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
