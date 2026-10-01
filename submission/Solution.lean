import SigGolf
import SigGolfCandidate.Transfer.Final

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6032` bytes, `W = 16384` bytes, `K = 131072` bytes (cache), `C = 10905` cycles (verify bound
`10841` plus the witness charge `⌈16384 / 256⌉ = 64`). Layout (bytes): message 64, secret key 128,
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

All five WOTS layers use the uniform target sum 181. This restores the five counter-search
factors 1.011 in the signing-budget proof, paying for the paired-search PORS cap reduction from 118 to 117
authentication slots. Sign and expand use the original inline target check; verify retains the
stack8 instruction layout and bottom-layer target register, now also set to 181. The in-place
chains, triple dispatch, first-chain initialization and all inherited verifier micro-cuts remain.
The digest
hashes to address 0 so its output register needs no load, the PORS stack register is zero-based and
its frame is rebased by 336 so the fold limit is the existing `x18 = 4095`, the SWAR masks are two
data words of the image loaded in the root tails, the root's `E = 1` and empty-stack checks compare
registers directly, redundant hash-length reloads and `lui/addi` constant pairs reachable from
`x18` are dropped, and the top layer's route needs no masking (its remaining 11 route bits fit).

The verifier ports the OTS modular checksum and constant-reuse optimizations: each layer
uses an exact remainder modulo 4095, and the rebased address register doubles as the
modulus. The shared chain code dispatches triples. The zero-shift extractions after triples
0 and 7 read the packed register directly, saving two copies per layer. Chain 0 initializes
the running tweak from the layer header in both its hash and digit-7 copy paths; subsequent
chains increment that tweak. This removes the separate initialization from each layer's
prologue, saving another cycle per layer. These two changes save fifteen cycles in total.
Each
Merkle path jumps once per leaf-index chunk into straight-line level code for that chunk value
(no per-level branch), the two heap indices below each root are stored from registers that
hold them, and each block of the last chunk carries its own copy of the next layer's transition. The PORS
segment dispatch uses 8-word table slots with the entry code inlined, and the fold limit is
checked once through the stream pointer instead of a per-segment counter. The startup reuses
the address base and the digest's known input length, saving four more instructions on
accepting runs. These verifier changes preserve the promoted scheme's hash queries and formats.

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

theorem signature_bytes : submission.sizes.signature = 6032 := rfl

theorem witness_bytes : submission.sizes.witness = 16384 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 150272, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 10905 :=
  SigGolfCandidate.certificateNew

end SigGolf.Challenge
