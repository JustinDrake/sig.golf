import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,4,7,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,4,7,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 128 KiB authenticated
paired-mask full cache. `S = 5728` bytes, `W = 25240` bytes, `K = 131072` bytes (cache), `C = 8996` cycles
(accepting-verify bound `8897` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 524288, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 8897); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).

The seven few-time banks retain 2,048 physical leaves each. Each digest selects one of 16 buckets per bank
and three distinct leaves among its 128 leaves. Authentication uses at most 90 child nodes plus 28 outer
nodes, for a cap of 118. Bits 206 through 210 of the digest must be zero; signing, expansion, and verification
all enforce this gate. The signature is 48 bytes smaller than the preceding 121-node construction. The
witness keeps the existing layer addresses, with a 480-byte gap after the shortened FTS stream.

The verifier retains the packed FTS/Merkle headers from pratikgx's PR333/335 and Frodan's PR342,
znan2's embedded constant loads, the lower seven-operation SWAR identity from i34-9's accepted PR283,
its analogous mixed-top identity, patternrecognition9-del's live-root technique, and Frodan's PR362
lower-chain dispatch saving. The full cache stores all 8190 top-tree nodes below the root, using paired
masks and a two-key four-lane polynomial MAC. The reduced signing hash work supports WOTS targets
126/195/195/195, saving 36 verification cycles at the same signature size.

This verifier adds a 16 KiB immutable table of chain-header doublewords. Inline WOTS heads load their
first step directly, saving 126 cycles across the four layers; bank setup, top-bank adjustment and
restoration add 21 cycles. The reused packed FTS cut saves another 32 cycles. The resulting certified
claim is 137 cycles below the 9133-cycle base; the source scheme and all three producer images are unchanged.

-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5728 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 8996 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
