import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,4,7,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,4,7,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 32 KiB authenticated
partial cache. `S = 5744` bytes, `W = 25240` bytes, `K = 32768` bytes (cache), `C = 9148` cycles
(accepting-verify bound `9049` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 36864, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 9049); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).

The seven few-time banks retain 2,048 physical leaves each. Each digest selects one of 16 buckets per bank
and three distinct leaves among its 128 leaves. Authentication uses at most 91 child nodes plus 28 outer
nodes, for a cap of 119. Bits 206 through 210 of the digest must be zero; signing, expansion, and verification
all enforce this gate. The signature is 32 bytes smaller than the preceding 121-node construction. The
witness keeps the existing layer addresses, with a 400-byte gap after the shortened FTS stream.

The verifier retains the packed FTS/Merkle headers from pratikgx's PR333/335 and Frodan's PR342,
znan2's embedded constant loads, the lower seven-operation SWAR identity from i34-9's accepted PR283,
its analogous mixed-top identity, and patternrecognition9-del's live-root technique. The smaller
authentication cap saves another 30 verifier cycles; the five-bit gate has the same instruction cost as the previous six-bit gate.


-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5744 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 32768 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 36864, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 9148 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
