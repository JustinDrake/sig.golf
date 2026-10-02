import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,3,8,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,3,8,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 32 KiB authenticated
partial cache. `S = 5824` bytes, `W = 25240` bytes, `K = 32768` bytes (cache), `C = 9203` cycles
(accepting-verify bound `9104` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 36864, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 9104); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).

Combines the packed FTS/Merkle header construction from pratikgx's PR333/335 and Frodan's PR342
with znan2's embedded constant loads, the lower seven-operation SWAR identity from i34-9's accepted PR283,
its analogous mixed-top identity, and patternrecognition9-del's live-root technique. This follow-up retains that accepted composition and integrates jungjipdo's
persistent coordinate comparands. Two setup instructions preload x6 = 1 and x19 = frameA 0;
seven coordinate boundaries each save two instructions, and the forest tag reuses x18.
The comparands and forest tag save thirteen ordinary cycles. Packing the leaf header in x28
adds one setup instruction and removes twenty-one per-leaf stores, saving twenty more.
The net reduction from the accepted 9236-cycle source is thirty-three ordinary cycles. The exact source semantics, producer images,
security parameters and hash queries are unchanged. The full hosted certificate is required.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5824 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 32768 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 36864, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 9203 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
