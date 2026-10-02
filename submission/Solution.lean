import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,3,8,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,3,8,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 32 KiB authenticated
partial cache. `S = 5824` bytes, `W = 25240` bytes, `K = 32768` bytes (cache), `C = 9370` cycles
(accepting-verify bound `9271` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 36864, signature 28672, witness 2048.

The final comparison uses its high-word subtraction as the HALT exit code, saving one accepting instruction.
The layer-3 transition builds its SWAR lane mask from one 32-bit constant, reads the tree index directly and
reuses `t1 = 1` from the FTS; the top-layer transition drops its `s7` copy, derives `0x3333…` from
`0x0F0F…` and `s3` from `s6`; the FTS setup derives three header constants from `s2 = 4095` and keeps `t1 = 1`
and `s3 = 0x600` as the comparands of the seven coordinate-end checks (one `bne` each); the forest header word
and the digest header word come from `s2`.
The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 9271); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5824 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 32768 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 36864, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 9370 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
