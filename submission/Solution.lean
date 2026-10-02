import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,3,8,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,3,8,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 32 KiB authenticated
partial cache. `S = 5824` bytes, `W = 25240` bytes, `K = 32768` bytes (cache), `C = 9374` cycles
(accepting-verify bound `9275` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 36864, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 9275); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).

Verifier-only optimization of znan2's accepted constant-load source 7aceaef8dcea5a9e0184089e11665239fa338ddf,
built on nconsigny's accepted T3 construction b1f587fedc7fef9144d53dddf7363e73fb05182a.
The lower 3-bit SWAR uses the seven-operation identity from i34-9's accepted PR283,
with a strengthened operand bound; the mixed top 2-bit sum uses the analogous identity.
The final root remains at the live HASH destination, following patternrecognition9-del's accepted live-root technique.
All four layers save two ordinary instructions; the final root saves one. Source programs,
query bytes, security and signing/expansion budgets remain unchanged.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5824 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 32768 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 36864, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 9374 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
