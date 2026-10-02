import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,3,8,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,3,8,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 32 KiB authenticated
partial cache. `S = 5824` bytes, `W = 25240` bytes, `K = 32768` bytes (cache), `C = 9355` cycles
(accepting-verify bound `9256` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
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
accepting-verify bound 9256); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).
The last selection's fall-through block now falls directly into the FTS setup at word 375 and the other
selection outcomes jump straight there (no `j 375` trampoline), and layer 3 forms `2^40` as `slli t3, t1, 40`
from the setup's `t1 = 1`, saving two cycles.
Embedded constants (after znan2's 7d2f35bf): the verifier embeds 96 bytes of constants; the FTS setup loads three
of its constants through `sp = 0x1000000`, which stays the data page through the FTS phase, and layer 3's one-time
load block reads the SWAR masks, the header word and the dispatch mask, saving eight cycles.
Ported from jungjipdo's f3000e6a (C 9370): the digest header word from `s2`, and the top-layer transition without
its `s7` copy, with `0x3333…` derived from `0x0F0F…` and `s3` from `s6` (five cycles).
From ae21d3da (C 9362): the lower layers' leaf-pk dispatch drops its mask (the heap sentinel is absorbed by the jump
displacement) and the top layer's chunk-1 Merkle dispatch reuses `gp = s7 >> 6` and the carried `a5` (five cycles).
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5824 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 32768 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 36864, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 9355 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
