import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,4,7,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,4,7,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 128 KiB authenticated
paired-mask full cache. `S = 5616` bytes, `W = 25240` bytes, `K = 131072` bytes (cache), `C = 8749` cycles
(accepting-verify bound `8650` plus the witness charge `⌈25240 / 256⌉ = 99`). Layout (bytes): message 64,
secret key 128, public key 160, cache 524288, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 8650); the source closure supplies per-key completeness, the signing and expansion
compression moments and the hash-only facts (`Final.sourceFacts_of_securityP`), and the padded game's
127-bit security is bridged to the organizer's game (`Final/Bridge*`).

The seven few-time banks retain 2,048 physical leaves each. Each digest selects one of 16 buckets per bank
and three distinct leaves among its 128 leaves. Authentication uses at most 87 child nodes plus 28 outer
nodes, for a cap of 115. Bits 206 through 208 of the digest must be zero; signing, expansion, and verification
all enforce this gate. The top layer uses 51 radix-five and three radix-four chains, packed into 17 seven-bit
triple ranks and six tail bits; strong decoding rejects ranks above 124 and requires digit sum 126. This
removes four chain values, saving 64 bytes relative to the preceding full-cache construction. The
witness keeps the existing layer addresses, with a 720-byte gap after the shortened FTS stream.

The verifier retains the packed FTS/Merkle headers from pratikgx's PR333/335 and Frodan's PR342,
znan2's embedded constant loads, the lower seven-operation SWAR identity from i34-9's accepted PR283,
patternrecognition9-del's live-root technique and terminal-store saving, and Frodan's PR362
lower-chain dispatch saving. The full cache stores all 8190 top-tree nodes below the root, using paired
masks and a two-key four-lane polynomial MAC. The reduced signing hash work supports WOTS targets
126/195/195/194. The new packed decoder and 54-chain top verifier include a proved eleven-cycle minimum
terminal-store credit on every accepted top encoding. The forest verifier carries the complete leaf
header and persistent coordinate comparands, reducing its accepting prefix by 32 cycles to 2791; the relabelled FTS header (word 1 bit-reversed, a
2048-word header table) saves one cycle per fold, to 2676. The digest header word is formed by one instruction
from the constant 4095 (subflatus3's e1344b79 cut, idea jungjipdo), giving 2675. The lower layers carry znan2's
T3T cuts (lower checksum register, leaf dispatch, layer-3 index copy, top Merkle chunk-0 dispatch; 8 cycles).
The three lower layers read each WOTS chain's header word from a read-only header table in the image (erickeigen's
59cbf8ec table design, ported by znan2's T3X; 23 cycles per layer); the table's 4096-byte banks are centred on
4096-aligned addresses so each layer's entry stub is a single `lui` (T3Y, one more cycle per layer).
Each Merkle path stores the node header's word 0 with a single doubleword store per level from a register merged
once at level 0 (23 cycles). The top decoder's tail table is complemented so the digit-sum check is one
comparison (cryptogakusei's 15e2fb43, 2 cycles).
The top layer's chain heads read their header words (with the first digit) from bank 0 of the same header
table, set up by the lower layers' leaf return, and skip the first step's byte store (erickeigen's 59cbf8ec table
design on the top layer, znan2's BIG3; 54 cycles).
That tree (znan2's 0e4be4ce) has the complete charged bound 8794.
Lower table-slot chain heads (this submission). In the lower layers the first chain of each digit triple (its head
sits in a `ttab` slot) and the checksum chain (a `ctab` slot) still loaded the digit-zero header word and then jumped
into the shared ladder at the first rung's byte store. The slot is static per table row, so its digit `d` is a
constant: each head now loads the header word of digit `d` from the same header table and jumps straight onto that
rung's `ecall`; at digit 6 the head's `addi a2, a0, 48` becomes the rung's `addi a2, zero, slot`, so it lands on the
last `ecall`. The shared ladder code is unchanged. One cycle per table-slot chain (fifteen per lower layer; two at
digit 6): `chainCost` of those chains drops from `70 - 9 d` to `69 - 9 d`, the lower chain phase from
`3008 - 9 target` to `2993 - 9 target`, the accepting bound to 8650 and the complete charged bound to 8749.
The paired radix-five table decoder and all table memory-preservation proofs are retained.



-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5616 := rfl

theorem witness_bytes : submission.sizes.witness = 25240 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 8749 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
