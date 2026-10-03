import SigGolf
import SigGolfCandidate.T3M.Final.Conditional
import SigGolfCandidate.T3.Secc.Final
import SigGolfCandidate.T3.PackedHeap

/-!
# sig.golf solution: base T3 (four-layer hypertree with BPORS(7,4,7,3) few-time signatures)

A four-layer hypertree (heights 12/7/6/6) with BPORS(7,4,7,3) few-time signatures at the bottom, a mixed-radix
top layer, radix-8 + checksum lower layers, a one-block counter-in-tweak digest and a 128 KiB authenticated
paired-mask full cache. `S = 5616` bytes, `W = 24264` bytes, `K = 131072` bytes (cache), `C = 8683` cycles
(accepting-verify bound `8588` plus the witness charge `⌈24264 / 256⌉ = 95`). Layout (bytes): message 64,
secret key 128, public key 160, cache 524288, signature 28672, witness 2048.

The certificate is `SigGolfCandidate.T3M.Final.certificate_of_security` applied to the security proof of the
padded source game `SigGolfCandidate.T3M.Final.SecurityP`. It is transferred from a certificate for the same
images under the previous organizer contract (kept verbatim as `SigGolfCandidate.Legacy`):
`SigGolfCandidate.Transfer` proves that both contracts' machines and runs agree on admissible images and
transfers each statement. In the legacy certificate the four frozen RISC-V images (`T3M/Images/*`) are proved to
refine the source programs of `SigGolfCandidate.T3.Core` under one injective relabeling of oracle inputs
(`Final.pending_holds`: exact values, hash calls and compressions for every input, termination, and the
accepting-verify bound 8588); the source closure supplies per-key completeness, the signing and expansion
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
That tree (znan2's 0e4be4ce, building on erickeigen's 59cbf8ec header-table design) has the complete charged bound 8794.
Lower table-slot chain heads (V1). In the lower layers the first chain of each digit triple (its head
sits in a `ttab` slot) and the checksum chain (a `ctab` slot) still loaded the digit-zero header word and then jumped
into the shared ladder at the first rung's byte store. The slot is static per table row, so its digit `d` is a
constant: each head now loads the header word of digit `d` from the same header table and jumps straight onto that
rung's `ecall`; at digit 6 the head's `addi a2, a0, 48` becomes the rung's `addi a2, zero, slot`, so it lands on the
last `ecall`. The shared ladder code is unchanged. One cycle per table-slot chain (fifteen per lower layer; two at
digit 6): `chainCost` of those chains drops from `70 - 9 d` to `69 - 9 d`, the lower chain phase from
`3008 - 9 target` to `2993 - 9 target`, the accepting bound to 8650 and the complete charged bound to 8749.
Layers 3 and 2 no longer restore `t3` to the bank-0 midpoint in their leaf-pk blocks: the next lower layer's entry stub
overwrites it before any read, and only layer 1's restore (read by the top heads) is kept. The two leaf-pk blocks are
one instruction shorter (`lfSteps` 11 on layers 3 and 2), the accepting bound is 8648 and the complete charged bound
is 8747.
Counter and checksum checks: the FTS exit's load block now sets `s3 = 2^22` (`lui s3, 0x400`) in place of the dead
`ld t3`; `s3` is read-only through the lower layers, so every layer's counter check is one `bgeu gp, s3` instead of
`srli ra, gp, 22; bnez ra` (one cycle per layer). The lower checksum range check is `bltu t6, t4` with the step
register `t6 = 7` instead of `sltiu gp, t4, 8; beqz gp` (one cycle per lower layer). The accepting bound is 8641 and
the complete charged bound is 8740.
The top layer's Merkle level 0 no longer stores the (zero) top tree word over `tp`'s upper half nor reloads `tp`
(`tp` already holds the complete header word 0), two cycles: the accepting bound is 8639 and the complete charged bound
is 8738.
The lower layers' Merkle dispatch (`lui a5, 0xce; slli a4, s7, 2; add; jalr`) becomes `slli a4, s7, 9; add; jalr`
with the chain table's base `a5 = 0x6e000` still in place: each leaf's dispatch word is a `j` placed in a free column
of the chain dispatch table (`0x6e000 + 512 s7 - 2024`, layer 2 `- 2020`), one cycle per lower layer: the accepting
bound is 8636 and the complete charged bound is 8735.
Each lower transition copy now ends with the entry stub inlined (`lui t3, bank; jalr ra, a4, -1760` instead of
`jal ra, stub`) and its leaf-pk block copied right after it into the copy's unused words (instead of the return
`j` to a shared leaf-pk slot), two cycles per lower layer: the accepting bound is 8630 and the complete charged bound
is 8729.
The top layer's transition no longer shifts `t5` (the top tree is zero): `slli tp, t5, 32; lui gp, 1; or s7, t5, gp`
replaces `mv s7, t5; srli t5, t5, 12; slli tp, s7, 32; or tp, tp, t5; lui gp, 1; or s7, s7, gp` (three cycles; the top's
Merkle words no longer read `t5`): the accepting bound is 8627 and the complete charged bound is 8726.
The paired radix-five table decoder and all table memory-preservation proofs are retained.
FTS leaf header words stored by the selection (F5, this submission). Each FTS leaf's header word 1 is the FTS header
table entry of its leaf. The selection used to store the 21 sorted table addresses at `ETAB`, and every leaf code then
loaded its address, loaded the table word and stored it into the leaf block's header slot (`ld gp; ld s7; sd s7`). Now
each coordinate's selection loads its three table words once (`ld ra/s7/s9, 0(x_j)`, three cycles) and its sort tree
stores them straight into the sorted leaves' header slots (`leafT + 8`, the `sd` that stored the address); the leaf
code only reads the word back (`ld s7, 24(a0)`). That is 3 more cycles per coordinate and 2 fewer per leaf, a net
21 cycles. No FTS write touches a leaf block's header word 1 (all fold, frame and forest writes lie outside
the leaf region, `FB.thdr`), so the stored words survive until their leaves are hashed. The witness invariant of the
selection now excludes those 21 words (`SelIn.wit`, `T8`). The FTS accepting prefix becomes 2654, the accepting bound
8629 and the complete charged bound 8728 on V1; with the layer-3/2 `t3` cut above (v1e, -2) the
accepting bound is 8627 and the complete charged bound 8726; with the counter and
checksum checks above (v3, -7) the accepting bound is 8620 and the complete charged bound 8719; with the top Merkle
level-0 and lower Merkle dispatch cuts above (v4, -5) the accepting bound is 8615 and the complete charged bound 8714;
with the inlined lower entry stubs and leaf-pk blocks and the top transition above (L2, TOP-trans, -9) the
accepting bound is 8606 and the complete charged bound 8705.
Witness gaps (W). The fold stream region now ends at the pointer cap (`streamEnd = 10568`; at most 115 folds, so the
honest stream never reaches past it) instead of 720 bytes later, and the top layer's 256-byte unused tail is gone:
the four layer regions are packed from 10568 (layer bases 10568 / 14792 / 17992 / 21128), `W = 24264` and the
witness charge is `⌈24264 / 256⌉ = 95` (was 99). The verify image's layer base constants and the expand image's
per-layer witness addresses move accordingly.
The top leaf-pk block drops its `lui a5, 0xce` (TOP-lui): the top chains' final radix-four dispatch already leaves
`a5 = 0xce000`, now carried by the top chains' output invariant (one cycle): the accepting bound is 8605 and the
complete charged bound is 8704.
The layer-2 and layer-1 decode blocks drop their `lui a5, 0x6e` (A5): the Merkle check of the layer above already
leaves `a5 = 0x6e000`, carried through the transition's known registers (two cycles): the accepting bound is 8603
and the complete charged bound is 8702 with `W = 25240`; with the packed witness (`W = 24264`, charge 95) the
complete charged bound is 8698.
F4: the merge code (`entry0_M` and both merge ladders with their tails, words 4841 .. 5084) has a second copy at the
end of the verify image (words 210432 .. 210675, chunk 822) that table `ptab_l`'s merge slots enter; the original
re-dispatches through `s10 = ptab_n`, the copy through `s5 = ptab_l`. The 14 table switches `mv s4, s10 / s5` of the
leaf codes are gone (each leaf dispatch adds its table register; the leaf code block is compacted to end at the
forest, starting at 469), so the FTS accepting prefix becomes 2640 (fourteen cycles): the accepting bound is 8589 and
the complete charged bound is 8684.


FTS setup fallthrough: the reachable words 469..721 move to 401..653. The setup no longer jumps at word 401.
External rejection branches retain their destinations, and indirect dispatch links follow the relocated code.
The forest prefix drops from 2640 to 2639, so accepting verification is 8588 and the charged bound is 8683.
The unsigned lower checksum branch is already present in the base; no additional checksum saving is claimed.
-/

namespace SigGolf.Challenge

def submission : SigGolf.Submission := SigGolfCandidate.T3M.Final.submissionNew

theorem signature_bytes : submission.sizes.signature = 5616 := rfl

theorem witness_bytes : submission.sizes.witness = 24264 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 524288, signature := 28672, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 8683 :=
  SigGolfCandidate.T3M.Final.certificate_of_security SigGolfCandidate.T3.Secc.t3_securityP

end SigGolf.Challenge
