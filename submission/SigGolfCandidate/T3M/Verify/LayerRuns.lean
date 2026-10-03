import SigGolfCandidate.T3M.Verify.Spec

/-! # V1 layers: the transition copies and the leaf-pk blocks (expected path runs)

Every start of layer `lay` runs its own copy of the transition (`trPc lay c`, `xtrTab`): layer 3 one copy after the
forest hash (with the layer constants `hyper`), layers 2, 1 one per shape block of layer `lay + 1`'s Merkle code
(64, 64), layer 0 one per shape block of layer 1 (128). A copy is

* **A** (`specA`, up to the encoding `ecall`): `[sub s11, s8]`, the route (`s7 = 2^h | leaf`, `t5 = tree`,
  `tp = tree | leaf << 32`), the encoding header `T(4, lay, tree, 0, leaf)` at `0x110`, the counter (`lwu` from the
  witness header) checked `< 2^22` and stored at `0x120`, `a0 = 0x100`, `a2 = 0x140`;
* **B** (`specBl` lower / `specBt` top, after the `ecall`, up to the `jalr ra` into the chain code): the decode
  (range `srli 62` / `srli 61`, the SWAR sums of `Decode`, the checksum test `sltiu 8` / the total `126`), the chain
  prologue (`s6`, `s3`, `s8` (top), the table window `a5`, the extraction of triple / quad 0);
* the three rejections (counter, range, checksum / total), each `j reject` to the HALT(1) at word 743;
* the leaf-pk block (`specLf`, at the return pc `trPc + retOff`): the leaf header `T(2)`, the node word `tp = T(3)` for
  the Merkle levels, `a0`, `a1` (= 768, 704 lower; 512, 960 top, which also zeroes `0x5B0 .. 0x5C0`), the dispatch
  `jalr` into the jump table `stab_lay_0` by the leaf's chunk-0 bits.

All runs use V2's `runAt` (path runs with known registers) and `specB`; `copyCheck lay p` checks a copy at `p`. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

/-- The transition copies of layer `lay` (word index of `xtr{lay}_*`, in pc order). -/
def xtrTab : List (List Nat) :=
  [[18455, 18589, 18723, 18857, 18991, 19125, 19259, 19393, 19527, 19661, 19795, 19929, 20063, 20197, 20331, 20465,
    20599, 20733, 20867, 21001, 21135, 21269, 21403, 21537, 21671, 21805, 21939, 22073, 22207, 22341, 22475, 22609,
    22743, 22877, 23011, 23145, 23279, 23413, 23547, 23681, 23815, 23949, 24083, 24217, 24351, 24485, 24619, 24753,
    24887, 25021, 25155, 25289, 25423, 25557, 25691, 25825, 25959, 26093, 26227, 26361, 26495, 26629, 26763, 26897,
    27031, 27165, 27299, 27433, 27567, 27701, 27835, 27969, 28103, 28237, 28371, 28505, 28639, 28773, 28907, 29041,
    29175, 29309, 29443, 29577, 29711, 29845, 29979, 30113, 30247, 30381, 30515, 30649, 30783, 30917, 31051, 31185,
    31319, 31453, 31587, 31721, 31855, 31989, 32123, 32257, 32391, 32525, 32659, 32793, 32927, 33061, 33195, 33329,
    33463, 33597, 33731, 33865, 33999, 34133, 34267, 34401, 34535, 34669, 34803, 34937, 35071, 35205, 35339, 35473],
   [11985, 12086, 12187, 12288, 12389, 12490, 12591, 12692, 12793, 12894, 12995, 13096, 13197, 13298, 13399, 13500,
    13601, 13702, 13803, 13904, 14005, 14106, 14207, 14308, 14409, 14510, 14611, 14712, 14813, 14914, 15015, 15116,
    15217, 15318, 15419, 15520, 15621, 15722, 15823, 15924, 16025, 16126, 16227, 16328, 16429, 16530, 16631, 16732,
    16833, 16934, 17035, 17136, 17237, 17338, 17439, 17540, 17641, 17742, 17843, 17944, 18045, 18146, 18247, 18348],
   [5521, 5622, 5723, 5824, 5925, 6026, 6127, 6228, 6329, 6430, 6531, 6632, 6733, 6834, 6935, 7036,
    7137, 7238, 7339, 7440, 7541, 7642, 7743, 7844, 7945, 8046, 8147, 8248, 8349, 8450, 8551, 8652,
    8753, 8854, 8955, 9056, 9157, 9258, 9359, 9460, 9561, 9662, 9763, 9864, 9965, 10066, 10167, 10268,
    10369, 10470, 10571, 10672, 10773, 10874, 10975, 11076, 11177, 11278, 11379, 11480, 11581, 11682, 11783, 11884],
   [660]]

/-- The number of transition copies of layer `lay`. -/
def nCopy (lay : Nat) : Nat := (xtrTab.getD lay []).length
/-- Start of transition copy `c` of layer `lay`. -/
def trPc (lay c : Nat) : Nat := (xtrTab.getD lay []).getD c 0

/-- A constant word. -/
def kw (k : Nat) : E := .c (BitVec.ofNat 64 k)

/-! ## Layer constants -/

/-- Merkle height. -/
def hL (lay : Nat) : Nat := [12, 7, 6, 6].getD lay 0
/-- Steps of A; layer 3 reuses four constants from the forest. -/
def stepsA (lay : Nat) : Nat := if lay = 0 then 16 else 15
/-- The return pc of the chain code (the leaf-pk block) relative to the copy. -/
def retOff (lay : Nat) : Nat := if lay = 0 then 69 else 46
/-- The chain base register value: lower layers `WIT + chainBase + 1024`; the top `WIT + chainBase + 960`. -/
def s6v (lay : Nat) : Nat := [15064, 19288, 22424, 25560].getD lay 0
/-- The top's base for its chains 0 .. 48 (`s3`). -/
def s3v : Nat := 15768
/-- Core's targets. -/
def tgtL (lay : Nat) : Nat := [126, 195, 195, 194].getD lay 0
/-- Header word 0 of tag `t` and layer `lay` (`1 | t << 8 | lay << 16`). -/
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
/-- The HALT(1) `ecall` of `reject`. -/
def rejEcall : Nat := 743
/-- The jump table `stab_lay_0` of the Merkle shape dispatch. -/
def stabIdx (lay : Nat) : Nat := [209768, 209640, 209576, 209512].getD lay 0
/-- The mask of the leaf's chunk-0 bits in the dispatch (`slli a4, s7, 2; andi a4, …`). -/
def stabMask (lay : Nat) : Nat := if lay = 1 then 508 else 252

/-- The 3-bit SWAR masks and the 2-bit ones (top). -/
def M1c : Nat := 8198552921648689607
def M2c : Nat := 17311559823019733055
def M4c : Nat := 3689348814741910323
def M8c : Nat := 1085102592571150095

/-- Constants carried from the forest after the loader changes `sp`. -/
def afterLoadK : List (Reg × Word) := baseK ++ [(.x7,2),(.x8,3),(.x9,4),(.x13,5),
  (.x6,1),(.x26,6),(.x31,7),(.x24,0x10000),(.x19,BitVec.ofNat 64 (2^62))]

/-- Lower carries compose with the top-head bank produced by the layer-1 leaf return. -/
def topBank : Nat := HDATA + 2049
def entry28 (lay : Nat) : Nat := if lay = 2 then headerBank 3 0 else if lay = 1 then headerBank 2 0 else if lay = 0 then topBank else 2 ^ 40
def leaf28 (lay : Nat) : Nat := if lay = 3 then headerBank 3 0 else if lay = 2 then headerBank 2 0 else topBank

/-- The known registers at a transition start (layer 3: `t0`, `s2` and the five constants of the load block
`ld3Spec`; `hyper` sets the rest). -/
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then afterLoadK ++ [(.x21, BitVec.ofNat 64 M2c), (.x20, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 (lay + 1))), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (entry28 lay)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x19, BitVec.ofNat 64 (2^62))]

/-- The constant registers through a layer (after A): `s11 = 0x101 | lay << 16`, the masks, the step registers. -/
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x19, BitVec.ofNat 64 (2^62))] ++ (if lay = 3 then [] else [(.x28, BitVec.ofNat 64 (entry28 lay))])

/-- Lower-chain constants after the header-table entry stub. -/
def lowerLayK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank lay 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x19, BitVec.ofNat 64 (2^62))]

/-- Four loads after the forest HASH use the carried stack pointer and range bound.
Layer 3 starts at word 660. -/
def ld3Spec : Spec :=
  ⟨[(.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))),
      (.x27, .ld (kw (DATA + 24))), (.x2, .ld (kw (DATA + 32)))],
    [], 660, false, 4, [], none, 4⟩

def ld3Check : Bool := specB [] [] afterLoadK (runAt carryK [660] 656 []) ld3Spec [] afterLoadK [.x22]

/-- ... and the encoding `ecall`'s arguments. -/
def bK (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, 256), (.x12, 320)]

/-! ## A: route, header, counter -/

/-- The register holding the remaining index bits (`s6` for layer 3, `t5` below). -/
def rReg (lay : Nat) : Reg := if lay = 3 then .x22 else .x30
def leafE (lay : Nat) : E := if lay = 0 then .reg .x30 else .bin .and (.reg (rReg lay)) (kw (2 ^ hL lay - 1))
def treeE (lay : Nat) : E := .bin .srl (.reg (rReg lay)) (kw (hL lay))
def tpE (lay : Nat) : E := .bin .or (.bin .sll (leafE lay) (kw 32)) (treeE lay)
def s7E (lay : Nat) : E := .bin .or (leafE lay) (kw (2 ^ hL lay))
/-- The counter (`lwu` of the witness header word). -/
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * ((lay + 1) % 2))) (.ld (kw (0x810 + 8 * ((lay + 1) / 2))))
def ctrBr (lay : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl (ctrE lay) (kw 22), kw 0, d⟩

def specA (lay p : Nat) : Spec :=
  ⟨[(.x4, tpE lay), (.x23, s7E lay), (.x30, treeE lay), (.x3, ctrE lay)],
   [(⟨none, BitVec.ofNat 64 288⟩, .bin (.st .w 0) (.ld (kw 288)) (ctrE lay)), (⟨none, BitVec.ofNat 64 280⟩, tpE lay),
    (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay false], none, stepsA lay⟩

def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 280⟩, tpE lay), (⟨none, BitVec.ofNat 64 272⟩, kw (hw 4 lay))],
   rejEcall, true, stepsA lay, [ctrBr lay true], none, stepsA lay⟩

/-! ## B: decode and the chain prologue -/

def a6E : E := .ld (kw 320)
def a7E : E := .ld (kw 328)
def b1E : E := .bin .sll a7E (kw 1)
/-- The lower decode's partial sums (`sw1`) and the digit sum (`remu 4095`). -/
def sw1RefE : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl b1E (kw 3)) (kw M1c))) (.bin .and b1E (kw M1c))
def swLowE : E := .bin .add (.bin .and a6E (kw M1c)) (.bin .and b1E (kw M1c))
def sw1E : E := .bin .add swLowE (.bin .srl (.bin .sub (.bin .add a6E b1E) swLowE) (kw 3))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
/-- The checksum register `t4 = 7 - ck = sum - (target - 7)` (`addi t4, s9, 7 - target`). -/
def t4E (lay : Nat) : E := .bin .add sumE (kw (2 ^ 64 - (tgtL lay - 7)))
def rngBr (k : Nat) (d : Bool) : Br :=
  if k = 62 then ⟨.geu, a7E, kw (2^62), d⟩ else ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.eq, .bin .sltu (t4E lay) (kw 8), kw 0, d⟩
/-- `a7 = (v1 << 1) | v0 >> 63`. -/
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
/-- The dispatch into `ttab` slot 0 (lower) / `qtab` slot 0 (top). -/
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))

def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE), (.x25, sumE), (.x29, t4E lay), (.x3, .bin .srl a6E (kw 63)), (.x14, x14l)],
   [], 0, false, 29, [ckBr lay false, rngBr 62 false], some tgtl, 32⟩

def postBl (lay p : Nat) : List (Reg × Word) :=
  lowerLayK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay - 1))]

def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, (if k = 62 then 6 else 7), [rngBr k true], none, (if k = 62 then 6 else 7)⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 21, [ckBr lay true, rngBr 62 false], none, 24⟩

/-- The top decode's sums: the 3-bit SWAR of `g = v1 >>> 34` (`remu 4095` into `t4`), the 2-bit SWAR of `v0` and
`c = v1 mod 2^34` (`remu 255`), the total. -/
def gE : E := .bin .srl a7E (kw 34)
def p3E : E := .bin .add (.bin .and (.bin .srl gE (kw 3)) (kw M1c)) (.bin .and gE (kw M1c))
def s3E : E := .bin .remu (.bin .and (.bin .add p3E (.bin .srl p3E (kw 6))) (kw M2c)) (kw 4095)
def c34E : E := .bin .srl (.bin .sll a7E (kw 30)) (kw 30)
def l1E : E := .bin .add (.bin .and (.bin .srl a6E (kw 2)) (kw M4c)) (.bin .and a6E (kw M4c))
def l2E : E := .bin .add (.bin .and (.bin .srl c34E (kw 2)) (kw M4c)) (.bin .and c34E (kw M4c))
def lRefE : E := .bin .add l1E l2E
def lLowE : E := .bin .add (.bin .and a6E (kw M4c)) (.bin .and c34E (kw M4c))
def lE : E := .bin .add lLowE (.bin .srl (.bin .sub (.bin .add a6E c34E) lLowE) (kw 2))
def pE : E := .bin .add (.bin .and (.bin .srl lE (kw 4)) (kw M8c)) (.bin .and lE (kw M8c))
def totE : E := .bin .add (.bin .remu pE (kw 255)) s3E
def totBr (d : Bool) : Br := ⟨.ne, totE, kw 126, d⟩
def x14t : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 0xae000)
def tgtt : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 711072)) (.c (~~~1#64))

def specBt (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, .bin .sll a7E (kw 2)), (.x3, totE), (.x14, x14t), (.x25, .bin .and c34E (kw M4c))],
   [], 0, false, 52, [totBr false, rngBr 61 false], some tgtt, 58⟩

/-- After the top decode: the 2-bit masks, the quad mask in `s8`, `t4 = 8` (no checksum chain). -/
def postBt (p : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 0)), (.x2, 0x3fe00), (.x20, BitVec.ofNat 64 M4c), (.x21, BitVec.ofNat 64 M8c),
    (.x11, 64), (.x28, BitVec.ofNat 64 topBank), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7),
    (.x22, BitVec.ofNat 64 (s6v 0)), (.x19, BitVec.ofNat 64 s3v), (.x24, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]

def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩

/-! ## The leaf-pk block -/

/-- At the leaf-pk block: the layer constants and the chain code's leftovers. -/
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))] ++ (if lay = 0 then [] else [(.x6, 1), (.x28, BitVec.ofNat 64 (headerBank lay 0))])

/-- The dispatch target in `stab_lay_0` (`(s7 << 2 &&& mask) + window + imm`). -/
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay))) (kw 0xce000)
  else .bin .add (.bin .sll (.reg .x23) (kw 2)) (kw 0xce000)
def tgtLfOld (lay : Nat) : E :=
  .bin .and (.bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay)))
    (kw (0x1000 + 4 * stabIdx lay))) (.c (~~~1#64))

/-- Lower-layer sentinel bits are absorbed by the jump displacement. -/
def tgtLf (lay : Nat) : E :=
  if lay = 0 then tgtLfOld lay
  else .bin .and (.bin .add (.bin .sll (.reg .x23) (kw 2))
    (kw (0x1000 + 4 * stabIdx lay - 4 * 2 ^ hL lay))) (.c (~~~1#64))

def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1400⟩, kw 0), (⟨none, BitVec.ofNat 64 1392⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 13, [], some (tgtLf lay), 13⟩
  else
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false, (if lay = 3 ∨ lay = 2 then 10 else 11), [],
     some (tgtLf lay), (if lay = 3 ∨ lay = 2 then 10 else 11)⟩

def postLf (lay : Nat) : List (Reg × Word) :=
  (baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))] ++ (if lay = 0 then [] else [(.x6, 1)])) ++ [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, 0xce000)] ++ (if lay = 0 then [] else [(.x28, BitVec.ofNat 64 (leaf28 lay))])

/-! ## The checks of a copy -/

def keepA : List Reg := []
def keepB : List Reg := [.x4, .x23, .x30]
def keepLf : List Reg := [.x23, .x30, .x22]

def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- The two direct jumps preserve the top leaf return address and enter the shared packed decoder. -/
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x1, kw (0x1000 + 4 * (p + 69)))], [], 96160, false, 2, [], none, 2⟩

/-- All runs of the transition copy at `p` of layer `lay` and of its leaf-pk block. -/
def copyCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) keepA &&
  specB [] [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [96160] (p + stepsA lay + 1) []) (specTopCall p) [] [] keepTopCall
  else
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
      (postBl lay p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf

/-- All copies of layer `lay` from index `lo`, `n` of them. -/
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)

end SigGolfCandidate.T3M
