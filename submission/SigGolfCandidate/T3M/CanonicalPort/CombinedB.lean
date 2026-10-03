import SigGolfCandidate.T3M.CanonicalPort.CombinedA

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart25

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

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify

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
   [11984, 12085, 12186, 12287, 12388, 12489, 12590, 12691, 12792, 12893, 12994, 13095, 13196, 13297, 13398, 13499,
    13600, 13701, 13802, 13903, 14004, 14105, 14206, 14307, 14408, 14509, 14610, 14711, 14812, 14913, 15014, 15115,
    15216, 15317, 15418, 15519, 15620, 15721, 15822, 15923, 16024, 16125, 16226, 16327, 16428, 16529, 16630, 16731,
    16832, 16933, 17034, 17135, 17236, 17337, 17438, 17539, 17640, 17741, 17842, 17943, 18044, 18145, 18246, 18347],
   [5520, 5621, 5722, 5823, 5924, 6025, 6126, 6227, 6328, 6429, 6530, 6631, 6732, 6833, 6934, 7035,
    7136, 7237, 7338, 7439, 7540, 7641, 7742, 7843, 7944, 8045, 8146, 8247, 8348, 8449, 8550, 8651,
    8752, 8853, 8954, 9055, 9156, 9257, 9358, 9459, 9560, 9661, 9762, 9863, 9964, 10065, 10166, 10267,
    10368, 10469, 10570, 10671, 10772, 10873, 10974, 11075, 11176, 11277, 11378, 11479, 11580, 11681, 11782, 11883],
   [661]]

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
def stepsA (lay : Nat) : Nat := if lay = 3 then 19 else if lay = 0 then 15 else 14
/-- The return pc of the chain code (the leaf-pk block) relative to the copy. -/
def retOff (lay : Nat) : Nat := if lay = 0 then 19 else if lay = 3 then 49 else 44
/-- The chain base register value: lower layers `WIT + chainBase + 1024`; the top `WIT + chainBase + 960`. -/
def s6v (lay : Nat) : Nat := [15064, 19288, 22424, 25560].getD lay 0
/-- The top's base for its chains 0 .. 48 (`s3`). -/
def s3v : Nat := 15768
/-- Core's targets. -/
def tgtL (lay : Nat) : Nat := [126, 195, 195, 194].getD lay 0
/-- Header word 0 of tag `t` and layer `lay` (`1 | t << 8 | lay << 16`). -/
def hw (t lay : Nat) : Nat := 1 + 256 * t + 65536 * lay
/-- The encoding block of layer `lay`'s transition: `0x100` for layer 3; below (E8) the last Merkle block (level
`h - 1`) of layer `lay + 1`, hashed in place (`WIT + layerBase (lay + 1)`). -/
def encB (lay : Nat) : Nat := [17816, 21016, 24152, 256].getD lay 0
/-- The witness words a copy writes (E8, below layer 3: `T(4)` and the counter into the encoding block). -/
def copyAllow (lay : Nat) : List Nat := [encB lay + 16, encB lay + 24, encB lay + 32]
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
def afterLoadK : List (Reg × Word) := baseK ++ [(.x7,2),(.x8,3),(.x9,4),(.x13,5)]

/-- The known registers at a transition start (layer 3: `t0`, `s2` and the five constants of the load block
`ld3Spec`; `hyper` sets the rest). -/
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then afterLoadK ++ [(.x28, BitVec.ofNat 64 (2 ^ 40)), (.x21, BitVec.ofNat 64 M2c), (.x20, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, BitVec.ofNat 64 0x3fe00)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 (lay + 1))), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x22, BitVec.ofNat 64 (s6v (lay + 1)))]

/-- The constant registers through a layer (after A): `s11 = 0x101 | lay << 16`, the masks, the step registers. -/
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (if lay = 3 then 2 ^ 40 else headerBank 0 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- Lower-chain constants after the header-table entry stub. -/
def lowerLayK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank lay 0)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- Five loads after the forest HASH use the carried `sp = 2^24`, retaining
four other constants. Layer 3 starts at word 661. -/
def ld3Spec : Spec :=
  ⟨[(.x28, .ld (kw DATA)), (.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))),
      (.x27, .ld (kw (DATA + 24))), (.x2, .ld (kw (DATA + 32)))],
    [], 661, false, 5, [], none, 5⟩

def ld3Check : Bool := specB [] [] afterLoadK (runAt carryK [661] 656 []) ld3Spec [] afterLoadK [.x22]

/-- The known registers of B (full E8: the decode reads the answer through `a2`, so `x12` stays symbolic). -/
def bKB (lay : Nat) : List (Reg × Word) := layK lay ++ [(.x10, BitVec.ofNat 64 (encB lay))]
/-- ... and the encoding `ecall`'s arguments. -/
def bK (lay : Nat) : List (Reg × Word) := bKB lay ++ (if lay = 3 then [(.x12, 320)] else [])
/-- The encoding output (`a2`): `0x140` for layer 3; below (full E8) the node slot of the block, `L` or `R`. -/
def dstSet (lay : Nat) : List Nat := if lay = 3 then [320] else [encB lay, encB lay + 48]

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
   [(⟨none, BitVec.ofNat 64 (encB lay + 32)⟩, .bin (.st .w 0) (.ld (kw (encB lay + 32))) (ctrE lay)),
    (⟨none, BitVec.ofNat 64 (encB lay + 24)⟩, tpE lay), (⟨none, BitVec.ofNat 64 (encB lay + 16)⟩, kw (hw 4 lay))],
   p + stepsA lay, true, stepsA lay, [ctrBr lay false], none, stepsA lay⟩

/-- Steps of the counter rejection: A's, plus (E8, below layer 3) the `a0` set before the branch. -/
def rejSt (lay : Nat) : Nat := stepsA lay + (if lay = 3 then 0 else 2)

def rejA (lay p : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)],
   [(⟨none, BitVec.ofNat 64 (encB lay + 24)⟩, tpE lay), (⟨none, BitVec.ofNat 64 (encB lay + 16)⟩, kw (hw 4 lay))],
   rejEcall, true, rejSt lay, [ctrBr lay true], none, rejSt lay⟩

/-! ## B: decode and the chain prologue -/

/-- Full E8: the decode loads the answer through the encoding output pointer (`ld a6, 0(a2)`, `ld a7, 8(a2)`). -/
def a6E : E := .ld (.reg .x12)
def a7E : E := .ld (.bin .add (.reg .x12) (kw 8))
/-- The two loads' validity side conditions (symbolic base `a2`). -/
def ansObl : List Oblig := [.valid ⟨some (.reg .x12), BitVec.ofNat 64 8⟩ 8, .valid ⟨some (.reg .x12), BitVec.ofNat 64 0⟩ 8]
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
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
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
  lowerLayK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay))]

def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [rngBr k true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 22, [ckBr lay true, rngBr 62 false], none, 25⟩

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
    (.x11, 64), (.x28, BitVec.ofNat 64 (headerBank 0 0)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7),
    (.x22, BitVec.ofNat 64 (s6v 0)), (.x19, BitVec.ofNat 64 s3v), (.x24, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]

def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩

/-! ## The leaf-pk block -/

/-- At the leaf-pk block: the layer constants and the chain code's leftovers. -/
def leafK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))] ++ (if lay = 0 then [] else [(.x6, 1)])

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
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false, 11, [],
     some (tgtLf lay), 11⟩

def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 896 else 704)),
    (.x15, 0xce000)] ++ (if lay = 0 then [] else [(.x28, BitVec.ofNat 64 (headerBank 0 0))])

/-! ## The checks of a copy -/

def keepA (lay : Nat) : List Reg := if lay = 3 then [] else [.x12]
def keepB : List Reg := [.x4, .x23, .x30]
def keepLf : List Reg := [.x23, .x30, .x22]

def keepTopCall : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- Full E8: the two answer loads through `a2` and `jal ra` into the shared packed decoder after its loads. -/
def specTopCall (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7E), (.x1, kw (0x1000 + 4 * (p + 19)))], [], 96162, false, 3, [], none, 3⟩

/-- All runs of the transition copy at `p` of layer `lay` and of its leaf-pk block. -/
def copyCheck (lay p : Nat) : Bool :=
  specB (copyAllow lay) [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) (keepA lay) &&
  specB (copyAllow lay) [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] [] (runAt [] [96162] (p + stepsA lay + 1) []) (specTopCall p) ansObl [] keepTopCall
  else
    specB [] [] baseK (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) ansObl
      (postBl lay p) keepB &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) ansObl [] [] &&
    specB [] [] [] (runAt (bKB lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) ansObl [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf

/-- All copies of layer `lay` from index `lo`, `n` of them. -/
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)

end SigGolfCandidate.T3M.CanonicalPort
end CanonicalPortPart25

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart26

/-! # V3: the Merkle shape blocks and the final compare (expected path runs)

After the leaf-pk block (V1's `LeafOut`, at the `stab_lay_0` word of the leaf's low bits), one computed jump per chunk
of the leaf index enters a **shape block** `shp_lay_ci_sh` of straight-line levels (`sh` = the chunk's bits of the leaf;
layer 0 has two chunks, levels 0..5 and 6..11, the other layers one). Level `l` of a block is

    addi a2, s6, cur(l)        -- the HASH below writes the current node into block l (R if bit l of the leaf is 1)
    ecall                      -- l = 0: the leaf-pk HASH (a0, a1 from the leaf-pk block); else block l - 1
    [li a1, 64]                -- after the leaf-pk HASH only
    addi a0, s6, blk(l); sd tp, 16(a0); sw t5, 24(a0)       -- T(3, lay, tree, 0, heap): word 0, the tree
    sw heap, 28(a0)            -- the parent's heap index: a constant register 1..7 (the top three levels),
                               -- `li gp, heap` (the other levels), `srli gp, s7, l + 1` (layer 0, chunk 0)

with `blk(l) = WIT + layerBase lay + 64 (h - 1 - l)` (V1's `s6 - 1024 - 64 (l + 1)`, top `s6 - 960 - 64 (l + 1)`),
`cur(l) = blk(l) + 48 · bit l`. After the last level: the root HASH (`li a2, 0x100 / 0x180; ecall`) followed by the next
layer's transition copy (`trPc (lay - 1) sh`) or a compare copy (`xcmp`); after level 5 of layer 0's chunk 0 the
dispatch `slli a4, gp, 2; add a4, a5; jalr -608(a4)` into `stab_0_1` (gp = s7 >> 6 from the level's heap store).

Families (each a path run checked by `specB`, kernel-checked in `MerkleCheck*`):
* `mkEntCheck lay ci sh`: the table word `j shp_lay_ci_sh` and the first `addi a2`, to the first `ecall` (2 steps);
* `mkLvlCheck lay ci sh kk`: level `mkLo lay ci + kk` from after its `ecall` to the next `ecall` (or through the chunk
  dispatch to its symbolic jump);
* `cmpCheck c`: the compare copy `c` (`ld/ld/bne` twice, HALT(0) / HALT(1)).

Layout facts (word indices, `t3m/images/verify.labels`): `stab_3_0` 209512, `stab_2_0` 209576, `stab_1_0` 209640,
`stab_0_0` 209768, `stab_0_1` 209832; `shp_3_0_sh` = 5487 + 101 sh, `shp_2_0_sh` = 11951 + 101 sh, `shp_1_0_sh` =
18416 + 134 sh, `shp_0_0_sh` = 35567 + 48 sh, `shp_0_1_sh` = 38641 + 53 sh, `xcmp` copy `c` = 38676 + 53 c (checked
against the disassembly by `checks/gen/merkle_check.py`, and by the kernel through the runs below).

BIG2 (Merkle word 0): level 0 keeps `sd tp, 16(a0); sw t5, 20(a0)` and adds `ld tp, 16(a0)`, so `tp` holds the merged
header word 0 (`mkX4`); every later level (including layer 0's chunk 1) stores it with `sd tp, 16(a0)` alone. Each
block's Merkle part is shorter by 4 / 4 / 5 / 4 / 6 words (layers 3, 2, 1, layer 0 chunks 0, 1) and ends where it
did, so its start (the table target) is that many words later (the words before it are unreached `nop`s). -/

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.CanonicalPort.Verify

/-! ## Layout -/

/-- Chunks of the leaf index: layer 0 has two (levels 0..5, 6..11), the others one. -/
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
/-- The first level of chunk `ci`. -/
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
/-- The levels of chunk `ci`. -/
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
/-- The jump table `stab_lay_ci` (word index of its entry 0). -/
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 209832 else stabIdx lay
/-- The shape block `shp_lay_ci_sh` (word index of its first instruction). -/
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 5487 + 101 * sh else if lay = 2 then 11951 + 101 * sh
  else if lay = 1 then 18416 + 134 * sh else if ci = 0 then 35567 + 48 * sh else 38641 + 53 * sh
/-- The parent's heap index is a constant register at the top three levels. -/
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
/-- Instruction words of level `l`: level 0 `addi a2; ecall; li a1; addi a0; sd tp; sw t5; ld tp; [li gp]; sd`
(BIG2: the `ld` makes `tp` the merged header word 0), later levels `addi a2; ecall; addi a0; sd tp; [li gp]; sd`. -/
def mkWords (lay l : Nat) : Nat := (if l = 0 then 8 else 5) + (if mkReg lay l then 0 else 1)
/-- Offset of level `kk` of chunk `ci` from the start of its block. -/
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- W's `layerBase` (the start of layer `lay`'s region, witness offset). -/
def mkBase (lay : Nat) : Nat := [11288, 15768, 18968, 22104].getD lay 0
/-- The Merkle block of level `l`: witness offset (W's `merkleBlock lay l`) and absolute address. -/
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
/-- Its current-node slot when the node is a left (`b = 0`, `L`) or right (`b = 1`, `R`) child. -/
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
/-- The root HASH's destination: the next encoding block's `M` (`0x100`) or the root slot (`0x180`). -/
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then 13336 + 48 * (leaf / 2048 % 2) else 256

/-- The final top HASH retains its current output pointer. -/
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
/-- The parent heap index stored at level `l` of block `sh` (the constant ones). -/
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)

/-! ## Registers -/

/-- The constant registers of the Merkle code (including the leaf-established dispatch window): `t0`, `s2`, `s6`, `tp = T(3)`'s word 0, the heap registers 1..7. -/
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, 0xce000)]

/-- BIG2: the same without `tp` (after level 0 `tp` holds the merged header word 0, `mkX4`). -/
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, 0xce000)]

/-- BIG2: the merged header word 0 (`T(3)`'s word 0 in the low half, `t5` = the tree in the high half). -/
def mkX4 (lay : Nat) : E := .bin (.st .w 4) (kw (hw 3 lay)) (.reg .x30)

/-- Registers that no Merkle run writes or knows (kept for the next transition: `sp`, `s4`, `s5`, `s7`, `s8`, `s11`,
`t3`, `t5`, ...). -/
def mkKeep : List Reg := [.x1, .x2, .x16, .x17, .x19, .x20, .x21, .x23, .x24, .x25, .x27, .x28, .x29, .x30]

/-! ## The entry of a shape block -/

/-- From the table word: `j shp_lay_ci_sh; addi a2, s6, cur(lo)`, stopping at the first `ecall` (no writes). -/
def mkEntSpec (lay ci sh : Nat) : Spec := ⟨[], [], mkShp lay ci sh + 1, true, 2, [], none, 2⟩

def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci) (sh % 2)))]

def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14, .x4]

def mkEntCheck (lay ci sh : Nat) : Bool :=
  specB [] [] baseK (runAt (mkKc lay) [] (mkTab lay ci + sh) []) (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep

/-! ## A level -/

/-- The value of the heap store (`sw heap, 28(a0)`). -/
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 1)) else kw (mkHeap lay ci sh l)

/-- The header word 0 store of level `l`: level 0 stores `T(3)`'s word 0 and the tree (`sd tp; sw t5`), later
levels store the merged `tp` (BIG2). -/
def mkHdrE (lay l : Nat) : E := if l = 0 then mkX4 lay else .reg .x4

/-- The two header writes of level `l`: word 1 `tree | heap << 32` (two `sw`), word 0 `T(3)`. -/
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩, mkHeapE lay ci sh l),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, mkHdrE lay l)]

/-- Level 0's `ld tp` leaves the merged word in `tp` (BIG2); later levels keep `tp`. -/
def mkLvlRegs (lay l : Nat) : List (Reg × E) := if l = 0 then [(.x4, mkX4 lay)] else []

/-- The registers a level keeps: `tp` after level 0. -/
def mkLvlKeep (l : Nat) : List Reg := if l = 0 then [] else [.x4]

def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]

/-- The chunk-1 dispatch target of layer 0 (`((s7 >> 6) << 2) + 0xce000 - 608`, even). -/
def mkDispTgt : E :=
  .bin .and (.bin .add (.bin .sll (.bin .srl (.reg .x23) (kw 6)) (kw 2)) (kw 843168)) (.c (~~~1#64))

/-- Steps of the level body (after its `ecall`, before the next `addi a2` / `li a2` / dispatch). -/
def mkBody (lay l : Nat) : Nat := (if l = 0 then 5 else 2) + (if mkReg lay l then 1 else 2)

/-- Is level `kk` of chunk `ci` the last of a chunk followed by the chunk-1 dispatch? -/
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)

/-- The next `a2`: the next level's current slot, or the root destination. -/
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else if lay = 0 then 13336 + 48 * (sh / 32 % 2) else 256

/-- A level ending at the next `ecall` (the next level's HASH or the root HASH). -/
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk),
    mkShp lay ci sh + mkOff lay ci (kk + 1) + mkMove lay (mkLo lay ci + kk), true,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk), [], none,
    mkBody lay (mkLo lay ci + kk) + mkMove lay (mkLo lay ci + kk)⟩

/-- Level 5 of layer 0's chunk 0, ending with the chunk-1 dispatch (a jump to `stab_0_1`). -/
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨mkLvlRegs lay (mkLo lay ci + kk), mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false,
    mkBody lay (mkLo lay ci + kk) + 3, [], some mkDispTgt,
    mkBody lay (mkLo lay ci + kk) + 3⟩

/-- Known at the level body's start: the constants (with `tp = T(3)`'s word 0 at level 0 only), and `a1 = 64` after
the leaf-pk HASH. -/
def mkLvlK (lay l : Nat) : List (Reg × Word) := if l = 0 then mkK lay else mkKc lay ++ [(.x11, 64)]

def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]

def mkLvlPostD (lay ci kk : Nat) : List (Reg × Word) :=
  mkKc lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))), (.x15, 0xce000)]

def mkLvlKN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkLvlK lay (mkLo lay ci + kk) ++
    (if lay = 0 ∧ mkLo lay ci + kk = 11 then
      [(.x12, BitVec.ofNat 64 (13336 + 48 * (sh / 32 % 2)))] else [])

def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [])
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep (mkLo lay ci + kk)))

def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlK lay (mkLo lay ci + kk)) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp])
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci kk) (mkKeep ++ mkLvlKeep (mkLo lay ci + kk))

def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk

/-! ## Blocks -/

/-- The levels of a chunk with code: all for the top layer; below it (E8) the last level's header and the root HASH
are gone, the next transition's copy follows HASH `h - 1`. -/
def mkLvls (lay ci : Nat) : Nat := if lay = 0 then mkBits lay ci else mkBits lay ci - 1

/-- The entry and every level of block `sh` of chunk `ci` of layer `lay`. -/
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkLvls lay ci)).all (mkLvlCheck lay ci sh)

/-- Blocks `lo .. lo + n - 1` of chunk `ci` of layer `lay`. -/
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)

/-! ## The compare -/

/-- The compare copy `c` (after layer 0's shape block `shp_0_1_c`). -/
def cmpPc (c : Nat) : Nat := 38675 + 53 * c
def cmpDst (c : Nat) : Nat := 13336 + 48 * (c / 32 % 2)
def cmpK (c : Nat) : List (Reg × Word) := baseK ++ [(.x12, BitVec.ofNat 64 (cmpDst c))]
def cmpBr1 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c)), .ld (kw 160), d⟩
def cmpBr2 (c : Nat) (d : Bool) : Br := ⟨.ne, .ld (kw (cmpDst c + 8)), .ld (kw 168), d⟩

/-- The high-word difference is zero exactly when the high words agree. -/
def cmpDelta (c : Nat) : E := .bin .sub (.ld (kw (cmpDst c + 8))) (.ld (kw 168))

/-- Low words agree: high-word difference is the HALT exit code. -/
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta c)], [], cmpPc c + 7, true, 7, [cmpBr1 c false], none, 7⟩
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 c true], none, 5⟩
def cmpCheck (c : Nat) : Bool :=
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (runAt (cmpK c) [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []

end SigGolfCandidate.T3M.CanonicalPort
end CanonicalPortPart26

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart27

/-! # The final comparison using the HALT exit code

The root stays at its route-specific x12 destination. The low-word mismatch branches to the unchanged HALT(1) arm. Otherwise a subtraction of the high
words supplies the HALT exit code, which is zero exactly when those words agree. Every accepting
path takes seven instructions followed by HALT; the fuel bound conservatively remains nine.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.CanonicalPort
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.CanonicalPort.Verify
open SigGolfCandidate.T3 (Digest)

/-- A digest is determined by its two doublewords. -/
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]

/-- The state at a compare copy. -/
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c) ∧ KnownOK (cmpK c) t ∧ DigAt t (cmpDst c) root
  pk : PkOK pk t

theorem cmpBr1_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c)) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

theorem cmpBr2_holds (c : Nat) (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 c d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

set_option maxRecDepth 100000

/-- All 64 actual comparison copies satisfy the two complete path specifications. -/
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel

theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)

/-- Comparing both words by the final HALT exit code takes at most eight cycles. -/
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc, hknown, hroot⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 (cmpDst c)) = root.extractLsb' 0 64 := hroot.1
  have hr8 : t.getMem (BitVec.ofNat 64 (cmpDst c + 8)) = root.extractLsb' 64 64 := hroot.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds c t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc hknown (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta c) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc hknown (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart27

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
section CanonicalPortPart28

/-! Kernel check of every transition copy of the four layers (`copyCheck`): the transitions, their rejections and
the leaf-pk blocks. -/

namespace SigGolfCandidate.T3M.CanonicalPort

set_option maxRecDepth 100000

theorem ld3Check_ok : ld3Check = true := by decide +kernel
theorem layerCheck_3 : layerCheck 3 0 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 0 64 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 0 64 = true := by decide +kernel
theorem layerCheck_0a : layerCheck 0 0 64 = true := by decide +kernel
theorem layerCheck_0b : layerCheck 0 64 64 = true := by decide +kernel

theorem nCopy_eq : nCopy 3 = 1 ∧ nCopy 2 = 64 ∧ nCopy 1 = 64 ∧ nCopy 0 = 128 := by decide

theorem copyCheck_at (lay c : Nat) (hlay : lay < 4) (hc : c < nCopy lay) : copyCheck lay (trPc lay c) = true := by
  obtain ⟨n3, n2, n1, n0⟩ := nCopy_eq
  have hall : ∀ lo n, layerCheck lay lo n = true → lo ≤ c → c < lo + n → copyCheck lay (trPc lay c) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h c (List.mem_range'_1.mpr ⟨h1, h2⟩)
  interval_cases lay
  · by_cases h : c < 64
    · exact hall 0 64 layerCheck_0a (by omega) (by omega)
    · exact hall 64 64 layerCheck_0b (by omega) (by omega)
  · exact hall 0 64 layerCheck_1 (by omega) (by omega)
  · exact hall 0 64 layerCheck_2 (by omega) (by omega)
  · exact hall 0 1 layerCheck_3 (by omega) (by omega)

end SigGolfCandidate.T3M.CanonicalPort

end CanonicalPortPart28
