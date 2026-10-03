import SigGolfCandidate.T3M.Verify.Spec

/-! # V1 layers: the transition copies and the leaf-pk blocks (expected path runs)

Every start of layer `lay` runs its own copy of the transition (`trPc lay c`, `xtrTab`): layer 3 one copy after the
forest hash (with the layer constants `hyper`), layers 2, 1 one per shape block of layer `lay + 1`'s Merkle code
(64, 64), layer 0 one per shape block of layer 1 (128). A copy is

* **A** (`specA`, up to the encoding `ecall`): `[sub s11, s8]`, the route (`s7 = 2^h | leaf`, `t5 = tree`,
  `tp = tree | leaf << 32`), the encoding header `T(4, lay, tree, 0, leaf)` at `0x110`, the counter (`lwu` from the
  witness header) checked `< 2^22` and stored at `0x120`, `a0 = 0x100`, `a2 = 0x140`;
* **B** (`specBl` lower / `specBt` top, after the `ecall`, up to the `jalr ra` into the chain code): the decode
  (range `srli 62` / `srli 61`, the SWAR sums of `Decode`, the unsigned checksum test against carried `7` / the total `126`), the chain
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
  [[18450, 18584, 18718, 18852, 18986, 19120, 19254, 19388, 19522, 19656, 19790, 19924, 20058, 20192, 20326, 20460,
    20594, 20728, 20862, 20996, 21130, 21264, 21398, 21532, 21666, 21800, 21934, 22068, 22202, 22336, 22470, 22604,
    22738, 22872, 23006, 23140, 23274, 23408, 23542, 23676, 23810, 23944, 24078, 24212, 24346, 24480, 24614, 24748,
    24882, 25016, 25150, 25284, 25418, 25552, 25686, 25820, 25954, 26088, 26222, 26356, 26490, 26624, 26758, 26892,
    27026, 27160, 27294, 27428, 27562, 27696, 27830, 27964, 28098, 28232, 28366, 28500, 28634, 28768, 28902, 29036,
    29170, 29304, 29438, 29572, 29706, 29840, 29974, 30108, 30242, 30376, 30510, 30644, 30778, 30912, 31046, 31180,
    31314, 31448, 31582, 31716, 31850, 31984, 32118, 32252, 32386, 32520, 32654, 32788, 32922, 33056, 33190, 33324,
    33458, 33592, 33726, 33860, 33994, 34128, 34262, 34396, 34530, 34664, 34798, 34932, 35066, 35200, 35334, 35468],
   [11980, 12081, 12182, 12283, 12384, 12485, 12586, 12687, 12788, 12889, 12990, 13091, 13192, 13293, 13394, 13495,
    13596, 13697, 13798, 13899, 14000, 14101, 14202, 14303, 14404, 14505, 14606, 14707, 14808, 14909, 15010, 15111,
    15212, 15313, 15414, 15515, 15616, 15717, 15818, 15919, 16020, 16121, 16222, 16323, 16424, 16525, 16626, 16727,
    16828, 16929, 17030, 17131, 17232, 17333, 17434, 17535, 17636, 17737, 17838, 17939, 18040, 18141, 18242, 18343],
   [5516, 5617, 5718, 5819, 5920, 6021, 6122, 6223, 6324, 6425, 6526, 6627, 6728, 6829, 6930, 7031,
    7132, 7233, 7334, 7435, 7536, 7637, 7738, 7839, 7940, 8041, 8142, 8243, 8344, 8445, 8546, 8647,
    8748, 8849, 8950, 9051, 9152, 9253, 9354, 9455, 9556, 9657, 9758, 9859, 9960, 10061, 10162, 10263,
    10364, 10465, 10566, 10667, 10768, 10869, 10970, 11071, 11172, 11273, 11374, 11475, 11576, 11677, 11778, 11879],
   [634]]

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
def stepsA (lay : Nat) : Nat := if lay = 3 then 15 else if lay = 0 then 15 else 14
/-- The return pc of the chain code (the leaf-pk block) relative to the copy. -/
def retOff (lay : Nat) : Nat := if lay = 0 then 19 else if lay = 3 then 45 else 44
/-- The chain base register value: lower layers `WIT + chainBase + 1024`; the top `WIT + chainBase + 960`. -/
def s6v (lay : Nat) : Nat := [15064, 19288, 22424, 25560].getD lay 0
/-- The top's base for its chains 0 .. 48 (`s3`). -/
def s3v : Nat := 15768
/-- Core's targets. -/
def tgtL (lay : Nat) : Nat := [126, 195, 195, 195].getD lay 0
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
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x19, BitVec.ofNat 64 (2^62)), (.x22, BitVec.ofNat 64 (s6v (lay + 1)))]

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
Layer 3 starts at word 634. -/
def ld3Spec : Spec :=
  ⟨[(.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))),
      (.x27, .ld (kw (DATA + 24))), (.x2, .ld (kw (DATA + 32)))],
    [], 634, false, 4, [], none, 4⟩

def ld3Check : Bool := specB [] [] afterLoadK (runAt carryK [634] 630 []) ld3Spec [] afterLoadK [.x22]

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
def rngBr (k : Nat) (d : Bool) : Br :=
  if k = 62 then ⟨.geu, a7E, kw (2^62), d⟩ else ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.ltu, kw 7, t4E lay, d⟩
/-- `a7 = (v1 << 1) | v0 >> 63`. -/
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
/-- The dispatch into `ttab` slot 0 (lower) / `qtab` slot 0 (top). -/
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))

def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE), (.x25, sumE), (.x29, t4E lay), (.x3, .bin .srl a6E (kw 63)), (.x14, x14l)],
   [], 0, false, 28, [ckBr lay false, rngBr 62 false], some tgtl, 31⟩

def postBl (lay p : Nat) : List (Reg × Word) :=
  lowerLayK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay - 1))]

def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, (if k = 62 then 6 else 7), [rngBr k true], none, (if k = 62 then 6 else 7)⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 20, [ckBr lay true, rngBr 62 false], none, 23⟩

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

end SigGolfCandidate.T3M
