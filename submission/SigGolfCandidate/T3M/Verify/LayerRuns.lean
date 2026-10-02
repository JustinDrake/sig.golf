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
  [[18460, 18594, 18728, 18862, 18996, 19130, 19264, 19398, 19532, 19666, 19800, 19934, 20068, 20202, 20336, 20470,
    20604, 20738, 20872, 21006, 21140, 21274, 21408, 21542, 21676, 21810, 21944, 22078, 22212, 22346, 22480, 22614,
    22748, 22882, 23016, 23150, 23284, 23418, 23552, 23686, 23820, 23954, 24088, 24222, 24356, 24490, 24624, 24758,
    24892, 25026, 25160, 25294, 25428, 25562, 25696, 25830, 25964, 26098, 26232, 26366, 26500, 26634, 26768, 26902,
    27036, 27170, 27304, 27438, 27572, 27706, 27840, 27974, 28108, 28242, 28376, 28510, 28644, 28778, 28912, 29046,
    29180, 29314, 29448, 29582, 29716, 29850, 29984, 30118, 30252, 30386, 30520, 30654, 30788, 30922, 31056, 31190,
    31324, 31458, 31592, 31726, 31860, 31994, 32128, 32262, 32396, 32530, 32664, 32798, 32932, 33066, 33200, 33334,
    33468, 33602, 33736, 33870, 34004, 34138, 34272, 34406, 34540, 34674, 34808, 34942, 35076, 35210, 35344, 35478],
   [11989, 12090, 12191, 12292, 12393, 12494, 12595, 12696, 12797, 12898, 12999, 13100, 13201, 13302, 13403, 13504,
    13605, 13706, 13807, 13908, 14009, 14110, 14211, 14312, 14413, 14514, 14615, 14716, 14817, 14918, 15019, 15120,
    15221, 15322, 15423, 15524, 15625, 15726, 15827, 15928, 16029, 16130, 16231, 16332, 16433, 16534, 16635, 16736,
    16837, 16938, 17039, 17140, 17241, 17342, 17443, 17544, 17645, 17746, 17847, 17948, 18049, 18150, 18251, 18352],
   [5525, 5626, 5727, 5828, 5929, 6030, 6131, 6232, 6333, 6434, 6535, 6636, 6737, 6838, 6939, 7040,
    7141, 7242, 7343, 7444, 7545, 7646, 7747, 7848, 7949, 8050, 8151, 8252, 8353, 8454, 8555, 8656,
    8757, 8858, 8959, 9060, 9161, 9262, 9363, 9464, 9565, 9666, 9767, 9868, 9969, 10070, 10171, 10272,
    10373, 10474, 10575, 10676, 10777, 10878, 10979, 11080, 11181, 11282, 11383, 11484, 11585, 11686, 11787, 11888],
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
/-- Steps of A (layer 3 includes the `hyper` constants; layer 0 has `mv` and `lui; or`). -/
def stepsA (lay : Nat) : Nat := if lay = 3 then 23 else if lay = 0 then 15 else 15
/-- The return pc of the chain code (the leaf-pk block) relative to the copy. -/
def retOff (lay : Nat) : Nat := if lay = 3 then 55 else if lay = 0 then 67 else 47
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

/-- The known registers at a transition start (layer 3: `t0`, `s2` and the FTS's `t1 = 1`; `hyper` sets the rest). -/
def preK (lay : Nat) : List (Reg × Word) :=
  if lay = 3 then baseK ++ [(.x6, 1), (.x21, BitVec.ofNat 64 M2c), (.x20, BitVec.ofNat 64 M1c),
    (.x27, BitVec.ofNat 64 (hw 1 3)), (.x2, 0x3fe00)]
  else baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 (lay + 1))), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (2 ^ 40)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- The constant registers through a layer (after A): `s11 = 0x101 | lay << 16`, the masks, the step registers. -/
def layK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay)), (.x24, 0x10000), (.x2, 0x3fe00),
    (.x20, BitVec.ofNat 64 M1c), (.x21, BitVec.ofNat 64 M2c), (.x11, 64), (.x28, BitVec.ofNat 64 (2 ^ 40)),
    (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7)]

/-- After the forest HASH (word 656) a load block (656 .. 659: four `ld` through `sp`, which still holds the data
page set by the FTS setup) sets four of layer 3's constants (the SWAR masks, `s11`, and finally `sp` itself); the
transition copy proper starts at 660 (`trPc 3 0`). -/
def ld3Spec : Spec :=
  ⟨[(.x21, .ld (kw (DATA + 8))), (.x20, .ld (kw (DATA + 16))), (.x27, .ld (kw (DATA + 24))),
      (.x2, .ld (kw (DATA + 32)))],
    [], 660, false, 4, [], none, 4⟩

def ld3Check : Bool :=
  specB [] [] baseK (runAt (baseK ++ [(.x2, 0x1000000)]) [660] 656 []) ld3Spec [] baseK [.x22, .x6]

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
def sw1E : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl a6E (kw 3)) (kw M1c)) (.bin .and a6E (kw M1c)))
    (.bin .and (.bin .srl b1E (kw 3)) (kw M1c))) (.bin .and b1E (kw M1c))
def sumE : E := .bin .remu (.bin .and (.bin .add sw1E (.bin .srl sw1E (kw 6))) (kw M2c)) (kw 4095)
def t4E (lay : Nat) : E := .bin .sub (kw (tgtL lay)) sumE
def rngBr (k : Nat) (d : Bool) : Br := ⟨.ne, .bin .srl a7E (kw k), kw 0, d⟩
def ckBr (lay : Nat) (d : Bool) : Br := ⟨.eq, .bin .sltu (t4E lay) (kw 8), kw 0, d⟩
/-- `a7 = (v1 << 1) | v0 >> 63`. -/
def a7lE : E := .bin .or b1E (.bin .srl a6E (kw 63))
/-- The dispatch into `ttab` slot 0 (lower) / `qtab` slot 0 (top). -/
def x14l : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 0x6e000)
def tgtl : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x3fe00)) (kw 448800)) (.c (~~~1#64))

def specBl (lay p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, a7lE), (.x25, sumE), (.x29, t4E lay), (.x3, .bin .srl a6E (kw 63)), (.x14, x14l)],
   [], 0, false, 31, [ckBr lay false, rngBr 62 false], some tgtl, 34⟩

def postBl (lay p : Nat) : List (Reg × Word) :=
  layK lay ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x15, 0x6e000), (.x1, pcOf (p + retOff lay))]

def rejRng (k : Nat) : Spec := ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 7, [rngBr k true], none, 7⟩
def rejCk (lay : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 25, [ckBr lay true, rngBr 62 false], none, 28⟩

/-- The top decode's sums: the 3-bit SWAR of `g = v1 >>> 34` (`remu 4095` into `t4`), the 2-bit SWAR of `v0` and
`c = v1 mod 2^34` (`remu 255`), the total. -/
def gE : E := .bin .srl a7E (kw 34)
def p3E : E := .bin .add (.bin .and (.bin .srl gE (kw 3)) (kw M1c)) (.bin .and gE (kw M1c))
def s3E : E := .bin .remu (.bin .and (.bin .add p3E (.bin .srl p3E (kw 6))) (kw M2c)) (kw 4095)
def c34E : E := .bin .srl (.bin .sll a7E (kw 30)) (kw 30)
def l1E : E := .bin .add (.bin .and (.bin .srl a6E (kw 2)) (kw M4c)) (.bin .and a6E (kw M4c))
def l2E : E := .bin .add (.bin .and (.bin .srl c34E (kw 2)) (kw M4c)) (.bin .and c34E (kw M4c))
def lE : E := .bin .add l1E l2E
def pE : E := .bin .add (.bin .and (.bin .srl lE (kw 4)) (kw M8c)) (.bin .and lE (kw M8c))
def totE : E := .bin .add (.bin .remu pE (kw 255)) s3E
def totBr (d : Bool) : Br := ⟨.ne, totE, kw 126, d⟩
def x14t : E := .bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 0xae000)
def tgtt : E := .bin .and (.bin .add (.bin .and (.bin .sll a6E (kw 9)) (kw 0x1fe00)) (kw 711072)) (.c (~~~1#64))

def specBt (p : Nat) : Spec :=
  ⟨[(.x16, a6E), (.x17, .bin .sll a7E (kw 2)), (.x3, totE), (.x14, x14t), (.x25, .bin .and c34E (kw M4c))],
   [], 0, false, 51, [totBr false, rngBr 61 false], some tgtt, 57⟩

/-- After the top decode: the 2-bit masks, the quad mask in `s8`, `t4 = 8` (no checksum chain). -/
def postBt (p : Nat) : List (Reg × Word) :=
  baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 0)), (.x2, 0x3fe00), (.x20, BitVec.ofNat 64 M4c), (.x21, BitVec.ofNat 64 M8c),
    (.x11, 64), (.x28, BitVec.ofNat 64 (2 ^ 40)), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7),
    (.x22, BitVec.ofNat 64 (s6v 0)), (.x19, BitVec.ofNat 64 s3v), (.x24, 0x1fe00), (.x29, 8), (.x15, 0xae000),
    (.x1, pcOf (p + retOff 0))]

def rejTot : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], rejEcall, true, 42, [totBr true, rngBr 61 false], none, 48⟩

/-! ## The leaf-pk block -/

/-- At the leaf-pk block: the layer constants and the chain code's leftovers. -/
def leafK (lay : Nat) : List (Reg × Word) := baseK ++ [(.x27, BitVec.ofNat 64 (hw 1 lay))]

/-- The dispatch target in `stab_lay_0` (`(s7 << 2 &&& mask) + window + imm`). -/
def x14lf (lay : Nat) : E :=
  if lay = 0 then .bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay))) (kw 0xce000)
  else .bin .add (.bin .sll (.reg .x23) (kw 2)) (kw 0xce000)
def tgtLfOld (lay : Nat) : E :=
  .bin .and (.bin .add (.bin .and (.bin .sll (.reg .x23) (kw 2)) (kw (stabMask lay)))
    (kw (0x1000 + 4 * stabIdx lay))) (.c (~~~1#64))

/-- Lower-layer sentinel bits are absorbed by the jump displacement (from ae21d3da). -/
def tgtLf (lay : Nat) : E :=
  if lay = 0 then tgtLfOld lay
  else .bin .and (.bin .add (.bin .sll (.reg .x23) (kw 2))
    (kw (0x1000 + 4 * stabIdx lay - 4 * 2 ^ hL lay))) (.c (~~~1#64))

def specLf (lay : Nat) : Spec :=
  if lay = 0 then
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 1464⟩, kw 0), (⟨none, BitVec.ofNat 64 1456⟩, kw 0), (⟨none, BitVec.ofNat 64 536⟩, .reg .x4),
      (⟨none, BitVec.ofNat 64 528⟩, kw (hw 2 0))], 0, false, 13, [], some (tgtLf lay), 13⟩
  else
    ⟨[(.x14, x14lf lay)],
     [(⟨none, BitVec.ofNat 64 792⟩, .reg .x4), (⟨none, BitVec.ofNat 64 784⟩, kw (hw 2 lay))], 0, false, 10, [],
     some (tgtLf lay), 10⟩

def postLf (lay : Nat) : List (Reg × Word) :=
  leafK lay ++ [(.x3, BitVec.ofNat 64 (hw 2 lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)),
    (.x10, BitVec.ofNat 64 (if lay = 0 then 512 else 768)), (.x11, BitVec.ofNat 64 (if lay = 0 then 960 else 704)),
    (.x15, 0xce000)]

/-! ## The checks of a copy -/

def keepA : List Reg := []
def keepB : List Reg := [.x4, .x23, .x30]
def keepLf : List Reg := [.x23, .x30, .x22]

/-- All runs of the transition copy at `p` of layer `lay` and of its leaf-pk block. -/
def copyCheck (lay p : Nat) : Bool :=
  specB [] [] baseK (runAt (preK lay) [] p [.br false]) (specA lay p) [] (bK lay) keepA &&
  specB [] [] [] (runAt (preK lay) [] p [.br true]) (rejA lay p) [] [] [] &&
  (if lay = 0 then
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBt p) [] (postBt p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) rejTot [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 61) [] [] []
  else
    specB [] [] baseK (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br false, .jmp]) (specBl lay p) []
      (postBl lay p) keepB &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br false, .br true]) (rejCk lay) [] [] [] &&
    specB [] [] [] (runAt (bK lay) [] (p + stepsA lay + 1) [.br true]) (rejRng 62) [] [] []) &&
  specB [] [] baseK (runAt (leafK lay) [] (p + retOff lay) [.jmp]) (specLf lay) [] (postLf lay) keepLf

/-- All copies of layer `lay` from index `lo`, `n` of them. -/
def layerCheck (lay lo n : Nat) : Bool := (List.range' lo n).all fun c => copyCheck lay (trPc lay c)

end SigGolfCandidate.T3M
