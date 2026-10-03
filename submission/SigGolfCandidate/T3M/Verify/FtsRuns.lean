import SigGolfCandidate.T3M.Verify.Select
import SigGolfCandidate.T3M.Verify.FtsRev

/-!
# The FTS stream machine: layout and expected symbolic results of its code blocks (T3M verify)

Code (instruction indices of the frozen image, `t3m/images/verify.labels`): `fts_setup` 380; leaf `s = 3 c + j` at
`leafPc s` (7 instructions each, F4: the leaf block's `T` word 0, F5: `ld s7, 24(a0)` (the
header word 1 the selection stored), the
dispatch `lbu gp, 880(a4); slli 5; add s10 / s5; jalr s8`); `coord_end_c` at `coordEndPc c`; `forest` 648; the segment tables
`ptab_n` 744 / `ptab_l` 2792 (256 slots of 8 words); `entry0_{M,P,F}` 4841 / 4856 / 4862; the ladders `lad_X_t_r` at
`ladBase X t + 8 r` (`X` = 0 M (merge), 1 P (push), 2 F (final)); their tails after the destination hash
(`tailPc X c`, copy `c` = ladder `t` or `2` = `entry0_X`).

Families (each a path run checked by `specB` in `FtsCheck`):
* `setupCheck'` (380 → 469), `leafCheck s` (to the dispatch), `dispCheck pc` (a dispatch, stopping at the symbolic
  slot address), `slotCheck tb b` (to the pending hash / HALT(1)), `entCheck tb b` (`j lad`), `rungCheck X t r t'`
  (fold `r` to its hash, switching to ladder `t'`), `lastCheck X t` (rung 10 to the destination hash),
  `tailMCheck c d`, `tailPCheck c d`, `tailFCheck c`, `coordCheck c`, `forestCheck`.
-/

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Layout -/

/-- `a4` before the first segment: the header is read at `a4 + 880 = WIT + 1088`. -/
def A4_0 : Nat := 2256
/-- `a4` after 35 segments with exactly 115 folds (`t4`): the pointer cap. -/
def A4_LIMIT : Nat := 11736
def tbN : Nat := 0x1000 + 4 * 744
def tbL : Nat := 0x1000 + 4 * 2792
/-- Merge frame `d` (`[pnode | T | 0 | node]`, its `Q` at `- 16`; frame 0 = the empty stack, `Q` slot = sentinel). -/
def frameA (d : Nat) : Nat := 0x600 + 80 * d
def SENTINEL : Nat := 0x5F0
def FOREST : Nat := 0x700
/-- The forest-frame slot of coordinate `c`'s root (`[root_0 | T | root_1 .. root_6]`). -/
def forestSlot (c : Nat) : Nat := if c = 0 then 0x700 else 0x710 + 16 * c

/-- Constant registers of the FTS phase: `t0`, `s2`, `a1 = 64`, `t4 = A4_LIMIT`, `t6 = 1 << 16`, the two tables,
`t1 = 2^63` (n3-99: the bit-reversed root `FtsRev.rv 1` and the sibling mask), `s3 = frameA 0`. -/
def gkF : List (Reg × Word) :=
  baseK ++ [(.x11, 64), (.x29, BitVec.ofNat 64 A4_LIMIT), (.x31, 0x10000), (.x26, BitVec.ofNat 64 tbN),
    (.x21, BitVec.ofNat 64 tbL), (.x6, BitVec.ofNat 64 (2 ^ 63)), (.x19, BitVec.ofNat 64 (frameA 0))]

/-- The coordinate words: `s11 = w0` of a node header, `t3 = w0` of a leaf header (coordinate `c`). -/
def ckF (c : Nat) : List (Reg × Word) :=
  [(.x27, BitVec.ofNat 64 (0xa01 + 65536 * c)), (.x28, BitVec.ofNat 64 (0x901 + 65536 * c))]

/-- Fully assembled node and leaf address words, each including the fixed tree index. -/
def packedCK (c index : Nat) : List (Reg × Word) :=
  [(.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) index)),
   (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) index))]

/-- Both coordinate words are dynamic packed headers; no per-coordinate compile-time registers remain. -/
def leafCK (_c : Nat) : List (Reg × Word) := []

/-- F4: every leaf code is 7 words (no table switch: the dispatch adds the table register itself); the leaf code
block ends at the forest, so it starts at 469. -/
def leafPc (s : Nat) : Nat := 469 + 26 * (s / 3) + 7 * (s % 3)
/-- The dispatch (`lbu`) of leaf `s`. -/
def leafDisp (s : Nat) : Nat := leafPc s + 3
/-- The link of leaf `s`'s dispatch: the next leaf, or `coord_end` after leaf 2. -/
def leafRet (s : Nat) : Nat := leafPc s + 7
def coordEndPc (c : Nat) : Nat := 469 + 26 * c + 21
def forestPc : Nat := 648
/-- The layer-3 transition (`xtr3_1`), right after the forest HASH. -/
def layerPc : Nat := 656

/-- The table of leaf position `j` (`0` = `ptab_n`: push variant; `1` = `ptab_l`: final variant). -/
def tselJ (j : Nat) : Nat := if j = 2 then 1 else 0
def tabPc (tb : Nat) : Nat := if tb = 0 then tbN else tbL
/-- F4: the register holding table `tb`'s address (`s10 = tbN`, `s5 = tbL`, both constants of `gkF`, so the
dispatch's `add gp, gp, s10 / s5` folds to the table address). -/
def tabReg (tb : Nat) : Reg := if tb = 0 then .x26 else .x21
def tabBase (tb : Nat) : Nat := if tb = 0 then 744 else 2792
def slotPc (tb b : Nat) : Nat := tabBase tb + 8 * b

/-- Segment header byte `b`: `a = b % 16` folds, merge bit, parity bit `t`. -/
def segA (b : Nat) : Nat := b % 16
def segM (b : Nat) : Nat := b / 16 % 2
def segT (b : Nat) : Nat := b / 32 % 2
/-- The variant of byte `b` in table `tb`: merge `0`, push `1`, final `2`. -/
def segX (tb b : Nat) : Nat := if segM b = 1 then 0 else if tb = 0 then 1 else 2

def ladBase (X t : Nat) : Nat :=
  if X = 0 then (if t = 0 then 4865 else 4975)
  else if X = 1 then (if t = 0 then 5085 else 5186)
  else (if t = 0 then 5287 else 5385)
def ladPc (X t r : Nat) : Nat := ladBase X t + 7 * r
/-- `lbr_X_t_r` (`r ≥ 1`): the `addi a2` before the rung hash of fold `r - 1`. -/
def lbrPc (X t r : Nat) : Nat := ladBase X t + 7 * r - 2
def entry0Pc (X : Nat) : Nat := if X = 0 then 4841 else if X = 1 then 4856 else 4862
/-- The tail after the destination hash, copy `c` (`0, 1` = last rung of ladder `t = c`; `2` = `entry0_X`). -/
def tailPc (X c : Nat) : Nat := if c = 2 then entry0Pc X + 2 else ladPc X c 10 + 6
/-- The dispatch inside the merge tail copy `c`. -/
def mDispPc (c : Nat) : Nat := tailPc 0 c + 7

/-- F4: the merge code (`entry0_M` and both merge ladders with their tails, words 4841 .. 5084) has a second copy at
the end of the image (word 210432) for table `ptab_l` (`tb = 1`); it re-dispatches through `s5` instead of `s10`.
`cpOff tb X` is the offset of the copy that variant `X` of table `tb` runs in. -/
def MOFF : Nat := 210432 - 4841
def cpOff (tb X : Nat) : Nat := if X = 0 ∧ tb = 1 then MOFF else 0
def ladPcT (tb X t r : Nat) : Nat := ladPc X t r + cpOff tb X
def lbrPcT (tb X t r : Nat) : Nat := lbrPc X t r + cpOff tb X
def entry0PcT (tb X : Nat) : Nat := entry0Pc X + cpOff tb X
def tailPcT (tb X c : Nat) : Nat := tailPc X c + cpOff tb X
def mDispPcT (tb c : Nat) : Nat := mDispPc c + cpOff tb 0

/-! ## Expression helpers -/

def rE (r : Reg) : E := .reg r
/-- `x14 + k` as the executor builds it. -/
def a4E (k : Nat) : E := addC (.reg .x14) (BitVec.ofNat 64 k)
def a4A (k : Nat) : Addr := ⟨some (.reg .x14), BitVec.ofNat 64 k⟩
def notOne : E := .c (~~~1#64)
/-- t3-rl2: the parent `FtsRev.rv (E / 2)` of `x23 = FtsRev.rv E` (`slli x23, x23, 1`). -/
def eHalf : E := .bin .sll (.reg .x23) (cw 1)
/-- Both halves of a header word 1 written by `sw s6, 24; sw v, 28` over the old word `old`. -/
def sw2E (old v : E) : E := .bin (.st .w 4) (.bin (.st .w 0) old (.reg .x22)) v
/-- Fixed index in the upper half of the tag word. -/
def swTreeE (tag : E) : E := .bin (.st .w 4) tag (.reg .x22)


/-! ## Setup -/

def setupPost : List (Reg × Word) :=
  gkF ++ leafCK 0 ++ [(.x14, BitVec.ofNat 64 A4_0), (.x15, BitVec.ofNat 64 (frameA 0)), (.x25, BitVec.ofNat 64 FOREST)]

/-- T3K: the setup's six constants are loaded from the embedded data (words 383 .. 389: `lui sp, 0x1000` and six
`ld`, data words 5 .. 10); the rest of the setup is words 390 .. 400 and `j 469` at 401 (n3-99: `slli t1, gp, 63` at 392:
`t1 = 2^63`, the relabelled root `FtsRev.rv 1` and the sibling mask). -/
def setupLdK : List (Reg × Word) :=
  baseK ++ [(.x14, BitVec.ofNat 64 A4_0), (.x29, BitVec.ofNat 64 A4_LIMIT), (.x27, BitVec.ofNat 64 0xa01),
    (.x28, BitVec.ofNat 64 0x901), (.x26, BitVec.ofNat 64 tbN), (.x21, BitVec.ofNat 64 tbL)]

def setupLdSpec : Spec :=
  ⟨[(.x14, .ld (cw (DATA + 40))), (.x29, .ld (cw (DATA + 48))), (.x27, .ld (cw (DATA + 56))),
      (.x28, .ld (cw (DATA + 64))), (.x26, .ld (cw (DATA + 72))), (.x21, .ld (cw (DATA + 80)))],
    [], 390, false, 7, [], none, 7⟩

def setupLdCheckF : Bool := specB [] [] baseK (runAt baseK [390] 383 []) setupLdSpec [] baseK [.x22]

def setupSpecF : Spec :=
  ⟨[(.x27, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0xa01)),
    (.x28, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0x901))],
    [(⟨none, BitVec.ofNat 64 SENTINEL⟩, .c (-1#64))], 469, false, 12, [], none, 12⟩

def setupCheckF : Bool := specB [] [] gkF (runAt setupLdK [469] 390 []) setupSpecF [] setupPost [.x22]

/-- The three gate bits are N[206..208] = word3[14..16]. -/
def gateEF : E := .bin .and (.bin .srl (.reg .x28) (cw 14)) (cw 7)
def gateBrF (reject : Bool) : Br := ⟨.ne, gateEF, cw 0, reject⟩
def gateCheckF : Bool :=
  specB [] [] baseK (runAt baseK [383] 380 [.br false])
    ⟨[], [], 383, false, 3, [gateBrF false], none, 3⟩ [] baseK (.x2 :: selKeep)
def gateRejectCheckF : Bool :=
  specB [] [] [] (runAt baseK [] 380 [.br true]) (rejSpec 6 [gateBrF true]) [] [] []

/-! ## Leaf code (to the dispatch) -/

def ETABs (s : Nat) : Nat := ETAB + 8 * s
def leafT (s : Nat) : Nat := WIT + 64 + 48 * s + 16

def leafKnown (s : Nat) : List (Reg × Word) :=
  gkF ++ leafCK (s / 3)

/-- F5: `addi a0, s2, ...; sd t3, 16(a0); ld s7, 24(a0)`: the header word 1 the selection stored in the leaf block. -/
def leafSpec (s : Nat) : Spec :=
  ⟨[(.x23, .ld (cw (leafT s + 8))), (.x10, cw (WIT + 64 + 48 * s))],
    [(⟨none, BitVec.ofNat 64 (leafT s)⟩, .reg .x28)],
    leafDisp s, false, 3, [], none, 3⟩

/-- Path runs with `noAlias` (kept for the other FTS families). -/
def cfgN : Config := { noAlias := true }
def runAtN (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfgN vlook (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

def leafPost (s : Nat) : List (Reg × Word) :=
  gkF ++ leafCK (s / 3)

/-- F5: word 0 of leaf `s`'s header slot (the only witness word the leaf code writes). -/
def leafAllow (s : Nat) : List Nat := [leafT s]

def leafCheck (s : Nat) : Bool :=
  specB (leafAllow s) [] gkF (runAt (leafKnown s) [leafDisp s] (leafPc s) []) (leafSpec s) [] (leafPost s)
    [.x14, .x15, .x22, .x25, .x27, .x28]

/-! ## Dispatch -/

/-- The header byte `lbu gp, 880(a4)`. -/
def hdrByteE : E := .un (.ld .bu 0) (.ld (a4E 880))
def dispT (tb : Nat) : E := .bin .add (.bin .sll hdrByteE (cw 5)) (cw (tabPc tb))
def dispObl : List Oblig := [.align8 (.reg .x14), .valid (a4A 880) 1]

/-- A dispatch at `pc` (`link`: the link register is set to `pc + 4 + 3 = ret`). -/
def dispSpec (tb : Nat) (link : Option Nat) : Spec :=
  ⟨[(.x3, dispT tb)] ++ (match link with | some r => [(.x24, cw (0x1000 + 4 * r))] | none => []), [],
    0, false, 4, [], some (.bin .and (dispT tb) notOne), 4⟩

def dispKeep : List Reg := [.x10, .x14, .x15, .x20, .x22, .x23, .x25, .x27, .x28]

def dispCheck (pc tb : Nat) (link : Option Nat) : Bool :=
  specB [] [] gkF (runAt gkF [] pc [.jmp]) (dispSpec tb link) dispObl gkF
    (dispKeep ++ (match link with | some _ => [] | none => [.x24]))

def leafDispCheck (s : Nat) : Bool := dispCheck (leafDisp s) (tselJ (s % 3)) (some (leafRet s))
def mDispCheck (tb c : Nat) : Bool := dispCheck (mDispPcT tb c) tb none

/-! ## Table slots -/

/-- The destination of the last hash of variant `X`: merge frame `+48`, next frame `+0`, forest slot. -/
def destE (X : Nat) : E :=
  if X = 0 then .bin .add (.reg .x15) (cw 48) else if X = 1 then .bin .add (.reg .x15) (cw 80) else .reg .x25

/-- t3-rl2: the slot's side test on the sign of `x23 = FtsRev.rv E` (`t = 1`: `bge`, `t = 0`: `blt` to the bad slot),
`d` = taken (reject). -/
def parBr (t : Nat) (d : Bool) : Br := ⟨if t = 1 then .ge else .lt, .reg .x23, .c 0, d⟩

def slotSpec (tb b : Nat) : Spec :=
  let a := segA b
  if 11 < a then rejSpec 4 []
  else if a = 0 then
    ⟨[(.x14, a4E 8), (.x12, destE (segX tb b))], [], entry0PcT tb (segX tb b) + 1, true, 3, [], none, 3⟩
  else
    ⟨[(.x14, a4E (8 + 80 * a)), (.x12, a4E (888 + 48 * segT b))], [], slotPc tb b + 3, true, 3,
      [parBr (segT b) false], none, 3⟩

def slotKeep : List Reg := [.x10, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28]

def slotCheck1 (tb b : Nat) : Bool :=
  if 11 < segA b then specB [] [] [] (runAt gkF [] (slotPc tb b) []) (slotSpec tb b) [] [] []
  else if segA b = 0 then specB [] [] gkF (runAt gkF [] (slotPc tb b) []) (slotSpec tb b) [] gkF slotKeep
  else
    specB [] [] gkF (runAt gkF [] (slotPc tb b) [.br false]) (slotSpec tb b) [] gkF slotKeep &&
    specB [] [] [] (runAt gkF [] (slotPc tb b) [.br true]) (rejSpec 6 [parBr (segT b) true]) [] [] []

def slotCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => slotCheck1 tb b

/-- After the pending hash of a slot with `a ≥ 1`: `j lad_X_t_(11 - a)`. -/
def entCheck1 (tb b : Nat) : Bool :=
  segA b = 0 || 11 < segA b ||
    specB [] [] gkF (runAt gkF [ladPcT tb (segX tb b) (segT b) (11 - segA b)] (slotPc tb b + 4) [])
      ⟨[], [], ladPcT tb (segX tb b) (segT b) (11 - segA b), false, 1, [], none, 1⟩ [] gkF
      [.x10, .x12, .x14, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28]

def entCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => entCheck1 tb b

/-! ## Rungs -/

def rungMem (r : Nat) : List (Addr × E) :=
  [(a4A (80 * r + 24), eHalf), (a4A (80 * r + 16), .reg .x27)]

def rungObl (r : Nat) : List Oblig :=
  [.valid (a4A (80 * r + 24)) 8, .valid (a4A (80 * r + 16)) 8]

/-- t3-rl2: the next fold's side `t' = (E / 2) % 2` as the sign of `FtsRev.rv (E / 2)`. -/
def sideE : E := eHalf
def crossD (t t' : Nat) : Bool := decide (t ≠ t')
def rungBr (t t' : Nat) : Br := ⟨if t = 1 then .ge else .lt, sideE, .c 0, crossD t t'⟩

def rungSpec (tb X t r t' : Nat) : Spec :=
  ⟨[(.x10, a4E (80 * r)), (.x23, eHalf), (.x12, a4E (80 * (r + 1) + 48 * t'))], rungMem r,
    lbrPcT tb X t' (r + 1) + 1, true, 6, [rungBr t t'], none, 6⟩

def rungKeep : List Reg := [.x14, .x15, .x20, .x22, .x24, .x25, .x27, .x28]

def rungCheck1 (tb X t r t' : Nat) : Bool :=
  specB [] [.x14] gkF (runAt gkF [] (ladPcT tb X t r) [.br (crossD t t')]) (rungSpec tb X t r t') (rungObl r) gkF
    rungKeep

def lastSpec (tb X : Nat) (t : Nat) : Spec :=
  ⟨[(.x10, a4E 800), (.x23, eHalf), (.x12, destE X)], rungMem 10, ladPcT tb X t 10 + 5, true, 5, [], none, 5⟩

def lastCheck1 (tb X t : Nat) : Bool :=
  specB [] [.x14] gkF (runAt gkF [] (ladPcT tb X t 10) []) (lastSpec tb X t) (rungObl 10) gkF rungKeep

def rungCheck : Bool :=
  (List.range 2).all fun tb => (List.range 3).all fun X => (List.range 2).all fun t =>
    lastCheck1 tb X t && (List.range 10).all fun r => (List.range 2).all fun t' => rungCheck1 tb X t r t'

/-! ## Tails -/

def ka5 (d : Nat) : List (Reg × Word) := gkF ++ [(.x15, BitVec.ofNat 64 (frameA d))]

def qBr (d : Nat) (dd : Bool) : Br := ⟨.ne, .ld (cw (frameA d - 16)), .reg .x23, dd⟩

def tailMSpec (tb c d : Nat) : Spec :=
  ⟨[(.x23, eHalf), (.x10, cw (frameA d)), (.x15, cw (frameA d - 80))],
    [(⟨none, BitVec.ofNat 64 (frameA d + 24)⟩, eHalf),
      (⟨none, BitVec.ofNat 64 (frameA d + 16)⟩, .reg .x27)],
    mDispPcT tb c, false, 7, [qBr d false], none, 7⟩

def tailMCheck1 (tb c d : Nat) : Bool :=
  (d = 0 || specB [] [] gkF (runAt (ka5 d) [mDispPcT tb c] (tailPcT tb 0 c) [.br false]) (tailMSpec tb c d) []
      (ka5 (d - 1)) [.x14, .x20, .x22, .x24, .x25, .x27, .x28]) &&
  specB [] [] [] (runAt (ka5 d) [] (tailPcT tb 0 c) [.br true]) (rejSpec 5 [qBr d true]) [] [] []

def tailPSpec (d : Nat) : Spec :=
  ⟨[(.x3, .bin .xor (.reg .x23) (cw (2 ^ 63)))],
    [(⟨none, BitVec.ofNat 64 (frameA (d + 1) - 16)⟩, .bin .xor (.reg .x23) (cw (2 ^ 63)))],
    0, false, 4, [], some (.bin .and (.reg .x24) notOne), 4⟩

def tailPCheck1 (c d : Nat) : Bool :=
  specB [] [] gkF (runAt (ka5 d) [] (tailPc 1 c) [.jmp]) (tailPSpec d) [] (ka5 (d + 1))
    [.x14, .x20, .x22, .x23, .x24, .x25, .x27, .x28]

def tailFSpec : Spec := ⟨[], [], 0, false, 1, [], some (.bin .and (.reg .x24) notOne), 1⟩

def tailFCheck1 (c : Nat) : Bool :=
  specB [] [] gkF (runAt gkF [] (tailPc 2 c) [.jmp]) tailFSpec [] gkF
    [.x14, .x15, .x20, .x22, .x23, .x24, .x25, .x27, .x28]

def tailCheck : Bool :=
  (List.range 3).all fun c =>
    tailFCheck1 c && tailPCheck1 c 0 && tailPCheck1 c 1 && tailMCheck1 0 c 0 && tailMCheck1 0 c 1 &&
      tailMCheck1 0 c 2 && tailMCheck1 1 c 0 && tailMCheck1 1 c 1 && tailMCheck1 1 c 2

/-! ## Coordinate end and forest -/

/-- n3-99: the root test `x23 ≠ t1 = 2^63 = FtsRev.rv 1` (`bne s7, t1`). -/
def eBr (d : Bool) : Br := ⟨.ne, .reg .x23, cw (2 ^ 63), d⟩
def sBr (d : Bool) : Br := ⟨.ne, .reg .x15, .c (BitVec.ofNat 64 (frameA 0)), d⟩

def coordKnown (c : Nat) : List (Reg × Word) := gkF ++ leafCK c ++ [(.x25, BitVec.ofNat 64 (forestSlot c))]
def coordNext (c : Nat) : Nat := if c < 6 then leafPc (3 * (c + 1)) else forestPc
def coordPost (c : Nat) : List (Reg × Word) := if c < 6 then coordKnown (c + 1) else coordKnown c

def coordSpec (c : Nat) : Spec :=
  ⟨[(.x27, if c < 6 then .bin .add (.reg .x27) (cw 65536) else .reg .x27),
    (.x28, if c < 6 then .bin .add (.reg .x28) (cw 65536) else .reg .x28)],
    [], coordNext c, false, if c < 6 then 5 else 2, [sBr false, eBr false], none, if c < 6 then 5 else 2⟩

def coordCheck1 (c : Nat) : Bool :=
  specB [] [] gkF (runAt (coordKnown c) [coordNext c] (coordEndPc c) [.br false, .br false]) (coordSpec c) []
    (coordPost c) [.x14, .x15, .x22, .x23] &&
  specB [] [] [] (runAt (coordKnown c) [] (coordEndPc c) [.br true]) (rejSpec 4 [eBr true]) [] [] [] &&
  specB [] [] [] (runAt (coordKnown c) [] (coordEndPc c) [.br false, .br true])
    (rejSpec 5 [sBr true, eBr false]) [] [] []

def capBr (d : Bool) : Br := ⟨.ltu, .c (BitVec.ofNat 64 A4_LIMIT), .reg .x14, d⟩

def forestSpecF : Spec :=
  ⟨[(.x10, cw FOREST), (.x11, cw 128), (.x12, cw 0x100)],
    [(⟨none, BitVec.ofNat 64 (FOREST + 24)⟩, .reg .x22), (⟨none, BitVec.ofNat 64 (FOREST + 16)⟩, cw 0xb01)],
    655, true, 7, [capBr false], none, 7⟩

def forestCheckF : Bool :=
  specB [] [] baseK (runAt gkF [] forestPc [.br false]) forestSpecF [] baseK [.x22] &&
  specB [] [] [] (runAt gkF [] forestPc [.br true]) (rejSpec 4 [capBr true]) [] [] []

end SigGolfCandidate.T3M.Verify
