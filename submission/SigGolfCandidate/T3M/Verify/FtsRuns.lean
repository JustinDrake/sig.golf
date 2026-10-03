import SigGolfCandidate.T3M.Verify.FtsLayout
import SigGolfCandidate.T3M.Verify.FtsRev

/-!
# The FTS stream machine: layout and expected symbolic results of its code blocks (T3M verify)

Code (instruction indices of the frozen image, `t3m/images/verify.labels`): `fts_setup` 362; leaf `s = 3 c + j` at
`leafPc s` (10 / 9 / 10 instructions for `j = 0, 1, 2`: table switch, `ld s7, ETAB + 8 s`, the leaf block's `T`, the
dispatch `lbu gp, 880(a4); slli 7; add s4; jalr s8`); `coord_end_c` at `coordEndPc c`; `forest` 622; the segment tables
`ptab_n` 222208 / `ptab_l` 230400 (256 slots of 32 words); `entry0_{M,P,F}` 4841 / 4856 / 4862; the ladders `lad_X_t_r` at
`ladBase X t + 7 r` (`X` = 0 M (merge), 1 P (push), 2 F (final)); `tailPc X c` selects the shared or inline
tail after the destination hash.

Families (each a path run checked by `specB` in `FtsCheck`):
* `setupCheck'` (362 → 387), `leafCheck s` (to the dispatch), `dispCheck pc` (a dispatch, stopping at the symbolic
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
def tbN : Nat := 0xda000
def tbL : Nat := 0xe2000
/-- Merge frame `d` (`[pnode | T | 0 | node]`, its `Q` at `- 16`; frame 0 = the empty stack, `Q` slot = sentinel). -/
def frameA (d : Nat) : Nat := 0x600 + 80 * d
def SENTINEL : Nat := 0x5F0
def FOREST : Nat := 0x700
/-- The forest-frame slot of coordinate `c`'s root (`[root_0 | T | root_1 .. root_6]`). -/
def forestSlot (c : Nat) : Nat := if c = 0 then 0x700 else 0x710 + 16 * c

/-- Constant registers of the FTS phase: `t0`, `s2`, `a1 = 64`, `t4 = A4_LIMIT`, `t6 = 1 << 16`, the two tables, `t1 = 1`, and `s3 = frameA 0`. -/
def gkF : List (Reg × Word) :=
  carryK ++ [(.x11,64),(.x29,BitVec.ofNat 64 A4_LIMIT),(.x24,0x10000),(.x16,BitVec.ofNat 64 tbN),
    (.x21,BitVec.ofNat 64 tbL),(.x30,0x8000000000000000),(.x1,BitVec.ofNat 64 (frameA 0)),
    (.x6,1),(.x26,6),(.x31,7)]

/-- The coordinate words: `s11 = w0` of a node header, `t3 = w0` of a leaf header (coordinate `c`). -/
def ckF (c : Nat) : List (Reg × Word) :=
  [(.x27, BitVec.ofNat 64 (0xa01 + 65536 * c)), (.x28, BitVec.ofNat 64 (0x901 + 65536 * c))]

/-- Fully assembled node and leaf address words, each including the fixed tree index. -/
def packedCK (c index : Nat) : List (Reg × Word) :=
  [(.x27, BitVec.ofNat 64 (hdr1 (0xa01 + 65536 * c) index)),
   (.x28, BitVec.ofNat 64 (hdr1 (0x901 + 65536 * c) index))]

/-- Both coordinate words are dynamic packed headers; no per-coordinate compile-time registers remain. -/
def leafCK (_c : Nat) : List (Reg × Word) := []

def leafPc (s : Nat) : Nat := 387 + 34 * (s / 3) + (if s % 3 = 0 then 0 else if s % 3 = 1 then 10 else 19)
/-- The dispatch (`lbu`) of leaf `s`. -/
def leafDisp (s : Nat) : Nat := leafPc s + (if s % 3 = 1 then 5 else 6)
/-- The link of leaf `s`'s dispatch: the next leaf, or `coord_end` after leaf 2. -/
def leafRet (s : Nat) : Nat := leafPc s + (if s % 3 = 1 then 9 else 10)
def coordEndPc (c : Nat) : Nat := 387 + 34 * c + 29
def forestPc : Nat := 622
/-- The layer-3 transition (`xtr3_1`), right after the forest HASH. -/
def layerPc : Nat := 630

/-- The table of leaf position `j` (`0` = `ptab_n`: push variant; `1` = `ptab_l`: final variant). -/
def tselJ (j : Nat) : Nat := if j = 2 then 1 else 0
def tabPc (tb : Nat) : Nat := if tb = 0 then tbN else tbL
def tabBase (tb : Nat) : Nat := if tb = 0 then 222208 else 230400
def slotPc (tb b : Nat) : Nat := tabBase tb + 32 * b

/-- Dense segment header byte `b`: `b % 16` folds, `b / 16 % 2` merge flag, and `b / 32` containing three branch sides. Fold counts12..15 reject. -/
def segSides (b : Nat) : Nat := b / 32
def segA (b : Nat) : Nat := b % 16
def segM (b : Nat) : Nat := b / 16 % 2
def segT (b : Nat) : Nat := b / 32 % 2
/-- The variant of byte `b` in table `tb`: merge `0`, push `1`, final `2`. -/
def segX (tb b : Nat) : Nat := if segM b = 1 then 0 else if tb = 0 then 1 else 2

/-- Small complete graphs; merge with three folds still uses the shared ladder. -/
def inlineRow (X a : Nat) : Prop := a ≤ 2 ∨ (a = 3 ∧ X ≠ 0)
instance (X a : Nat) : Decidable (inlineRow X a) := inferInstanceAs (Decidable (_ ∨ _))
def rowPrefix (a : Nat) : Nat := if a = 0 then 3 else if a = 1 then 4 else 5
def rowTable (tb X : Nat) : Nat := if X = 0 then tb else if X = 1 then 0 else 1
def rowByte (X a bits : Nat) : Nat := a + (if X = 0 then 16 else 0) + 32 * bits
def rowPc (tb X a bits : Nat) : Nat := slotPc (rowTable tb X) (rowByte X a bits)
def inlineTailId (tb a bits : Nat) : Nat := 77 + 32 * tb + 8 * a + bits
def entrySteps (tb b : Nat) : Nat := if inlineRow (segX tb b) (segA b) then 0 else 1

def ladBase (X t : Nat) : Nat :=
  if X = 0 then (if t = 0 then 4865 else 4975)
  else if X = 1 then (if t = 0 then 5085 else 5186)
  else (if t = 0 then 5287 else 5385)
def ladPc (X t r : Nat) : Nat := ladBase X t + 7 * r
/-- `lbr_X_t_r` (`r ≥ 1`): the `addi a2` before the rung hash of fold `r - 1`. -/
def lbrPc (X t r : Nat) : Nat := ladBase X t + 7 * r - 2
def entry0Pc (X : Nat) : Nat := if X = 0 then 4841 else if X = 1 then 4856 else 4862
/-- The tail after the destination hash: copies 0..76 are shared tails; copies 77..140 select inline rows.
Unused merge/a=3 combinations duplicate an a=0 tail. -/
def tailPc (X c : Nat) : Nat :=
  if c < 77 then
    if c < 3 then (if c = 2 then entry0Pc X + 2 else ladPc X c 10 + 6) else (threeTails.getD X []).getD (c-3) 0
  else
    let a := (c-77)/8%4
    let a := if X = 0 ∧ a = 3 then 0 else a
    rowPc ((c-77)/32) X a ((c-77)%8) + rowPrefix a + 6*a
/-- The dispatch inside the merge tail copy `c`. -/
def mDispPc (c : Nat) : Nat := tailPc 0 c + 7

/-! ## Expression helpers -/

def rE (r : Reg) : E := .reg r
/-- `x14 + k` as the executor builds it. -/
def a4E (k : Nat) : E := addC (.reg .x14) (BitVec.ofNat 64 k)
def a4A (k : Nat) : Addr := ⟨some (.reg .x14), BitVec.ofNat 64 k⟩
def notOne : E := .c (~~~1#64)
def eHalf : E := .bin .sll (.reg .x23) (cw 1)
/-- Both halves of a header word 1 written by `sw s6, 24; sw v, 28` over the old word `old`. -/
def sw2E (old v : E) : E := .bin (.st .w 4) (.bin (.st .w 0) old (.reg .x22)) v
/-- Fixed index in the upper half of the tag word. -/
def swTreeE (tag : E) : E := .bin (.st .w 4) tag (.reg .x22)


/-! ## Setup -/

def setupPost : List (Reg × Word) :=
  gkF ++ leafCK 0 ++ [(.x14, BitVec.ofNat 64 A4_0), (.x15, BitVec.ofNat 64 (frameA 0)), (.x25, BitVec.ofNat 64 FOREST)]

/-- Setup words 362..368 load `sp`, four embedded data constants (words 5..8), and the two code-table
bases via LUI. The remaining setup is words 369..386 and falls through into the main loop at 387. -/
def setupLdK : List (Reg × Word) :=
  baseK ++ [(.x2,0x1000000),(.x14, BitVec.ofNat 64 A4_0), (.x29, BitVec.ofNat 64 A4_LIMIT), (.x27, BitVec.ofNat 64 0xa01),
    (.x28, BitVec.ofNat 64 0x901), (.x16, BitVec.ofNat 64 tbN), (.x21, BitVec.ofNat 64 tbL)]

def setupLdSpec : Spec :=
  ⟨[(.x2,cw 0x1000000),(.x14, .ld (cw (DATA + 40))), (.x29, .ld (cw (DATA + 48))), (.x27, .ld (cw (DATA + 56))),
      (.x28, .ld (cw (DATA + 64))), (.x16, cw tbN), (.x21, cw tbL)],
    [], 369, false, 7, [], none, 7⟩

def setupLdCheckF : Bool := specB [] [] baseK (runAt baseK [369] 362 []) setupLdSpec [] baseK [.x22]

def setupSpecF : Spec :=
  ⟨[(.x27, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0xa01)),
    (.x28, .bin .add (.bin .sll (.reg .x22) (cw 32)) (cw 0x901))],
    [(⟨none, BitVec.ofNat 64 SENTINEL⟩, cw 1)], 387, false, 18, [], none, 18⟩

def setupCheckF : Bool := specB [] [] gkF (runAt setupLdK [387] 369 []) setupSpecF [] setupPost [.x22]

/-- The ten gate bits are N[246..255] = word3[54..63]; accepted iff below 135 (`srli 54; sltiu 135; beqz`). -/
def gateEF : E := .bin .sltu (.bin .srl (.reg .x28) (cw 54)) (cw 135)
def gateBrF (reject : Bool) : Br := ⟨.eq, gateEF, cw 0, reject⟩
def gateCheckF : Bool :=
  specB [] [] baseK (runAt baseK [362] 359 [.br false])
    ⟨[], [], 362, false, 3, [gateBrF false], none, 3⟩ [] baseK selKeep
def gateRejectCheckF : Bool :=
  specB [] [] [] (runAt baseK [] 359 [.br true]) (rejSpec 6 [gateBrF true]) [] [] []

/-! ## Leaf code (to the dispatch) -/

def ETABs (s : Nat) : Nat := ETAB + 8 * s
def leafT (s : Nat) : Nat := WIT + 64 + 48 * s + 16

def leafKnown (s : Nat) : List (Reg × Word) :=
  gkF ++ leafCK (s / 3) ++ (if s % 3 = 1 then [(.x20, BitVec.ofNat 64 tbN)] else [])

def etabA (s : Nat) : Addr := ⟨some (.ld (cw (ETABs s))), 16⟩

def leafSpec (s : Nat) : Spec :=
  ⟨[(.x23, .ld (addC (.ld (cw (ETABs s))) 16#64)), (.x10, cw (WIT + 64 + 48 * s))],
    [(⟨none, BitVec.ofNat 64 (leafT s + 8)⟩, .ld (addC (.ld (cw (ETABs s))) 16#64)),
      (⟨none, BitVec.ofNat 64 (leafT s)⟩, .reg .x28)],
    leafDisp s, false, (if s % 3 = 1 then 5 else 6), [], none, (if s % 3 = 1 then 5 else 6)⟩

/-- The side conditions of the table read: it is valid and misses the leaf's header word 0. -/
def leafObl (s : Nat) : List Oblig := [.ne (etabA s) ⟨none, BitVec.ofNat 64 (leafT s)⟩, .valid (etabA s) 8]

/-- Path runs with `noAlias` (the table read sits behind the header store). -/
def cfgN : Config := { noAlias := true }
def runAtN (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfgN vlook (stops.map pcOf) 2000 (pcOf n) dirs (σK known) []

def leafPost (s : Nat) : List (Reg × Word) :=
  gkF ++ leafCK (s / 3) ++ [(.x20, BitVec.ofNat 64 (tabPc (tselJ (s % 3))))]

/-- The two words of leaf `s`'s header slot (the only witness words the leaf code writes). -/
def leafAllow (s : Nat) : List Nat := [leafT s, leafT s + 8]

def leafCheck (s : Nat) : Bool :=
  specB (leafAllow s) [] gkF (runAtN (leafKnown s) [leafDisp s] (leafPc s) []) (leafSpec s) (leafObl s) (leafPost s)
    [.x14, .x15, .x22, .x25, .x27, .x28]

/-! ## Dispatch -/

/-- The header byte `lbu gp, 880(a4)`. -/
def hdrByteE : E := .un (.ld .bu 0) (.ld (a4E 880))
def dispT : E := .bin .add (.bin .sll hdrByteE (cw 7)) (.reg .x20)
def dispObl : List Oblig := [.align8 (.reg .x14), .valid (a4A 880) 1]

/-- A dispatch at `pc` (`link`: the link register is set to `pc + 4 + 3 = ret`). -/
def dispSpec (link : Option Nat) : Spec :=
  ⟨[(.x3, dispT)] ++ (match link with | some r => [(.x17, cw (0x1000 + 4 * r))] | none => []), [],
    0, false, 4, [], some (.bin .and dispT notOne), 4⟩

def dispKeep : List Reg := [.x10, .x14, .x15, .x20, .x22, .x23, .x25, .x27, .x28]

def dispCheck (pc : Nat) (link : Option Nat) : Bool :=
  specB [] [] gkF (runAt gkF [] pc [.jmp]) (dispSpec link) dispObl gkF
    (dispKeep ++ (match link with | some _ => [] | none => [.x17]))

def leafDispCheck (s : Nat) : Bool := dispCheck (leafDisp s) (some (leafRet s))
def mDispCheck (c : Nat) : Bool := dispCheck (mDispPc c) none

/-! ## Table slots -/

/-- The destination of the last hash of variant `X`: merge frame `+48`, next frame `+0`, forest slot. -/
def destE (X : Nat) : E :=
  if X = 0 then .bin .add (.reg .x15) (cw 48) else if X = 1 then .bin .add (.reg .x15) (cw 80) else .reg .x25

def parE (a : Nat) : E := .bin .srl (.reg .x23) (cw (64-min a 3))
/-- The slot checks the low `min a 4` bits against the dense header's side code; `d` means the mismatch branch is taken. -/
def parBr (a bits : Nat) (d : Bool) : Br :=
  if a=1 then ⟨if bits%2=1 then .ge else .lt, .reg .x23, cw 0, d⟩
  else ⟨.ne, parE a, cw (T3.Rev.revBits (min a 3) (bits % segSideMod a)), d⟩

/-- A relocated HALT(1) stub. Its address is part of the checked specification. -/
def ftsRejSpec (pc steps : Nat) (brs : List Br) : Spec := { rejSpec steps brs with pc := pc }
def rowTailLen (X : Nat) : Nat := if X=0 then 11 else if X=1 then 4 else 1
def slotRejectPc (tb b : Nat) : Nat :=
  slotPc tb b + (if inlineRow (segX tb b) (segA b) then
    rowPrefix (segA b) + 6*segA b + rowTailLen (segX tb b) + 2 else 10)

def slotSpec (tb b : Nat) : Spec :=
  let a := segA b
  if 11 < a then ftsRejSpec (slotPc tb b+2) 2 []
  else if a = 0 then
    ⟨[(.x14,a4E 8),(.x12,destE (segX tb b))],[],slotPc tb b+2,true,2,[],none,2⟩
  else
    ⟨[(.x14,a4E (8+80*a)),(.x12,a4E (888+48*segT b))],[],slotPc tb b+3+(if a=1 then 0 else 1),true,
      3+(if a=1 then 0 else 1),[parBr a (b/32) false],none,3+(if a=1 then 0 else 1)⟩

def slotKeep : List Reg := [.x10, .x15, .x20, .x22, .x23, .x17, .x25, .x27, .x28]

def slotCheck1 (tb b : Nat) : Bool :=
  if 11 < segA b then specB [] [] [] (runAt gkF [] (slotPc tb b) []) (slotSpec tb b) [] [] []
  else if segA b = 0 then specB [] [] gkF (runAt gkF [] (slotPc tb b) []) (slotSpec tb b) [] gkF slotKeep
  else
    specB [] [] gkF (runAt gkF [] (slotPc tb b) [.br false]) (slotSpec tb b) [] gkF slotKeep &&
    specB [] [] [] (runAt gkF [] (slotPc tb b) [.br true]) (ftsRejSpec (slotRejectPc tb b) (4+(if segA b=1 then 0 else 1)) [parBr (segA b) (b / 32) true]) [] [] []

def slotCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => slotCheck1 tb b

/-- Actual fold start: small rows are contiguous, other rows retain their shared ladders. -/
def foldPc (tb X a bits t i : Nat) : Nat :=
  if inlineRow X a then rowPc tb X a bits + rowPrefix a + 6*i
  else if a=1 then ladPc X t 10 else threeFoldPc X a bits t i

def foldTailId (tb X a bits t : Nat) : Nat :=
  if inlineRow X a then inlineTailId tb a bits
  else if a=1 then t else threeTailId a bits t

def entSpec (tb b : Nat) : Spec :=
  ⟨[], [], foldPc tb (segX tb b) (segA b) (segSides b) (segT b) 0, false, entrySteps tb b, [], none, entrySteps tb b⟩

/-- After the pending hash: inline rows are already at the fold; otherwise execute the jump. -/
def entCheck1 (tb b : Nat) : Bool :=
  segA b = 0 || 11 < segA b ||
    (if inlineRow (segX tb b) (segA b) then
      decide (slotPc tb b + 4 + (if segA b=1 then 0 else 1) = (entSpec tb b).pc)
    else
    specB [] [] gkF (runAt gkF [foldPc tb (segX tb b) (segA b) (segSides b) (segT b) 0] (slotPc tb b + 4 + (if segA b=1 then 0 else 1)) [])
      (entSpec tb b) [] gkF
      [.x10, .x12, .x14, .x15, .x20, .x22, .x23, .x17, .x25, .x27, .x28])

def entCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => entCheck1 tb b

/-! ## Rungs -/

def rungMem (r : Nat) : List (Addr × E) :=
  [(a4A (80 * r + 24), eHalf), (a4A (80 * r + 16), .reg .x27)]

def rungObl (r : Nat) : List Oblig :=
  [.valid (a4A (80 * r + 24)) 8, .valid (a4A (80 * r + 16)) 8]

/-- The next fold's side `t' = (E >> 1) & 1` as the sign of `(E >> 1) << 63`. -/
def sideE : E := eHalf
def crossD (t t' : Nat) : Bool := decide (t ≠ t')
def rungBr (t t' : Nat) : Br := ⟨if t = 1 then .ge else .lt, sideE, .c 0, crossD t t'⟩

def rungSteps (i a : Nat) : Nat := if i+1<a then (if i<2 then 5 else 6) else 5

def rungSpec (tb X a bits t i t' : Nat) : Spec :=
  let r := 11-a+i
  ⟨[(.x10, a4E (80*r)), (.x23, eHalf), (.x12, a4E (80*(r+1)+48*t'))], rungMem r,
    foldPc tb X a bits t' (i+1)-1, true, rungSteps i a,
    (if i<2 then [] else [rungBr t t']), none, rungSteps i a⟩

def rungKeep : List Reg := [.x14, .x15, .x20, .x22, .x17, .x25, .x27, .x28]

def rungCheck1 (tb X a bits t i t' : Nat) : Bool :=
  specB [] [.x14] gkF
    (runAt gkF [] (foldPc tb X a bits t i) (if i<2 then [] else [.br (crossD t t')]))
    (rungSpec tb X a bits t i t') (rungObl (11-a+i)) gkF rungKeep

def lastSpec (tb X a bits t : Nat) : Spec :=
  ⟨[(.x10, a4E 800), (.x23, eHalf), (.x12, destE X)], rungMem 10,
    tailPc X (foldTailId tb X a bits t)-1, true, 5, [], none, 5⟩

def lastCheck1 (tb X a bits t : Nat) : Bool :=
  specB [] [.x14] gkF (runAt gkF [] (foldPc tb X a bits t (a-1)) [])
    (lastSpec tb X a bits t) (rungObl 10) gkF rungKeep

/-- First three nonfinal sides are fixed by the checked header; later sides are read dynamically. -/
def rungSides (bits i t t' : Nat) : Prop :=
  i<2 → t=bits/2^i%2 ∧ t'=bits/2^(i+1)%2
instance (bits i t t' : Nat) : Decidable (rungSides bits i t t') := inferInstanceAs (Decidable (_ → _))

def rungCheck : Bool :=
  (List.range 3).all fun X => (List.range' 1 11).all fun a => (List.range 2).all fun tb => (List.range 8).all fun bits =>
    (List.range 2).all fun t =>
      ((lastCheck1 tb X a bits t) &&
       (List.range (a-1)).all fun i => (List.range 2).all fun t' =>
          (!decide (rungSides bits i t t') || rungCheck1 tb X a bits t i t'))

/-! ## Tails -/


def ka5 (d : Nat) : List (Reg × Word) := gkF ++ [(.x15, BitVec.ofNat 64 (frameA d))]

def qBr (d : Nat) (dd : Bool) : Br := ⟨.ne, .ld (cw (frameA d - 16)), .reg .x23, dd⟩

def tailMSpec (c d : Nat) : Spec :=
  ⟨[(.x23, eHalf), (.x10, cw (frameA d)), (.x15, cw (frameA d - 80))],
    [(⟨none, BitVec.ofNat 64 (frameA d + 24)⟩, eHalf),
      (⟨none, BitVec.ofNat 64 (frameA d + 16)⟩, .reg .x27)],
    mDispPc c, false, 7, [qBr d false], none, 7⟩

def tailMCheck1 (c d : Nat) : Bool :=
  (d = 0 || specB [] [] gkF (runAt (ka5 d) [mDispPc c] (tailPc 0 c) [.br false]) (tailMSpec c d) []
      (ka5 (d - 1)) [.x14, .x20, .x22, .x17, .x25, .x27, .x28]) &&
  specB [] [] [] (runAt (ka5 d) [] (tailPc 0 c) [.br true])
    (ftsRejSpec (if c < 77 then rejectPc else tailPc 0 c + 13) (if c < 77 then 5 else 4) [qBr d true]) [] [] []

def tailPSpec (d : Nat) : Spec :=
  ⟨[(.x3, .bin .xor (.reg .x23) (cw (2 ^ 63)))],
    [(⟨none, BitVec.ofNat 64 (frameA (d + 1) - 16)⟩, .bin .xor (.reg .x23) (cw (2 ^ 63)))],
    0, false, 4, [], some (.bin .and (.reg .x17) notOne), 4⟩

def tailPCheck1 (c d : Nat) : Bool :=
  specB [] [] gkF (runAt (ka5 d) [] (tailPc 1 c) [.jmp]) (tailPSpec d) [] (ka5 (d + 1))
    [.x14, .x20, .x22, .x23, .x17, .x25, .x27, .x28]

def tailFSpec : Spec := ⟨[], [], 0, false, 1, [], some (.bin .and (.reg .x17) notOne), 1⟩

def tailFCheck1 (c : Nat) : Bool :=
  specB [] [] gkF (runAt gkF [] (tailPc 2 c) [.jmp]) tailFSpec [] gkF
    [.x14, .x15, .x20, .x22, .x23, .x17, .x25, .x27, .x28]

def tailCheck : Bool :=
  (List.range 141).all fun c =>
    tailFCheck1 c && tailPCheck1 c 0 && tailPCheck1 c 1 && tailMCheck1 c 0 && tailMCheck1 c 1 && tailMCheck1 c 2

/-! ## Coordinate end and forest -/

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
    629, true, 7, [capBr false], none, 7⟩
def forestCheckF : Bool :=
  specB [] [] carryK (runAt gkF [] forestPc [.br false]) forestSpecF [] carryK [.x22] &&
  specB [] [] [] (runAt gkF [] forestPc [.br true]) (rejSpec 4 [capBr true]) [] [] []

end SigGolfCandidate.T3M.Verify
