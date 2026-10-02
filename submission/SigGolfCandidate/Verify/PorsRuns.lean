import SigGolfCandidate.Verify.PorsMem

/-!
# The PORS stack machine: expected symbolic results of its code blocks

Families (each a list of path runs, checked by `pspecB` in the `PorsCheck*` files):

* `setup`: falling through from the digest HASH to `leaf_0` (leaf index table, tweak words, guard);
* `leaf s` (`s < 15`): pi byte, `x = PIND[pi & 0x78 / 8]`, the order checks, leaf tweak, secret,
  `E = x | 2^14`, `a0 = CB`, up to the dispatch (the rejects: HALT(1));
* `disp c` (`c < 18`): the dispatch `lbu T, 0(FR); slli; add TB; jalr` of leaf `c` (link `x24`)
  or of the merge tail copy `c - 15` (no link), stopping at the symbolic table entry;
* `tab tb b` (`tb < 2`, `b < 256`): the 8-word table slot `b` (`FR += 64 a + 64`, then for `a = 0`
  `j entry0_V`, for `a ≥ 1` the inlined entry code) up to the pending hash (`a > 14`: HALT(1);
  `a ≥ 1`: the parity test `andi T, E, 1; beq/bne T, x0, slot(b | 15)`, taken: HALT(1));
* `ent tb b`: after the pending hash in slot `b`, `a0 = NB; j lad_V_t_(14-a)`;
* `pos V t p t'`: ladder position `p` of stream `t` (sibling from `FR - 896 + 64 p`, `E >>= 1`, heap
  index, branch to stream `t'`), up to the next hash (`p = 13`: the variant's destination);
* tails `tailM c d`, `tailP c d`, `tailF c` (copy `c`: `0`, `1` = after stream `c`'s ladder, `2` = after
  `entry0_V`), with `STK = 80 d` known where the tail writes through it.

Variants: `V = 0` (M, merge), `1` (P, push), `2` (F, root).
-/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## pcs -/

def leafPc (s : Nat) : Nat := leafTab.getD s 0
/-- The dispatch of leaf `s` (after the leaf code). -/
def dispLeafPc (s : Nat) : Nat := leafPc s + (if s = 0 then 10 else if s = 14 then 13 else 11)
def entry0Pc (V : Nat) : Nat := entry0Tab.getD V 0
def ladPc (V t p : Nat) : Nat := ((ladTab.getD V []).getD t []).getD p 0
def lbrPc (V t p : Nat) : Nat := ((lbrTab.getD V []).getD t []).getD p 0
/-- Specialize two fold directions only for segments of at least three folds. -/
def prefixN (a : Nat) : Nat := if a < 3 then 0 else 2
def prefixSave (a : Nat) : Nat := if a < 3 then 0 else 1
def prefixPc (V a bits : Nat) : Nat :=
  if V < 2 then 146432 + ((V*12+a-3)*8+bits)*256
  else 195584 + ((a-3)*8+bits)*24
def njStart (V a bits : Nat) : Nat := prefixPc V a bits
def njTrackLen (V a : Nat) : Nat := 9 * (a - 3) + (if V = 0 then 19 else 12)
def njLadPc (V t a i bits : Nat) : Nat :=
  njStart V a bits + 16 + (if t = bits / 4 % 2 then 0 else njTrackLen V a) + 9*(i-2)
def njPosPc (V t a i bits : Nat) : Nat :=
  if i < 2 then njStart V a bits + 8*i else njLadPc V t a i bits
def njTailPc (V t a bits : Nat) : Nat := njLadPc V t a (a-1) bits + 8
def noJoin (V a : Nat) : Prop := V < 2 ∧ 3 ≤ a
instance (V a : Nat) : Decidable (noJoin V a) := inferInstanceAs (Decidable (V < 2 ∧ 3 ≤ a))
def tailCopies (V : Nat) : Nat := if V < 2 then 195 else 3
def tailSel (V t a bits : Nat) : Nat := if noJoin V a then 3 + (a-3)*16 + bits*2 + t else t
def segmentSave (V a : Nat) : Nat := if noJoin V a then 1 else 0
def posCodePc (V t a i bits : Nat) : Nat :=
  if noJoin V a then njPosPc V t a i bits
  else if 3 ≤ a ∧ i ≤ prefixN a then prefixPc V a bits + 8*i else ladPc V t (14-a+i)
def prefixBefore (V a i : Nat) : Nat := min i (prefixN a) - (if 2 ≤ V ∧ prefixN a < i ∧ 3 ≤ a then 1 else 0)
def foldBudget (V a i : Nat) : Nat :=
  if i < a then 16*(a-i)-1-(prefixN a-min i (prefixN a)) +
    (if 2 ≤ V ∧ 3 ≤ a ∧ i ≤ 2 then 1 else 0) else 0
def posCycles (V a i : Nat) : Nat :=
  (if i+1=a then 7 else 8) - (if i < prefixN a then 1 else 0) +
    (if 2 ≤ V ∧ 3 ≤ a ∧ i = prefixN a then 1 else 0)

/-- Start of the tail of variant `V`, copy `c` (after the destination hash). -/
def tailPc (V c : Nat) : Nat := if c < 3 then (if c = 2 then entry0Pc V + 2 else ladPc V c 13 + 8)
  else njTailPc V ((c-3)%2) ((c-3)/16+3) ((c-3)/2%8)
/-- The table of leaf `s` (`0` = normal, `1` = last leaf). -/
def tsel (s : Nat) : Nat := if s = 14 then 1 else 0

/-- The fixed x18 address anchor. The sparse-stream root cap instead uses x25 = 16384. -/
def FLIM : Nat := 4095

/-- The dispatch of merge-tail copy `c`. -/
def dispTailPc (c : Nat) : Nat := tailPc 0 c + 6
/-- Dispatch copies: leaves `0..14`, merge tails `15..17`. -/
def dispPc (c : Nat) : Nat := if c < 15 then dispLeafPc c else dispTailPc (c - 15)
/-- The start of the layer-4 precode after the root tail copy `c`. -/
def f4Pc (c : Nat) : Nat := if c = 2 then layerPcTab.getD 4 [] |>.getD 0 0
  else if c = 1 then (layerPcTab.getD 4 []).getD 1 0 else (layerPcTab.getD 4 []).getD 2 0

/-! ## Expressions -/

def ldR (r : Reg) (off : Nat) : E := .ld (addC (.reg r) (BitVec.ofNat 64 off))
/-- The fold `slliw x23, x23, 1` (the relabelled header field of the parent). -/
def eS : E := .bin (.w .sll) (.reg .x23) (cw 1)
/-- `x28 = sext32 (2^31)`: the sibling (`addw`) and root (`bne`) constant. -/
def sgn31 : Nat := 2 ^ 64 - 2 ^ 31
/-- The leaf header table (`revWord (2^14 ||| x)` at `RTAB + 8 x`). -/
def RTAB : Nat := 0xFDFFE0

/-- The high word of header `0`: `0xFFF` (`FLIM`), the prologue's `x18` (`lwu x18, 52(sp)`). -/
def rtHi (n : Nat) : Nat := if n = 0 then 0xFFF * 2 ^ 32 else if n = 2 then 13760 * 2 ^ 32 else 0
/-- The stored header word `n`: `revWord (2^14 ||| n)` in the low word (read with `lw`), `rtHi n`
above it. -/
def rtW (n : Nat) : Word := BitVec.ofNat 64 ((Ref.Rev.revWord (2 ^ 14 ||| n)).toNat + rtHi n)

/-- The verifier's data: the leaf header table. -/
def RtabData (s : MachineState) : Prop :=
  ∀ n, n ≤ 2 ^ 14 → s.getMem (BitVec.ofNat 64 (RTAB + 8 * n)) = rtW n
def notOne : E := .c (~~~1#64)
/-- The table slot address `(lbu FR << 5) + TB` (8-word slots). -/
def dispT (tb : Nat) : E :=
  .bin .add (.bin .sll (.un (.ld .bu 0) (.ld (.bin .add (.reg .x14) (cw 512)))) (cw 5)) (cw tb)
def dispObl : List Oblig := [.align8 (.reg .x14), .valid ⟨some (.reg .x14), BitVec.ofNat 64 512⟩ 1]

/-- The table of leaf `s`. -/
def tbOf (s : Nat) : Nat := if s = 14 then tbL else tbN

/-- The destination of the last hash of a segment of variant `V`. -/
def destE (V : Nat) : E :=
  if V = 0 then .bin .add (.reg .x15) (cw (EMPTY + 48)) else if V = 1 then .bin .add (.reg .x15) (cw (EMPTY + 112))
  else cw 0x130

def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc + 2, true, steps, brs, none, steps⟩

/-! ## Dispatch -/

/-- Dispatch copy `c` with table `tb` (the merge-tail copies run with either table). -/
def dispKnown (tb : Nat) : List (Reg × Word) := gkP ++ [(.x20, BitVec.ofNat 64 tb)]
def dispKeep : List Reg := [.x10, .x14, .x15, .x16, .x17, .x22, .x23]

def dispSpec (c tb : Nat) : Spec :=
  ⟨[(.x3, dispT tb)] ++ (if c < 15 then [(.x24, cw (0x1000 + 4 * (dispPc c + 4)))] else []), [],
    0, false, 4, [], some (.bin .and (dispT tb) notOne), 4⟩

def dispCheck2 (c tb : Nat) : Bool :=
  pspecB gkP (runAt (dispKnown tb) [] (dispPc c) [.jmp]) (dispSpec c tb) dispObl (dispKnown tb)
    (dispKeep ++ (if c < 15 then [] else [.x24]))

def dispCheck (c : Nat) : Bool :=
  if c < 15 then dispCheck2 c (tbOf c) else dispCheck2 c tbN && dispCheck2 c tbL

/-! ## Table entries -/

def tabBase (tb : Nat) : Nat := if tb = 0 then ptabN else ptabL
def segA (b : Nat) : Nat := b % 16
def segM (b : Nat) : Nat := b / 16 % 2
def segT (b : Nat) : Nat := b / 32 % 2
def segBits (b : Nat) : Nat := b / 32
def rev3 (t : Nat) : Nat := t%2*4 + t/2%2*2 + t/4%2
/-- The variant of byte `b` in table `tb`. -/
def segV (tb b : Nat) : Nat := if segM b = 1 then 0 else if tb = 0 then 1 else 2

/-- The slot's parity test `bge/blt x23, x0, slot(b | 15)` (`t = 1` / `t = 0`) on the sign of the
relabelled header (bit 0 of `E`), taken (reject) iff it differs from `t`. -/
def parBr (t : Nat) (d : Bool) : Br := ⟨if t = 1 then .ge else .lt, .reg .x23, .c 0, d⟩

def tagE : E := .bin (.w .srl) (.reg .x23) (cw 29)
def tagBr (b : Nat) (d : Bool) : Br :=
  if segA b < 3 then parBr (segT b) d else ⟨.ne, tagE, cw (rev3 (segBits b)), d⟩
def tabCycles (b : Nat) : Nat := if segA b < 3 then 3 else 4
def hashOffset (b : Nat) : Nat := if segA b < 3 then 3 else 4

/-- The start of table slot `b`. -/
def slotPc (tb b : Nat) : Nat := tabBase tb + 8 * b

/-- Table slot `b` up to the pending hash (`a = 0`: through `j entry0_V`; `a ≥ 1`: the inlined
entry code, parity test not taken). -/
def tabSpec (tb b : Nat) : Spec :=
  let a := segA b
  if a > 14 then rejSpec 4 []
  else
    ⟨[(.x14, addC (.reg .x14) (BitVec.ofNat 64 (64 * a + 64))),
      (.x12, if a = 0 then destE (segV tb b) else cw (0x1E0 + 16 * segT b))], [],
      if a = 0 then entry0Pc (segV tb b) + 1 else slotPc tb b + hashOffset b, true,
      tabCycles b, if a = 0 then [] else [tagBr b false], none, tabCycles b⟩

/-- Slot `b` (`1 ≤ a ≤ 14`) with a wrong parity bit: `j pors_bad_seg; j reject` from slot `b | 15`,
HALT(1). -/
def tabRej (b : Nat) : Spec := rejSpec (tabCycles b + 3) [tagBr b true]

def tabKeep : List Reg := [.x10, .x15, .x16, .x17, .x20, .x22, .x23, .x24]

def tabCheck1 (tb b : Nat) : Bool :=
  if segA b > 14 then pspecB [] (runAt gkP [] (slotPc tb b) []) (tabSpec tb b) [] [] []
  else if segA b = 0 then pspecB gkP (runAt gkP [] (slotPc tb b) []) (tabSpec tb b) [] gkP tabKeep
  else
    pspecB gkP (runAt gkP [] (slotPc tb b) [.br false]) (tabSpec tb b) [] gkP tabKeep &&
    pspecB [] (runAt gkP [] (slotPc tb b) [.br true]) (tabRej b) [] [] []

def tabCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => tabCheck1 tb b

/-! ## Entry tails and ladder positions -/

def entSpec (tb b : Nat) : Spec :=
  ⟨[(.x10, cw 0x1C0)], [], posCodePc (segV tb b) (segT b) (segA b) 0 (segBits b), false, 2, [], none, 2⟩

def entCheck1 (tb b : Nat) : Bool :=
  segA b = 0 || segA b > 14 ||
    pspecB gkP (runAt gkP [posCodePc (segV tb b) (segT b) (segA b) 0 (segBits b)] (slotPc tb b + hashOffset b + 1) []) (entSpec tb b) []
      (gkP ++ [(.x10, 0x1C0)]) [.x14, .x15, .x16, .x17, .x20, .x22, .x23, .x24]

def pentCheck : Bool := (List.range 2).all fun tb => (List.range 256).all fun b => entCheck1 tb b

def posKnown : List (Reg × Word) := gkP ++ [(.x10, 0x1C0)]
def posKeep : List Reg := [.x14, .x15, .x16, .x17, .x20, .x22, .x24]

def posMem (t p : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 eS), (⟨none, BitVec.ofNat 64 (0x1F8 - 16 * t)⟩, ldR .x14 ((2^64 - 384) + 64 * p + 8)),
    (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t)⟩, ldR .x14 ((2^64 - 384) + 64 * p))]

def posObl (p : Nat) : List Oblig :=
  [.valid ⟨some (.reg .x14), BitVec.ofNat 64 ((2^64 - 384) + 64 * p + 8)⟩ 8, .valid ⟨some (.reg .x14), BitVec.ofNat 64 ((2^64 - 384) + 64 * p)⟩ 8]

/-- The branch direction from stream `t` to stream `t'`. -/
def crossDir (t t' : Nat) : Bool := if t = 0 then t' = 1 else t' = 0

def posSpec (V t p t' : Nat) : Spec :=
  let regs0 := [(.x1, ldR .x14 ((2^64 - 384) + 64 * p)), (.x30, ldR .x14 ((2^64 - 384) + 64 * p + 8)), ((.x23 : Reg), eS)]
  if p = 13 then ⟨regs0 ++ [(.x12, destE V)], posMem t p, ladPc V t p + 7, true, 7, [], none, 7⟩
  else
    ⟨regs0 ++ [(.x12, cw (0x1E0 + 16 * t'))], posMem t p,
      lbrPc V t' (p + 1) + 1, true, 8,
      [⟨if t = 0 then .lt else .ge, eS, .c 0, crossDir t t'⟩], none, 8⟩

def posDirs (t p t' : Nat) : List Dir := if p = 13 then [] else [.br (crossDir t t')]

def posCheck1 (V t p t' : Nat) : Bool :=
  pspecB gkP (runAt posKnown [] (ladPc V t p) (posDirs t p t')) (posSpec V t p t') (posObl p)
    posKnown posKeep

def posCheck (V : Nat) : Bool :=
  (List.range 2).all fun t => (List.range 14).all fun p => (List.range 2).all fun t' =>
    (p = 13 && t' = 1) || posCheck1 V t p t'

def njPosSpec (V t a i bits t' : Nat) : Spec :=
  if i < prefixN a then
    ⟨[(.x1, ldR .x14 ((2^64 - 384) + 64 * (14-a+i))), (.x30, ldR .x14 ((2^64 - 384) + 64 * (14-a+i) + 8)),
      (.x23, eS), (.x12, cw (0x1E0 + 16 * t'))], posMem t (14-a+i),
      njPosPc V t a i bits + 7, true, 7, [], none, 7⟩
  else
    let q := posSpec V t (14-a+i) t'
    { q with pc := if i+1=a then njPosPc V t a i bits + 7 else njPosPc V t' a (i+1) bits - 1 }

/-- Exact run from a copied prefix or its one-instruction join to the original ladder. -/
def prefixPosSpec (V t a i bits t' : Nat) : Spec :=
  if noJoin V a then njPosSpec V t a i bits t' else
  let p := 14 - a + i
  if i < prefixN a then
    ⟨[(.x1, ldR .x14 ((2^64 - 384) + 64 * p)), (.x30, ldR .x14 ((2^64 - 384) + 64 * p + 8)),
      (.x23, eS), (.x12, cw (0x1E0 + 16 * t'))], posMem t p,
      prefixPc V a bits + 8 * i + 7, true, 7, [], none, 7⟩
  else
    let q := posSpec V t p t'
    if 3 ≤ a ∧ i = prefixN a then { q with steps := q.steps + 1, cycles := q.cycles + 1 } else q

def prefixCheck (V : Nat) : Bool :=
  ((List.range' 3 12).all fun a => (List.range 8).all fun bits =>
    ((List.range (prefixN a)).all fun i =>
      let t := bits / 2^i % 2
      let t' := bits / 2^(i+1) % 2
      pspecB gkP (runAt posKnown [] (posCodePc V t a i bits) [])
        (prefixPosSpec V t a i bits t') (posObl (14-a+i)) posKnown posKeep) &&
    ((List.range 2).all fun t' =>
      let i := prefixN a
      let t := bits / 2^i % 2
      (14-a+i = 13 && t' = 1) ||
      pspecB gkP (runAt posKnown [] (posCodePc V t a i bits) (posDirs t (14-a+i) t'))
        (prefixPosSpec V t a i bits t') (posObl (14-a+i)) posKnown posKeep))

def nojoinCheck (V : Nat) : Bool :=
  (List.range' 3 12).all fun a => (List.range 8).all fun bits =>
    (List.range a).all fun i => i < prefixN a ||
      (List.range 2).all fun t => (List.range 2).all fun t' =>
        (i+1=a && t'=1) ||
        pspecB gkP (runAt posKnown [] (posCodePc V t a i bits) (posDirs t (14-a+i) t'))
          (prefixPosSpec V t a i bits t') (posObl (14-a+i)) posKnown posKeep

/-! ## Tails -/

/-- The stack register is an offset; memory addresses retain the fixed EMPTY base. -/
def stkReg (d : Nat) : Nat := 80 * d
def stkOf (d : Nat) : Nat := EMPTY + 80 * d
def tailKnown (d : Nat) : List (Reg × Word) := gkP ++ [(.x15, BitVec.ofNat 64 (stkReg d))]
def tailKeep : List Reg := [.x14, .x16, .x17, .x20, .x22, .x24]

def tailMSpec (c d : Nat) : Spec :=
  ⟨[(.x3, ldE (stkOf d - 16)), (.x23, eS), (.x10, cw (stkOf d)), (.x15, .c (BitVec.ofNat 64 (stkReg d) - 80))],
    [(⟨none, BitVec.ofNat 64 (stkOf d + 8)⟩, stW (stkOf d + 8) eS)], dispTailPc c, false, 6,
    [⟨.ne, ldE (stkOf d - 16), .reg .x23, false⟩], none, 6⟩

def tailMRej (d : Nat) : Spec := rejSpec 5 [⟨.ne, ldE (stkOf d - 16), .reg .x23, true⟩]

def tailPSpec (d : Nat) : Spec :=
  ⟨[(.x15, cw (stkReg d + 80)), (.x3, .bin (.w .add) (.reg .x23) (cw sgn31))],
    [(⟨none, BitVec.ofNat 64 (stkOf d + 64)⟩, .bin (.w .add) (.reg .x23) (cw sgn31))], 0, false, 4, [],
    some (.bin .and (.reg .x24) notOne), 4⟩

def tailCheck (c : Nat) : Bool :=
  (List.range 15).all (fun d =>
    pspecB gkP (runAt (tailKnown d) [dispTailPc c] (tailPc 0 c) [.br false]) (tailMSpec c d) []
      (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkReg d) - 80) else p)
      tailKeep &&
    pspecB [] (runAt (tailKnown d) [] (tailPc 0 c) [.br true]) (tailMRej d) [] [] []) &&
  (List.range 14).all (fun d =>
    pspecB gkP (runAt (tailKnown d) [] (tailPc 1 c) [.jmp]) (tailPSpec d) []
      (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkReg d + 80)) else p)
      [.x14, .x16, .x17, .x20, .x22, .x23, .x24])

/-! ### The root tail (checks, layer constants) -/

/-- The fold limit: `bltu x18, x14` (`FR` beyond `FLIM`). -/
def fBr1 (d : Bool) : Br := ⟨.ltu, cw 16384, .reg .x14, d⟩
def fBr2 (d : Bool) : Br := ⟨.ne, .reg .x23, cw sgn31, d⟩
def fBr3 (d : Bool) : Br := ⟨.ne, .reg .x15, cw 0, d⟩

def tailFKnown : List (Reg × Word) := gkP ++ [(.x12, 0x130), (.x24, AUTHBASE)]

/-- Known at the start of the layer-4 transition: the layer constants the root tail sets
(`a5 = ttab + 2048`). The masks `x20`, `x21` and the dispatch
mask `sp = TMASK` are loaded from the verifier's data words through `sp = dataBase` and resolved
from protected memory in `tailF_step`. Retaining the x28=2688 initializer for carried-base subtraction makes the accepting tail take12 instructions. -/
def rootK : List (Reg × Word) :=
  baseK ++ [(.x29, 16384), (.x10, 0x100), (.x26, 6), (.x28, 2688), (.x15, TTA5), (.x14, KT4), (.x4, 0x1000000000000000), (.x24, AUTHBASE)]
def rootPost : List (Reg × Word) := rootK ++ [(.x11, 64), (.x12, 0x130)]

def tailFSpec (c : Nat) : Spec :=
  ⟨[(.x20, ldE 0xFDFFD0), (.x21, ldE 0xFDFFD8), (.x2, ldE 0xFDFFC8)], [], f4Pc c, false, 11,
    [fBr3 false, fBr2 false, fBr1 false], none, 11⟩

def tailFCheck (c : Nat) : Bool :=
  pspecB rootK (runAt tailFKnown [f4Pc c] (tailPc 2 c) [.br false, .br false, .br false]) (tailFSpec c) []
    rootPost [.x22] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br true]) (rejSpec 4 [fBr1 true]) [] [] [] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br false, .br true]) (rejSpec 5 [fBr2 true, fBr1 false]) [] [] [] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br false, .br false, .br true])
    (rejSpec 6 [fBr3 true, fBr2 false, fBr1 false]) [] [] []

/-! ## Leaves -/

/-- The register holding leaf `s`'s index (`XA`, `XB` alternate). -/
def xReg (s : Nat) : Reg := if s % 2 = 0 then .x16 else .x17
/-- `pi_s & 0x78` (the slot's byte offset in `PIND`; W1: `pi_s` at `WIT + 256 + s = 0x900 + s`). -/
def piT (s : Nat) : E := .un (.ld .bu (s % 8)) (ldE (PMS + 8 * (s / 8)))
def xE (s : Nat) : E := .ld (.bin .add (piT s) (cw PIND))
/-- W1: secret `s` in the tweak slot of chain block `(0, 2 + s)` (`WIT + 3072 + 64 s = 0x1400 + 64 s`). -/
def secA (s : Nat) : Nat := 0x800 + 3072 + 64 * s

def leafKnown : List (Reg × Word) := gkP ++ [(.x20, BitVec.ofNat 64 tbN)]
def pleafPost (s : Nat) : List (Reg × Word) := gkP ++ [(.x10, 0xC0)]
def pleafKeep (s : Nat) : List Reg := [xReg (s + 1), .x14, .x15, .x22, .x24]

def leafBrs (s : Nat) (d1 d2 : Bool) : List Br :=
  (if s = 14 then [⟨.geu, xE s, cw 0x20000, d2⟩] else []) ++
  (if s = 0 then [] else [⟨.geu, .reg (xReg (s + 1)), xE s, d1⟩])

/-- The table address `8 x + RTAB` of leaf `s`'s header. -/
def rtE (s : Nat) : E := .bin .add (xE s) (cw RTAB)
/-- The header field `lw x23, 48(x3)` with `x3 = 8*x + sp`: the sign-extended low word of the table entry. -/
def rtLw (s : Nat) : E := .un (.ld .w 0) (.ld (rtE s))

/-- Last-leaf table base from the unused high word of table entry two. -/
def leafTbE (s : Nat) : E := if s = 14 then .un (.ld .wu 4) (ldE (RTAB + 16)) else cw tbN

def leafSpec (s : Nat) : Spec :=
  ⟨[(.x20, leafTbE s), (xReg s, xE s), (.x23, rtLw s), (.x1, ldE (secA s)), (.x30, ldE (secA s + 8))],
    [(⟨none, BitVec.ofNat 64 0xE8⟩, ldE (secA s + 8)), (⟨none, BitVec.ofNat 64 0xE0⟩, ldE (secA s)),
      (⟨none, BitVec.ofNat 64 0xC8⟩, stW 0xC8 (xE s))],
    dispLeafPc s, false, if s = 0 then 10 else if s = 14 then 13 else 11, leafBrs s false false, none, if s = 0 then 10 else if s = 14 then 13 else 11⟩

/-- The `PIND` read (all paths). -/
def leafObl1 (s : Nat) : List Oblig := [.valid ⟨some (piT s), BitVec.ofNat 64 PIND⟩ 8]
/-- Accepting path: also the table read. -/
def leafObl (s : Nat) : List Oblig :=
  .align8 (xE s) :: .valid ⟨some (xE s), BitVec.ofNat 64 RTAB⟩ 4 :: leafObl1 s

def leafDirs (s : Nat) : List Dir :=
  if s = 0 then [] else if s = 14 then [.br false, .br false] else [.br false]

def leafCheck (s : Nat) : Bool :=
  pspecB gkP (runAt leafKnown [dispLeafPc s] (leafPc s) (leafDirs s)) (leafSpec s) (leafObl s)
    (pleafPost s) (pleafKeep s) &&
  (s = 0 || pspecB [] (runAt leafKnown [] (leafPc s) [.br true])
    (rejSpec (if s = 14 then 7 else 6) [⟨.geu, .reg (xReg (s + 1)), xE s, true⟩]) (leafObl1 s) [] []) &&
  (s != 14 || pspecB [] (runAt leafKnown [] (leafPc s) [.br false, .br true])
    (rejSpec 8 (leafBrs s false true)) (leafObl1 s) [] [])

end SigGolfCandidate.Verify

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Prologue, counter check, digest, PORS setup -/

/-- All registers except `x2` are zero; the loader sets `x2` to the verifier data base. -/
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0), (.x2, 0xFDFFB0)]

/-- `k0` without `x18`: what the prologue's first instruction `lwu x18, 52(sp)` keeps. -/
def k0x : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0), (.x2, 0xFDFFB0)]
/-- After the first instruction: `x18 = FLIM` (the high word of header `0`, `rtHi`). -/
def k1 : List (Reg × Word) := k0x ++ [(.x18, 0xFFF)]

/-- The prologue's first instruction `lwu x18, 52(sp)` (the high word of header `0` at `RTAB`). -/
def specLim : Spec := ⟨[(.x18, .un (.ld .wu 4) (ldE RTAB))], [], 1, false, 1, [], none, 1⟩

/-- Digest phase: witness bases and `P1 .. P5`. The prologue loads `x18 = 0xFFF` (`FLIM`, the
`x18`-relative witness base and the fold limit) from the high word of header `0`, so the relocated
leaf head needs no `x18` restore. -/
def gkD : List (Reg × Word) := [(.x5, 0), (.x19, 7), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x2, 0xFDFFB0)]
def dgK : List (Reg × Word) := gkD ++ [(.x18, 0xFFF), (.x10, 0), (.x11, 64), (.x12, 0), (.x15, 0)]

/-- The counters (W1a): `c0 .. c3` as two doublewords at `WIT + 2944`, `c4` as a word at `WIT + 2392`. -/
def ctrX : E := .bin .or (.bin .or (ldE 4992) (ldE 5000)) (.un (.ld .wu 0) (ldE 4736))
/-- The range check masks the merged counters with the data word at `sp + 8`
(`0xFFC00000FFC00000`, bits `22 .. 31` and `54 .. 63`). -/
def ctrE' : E := .bin .and ctrX (ldE 0xFDFFB8)

def specStartOk : Spec :=
  ⟨[], [(⟨none, BitVec.ofNat 64 24⟩, ldE 5064), (⟨none, BitVec.ofNat 64 16⟩, ldE 5056)],
    20, true, 19, [⟨.ne, ctrE', .c 0, false⟩], none, 19⟩
def specStartRej : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc + 2, true, 16, [⟨.ne, ctrE', .c 0, true⟩], none, 16⟩

def wLdE (i : Nat) : E := ldE (8 * i)
def idxE : E := .bin .srl (.bin .sll (wLdE 0) (cw 30)) (cw 30)
def hiE : E := .bin .sll (.bin .srl idxE (cw 32)) (cw 24)

/-- Leaf index `v_r` (bits `34 + 14 r ..` of the digest). -/
def pindE (r : Nat) : E :=
  let p := 34 + 14 * r
  let lo : E := .bin .srl (wLdE (p / 64)) (cw (p % 64 - 3))
  .bin .and (if p % 64 + 14 ≤ 64 then lo else .bin .or lo (.bin .sll (wLdE (p / 64 + 1)) (cw (64 - p % 64 + 3))))
    (cw 0x1FFF8)

/-- `tau mod 2^32` in the high half of word 0 (the relabelled `p` slot). -/
def lo32E : E := .bin .sll idxE (cw 32)
/-- Word 0 of the node buffers: `twLo 10 0 idx idx`. -/
def nbW0E : E := .bin .add (.bin .sll idxE (cw 24)) (cw 1537)
/-- Word 0 of the leaf buffer: `twLo 9 0 idx idx`. -/
def cbW0E : E := .bin .add (.bin .sll idxE (cw 24)) (cw 1281)

/-- The pre-masked selector word `k`: the witness word at `0x1270 + 8 k` masked with the data word
`PMASK` (`0x78` in every byte). -/
def pmE (k : Nat) : E := .bin .and (ldE (0x1270 + 8 * k)) (ldE 0xFDFFB0)

/-- The setup's stores. The relabelled header words hold `tau` in word 0, so the low halves of the
word-1 slots stay zero (no stores). -/
def psetupMem : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (PMS + 8)⟩, pmE 1), (⟨none, BitVec.ofNat 64 PMS⟩, pmE 0),
    (⟨none, BitVec.ofNat 64 0x240⟩, stW 0x240 (cw 1)), (⟨none, BitVec.ofNat 64 0xC0⟩, cbW0E)] ++
  ((List.range 14).reverse.map fun i => (⟨none, BitVec.ofNat 64 (PSB + 80 * i)⟩, nbW0E)) ++
  [(⟨none, BitVec.ofNat 64 0x1C0⟩, nbW0E), (⟨none, BitVec.ofNat 64 0x7F8⟩, cw 0x20000)] ++
  ((List.range 15).reverse.map fun r => (⟨none, BitVec.ofNat 64 (PIND + 8 * r)⟩, pindE r))

/-- Known after the setup: the PORS constants, `TB = ptab_n`, `FR` (first header at `FR + 592`),
the empty stack, the fold limit `FLIM`. -/
def setupPost : List (Reg × Word) :=
  gkP ++ [(.x20, BitVec.ofNat 64 tbN), (.x14, 7040), (.x15, 0),
    (.x18, BitVec.ofNat 64 FLIM)]

def setupSpec : Spec := ⟨[(.x22, idxE)], psetupMem, leafPc 0, false, 92, [], none, 92⟩

def startCheck : Bool :=
  specB [] (runAt k0 [1] 0 []) specLim k0x [] &&
  specB gkD (runAt k1 [] 1 [.br false]) specStartOk dgK [] &&
  specB [] (runAt k1 [] 1 [.br true]) specStartRej [] [] &&
  specB gkD (runAt dgK [leafPc 0] 21 []) setupSpec setupPost []

end SigGolfCandidate.Verify
