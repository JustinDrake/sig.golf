import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.PorsTab

/-! # Layer blocks (W1a): transition (route, encoding, check, chain prologue), leaf, compare

Every start of layer `lay` (layer 4: a PORS root tail; below: a block of the last fold chunk of
layer `lay + 1`) runs its own copy of the transition (`trPc lay c`):
* route and encoding (`stepsA` steps up to the encoding `ecall`; the counter is read from the
  witness, `c0 .. c3` in the tweak slot of block `(0, 0)`, `c4` at `2688`);
* the encoding check (`or; blt` for the top bits, the 7-step SWAR digit sum, `remu` by `x18 = 4095`,
  `bne KT`), then the chain prologue `li s6, base`, the extraction of triple 0
  and `jalr ra` into the layer-shared chain code (at most 25 steps, 28 cycles);
* at the return pc `retPc lay c`: the leaf tweak and the dispatch into the fold's shape block. -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- The number of copies of the transition of layer `lay`: layer 4 has one per PORS root tail;
below, every block of the last chunk of layer `lay + 1` ends with its own copy. -/
def nCopy (lay : Nat) : Nat := if lay = 4 then 3 else 2 ^ chBits (lay + 1) (nCh (lay + 1) - 1)

/-- Start of transition copy `c` of layer `lay`. -/
def trPc (lay c : Nat) : Nat := (layerPcTab.getD lay []).getD c 0
/-- The return pc of transition copy `c` (its leaf block, after `jalr ra`). -/
def retPc (lay c : Nat) : Nat := (retTab.getD lay []).getD c 0

/-- Start `t` of layer `lay`: a PORS root tail's copy (layer 4) or, in block `t` of the last fold chunk
of layer `lay + 1`, right after the hash of the node under the root: the fold stops there, the copy of
the root's other child into the encoding block (4 steps) and the transition follow. -/
def preStart (lay t : Nat) : Nat :=
  if lay = 4 then trPc 4 t
  else m4Pc (lay + 1) (nCh (lay + 1) - 1) t (chBits (lay + 1) (nCh (lay + 1) - 1) - 1) + 2

/-- Steps of the transition proper up to the encoding hash: layer 0 consumes the remaining route bits
directly (two `addi` for the sentinel, no mask/shift); layer 4 reuses the known hash length. -/
def stepsT (lay : Nat) : Nat := if lay = 0 then 7 else 10
/-- Steps from `preStart` to the encoding hash: below layer 4, the 4 steps of the sibling copy first. -/
def stepsA (lay : Nat) : Nat := stepsT lay + (if lay = 4 then 0 else 4)
def encPc (lay t : Nat) : Nat := trPc lay t + stepsT lay

/-- The node under the root of the tree below (in EB+32 = `0x120`) is the root's left child: then the
encoding block is `0x110 ..` (`tweak | node | sibling | counter`), else `0x100 ..`
(`tweak | sibling | node | counter`; layer 4: `tweak | 0 | PORS root | counter`). -/
def xLeft (lay t : Nat) : Bool := lay != 4 && t / 2 ^ (heightL (lay + 1) - 1) % 2 == 0
def encB (_lay _t : Nat) : Nat := 0x100
def encD (lay t : Nat) : Nat := if xLeft lay t then 0x120 else 0x130
/-- Where the root's other child (the top sibling of the path of layer `lay + 1`) goes. -/
def sibSlot (lay t : Nat) : Nat := if xLeft lay t then 0x130 else 0x120
def topSib (lay : Nat) : Nat := sibAddr (lay + 1) (heightL (lay + 1) - 1)

/-- Known registers at the transition start. -/
def l4K : List (Reg × Word) := gkL ++ [(.x11, 64), (.x12, 0x130), (.x14, KT4)]
def aK (lay t : Nat) : List (Reg × Word) :=
  gkL ++ [(.x10, 0x340), (.x11, 64), (.x12, BitVec.ofNat 64 (encD lay t)), (.x22, BitVec.ofNat 64 (s6N (lay + 1)))]
def preK (lay t : Nat) : List (Reg × Word) := if lay = 4 then l4K else aK lay t

/-- Known registers after the encoding hash call of transition copy `t`. -/
def bK (lay t : Nat) : List (Reg × Word) :=
  gkL ++ [ (.x10, BitVec.ofNat 64 (encB lay t)), (.x11, 64),
      (.x12, BitVec.ofNat 64 (encD lay t))] ++
    (if lay = 4 then [(.x14, KT4)] else [(.x22, BitVec.ofNat 64 (s6N (lay + 1)))])

def uEr (lay : Nat) : E :=
  if lay = 0 then .reg .x30
  else .bin .and (.reg (if lay = 4 then .x22 else .x30)) (cw (2 ^ heightL lay - 1))
def tauEr (lay : Nat) : E :=
  if lay = 0 then cw 0 else .bin .srl (.reg (if lay = 4 then .x22 else .x30)) (cw (heightL lay))
/-- Keep the final leaf index physically after the top tree address becomes zero. -/
def carryEr (lay : Nat) : E := if lay = 0 then uEr lay else tauEr lay
def x31Er (lay : Nat) : E :=
  if lay = 0 then .bin .sll (.reg .x30) (cw 32)
  else .bin .add (tauEr lay) (.bin .sll (uEr lay) (cw 32))
/-- `U = e | 2^h` (heap sentinel): `ori` (h < 11) or two `addi 1024` (h = 11). -/
def uHE (lay : Nat) : E :=
  if lay = 0 then .bin .xor (uEr lay) (cw 4095) else .bin .or (uEr lay) (cw (2 ^ heightL lay))

/-- The doubleword holding layer `lay`'s counter (`c4` at witness 2688, `c0 .. c3` in the tweak
slot of chain block `(0, 0)` at witness 2944). -/
def ctrA (lay : Nat) : Nat := if lay = 4 then 0x800 + 2688 else 0x800 + 2944 + 8 * (lay / 2)
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (ctrA lay))

def encHeaderE (lay : Nat) : E :=
  if lay < 4 then .bin (.st .b 2) (ldE 256) (cw lay) else cw Ref.MaskHeader.M1

def specA (lay t : Nat) : Spec :=
  ⟨[(.x23, uHE lay), (.x30, carryEr lay), (.x31, x31Er lay)],
   [(⟨none, BitVec.ofNat 64 (encB lay t + 16)⟩, ctrE lay),
    (⟨none, BitVec.ofNat 64 (encB lay t + 8)⟩, x31Er lay),
    (⟨none, BitVec.ofNat 64 (encB lay t)⟩,
      encHeaderE lay)] ++
   (if lay = 4 then [] else
     [(⟨none, BitVec.ofNat 64 (sibSlot lay t + 8)⟩, ldE (topSib lay + 8)),
      (⟨none, BitVec.ofNat 64 (sibSlot lay t)⟩, ldE (topSib lay))]),
   encPc lay t, true, stepsA lay, [], none, stepsA lay⟩

/-! ## The encoding check (`remu x25, x25, x18`; layers 0 .. 3 compare `KT`, layer 4 reuses `x14 = KT4`,
targets185/186, with no checksum correction) and the chain prologue -/

/-- Four selector paths: AB, gated AB, BC, CD. The gated AB case is rejected by padding. -/
def selOf (a : BitVec 256) : Nat :=
  if a.getLsbD 127 then (if SigGolfCandidate.Ref.encodingGate a then 3 else 1)
  else if a.getLsbD 63 then 2 else 0

def selSteps (hi : Nat) : Nat := if hi = 0 then 2 else if hi = 2 then 5 else 6
def d0E (out hi : Nat) : E := ldE (out + (if hi = 2 then 8 else if hi = 3 then 16 else 0))
def d1E (out hi : Nat) : E := ldE (out + (if hi = 2 then 16 else if hi = 3 then 24 else 8))
def encObligs : List Oblig := []
theorem encObligs_holds (s : MachineState) : ∀ o ∈ encObligs, o.holds s := by simp [encObligs]
def selLow (hi : Nat) : Bool := decide (hi = 0 ∨ hi = 2)
def selSecond (hi : Nat) : Bool := decide (hi = 0 ∨ hi = 1)
def selDirs (hi : Nat) : List Dir := [.br (selLow hi), .br (if selLow hi then selSecond hi else decide (hi = 3))]
def selBrs (out hi : Nat) : List Br :=
  [(if selLow hi then ⟨.ge, ldE out, cw 0, selSecond hi⟩
    else ⟨.geu, ldE out, cw (2 ^ 60), decide (hi = 3)⟩),
   ⟨.ge, ldE (out + 8), cw 0, selLow hi⟩]


def m1E : E := .c M1w
def m2E : E := .c M2w
def orE (out hi : Nat) : E := .bin .or (d0E out hi) (d1E out hi)
/-- The reference lane word: `((A >> 3) & M1) + (A & M1) + ((B >> 3) & M1) + (B & M1)`
(11 six-bit lanes of two digits each; `Swar.sw1`). -/
def swA3ref (out hi : Nat) : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl (d0E out hi) (cw 3)) m1E) (.bin .and (d0E out hi) m1E))
    (.bin .and (.bin .srl (d1E out hi) (cw 3)) m1E)) (.bin .and (d1E out hi) m1E)
/-- The even-digit lanes `t1 = (A & M1) + (B & M1)`. -/
def swT1 (out hi : Nat) : E := .bin .add (.bin .and (d0E out hi) m1E) (.bin .and (d1E out hi) m1E)
/-- The lane word as the machine computes it in 7 ALU steps: `t1 + ((A + B - t1) >> 3)`; equal to
`swA3ref` when both words are below `2^63` (`LayArith.swA3_eval`): `A + B - t1` is the sum of the
odd-digit parts, a multiple of 8 without overflow. -/
def swA3 (out hi : Nat) : E :=
  .bin .add (swT1 out hi)
    (.bin .srl (.bin .sub (.bin .add (d0E out hi) (d1E out hi)) (swT1 out hi)) (cw 3))
def swA4 (out hi : Nat) : E := .bin .add (swA3 out hi) (.bin .srl (swA3 out hi) (cw 6))
def swA5 (out hi : Nat) : E := .bin .and (swA4 out hi) m2E
def swA6 (out hi : Nat) : E := .bin .add (swA5 out hi) (.bin .srl (swA5 out hi) (cw 12))
def swA7 (out hi : Nat) : E := .bin .add (swA6 out hi) (.bin .srl (swA6 out hi) (cw 24))
def swSBase (out hi : Nat) : E := .bin .remu (swA5 out hi) (cw 4095)
def swS (out hi : Nat) (_lay : Nat) : E := swSBase out hi

/-- The table index of triple 0 (`slli a4, a6, 9; and a4, a4, sp; add a4, a4, a5`) and the
dispatch target (`jalr ra, -2048(a4)`). -/
def x14E (out hi : Nat) : E := .bin .add (.bin .and (.bin .sll (d0E out hi) (cw 9)) (.c TMASK)) (.c TTA5)
def tgt0 (out hi : Nat) : E := .bin .and (.bin .add (.bin .and (.bin .sll (d0E out hi) (cw 9)) (.c TMASK)) (cw 0x4f800)) (.c (~~~1#64))

def stepsB (_lay : Nat) : Nat := 25
def stepsBPath (hi _lay : Nat) : Nat := 19 + selSteps hi
def cyclesBPath (hi lay : Nat) : Nat := stepsBPath hi lay + 3

theorem stepsBPath_le (hi lay : Nat) : stepsBPath hi lay ≤ stepsB lay := by
  unfold stepsBPath stepsB selSteps; split_ifs <;> omega
theorem cyclesBPath_le (hi lay : Nat) : cyclesBPath hi lay ≤ stepsB lay + 3 := by
  have := stepsBPath_le hi lay; unfold cyclesBPath; omega
/-- One REMU costs four cycles rather than one. -/
def cyclesB (lay : Nat) : Nat := stepsB lay + 3

/-- AB has already checked both padding bits. BC checks its new high word; CD checks the OR. -/
def padDirs (hi : Nat) (bad : Bool) : List Dir :=
  if hi = 0 ∨ hi = 1 then [] else [.br (if hi = 2 then !bad else bad)]
def padBrs (out hi : Nat) (bad : Bool) : List Br :=
  if hi = 0 ∨ hi = 1 then [] else
    [if hi = 2 then ⟨.ge, d1E out hi, cw 0, !bad⟩ else ⟨.lt, orE out hi, cw 0, bad⟩]

def specBok (out hi : Nat) (lay : Nat) : Spec :=
  ⟨[(.x14, (x14E out hi)), (.x16, (d0E out hi)), (.x17, (d1E out hi))], [], 0, false, stepsBPath hi lay,
   ([⟨.ne, (swS out hi lay), .c (KTof lay), false⟩] ++ padBrs out hi false ++ selBrs out hi), some (tgt0 out hi), cyclesBPath hi lay⟩

/-- Known registers on entry of the chain code. The folded dispatch needs no table-base register. -/
def chKa (lay c : Nat) : List (Reg × Word) :=
  chK0 ++ [(.x22, BitVec.ofNat 64 (s6N lay)), (.x1, pcOf (retPc lay c))]

def rejK : List (Reg × E) := [(.x5, cw 1), (.x10, cw 1)]

def rej1Steps (hi : Nat) : Nat := if hi = 1 then 8 else 11
def specRej1 (out hi : Nat) : Spec := ⟨rejK, [], rejectPc + 2, true, rej1Steps hi,
  padBrs out hi true ++ selBrs out hi, none, rej1Steps hi⟩
def specRej2 (out hi : Nat) (lay : Nat) : Spec :=
  ⟨rejK, [], rejectPc + 2, true, 17 + selSteps hi,
    [⟨.ne, (swS out hi lay), .c (KTof lay), true⟩] ++ padBrs out hi false ++ selBrs out hi,
    none, 20 + selSteps hi⟩

/-! ## Leaf -/

/-- The leaf code at the return pc: the leaf tweak, then the dispatch into the shape block of
chunk 0. -/
def leafSteps (lay : Nat) : Nat := if lay = 0 then 8 else if lay < 4 then 6 else 7

def leafRawSteps (lay : Nat) : Nat := if lay = 0 then 7 else leafSteps lay

def topDispTgt : E :=
  mkBin .and (mkAdd (mkBin .sll (.reg .x23) (cw 3)) (cw 779264)) (.c (~~~1#64))

def leafK (lay : Nat) : List (Reg × Word) := chK0 ++ [(.x20,M1w), (.x22, BitVec.ofNat 64 (s6N lay))]

def specLeaf (lay : Nat) : Spec :=
  ⟨[(.x10, cw 832), (.x11, cw 704)],
   [(⟨none, BitVec.ofNat 64 840⟩, .reg .x31)] ++
     (if lay < 4 then [] else [(⟨none, BitVec.ofNat 64 832⟩, cw Ref.MaskHeader.M1)]),
   0, false, leafRawSteps lay, [], some (if lay = 0 then topDispTgt else dispTgt lay 0), leafRawSteps lay⟩

def leafKeep : List Reg := [.x17, .x23, .x30, .x31]
def leafPost (lay : Nat) : List (Reg × Word) :=
  fk false 0x340 704 ++ [(.x22, BitVec.ofNat 64 (s6N lay))]

/-! ## Compare -/

def cmpPc (t : Nat) : Nat := compareTab.getD t 0
def cmpK : List (Reg × Word) := fk false 0x340 64 ++ [(.x12, 0x180)]
def cmpDiff : E := .bin .sub (ldE 392) (ldE 168)
def specAcc (t : Nat) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cmpDiff)], [], cmpPc t + 7, true, 7,
   [⟨.ne, ldE 384, ldE 160, false⟩], none, 7⟩
def specCR1 (t : Nat) : Spec :=
  ⟨rejK, [], cmpPc t + 11, true, 5, [⟨.ne, ldE 384, ldE 160, true⟩], none, 5⟩


/-! ## The per-layer check -/

/-- Everything of transition copy `t` of layer `lay`. -/
def halfCheck (lay t : Nat) (hi : Nat) : Bool :=
  if hi = 1 then
    specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi)) (specRej1 (encD lay t) hi) encObligs [] []
  else
    specOB gkL (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi false ++ [.br false, .jmp])) (specBok (encD lay t) hi lay) encObligs
      (chKa lay t) [.x23, .x30, .x31] &&
    (hi == 0 || specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi true)) (specRej1 (encD lay t) hi) encObligs [] []) &&
    specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi false ++ [.br true])) (specRej2 (encD lay t) hi lay) encObligs [] []

def copyCheck (lay t : Nat) : Bool :=
  specB gkL (runAt (preK lay t) [] (preStart lay t) []) (specA lay t) (bK lay t) [] &&
  ((List.range 4).all (halfCheck lay t)) &&
  specB gkL (runAt (leafK lay) [] (retPc lay t) [.jmp]) (specLeaf lay) (leafPost lay) leafKeep

def layerCheck (lay : Nat) : Bool :=
  ((List.range (nCopy lay)).all fun t => copyCheck lay t) &&
  (lay != 0 || (List.range 32).all fun t =>
    specB [] (runAt cmpK [] (cmpPc t) [.br false]) (specAcc t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [])

end SigGolfCandidate.Verify
