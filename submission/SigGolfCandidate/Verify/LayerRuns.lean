import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.PorsTab

/-! # Layer blocks (W1a): transition (route, encoding, check, chain prologue), leaf, compare

Every start of layer `lay` (layer 4: a PORS root tail; below: a block of the last fold chunk of
layer `lay + 1`) runs its own copy of the transition (`trPc lay c`):
* route and encoding (`stepsA` steps up to the encoding `ecall`; the counter is read from the
  witness, `c0 .. c3` in the tweak slot of block `(0, 0)`, `c4` at `2392`);
* the encoding check (`or; blt` for the top bits, the SWAR digit sum, `remu` by `x18 = 4095`,
  `bne KT`), then the chain prologue `li s6, base`, the extraction of triple 0
  and `jalr ra` into the layer-shared chain code (24 steps, 27 cycles);
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

/-- Start `t` of layer `lay`: a PORS root tail's copy (layer 4) or right after the root hash of
block `t` of the last chunk of layer `lay + 1`. -/
def preStart (lay t : Nat) : Nat :=
  if lay = 4 then trPc 4 t
  else m4Pc (lay + 1) (nCh (lay + 1) - 1) t (chBits (lay + 1) (nCh (lay + 1) - 1) - 1) + 9

/-- Steps of the transition up to the encoding hash: layer 0 consumes the remaining route bits
directly (two `addi` for the sentinel, no mask/shift); layer 4 reuses the known hash length. -/
def stepsA (lay : Nat) : Nat := if lay = 0 then 10 else if lay = 4 then 11 else 12
def encPc (lay t : Nat) : Nat := trPc lay t + stepsA lay

/-- Known registers at the transition start. -/
def l4K : List (Reg × Word) := gkL ++ [(.x11, 64), (.x12, 0x120), (.x27, 0x40401), (.x14, KT4)]
def aK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x10, 0x340), (.x11, 64), (.x12, 0x120), (.x27, BitVec.ofNat 64 (hWord (lay + 1) + 768)), (.x22, BitVec.ofNat 64 (s6N (lay + 1)))]
def preK (lay : Nat) : List (Reg × Word) := if lay = 4 then l4K else aK lay

/-- Known registers after the encoding hash call. -/
def bK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x27, BitVec.ofNat 64 (hWord lay + 768)), (.x10, 0x100), (.x11, 64), (.x12, 0x120)] ++
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
  if lay = 0 then .bin .add (uEr lay) (cw 2048) else .bin .or (uEr lay) (cw (2 ^ heightL lay))

/-- The doubleword holding layer `lay`'s counter (`c4` at witness 2392, `c0 .. c3` in the tweak
slot of chain block `(0, 0)` at witness 2944). -/
def ctrA (lay : Nat) : Nat := if lay = 4 then 0x800 + 2392 else 0x800 + 2944 + 8 * (lay / 2)
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (ctrA lay))

def specA (lay t : Nat) : Spec :=
  ⟨[(.x23, uHE lay), (.x30, carryEr lay), (.x31, x31Er lay)],
   [(⟨none, BitVec.ofNat 64 312⟩, .c 0), (⟨none, BitVec.ofNat 64 304⟩, ctrE lay),
    (⟨none, BitVec.ofNat 64 264⟩, x31Er lay), (⟨none, BitVec.ofNat 64 256⟩, cw (hWord lay + 768))],
   encPc lay t, true, stepsA lay, [], none, stepsA lay⟩

/-! ## The encoding check (`remu x25, x25, x18`; layers 0 .. 3 compare `KT`, layer 4 reuses `x14 = KT4`,
targets185/186, retaining a one-step zero correction in layer0) and the chain prologue -/

/-- Four selector paths: AB, gated AB, BC, CD. The gated AB case is rejected by padding. -/
def selOf (a : BitVec 256) : Nat :=
  if a.getLsbD 127 then (if SigGolfCandidate.Ref.encodingGate a then 3 else 1)
  else if a.getLsbD 63 then 2 else 0

def selSteps (hi : Nat) : Nat := if hi = 0 then 4 else if hi = 1 then 5 else 7
def d0E (hi : Nat) : E := ldE (if hi = 2 then 296 else if hi = 3 then 304 else 288)
def d1E (hi : Nat) : E := ldE (if hi = 2 then 304 else if hi = 3 then 312 else 296)
def encObligs : List Oblig := []
theorem encObligs_holds (s : MachineState) : ∀ o ∈ encObligs, o.holds s := by simp [encObligs]
def selLow (hi : Nat) : Bool := decide (hi = 0 ∨ hi = 2)
def selSecond (hi : Nat) : Bool := decide (hi = 0 ∨ hi = 1)
def selDirs (hi : Nat) : List Dir := [.br (selLow hi), .br (selSecond hi)]
def selBrs (hi : Nat) : List Br :=
  [(if selLow hi then ⟨.ge, ldE 288, cw 0, selSecond hi⟩
    else ⟨.eq, E.bin .srl (ldE 288) (cw 60), cw 0, selSecond hi⟩),
   ⟨.ge, ldE 296, cw 0, selLow hi⟩]

def m1E : E := .c M1w
def m2E : E := .c M2w
def orE (hi : Nat) : E := .bin .or (d0E hi) (d1E hi)
def swA3 (hi : Nat) : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl (d0E hi) (cw 3)) m1E) (.bin .and (d0E hi) m1E))
    (.bin .and (.bin .srl (d1E hi) (cw 3)) m1E)) (.bin .and (d1E hi) m1E)
def swA4 (hi : Nat) : E := .bin .add (swA3 hi) (.bin .srl (swA3 hi) (cw 6))
def swA5 (hi : Nat) : E := .bin .and (swA4 hi) m2E
def swA6 (hi : Nat) : E := .bin .add (swA5 hi) (.bin .srl (swA5 hi) (cw 12))
def swA7 (hi : Nat) : E := .bin .add (swA6 hi) (.bin .srl (swA6 hi) (cw 24))
def swSBase (hi : Nat) : E := .bin .remu (swA5 hi) (cw 4095)
def swS (hi : Nat) (_lay : Nat) : E := swSBase hi

/-- The table index of triple 0 (`slli a4, a6, 9; and a4, a4, sp; add a4, a4, a5`) and the
dispatch target (`jalr ra, -2048(a4)`). -/
def x14E (hi : Nat) : E := .bin .add (.bin .and (.bin .sll (d0E hi) (cw 9)) (.c TMASK)) (.c TTA5)
def tgt0 (hi : Nat) : E := .bin .and (.bin .add (.bin .and (.bin .sll (d0E hi) (cw 9)) (.c TMASK)) (cw 0x4f800)) (.c (~~~1#64))

def stepsB (lay : Nat) : Nat := (if lay = 4 then 29 else 28)
def stepsBPath (hi lay : Nat) : Nat := (if lay = 4 then 22 else 21) + selSteps hi
def cyclesBPath (hi lay : Nat) : Nat := stepsBPath hi lay + 3

theorem stepsBPath_le (hi lay : Nat) : stepsBPath hi lay ≤ stepsB lay := by
  unfold stepsBPath stepsB selSteps; split_ifs <;> omega
theorem cyclesBPath_le (hi lay : Nat) : cyclesBPath hi lay ≤ stepsB lay + 3 := by
  have := stepsBPath_le hi lay; unfold cyclesBPath; omega
/-- One REMU costs four cycles rather than one. -/
def cyclesB (lay : Nat) : Nat := stepsB lay + 3

def specBok (hi : Nat) (lay : Nat) : Spec :=
  ⟨[(.x14, (x14E hi)), (.x16, (d0E hi)), (.x17, (d1E hi))], [], 0, false, stepsBPath hi lay,
   ([⟨.ne, (swS hi lay), .c (KTof lay), false⟩, ⟨.lt, (orE hi), .c 0, false⟩] ++ selBrs hi), some (tgt0 hi), cyclesBPath hi lay⟩

/-- Known registers on entry of the chain code; chain 0 initializes `x25` from `x27`. -/
def chKa (lay c : Nat) : List (Reg × Word) :=
  chK0 ++ [(.x22, BitVec.ofNat 64 (s6N lay)),
    (.x27, BitVec.ofNat 64 (hWord lay + 768)), (.x1, pcOf (retPc lay c))]

def rejK : List (Reg × E) := [(.x5, cw 1), (.x10, cw 1)]

def specRej1 (hi : Nat) : Spec := ⟨rejK, [], rejectPc + 2, true, selSteps hi + 5, [⟨.lt, (orE hi), .c 0, true⟩] ++ selBrs hi, none, selSteps hi + 5⟩
def specRej2 (hi : Nat) (lay : Nat) : Spec :=
  ⟨rejK, [], rejectPc + 2, true, 19 + selSteps hi, [⟨.ne, (swS hi lay), .c (KTof lay), true⟩, ⟨.lt, (orE hi), .c 0, false⟩] ++ selBrs hi, none, 22 + selSteps hi⟩

/-! ## Leaf -/

/-- The leaf code at the return pc: the leaf tweak, then the dispatch into the shape block of
chunk 0. -/
def leafSteps (lay : Nat) : Nat := if lay = 0 then 10 else 9

def leafK (lay : Nat) : List (Reg × Word) := chK0 ++ [(.x27, BitVec.ofNat 64 (hWord lay + 768)), (.x22, BitVec.ofNat 64 (s6N lay))]

def specLeaf (lay : Nat) : Spec :=
  ⟨[(.x10, cw 832), (.x11, cw 704)],
   [(⟨none, BitVec.ofNat 64 840⟩, .reg .x31), (⟨none, BitVec.ofNat 64 832⟩, cw (hWord lay + 256))],
   0, false, leafSteps lay, [], some (dispTgt lay 0), leafSteps lay⟩

def leafKeep : List Reg := [.x16, .x17, .x23, .x30, .x31]
def leafPost (lay : Nat) : List (Reg × Word) :=
  fk false 0x340 704 ++ [(.x27, BitVec.ofNat 64 (hWord lay + 768)), (.x22, BitVec.ofNat 64 (s6N lay))]

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
  specOB gkL (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br false, .br false, .jmp])) (specBok hi lay) encObligs
    (chKa lay t) [.x23, .x30, .x31] &&
  specOB [] (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br true])) (specRej1 hi) encObligs [] [] &&
  specOB [] (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br false, .br true])) (specRej2 hi lay) encObligs [] []

def copyCheck (lay t : Nat) : Bool :=
  specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) [] &&
  ((List.range 4).all (halfCheck lay t)) &&
  specB gkL (runAt (leafK lay) [] (retPc lay t) [.jmp]) (specLeaf lay) (leafPost lay) leafKeep

def layerCheck (lay : Nat) : Bool :=
  ((List.range (nCopy lay)).all fun t => copyCheck lay t) &&
  (lay != 0 || (List.range 32).all fun t =>
    specB [] (runAt cmpK [] (cmpPc t) [.br false]) (specAcc t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [])

end SigGolfCandidate.Verify
