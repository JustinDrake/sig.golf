import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.PorsTab

/-! # Layer blocks (W1a): transition (route, encoding, check, chain prologue), leaf, compare

Every start of layer `lay` (layer 4: a PORS root tail; below: a block of the last fold chunk of
layer `lay + 1`) runs its own copy of the transition (`trPc lay c`):
* route and encoding (`stepsA` steps up to the encoding `ecall`; the counter is read from the
  witness, `c0 .. c3` in the tweak slot of block `(0, 0)`, `c4` at `2392`);
* the encoding check (`or; blt` for the top bits, the SWAR digit sum, `remu` by `x18 = 4095`,
  `bne KT`), then the chain prologue `li s6, base; sub s9, s11, t3`, the extraction of triple 0
  and `jalr ra` into the layer-shared chain code (25 steps, 28 cycles);
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

/-- Steps of the transition up to the encoding hash (layer 0: two `addi` for the sentinel). -/
def stepsA (lay : Nat) : Nat := if lay = 0 then 15 else if lay = 4 then 13 else 14
def encPc (lay t : Nat) : Nat := trPc lay t + stepsA lay

/-- Known registers at the transition start. -/
def l4K : List (Reg × Word) := gkL ++ [(.x11, 64), (.x12, 0x120), (.x27, 0x40101)]
def aK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x10, 0x1C0), (.x11, 64), (.x12, 0x120), (.x27, BitVec.ofNat 64 (hWord (lay + 1)))]
def preK (lay : Nat) : List (Reg × Word) := if lay = 4 then l4K else aK lay

/-- Known registers after the encoding hash call. -/
def bK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x27, BitVec.ofNat 64 (hWord lay)), (.x10, 0x100), (.x11, 64), (.x12, 0x140)]

def uEr (lay : Nat) : E :=
  .bin .and (.reg (if lay = 4 then .x22 else .x30)) (cw (2 ^ heightL lay - 1))
def tauEr (lay : Nat) : E := .bin .srl (.reg (if lay = 4 then .x22 else .x30)) (cw (heightL lay))
def x31Er (lay : Nat) : E := .bin .add (tauEr lay) (.bin .sll (uEr lay) (cw 32))
/-- `U = e | 2^h` (heap sentinel): `ori` (h < 11) or two `addi 1024` (h = 11). -/
def uHE (lay : Nat) : E :=
  if lay = 0 then .bin .add (uEr lay) (cw 2048) else .bin .or (uEr lay) (cw (2 ^ heightL lay))

/-- The doubleword holding layer `lay`'s counter (`c4` at witness 2392, `c0 .. c3` in the tweak
slot of chain block `(0, 0)` at witness 2944). -/
def ctrA (lay : Nat) : Nat := if lay = 4 then 0x800 + 2392 else 0x800 + 2944 + 8 * (lay / 2)
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (ctrA lay))

def specA (lay t : Nat) : Spec :=
  ⟨[(.x23, uHE lay), (.x30, tauEr lay), (.x31, x31Er lay)],
   [(⟨none, BitVec.ofNat 64 312⟩, .c 0), (⟨none, BitVec.ofNat 64 304⟩, ctrE lay),
    (⟨none, BitVec.ofNat 64 264⟩, x31Er lay), (⟨none, BitVec.ofNat 64 256⟩, cw (hWord lay + 768))],
   encPc lay t, true, stepsA lay, [], none, stepsA lay⟩

/-! ## The encoding check (`remu x25, x25, x18; bne KT`) and the chain prologue -/

def d0E : E := ldE 320
def d1E : E := ldE 328
def m1E : E := .c M1w
def m2E : E := .c M2w
def orE : E := .bin .or d0E d1E
def swA3 : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl d0E (cw 3)) m1E) (.bin .and d0E m1E))
    (.bin .and (.bin .srl d1E (cw 3)) m1E)) (.bin .and d1E m1E)
def swA4 : E := .bin .add swA3 (.bin .srl swA3 (cw 6))
def swA5 : E := .bin .and swA4 m2E
def swA6 : E := .bin .add swA5 (.bin .srl swA5 (cw 12))
def swA7 : E := .bin .add swA6 (.bin .srl swA6 (cw 24))
def swSBase : E := .bin .remu swA5 (cw 4095)
def swS (lay : Nat) : E :=
  if 4 ≤ lay then .bin .add swSBase (cw (2 ^ 64 - 2))
  else if 3 ≤ lay then .bin .add swSBase (cw (2 ^ 64 - 1)) else swSBase

/-- The table index of triple 0 (`slli a4, a6, 9; and a4, a4, sp; add a4, a4, a5`) and the
dispatch target (`jalr ra, -2048(a4)`). -/
def x14E : E := .bin .add (.bin .and (.bin .sll d0E (cw 9)) (.c TMASK)) (.c TTA5)
def tgt0 : E := .bin .and (.bin .add (.bin .and (.bin .sll d0E (cw 9)) (.c TMASK)) (cw 0x4f800)) (.c (~~~1#64))

def stepsB (lay : Nat) : Nat := if 3 ≤ lay then 26 else 25
/-- One REMU costs four cycles rather than one. -/
def cyclesB (lay : Nat) : Nat := stepsB lay + 3

def specBok (lay : Nat) : Spec :=
  ⟨[(.x14, x14E), (.x16, d0E), (.x17, d1E)], [], 0, false, stepsB lay,
   [⟨.ne, swS lay, .c KT, false⟩, ⟨.lt, orE, .c 0, false⟩], some tgt0, cyclesB lay⟩

/-- Known registers on entry of the chain code (`li s6; sub s9, s11, t3; jalr ra`). -/
def chKa (lay c : Nat) : List (Reg × Word) :=
  chK0 ++ [(.x22, BitVec.ofNat 64 (s6N lay)), (.x25, BitVec.ofNat 64 (hWord lay) - K40),
    (.x27, BitVec.ofNat 64 (hWord lay)), (.x1, pcOf (retPc lay c))]

def rejK : List (Reg × E) := [(.x5, cw 1), (.x10, cw 1)]

def specRej1 : Spec := ⟨rejK, [], rejectPc + 2, true, 7, [⟨.lt, orE, .c 0, true⟩], none, 7⟩
def specRej2 (lay : Nat) : Spec :=
  ⟨rejK, [], rejectPc + 2, true, 21 + (if 3 ≤ lay then 1 else 0), [⟨.ne, swS lay, .c KT, true⟩, ⟨.lt, orE, .c 0, false⟩], none, 24 + (if 3 ≤ lay then 1 else 0)⟩

/-! ## Leaf -/

/-- The leaf code at the return pc: the leaf tweak, then the dispatch into the shape block of
chunk 0. -/
def leafSteps (lay : Nat) : Nat := if lay = 0 then 13 else 12

def leafK (lay : Nat) : List (Reg × Word) := chK0 ++ [(.x27, BitVec.ofNat 64 (hWord lay))]

def specLeaf (lay : Nat) : Spec :=
  ⟨[(.x10, cw 832), (.x11, cw 704)],
   [(⟨none, BitVec.ofNat 64 456⟩, stW0 456 (.reg .x30)), (⟨none, BitVec.ofNat 64 448⟩, cw (hWord lay + 512)),
    (⟨none, BitVec.ofNat 64 840⟩, .reg .x31), (⟨none, BitVec.ofNat 64 832⟩, cw (hWord lay + 256))],
   0, false, leafSteps lay, [], some (dispTgt lay 0), leafSteps lay⟩

def leafKeep : List Reg := [.x16, .x17, .x23, .x30, .x31]
def leafPost (lay : Nat) : List (Reg × Word) :=
  fk false 0x340 704 ++ [(.x27, BitVec.ofNat 64 (hWord lay))]

/-! ## Compare -/

def cmpPc (t : Nat) : Nat := compareTab.getD t 0
def cmpK : List (Reg × Word) := fk false 0x1C0 64 ++ [(.x12, 0x180)]
def specAcc (t : Nat) : Spec :=
  ⟨[(.x5, cw 1), (.x10, .bin .xor (ldE 392) (ldE 168))], [], cmpPc t + 7, true, 7,
   [⟨.ne, ldE 384, ldE 160, false⟩], none, 7⟩
def specCR1 (t : Nat) : Spec :=
  ⟨rejK, [], cmpPc t + 11, true, 5, [⟨.ne, ldE 384, ldE 160, true⟩], none, 5⟩
/-! ## The per-layer check -/

/-- Everything of transition copy `t` of layer `lay`. -/
def copyCheck (lay t : Nat) : Bool :=
  specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) [] &&
  specB gkL (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br false, .jmp]) (specBok lay)
    (chKa lay t) [.x23, .x30, .x31] &&
  specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br true]) specRej1 [] [] &&
  specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br true]) (specRej2 lay) [] [] &&
  specB gkL (runAt (leafK lay) [] (retPc lay t) [.jmp]) (specLeaf lay) (leafPost lay) leafKeep

def layerCheck (lay : Nat) : Bool :=
  ((List.range (nCopy lay)).all fun t => copyCheck lay t) &&
  (lay != 0 || (List.range 32).all fun t =>
    specB [] (runAt cmpK [] (cmpPc t) [.br false]) (specAcc t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [])

end SigGolfCandidate.Verify
