import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.PorsTab

/-! # Layer blocks: precode (route, encoding, check, chain-0 dispatch), leaf, compare -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv


/-- The number of copies of the precode of layer `lay`: layer 4 has one per PORS root tail; below,
every block of the last chunk of layer `lay + 1` ends with its own copy. -/
def nCopy (lay : Nat) : Nat := if lay = 4 then 3 else 2 ^ chBits (lay + 1) (nCh (lay + 1) - 1)

/-- The number of copies of the precode itself (the layer transition): one per start. -/
def nEnc (lay : Nat) : Nat := nCopy lay

/-- The copy of the transition that start `t` runs. -/
def encCp (_lay t : Nat) : Nat := t

/-- Start of transition copy `c` of layer `lay`. -/
def trPc (lay c : Nat) : Nat := (layerPcTab.getD lay []).getD c 0

/-- Start `t` of the precode of layer `lay`: after the PORS root tail's layer constants
(layer 4) or right after the root hash of block `t` of the last chunk of layer `lay + 1`. -/
def preStart (lay t : Nat) : Nat :=
  if lay = 4 then trPc 4 t
  else m4Pc (lay + 1) (nCh (lay + 1) - 1) t (chBits (lay + 1) (nCh (lay + 1) - 1) - 1) + 9

/-- Steps to the encoding hash; the top route is already an eleven-bit leaf index. -/
def stepsT (lay : Nat) : Nat := if lay = 0 then 13 else if lay = 4 then 15 else 14
/-- Steps from a precode start (every start runs its own copy). -/
def stepsA (lay : Nat) : Nat := stepsT lay
def encPcC (lay c : Nat) : Nat := trPc lay c + stepsT lay
def encPc (lay t : Nat) : Nat := encPcC lay (encCp lay t)

/-- Known registers at the precode start. -/
def l4K : List (Reg × Word) := gkL0 ++ [(.x11, 64), (.x12, 0x120), (.x27, 0x40101)]
def aK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x10, 0x1C0), (.x11, 64), (.x12, 0x120),
    (.x27, BitVec.ofNat 64 (hWord (lay + 1))), (.x15, BitVec.ofNat 64 (bVal (lay + 1) 41))]
def preK (lay : Nat) : List (Reg × Word) := if lay = 4 then l4K else aK lay

/-- Known registers after the encoding hash call. -/
def bK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x27, BitVec.ofNat 64 (hWord lay)), (.x10, 0x100),
    (.x11, 64), (.x12, 0x140)] ++
    (if lay < 4 then [(.x15, BitVec.ofNat 64 (bVal (lay + 1) 41))] else [])

/-- At the top layer, the incoming route is already an 11-bit leaf index. -/
def uEr (lay : Nat) : E :=
  if lay = 0 then .reg .x30 else
    .bin .and (.reg (if lay = 4 then .x22 else .x30)) (cw (2 ^ heightL lay - 1))
def tauEr (lay : Nat) : E :=
  if lay = 0 then cw 0 else
    .bin .srl (.reg (if lay = 4 then .x22 else .x30)) (cw (heightL lay))
def x31Er (lay : Nat) : E :=
  if lay = 0 then .bin .sll (uEr lay) (cw 32) else
    .bin .add (tauEr lay) (.bin .sll (uEr lay) (cw 32))
/-- `U = e | 2^h` (heap sentinel): `ori` (h < 11) or two `addi 1024` (h = 11). -/
def uHE (lay : Nat) : E :=
  if lay = 0 then .bin .add (uEr lay) (cw 2048) else .bin .or (uEr lay) (cw (2 ^ heightL lay))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (0x20B8 + 8 * (lay / 2)))

def specA (lay t : Nat) : Spec :=
  ⟨[(.x23, uHE lay), (.x30, tauEr lay), (.x31, x31Er lay)],
   [(⟨none, BitVec.ofNat 64 312⟩, .c 0), (⟨none, BitVec.ofNat 64 304⟩, ctrE lay),
    (⟨none, BitVec.ofNat 64 264⟩, x31Er lay), (⟨none, BitVec.ofNat 64 256⟩, cw (hWord lay + 768))],
   encPc lay t, true, stepsA lay, [], none, stepsA lay⟩

/-! ## The encoding check (`remu x25, x25, x18; bne KT`)

The OTS RISC-V modular fold applies to six base-4096 lanes. Their sum is below
4095, so the remainder is exact. The LeanISA constant-reuse technique is applied
to `x18`: its rebased address value is also the modulus. The remainder costs four
cycles, replacing six shift/add instructions and the final shift (seven cycles).
The code is regenerated (`gen/verify`), so no padding preserves the old addresses.
-/

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
def swS : E := .bin .remu swA5 (cw 4095)

/-- The dispatch register of a site computed from the digit word `D`. -/
def maskD (i : Nat) (D : E) : E :=
  if isSingle i then mkBin .sll (mkBin .srl D (cw 60)) (cw 4)
  else if i % 21 = 0 then mkBin .and (mkBin .sll D (cw 4)) (cw 0x3F0)
  else mkBin .and (mkBin .srl D (cw (3 * (i % 21) - 4))) (cw 0x3F0)

def rE0 (lay : Nat) : E := mkBin .add (maskD 0 d0E) (cw (bVal lay 0))

def stepsB (lay : Nat) : Nat := if lay = 4 then 32 else 29

/-- One REMU costs four cycles rather than one. -/
def cyclesB (lay : Nat) : Nat := stepsB lay + 3

/-- Chain setup: `sw H, CB; sd X31, CB+8` (layer 4 also zeroes CB+32..48, left by the last PORS leaf), then
chain 0's head writes byte 5 (`i = 0`, stored from `zero`). -/
def setupMem (lay : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 192⟩, .bin (.st .b 5) (stW0 192 (cw (hWord lay))) (cw 0))] ++
  (if lay = 4 then [(⟨none, BitVec.ofNat 64 232⟩, .c 0), (⟨none, BitVec.ofNat 64 224⟩, .c 0)] else []) ++
  [(⟨none, BitVec.ofNat 64 200⟩, .reg .x31)]

def specBok (lay t : Nat) : Spec :=
  ⟨[(.x1, ldE (chainAddr lay 0)), (.x2, ldE (chainAddr lay 0 + 8)), (.x14, rE0 lay),
    (.x15, cw (bVal lay 0)), (.x16, d0E), (.x17, d1E)],
   setupMem lay, 0, false, stepsB lay,
   [⟨.ne, swS, .c KT, false⟩, ⟨.lt, orE, .c 0, false⟩],
   some (mkBin .and (mkAdd (rE0 lay) (.c (BitVec.ofNat 64 (tabAddr lay 0) - BitVec.ofNat 64 (bVal lay 0))))
     (.c (~~~1#64))), cyclesB lay⟩

def rejK : List (Reg × E) := [(.x5, cw 1), (.x10, cw 1)]

def specRej1 : Spec := ⟨rejK, [], rejectPc + 2, true, 7, [⟨.lt, orE, .c 0, true⟩], none, 7⟩
def specRej2 : Spec :=
  ⟨rejK, [], rejectPc + 2, true, 21, [⟨.ne, swS, .c KT, true⟩, ⟨.lt, orE, .c 0, false⟩], none, 24⟩

/-! ## Leaf -/

/-- The leaf code: the leaf tweak, then the dispatch into the shape block of chunk 0. -/
def leafSteps (lay : Nat) : Nat := if lay = 0 then 13 else 12

def specLeaf (lay : Nat) : Spec :=
  ⟨[(.x10, cw 832), (.x11, cw 704)],
   [(⟨none, BitVec.ofNat 64 456⟩, stW0 456 (.reg .x30)), (⟨none, BitVec.ofNat 64 448⟩, cw (hWord lay + 512)),
    (⟨none, BitVec.ofNat 64 840⟩, .reg .x31), (⟨none, BitVec.ofNat 64 832⟩, cw (hWord lay + 256))],
   0, false, leafSteps lay, [], some (dispTgt lay 0), leafSteps lay⟩

def leafKeep : List Reg := [.x16, .x17, .x23, .x30, .x31]
def leafPost (lay : Nat) : List (Reg × Word) :=
  fk false 0x340 704 ++ [(.x27, BitVec.ofNat 64 (hWord lay)),
    (.x15, BitVec.ofNat 64 (bVal lay 41))]

/-! ## Compare -/

def cmpPc (t : Nat) : Nat := compareTab.getD t 0
def cmpK : List (Reg × Word) := fk false 0x1C0 64 ++ [(.x12, 0x180)]
def specAcc (t : Nat) : Spec :=
  ⟨[(.x5, cw 1), (.x10, .bin .xor (ldE 392) (ldE 168))], [], cmpPc t + 7, true, 7,
   [⟨.ne, ldE 384, ldE 160, false⟩], none, 7⟩
def specCR1 (t : Nat) : Spec :=
  ⟨rejK, [], cmpPc t + 11, true, 5, [⟨.ne, ldE 384, ldE 160, true⟩], none, 5⟩
/-! ## The per-layer check -/

def layerCheck (lay : Nat) : Bool :=
  ((List.range (nCopy lay)).all fun t =>
    specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) []) &&
  ((List.range (nEnc lay)).all fun c =>
    specB gkL (runAt (bK lay) [] (encPcC lay c + 1) [.br false, .br false, .jmp]) (specBok lay c)
      (chKa lay) [.x23, .x30, .x31] &&
    specB [] (runAt (bK lay) [] (encPcC lay c + 1) [.br true]) specRej1 [] [] &&
    specB [] (runAt (bK lay) [] (encPcC lay c + 1) [.br false, .br true]) specRej2 [] []) &&
  (lay != 0 || (List.range 32).all fun t =>
    specB [] (runAt cmpK [] (cmpPc t) [.br false]) (specAcc t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] []) &&
  specB gkL (runAt (headK lay 42) [] (nextPc' lay 41) [.jmp]) (specLeaf lay) (leafPost lay) leafKeep

end SigGolfCandidate.Verify
