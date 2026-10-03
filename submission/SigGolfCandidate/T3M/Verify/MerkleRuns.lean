import SigGolfCandidate.T3M.Verify.LayerRuns

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

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify

/-! ## Layout -/

/-- Chunks of the leaf index: layer 0 has two (levels 0..5, 6..11), the others one. -/
def mkNch (lay : Nat) : Nat := if lay = 0 then 2 else 1
/-- The first level of chunk `ci`. -/
def mkLo (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
/-- The levels of chunk `ci`. -/
def mkBits (lay ci : Nat) : Nat := if lay = 0 then 6 else hL lay
/-- The jump table `stab_lay_ci` (word index of its entry 0). -/
def mkTab (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 209832 else stabIdx lay
/-- M1: the dispatch word of block `sh` of chunk `ci`. -/
def mkTabW (lay ci sh : Nat) : Nat := if lay = 0 ∧ ci = 1 then 209832 + sh else stabW lay sh
/-- The shape block `shp_lay_ci_sh` (word index of its first instruction). -/
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 5487 + 101 * sh else if lay = 2 then 11951 + 101 * sh
  else if lay = 1 then 18416 + 134 * sh else if ci = 0 then 35567 + 48 * sh else 38641 + 53 * sh
/-- The parent's heap index is a constant register at the top three levels. -/
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
/-- Instruction words of level `l`: level 0 `addi a2; ecall; li a1; addi a0; sd tp; sw t5; ld tp; [li gp]; sd`
(BIG2: the `ld` makes `tp` the merged header word 0), later levels `addi a2; ecall; addi a0; sd tp; [li gp]; sd`. -/
def mkWords (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 6 else 8) else 5) + (if mkReg lay l then 0 else 1)
/-- Offset of level `kk` of chunk `ci` from the start of its block. -/
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- W's `layerBase` (the start of layer `lay`'s region, witness offset). -/
def mkBase (lay : Nat) : Nat := [10568, 14792, 17992, 21128].getD lay 0
/-- The Merkle block of level `l`: witness offset (W's `merkleBlock lay l`) and absolute address. -/
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
/-- Its current-node slot when the node is a left (`b = 0`, `L`) or right (`b = 1`, `R`) child. -/
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
/-- The root HASH's destination: the next encoding block's `M` (`0x100`) or the root slot (`0x180`). -/
def mkDst (lay leaf : Nat) : Nat := if lay = 0 then 12616 + 48 * (leaf / 2048 % 2) else 256

/-- The final top HASH retains its current output pointer. -/
def mkMove (lay level : Nat) : Nat := if lay = 0 ∧ level = 11 then 0 else 1
/-- The parent heap index stored at level `l` of block `sh` (the constant ones). -/
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)

/-! ## Registers -/

/-- The constant registers of the Merkle code (including the leaf-established dispatch window): `t0`, `s2`, `s6`, `tp = T(3)`'s word 0, the heap registers 1..7. -/
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, BitVec.ofNat 64 (if lay = 0 then 0xce000 else 0x6e000))]

/-- BIG2: the same without `tp` (after level 0 `tp` holds the merged header word 0, `mkX4`). -/
def mkKc (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, BitVec.ofNat 64 (if lay = 0 then 0xce000 else 0x6e000))]

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
  specB [] [] baseK (runAt (mkKc lay) [] (mkTabW lay ci sh) []) (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep

/-! ## A level -/

/-- The value of the heap store (`sw heap, 28(a0)`). -/
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 1)) else kw (mkHeap lay ci sh l)

/-- The header word 0 store of level `l`: level 0 stores `T(3)`'s word 0 and the tree (`sd tp; sw t5`), later
levels store the merged `tp` (BIG2). -/
def mkHdrE (lay l : Nat) : E := if l = 0 then (if lay = 0 then kw (hw 3 lay) else mkX4 lay) else .reg .x4

/-- The two header writes of level `l`: word 1 `tree | heap << 32` (two `sw`), word 0 `T(3)`. -/
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩, mkHeapE lay ci sh l),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, mkHdrE lay l)]

/-- Level 0's `ld tp` leaves the merged word in `tp` (BIG2); later levels keep `tp`. -/
def mkLvlRegs (lay l : Nat) : List (Reg × E) :=
  if l = 0 then (if lay = 0 then [(.x4, kw (hw 3 lay))] else [(.x4, mkX4 lay)]) else []

/-- The registers a level keeps: `tp` after level 0. -/
def mkLvlKeep (lay l : Nat) : List Reg := if l = 0 then [] else [.x4]

def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]

/-- The chunk-1 dispatch target of layer 0 (`((s7 >> 6) << 2) + 0xce000 - 608`, even). -/
def mkDispTgt : E :=
  .bin .and (.bin .add (.bin .sll (.bin .srl (.reg .x23) (kw 6)) (kw 2)) (kw 843168)) (.c (~~~1#64))

/-- Steps of the level body (after its `ecall`, before the next `addi a2` / `li a2` / dispatch). -/
def mkBody (lay l : Nat) : Nat := (if l = 0 then (if lay = 0 then 3 else 5) else 2) + (if mkReg lay l then 1 else 2)

/-- Is level `kk` of chunk `ci` the last of a chunk followed by the chunk-1 dispatch? -/
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)

/-- The next `a2`: the next level's current slot, or the root destination. -/
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else if lay = 0 then 12616 + 48 * (sh / 32 % 2) else 256

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
      [(.x12, BitVec.ofNat 64 (12616 + 48 * (sh / 32 % 2)))] else [])

def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlKN lay ci sh kk) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [])
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ (.x14 :: mkLvlKeep lay (mkLo lay ci + kk)))

def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlK lay (mkLo lay ci + kk)) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp])
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci kk) (mkKeep ++ mkLvlKeep lay (mkLo lay ci + kk))

def mkLvlCheck (lay ci sh kk : Nat) : Bool :=
  if mkIsDisp lay ci kk then mkLvlCheckD lay ci sh kk else mkLvlCheckN lay ci sh kk

/-! ## Blocks -/

/-- The entry and every level of block `sh` of chunk `ci` of layer `lay`. -/
def mkBlockCheck (lay ci sh : Nat) : Bool :=
  mkEntCheck lay ci sh && (List.range (mkBits lay ci)).all (mkLvlCheck lay ci sh)

/-- Blocks `lo .. lo + n - 1` of chunk `ci` of layer `lay`. -/
def mkChunkCheck (lay ci lo n : Nat) : Bool := (List.range' lo n).all (mkBlockCheck lay ci)

/-! ## The compare -/

/-- The compare copy `c` (after layer 0's shape block `shp_0_1_c`). -/
def cmpPc (c : Nat) : Nat := 38675 + 53 * c
def cmpDst (c : Nat) : Nat := 12616 + 48 * (c / 32 % 2)
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

end SigGolfCandidate.T3M
