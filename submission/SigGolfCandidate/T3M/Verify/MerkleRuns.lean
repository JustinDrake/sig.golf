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
dispatch `slli a4, gp, 2; add a4, a5; jalr -608(a4)` into `stab_0_1` (gp = s7 >> 6 from the level's heap store,
a5 = 0xce000 carried from leaf-pk).

Families (each a path run checked by `specB`, kernel-checked in `MerkleCheck*`):
* `mkEntCheck lay ci sh`: the table word `j shp_lay_ci_sh` and the first `addi a2`, to the first `ecall` (2 steps);
* `mkLvlCheck lay ci sh kk`: level `mkLo lay ci + kk` from after its `ecall` to the next `ecall` (or through the chunk
  dispatch to its symbolic jump);
* `cmpCheck c`: the compare copy `c` (low `ld/ld/bne`, high SUB-as-exit HALT).

Layout facts (word indices, `t3m/images/verify.labels`): `stab_3_0` 209512, `stab_2_0` 209576, `stab_1_0` 209640,
`stab_0_0` 209768, `stab_0_1` 209832; `shp_3_0_sh` = 5483 + 101 sh, `shp_2_0_sh` = 11947 + 101 sh, `shp_1_0_sh` =
18411 + 134 sh, `shp_0_0_sh` = 35563 + 48 sh, `shp_0_1_sh` = 38635 + 53 sh, `xcmp` copy `c` = 38676 + 53 c (checked
against the disassembly by `checks/gen/merkle_check.py`, and by the kernel through the runs below). -/

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
/-- The shape block `shp_lay_ci_sh` (word index of its first instruction). -/
def mkShp (lay ci sh : Nat) : Nat :=
  if lay = 3 then 5483 + 101 * sh else if lay = 2 then 11947 + 101 * sh
  else if lay = 1 then 18411 + 134 * sh else if ci = 0 then 35563 + 48 * sh else 38635 + 53 * sh
/-- The parent's heap index is a constant register at the top three levels. -/
def mkReg (lay l : Nat) : Bool := decide (hL lay ≤ l + 3)
/-- Instruction words of level `l` (`addi a2; ecall; [li a1]; addi a0; sd; sw; [li gp / srli gp]; sw`). -/
def mkWords (lay l : Nat) : Nat := 6 + (if l = 0 then 1 else 0) + (if mkReg lay l then 0 else 1)
/-- Offset of level `kk` of chunk `ci` from the start of its block. -/
def mkOff (lay ci : Nat) : Nat → Nat
  | 0 => 0
  | kk + 1 => mkOff lay ci kk + mkWords lay (mkLo lay ci + kk)
/-- W's `layerBase` (the start of layer `lay`'s region, witness offset). -/
def mkBase (lay : Nat) : Nat := [11288, 15768, 18968, 22104].getD lay 0
/-- The Merkle block of level `l`: witness offset (W's `merkleBlock lay l`) and absolute address. -/
def mkBo (lay l : Nat) : Nat := mkBase lay + 64 * (hL lay - 1 - l)
def mkBlk (lay l : Nat) : Nat := 0x800 + mkBo lay l
/-- Its current-node slot when the node is a left (`b = 0`, `L`) or right (`b = 1`, `R`) child. -/
def mkCur (lay l b : Nat) : Nat := mkBlk lay l + 48 * b
/-- The root HASH's destination: the next encoding block's `M` (`0x100`) or the root slot (`0x180`). -/
def mkDst (lay : Nat) : Nat := if lay = 0 then 384 else 256
/-- The parent heap index stored at level `l` of block `sh` (the constant ones). -/
def mkHeap (lay ci sh l : Nat) : Nat := (2 ^ hL lay + sh * 2 ^ mkLo lay ci) / 2 ^ (l + 1)

/-! ## Registers -/

/-- The constant registers of the Merkle code: `t0`, `s2`, `s6`, `tp = T(3)`'s word 0, the heap registers 1..7. -/
def mkK (lay : Nat) : List (Reg × Word) :=
  baseK ++ [(.x22, BitVec.ofNat 64 (s6v lay)), (.x4, BitVec.ofNat 64 (hw 3 lay)), (.x6, 1), (.x7, 2), (.x8, 3),
    (.x9, 4), (.x13, 5), (.x26, 6), (.x31, 7), (.x15, 0xce000)]

/-- Registers that no Merkle run writes or knows (kept for the next transition: `sp`, `s4`, `s5`, `s7`, `s8`, `s11`,
`t3`, `t5`, ...). -/
def mkKeep : List Reg := [.x1, .x2, .x16, .x17, .x19, .x20, .x21, .x23, .x24, .x25, .x27, .x28, .x29, .x30]

/-! ## The entry of a shape block -/

/-- From the table word: `j shp_lay_ci_sh; addi a2, s6, cur(lo)`, stopping at the first `ecall` (no writes). -/
def mkEntSpec (lay ci sh : Nat) : Spec := ⟨[], [], mkShp lay ci sh + 1, true, 2, [], none, 2⟩

def mkEntPost (lay ci sh : Nat) : List (Reg × Word) :=
  mkK lay ++ [(.x12, BitVec.ofNat 64 (mkCur lay (mkLo lay ci) (sh % 2)))]

def mkEntKeep : List Reg := mkKeep ++ [.x10, .x11, .x14]

def mkEntCheck (lay ci sh : Nat) : Bool :=
  specB [] [] baseK (runAt (mkK lay) [] (mkTab lay ci + sh) []) (mkEntSpec lay ci sh) [] (mkEntPost lay ci sh) mkEntKeep

/-! ## A level -/

/-- The value of the heap store (`sw heap, 28(a0)`). -/
def mkHeapE (lay ci sh l : Nat) : E :=
  if lay = 0 ∧ ci = 0 then .bin .srl (.reg .x23) (kw (l + 1)) else kw (mkHeap lay ci sh l)

/-- The two header writes of level `l`: word 1 `tree | heap << 32` (two `sw`), word 0 `T(3)`. -/
def mkLvlMem (lay ci sh l : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 (mkBlk lay l + 24)⟩,
      .bin (.st .w 4) (.bin (.st .w 0) (.ld (kw (mkBlk lay l + 24))) (.reg .x30)) (mkHeapE lay ci sh l)),
   (⟨none, BitVec.ofNat 64 (mkBlk lay l + 16)⟩, kw (hw 3 lay))]

def mkLvlAllow (lay l : Nat) : List Nat := [mkBlk lay l + 16, mkBlk lay l + 24]

/-- The chunk-1 dispatch target of layer 0 (`((s7 >> 6) << 2) + 0xce000 - 608`, even). -/
def mkDispTgt : E :=
  .bin .and (.bin .add (.bin .sll (.bin .srl (.reg .x23) (kw 6)) (kw 2)) (kw 843168)) (.c (~~~1#64))

/-- Steps of the level body (after its `ecall`, before the next `addi a2` / `li a2` / dispatch). -/
def mkBody (lay l : Nat) : Nat := (if l = 0 then 1 else 0) + 3 + (if mkReg lay l then 1 else 2)

/-- Is level `kk` of chunk `ci` the last of a chunk followed by the chunk-1 dispatch? -/
def mkIsDisp (lay ci kk : Nat) : Bool := decide (lay = 0 ∧ ci = 0 ∧ kk + 1 = mkBits lay ci)

/-- The next `a2`: the next level's current slot, or the root destination. -/
def mkNextA2 (lay ci sh kk : Nat) : Nat :=
  if kk + 1 < mkBits lay ci then mkCur lay (mkLo lay ci + kk + 1) (sh / 2 ^ (kk + 1) % 2) else mkDst lay

/-- A level ending at the next `ecall` (the next level's HASH or the root HASH). -/
def mkLvlSpecN (lay ci sh kk : Nat) : Spec :=
  ⟨[], mkLvlMem lay ci sh (mkLo lay ci + kk), mkShp lay ci sh + mkOff lay ci (kk + 1) + 1, true,
    mkBody lay (mkLo lay ci + kk) + 1, [], none, mkBody lay (mkLo lay ci + kk) + 1⟩

/-- Level 5 of layer 0's chunk 0, ending with the chunk-1 dispatch (a jump to `stab_0_1`). -/
def mkLvlSpecD (lay ci sh kk : Nat) : Spec :=
  ⟨[], mkLvlMem lay ci sh (mkLo lay ci + kk), 0, false, mkBody lay (mkLo lay ci + kk) + 3, [], some mkDispTgt,
    mkBody lay (mkLo lay ci + kk) + 3⟩

/-- Known at the level body's start: the constants, and `a1 = 64` after the leaf-pk HASH. -/
def mkLvlK (lay l : Nat) : List (Reg × Word) := mkK lay ++ (if l = 0 then [] else [(.x11, 64)])

def mkLvlPostN (lay ci sh kk : Nat) : List (Reg × Word) :=
  mkK lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))),
    (.x12, BitVec.ofNat 64 (mkNextA2 lay ci sh kk))]

def mkLvlPostD (lay ci kk : Nat) : List (Reg × Word) :=
  mkK lay ++ [(.x11, 64), (.x10, BitVec.ofNat 64 (mkBlk lay (mkLo lay ci + kk))), (.x15, 0xce000)]

def mkLvlCheckN (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlK lay (mkLo lay ci + kk)) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [])
    (mkLvlSpecN lay ci sh kk) [] (mkLvlPostN lay ci sh kk) (mkKeep ++ [.x14])

def mkLvlCheckD (lay ci sh kk : Nat) : Bool :=
  specB (mkLvlAllow lay (mkLo lay ci + kk)) [] baseK
    (runAt (mkLvlK lay (mkLo lay ci + kk)) [] (mkShp lay ci sh + mkOff lay ci kk + 2) [.jmp])
    (mkLvlSpecD lay ci sh kk) [] (mkLvlPostD lay ci kk) mkKeep

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
def cmpPc (c : Nat) : Nat := 38676 + 53 * c
def cmpBr1 (d : Bool) : Br := ⟨.ne, .ld (kw 384), .ld (kw 160), d⟩
def cmpBr2 (d : Bool) : Br := ⟨.ne, .ld (kw 392), .ld (kw 168), d⟩

/-- The high-word difference is zero exactly when the high words agree. -/
def cmpDelta : E := .bin .sub (.ld (kw 392)) (.ld (kw 168))

/-- The low words agree: compute the high-word difference and HALT with that exit code. -/
def cmpAcc (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, cmpDelta)], [], cmpPc c + 7, true, 7, [cmpBr1 false], none, 7⟩
/-- The low doublewords differ: HALT(1) after five instructions. -/
def cmpRej1 (c : Nat) : Spec :=
  ⟨[(.x5, kw 1), (.x10, kw 1)], [], cmpPc c + 11, true, 5, [cmpBr1 true], none, 5⟩

def cmpCheck (c : Nat) : Bool :=
  specB [] [] [] (runAt baseK [] (cmpPc c) [.br false]) (cmpAcc c) [] [] [] &&
  specB [] [] [] (runAt baseK [] (cmpPc c) [.br true]) (cmpRej1 c) [] [] []

end SigGolfCandidate.T3M
