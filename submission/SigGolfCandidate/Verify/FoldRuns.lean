import SigGolfCandidate.Verify.Post
import SigGolfCandidate.Verify.Tab

/-! # Merkle fold levels (M4 shape blocks): expected symbolic results

After the leaf hash, one computed jump per chunk of the leaf index enters a block of
straight-line levels for that chunk value (layers 1..4: one chunk of `h` bits; layer 0: 6 + 5
bits). Block `v` of chunk `ci` starts at word `m4Base + v * 2 ^ m4Sh`; level `kk` of the chunk
(`lam = chB0 + kk`) starts with `li a2, 0x360 + 16 t; ecall` (the hash of the node below, into
the slot of side `t = v / 2^kk % 2`) at offset `m4Off kk`. -/

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def cw (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldE (a : Nat) : E := .ld (cw a)
def stW (a : Nat) (v : E) : E := .bin (.st .w 4) (ldE a) v
def stW0 (a : Nat) (v : E) : E := .bin (.st .w 0) (ldE a) v

/-- Layer heights (layer 0 = top) and witness offsets of the paths (W1a, `Ref.pathOff`). -/
def heightL (lay : Nat) : Nat := [11, 6, 6, 6, 5].getD lay 0
def pathOffL (lay : Nat) : Nat := [2704, 4032, 4416, 4800, 5184].getD lay 0
def pathStrideL (lay : Nat) : Nat := if lay = 0 then 16 else 64

/-- Known registers: FORS (`kind = true`) or layers. -/
def gkOf (kind : Bool) : List (Reg × Word) := if kind then gkF else gkL

def fk (kind : Bool) (a0 a1 : Nat) : List (Reg × Word) :=
  gkOf kind ++ [(.x10, BitVec.ofNat 64 a0), (.x11, BitVec.ofNat 64 a1)]

def fkeep (kind : Bool) : List Reg :=
  if kind then [.x16, .x17, .x22, .x23, .x25, .x27, .x28, .x29, .x30, .x31]
  else [.x14, .x16, .x17, .x23, .x27, .x30, .x31]

def okFold (kind : Bool) (o : Option PRes) (e : PRes) (post : List (Reg × Word)) : Bool :=
  optBeq o e && resOK (gkOf kind) e && knownB post e && keepB (fkeep kind) e

/-! ## Shape blocks (tables in `Tab.lean`) -/

def m4Get (lay ci j : Nat) : Nat := ((m4Tab.getD lay []).getD ci []).getD j 0
/-- First word of block 0 of chunk `ci`. -/
def m4Base (lay ci : Nat) : Nat := m4Get lay ci 0
/-- log2 of the block size in words. -/
def m4Sh (lay ci : Nat) : Nat := m4Get lay ci 1
/-- The dispatch constants: `lui` value and the offset added to the shifted index. -/
def m4Hi (lay ci : Nat) : Nat := m4Get lay ci 4
def m4Doff (lay ci : Nat) : Nat := m4Get lay ci 5
/-- Offset of level `kk` in a block of chunk `ci`. -/
def m4Off (lay ci kk : Nat) : Nat := ((m4OffTab.getD lay []).getD ci []).getD kk 0

/-- Chunks of the leaf index: layer 0 has two (bits 0..5, 6..10), the others one. -/
def nCh (lay : Nat) : Nat := if lay = 0 then 2 else 1
def chB0 (lay ci : Nat) : Nat := if lay = 0 ∧ ci = 1 then 6 else 0
def chBits (lay ci : Nat) : Nat := if lay = 0 then (if ci = 0 then 6 else 5) else heightL lay
/-- The fold-dispatch page offset `m4Hi lay 0 / 512` that layers 1..4 add into `x23`. -/
def uOff (lay : Nat) : Nat := if lay = 1 then 456 else if lay = 2 then 392 else 328
/-- `x23` from the transition on: layer 0 the reflected heap index, layers 1..4 the heap index plus
the dispatch page offset (`addi` replaces the sentinel `ori`). -/
def heapU (lay e : Nat) : Nat := if lay = 0 then 4095 - e else e + 2 ^ heightL lay + uOff lay


/-- The chunk holding level `lam`. -/
def chOf (lay lam : Nat) : Nat := if lay = 0 ∧ 6 ≤ lam then 1 else 0

/-- The `li a2` of level `kk` of block `v` of chunk `ci`. -/
def m4Pc (lay ci v kk : Nat) : Nat :=
  m4Base lay ci + (if lay = 0 then 2 ^ chBits lay ci - 1 - v else v) * 2 ^ m4Sh lay ci + m4Off lay ci kk

/-- Sibling witness address of level `lam`. -/
def sibAddr (lay lam : Nat) : Nat := 0x800 + pathOffL lay + pathStrideL lay * lam

/-- M4c: the parent of level `lam` is at depth `h - lam - 1`; at depths 1 and 2 (heap indices
2..7) its index is a constant stored from the register that holds it. -/
def isConstLvl (lay lam : Nat) : Bool := lam + 3 = heightL lay || lam + 2 = heightL lay

/-- Destination of the root hash of the top layer: FO. (Below the top layer no root is hashed; `0x120`
is where the node under the root goes, see `nodeDst`.) -/
def dstOf (lay : Nat) : Nat := if lay = 0 then 0x180 else 0x120

/-- Destination of the hash that produces the node of level `lam` on the path (`t` = its side): its slot
of the node buffer, except below the top layer for the node under the root, which goes straight into
the next layer's encoding block (`0x120`; the root's other child is copied next to it by the transition). -/
def nodeDst (lay lam t : Nat) : Nat :=
  if lay ≠ 0 ∧ lam + 1 = heightL lay then 0x120 + 16 * t else 0x360 + 16 * t

/-- The number of level runs of a block of chunk `ci`: below the top layer the last level (the root) has
none. -/
def lvlN (lay ci : Nat) : Nat := if lay = 0 then chBits lay ci else chBits lay ci - 1

/-- `x3` after the chunk dispatch into chunk `ci` (`[andi] slli; lui; add`). -/
def dispGp (lay ci : Nat) : E :=
  let idx : E := if nCh lay = 1 then .reg .x23
    else if ci = 0 then mkBin .and (.reg .x23) (cw 63)
    else mkBin .and (.reg .x23) (.c (BitVec.ofNat 64 (2 ^ 64 - 64)))
  let sh := if nCh lay = 2 ∧ ci = 1 then m4Sh lay ci + 2 - 6 else m4Sh lay ci + 2
  if nCh lay = 1 then mkBin .sll (.reg .x23) (cw sh)
  else mkAdd (mkBin .sll idx (cw sh)) (cw (m4Hi lay ci))

/-- The target of the chunk dispatch (`jalr zero, lo(gp)`). -/
def dispTgt (lay ci : Nat) : E :=
  mkBin .and (mkAdd (dispGp lay ci) (.c (BitVec.ofNat 64 (m4Doff lay ci) - BitVec.ofNat 64 (m4Hi lay ci))))
    (.c (~~~1#64))

/-- The value stored into NB+12 (NB = LB = 0x340) (the parent's heap index) by level `kk` of block `v`: the
constant 1 at the root, M4c constants (`sw R`) at depths 1 and 2 of the last chunk, else
`srli TP, E, lam + 1`. -/
def lvlNb (lay ci v kk : Nat) : E :=
  let lam := chB0 lay ci + kk
  if lam + 1 = heightL lay then cw 1
  else if kk + 1 < chBits lay ci ∧ (isConstLvl lay lam = true ∨ lay ≠ 0) then
    cw (if lay = 0 then 3 * 2 ^ (heightL lay - (lam + 1)) - 1 -
      (2 ^ (heightL lay - (lam + 1)) + v / 2 ^ (kk + 1))
      else 2 ^ (heightL lay - (lam + 1)) + v / 2 ^ (kk + 1))
  else .bin .srl (.reg .x23) (cw (lam + 1))

/-- The memory writes of a level: NB+12, then the sibling into the slot `1 - t`. -/
def lvlMem (lay lam t : Nat) (nb : E) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 0x348⟩, stW 0x348 nb),
   (⟨none, BitVec.ofNat 64 (0x370 - 16 * t + 8)⟩, ldE (sibAddr lay lam + 8)),
   (⟨none, BitVec.ofNat 64 (0x370 - 16 * t)⟩, ldE (sibAddr lay lam))] ++
  (if lam = 0 then [(⟨none, BitVec.ofNat 64 0x340⟩, .bin (.st .b (if lay < 4 then 2 else 1)) (ldE 0x340) (cw (if lay < 4 then lay else 3)))] else [])

/-- Known registers at the start of level `lam`. -/
def foldK (lay len : Nat) : List (Reg × Word) :=
  fk false 0x340 len ++ [(.x29, BitVec.ofNat 64 (5632 + 2688 * lay))]

def lvlK (lay lam : Nat) : List (Reg × Word) :=
  foldK lay (if lam = 0 then 704 else 64)

/-- The registers common to every level: the known ones (level 0 sets `a0, a1` for the node
hashes), `ra, gp` = the sibling (W1a: `sp` holds the triple mask). -/
def lvlRegs (lay lam : Nat) : RegFile :=
  let base := RegFile.withKnown (lvlK lay lam)
  let rf0 := if lam = 0 then base.set .x11 (cw 64) else base
  (rf0.set .x1 (ldE (sibAddr lay lam))).set .x3 (ldE (sibAddr lay lam + 8))

/-- Level `kk` of block `v` of chunk `ci` of layer `lay`, from after the `ecall` of its node
hash: load the sibling into the other slot, store the parent's heap index into NB+12, then the
next level's `li a2` (stopping at its `ecall`), or at the end of chunk 0 of layer 0 the dispatch
into chunk 1 (a jump to a symbolic target), or for the root `li a2, dst` and its `ecall`. -/
def lvlExp (lay ci v kk : Nat) : PRes :=
  let lam := chB0 lay ci + kk
  let mem := lvlMem lay lam (v / 2 ^ kk % 2) (lvlNb lay ci v kk)
  let hs := if lam = 0 then 2 else 0
  if lam + 1 = heightL lay then
    ⟨⟨(lvlRegs lay lam).set .x12 (cw (dstOf lay)), mem, []⟩, pcOf (m4Pc lay ci v kk + 8), true, 6, 6, [], none⟩
  else if kk + 1 < chBits lay ci then
    let rf := if isConstLvl lay lam then lvlRegs lay lam
      else if lay ≠ 0 then (lvlRegs lay lam).set .x25 (cw (2 ^ (heightL lay - (lam + 1)) + v / 2 ^ (kk + 1)))
      else (lvlRegs lay lam).set .x25 (.bin .srl (.reg .x23) (cw (lam + 1)))
    let n := hs + (if isConstLvl lay lam then 6 else 7)
    ⟨⟨rf.set .x12 (cw (nodeDst lay (lam + 1) (v / 2 ^ (kk + 1) % 2))), mem, []⟩,
      pcOf (m4Pc lay ci v (kk + 1) + 1), true, n, n, [], none⟩
  else
    ⟨⟨(lvlRegs lay lam).set .x25 (.bin .srl (.reg .x23) (cw (lam + 1))), mem, []⟩,
      0, false, hs + 7, hs + 7, [], some (mkBin .and (.reg .x16) (.c (~~~1#64)))⟩

/-- Direction list of a level run: stop at the dispatch jump at the end of a chunk. -/
def lvlDirs (lay ci kk : Nat) : List Dir :=
  if chB0 lay ci + kk + 1 = heightL lay then [] else if kk + 1 < chBits lay ci then [] else [.jmp]

/-- Known registers after a level run: the node-hash arguments (`a2` too unless the run stops at
the chunk dispatch). -/
def lvlPost (lay ci v kk : Nat) : List (Reg × Word) :=
  if chB0 lay ci + kk + 1 = heightL lay then foldK lay 64 ++ [(.x12, BitVec.ofNat 64 (dstOf lay))]
  else if kk + 1 < chBits lay ci then
    foldK lay 64 ++ [(.x12, BitVec.ofNat 64 (nodeDst lay (chB0 lay ci + kk + 1) (v / 2 ^ (kk + 1) % 2)))]
  else foldK lay 64

/-- Block entry: `li a2, 0x360 + 16 t` (`t = v % 2`), stopping at the `ecall`. -/
def entExp (lay ci v : Nat) : PRes :=
  ⟨⟨(RegFile.withKnown (lvlK lay (chB0 lay ci))).set .x12 (cw (0x360 + 16 * (v % 2))), [], []⟩,
    pcOf (m4Pc lay ci v 0 + 1), true, 1, 1, [], none⟩

def entPost (lay ci v : Nat) : List (Reg × Word) :=
  lvlK lay (chB0 lay ci) ++ [(.x12, BitVec.ofNat 64 (0x360 + 16 * (v % 2)))]

/-- The entry and all levels of block `v` of chunk `ci` of layer `lay`. -/
def blockCheck (lay ci v : Nat) : Bool :=
  okFold false (runAt (lvlK lay (chB0 lay ci)) [] (m4Pc lay ci v 0) []) (entExp lay ci v) (entPost lay ci v) &&
  (List.range (lvlN lay ci)).all fun kk =>
    okFold false (runAt (lvlK lay (chB0 lay ci + kk)) [] (m4Pc lay ci v kk + 2) (lvlDirs lay ci kk))
      (lvlExp lay ci v kk) (lvlPost lay ci v kk)

/-- Blocks `a .. a + n - 1` of chunk `ci` of layer `lay`. -/
def foldCheck (lay ci a n : Nat) : Bool := (List.range' a n).all (blockCheck lay ci)


/-- Full-index return slots for the top tree's shared six- and five-level blocks. -/
def topSlotBase : Nat := 7168
def topSlotPc (E : Nat) : Nat := topSlotBase + 4 * (2047 - E)

def topSlotEnterExp (E : Nat) : PRes :=
  ⟨⟨(RegFile.withKnown (foldK 0 704)).set .x16 (cw (0x1000 + 4 * (topSlotPc E + 1))), [], []⟩,
    pcOf (m4Pc 0 0 (E % 64) 0), false, 1, 1, [], none⟩
def topSlotReturnExp (E : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (foldK 0 64), [], []⟩,
    pcOf (m4Pc 0 1 (E / 64) 0), false, 1, 1, [], none⟩
def topSlotCheck (E : Nat) : Bool :=
  optBeq (runAt (foldK 0 704) [m4Pc 0 0 (E % 64) 0] (topSlotPc E) []) (topSlotEnterExp E) &&
  optBeq (runAt (foldK 0 64) [m4Pc 0 1 (E / 64) 0] (topSlotPc E + 1) []) (topSlotReturnExp E)

end SigGolfCandidate.Verify
