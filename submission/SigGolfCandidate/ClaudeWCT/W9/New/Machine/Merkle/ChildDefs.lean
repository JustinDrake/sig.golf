import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3M.Verify.Exec
import SigGolfCandidate.T3M.Verify.Words
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildData

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def GoodQIm (im : Image) (s : MachineState) (N C : Nat) (Q : Prop) (A : Nat)
    (X : OracleComp HashSpec Obs) : Prop :=
  ∀ F, N ≤ F → obs <$> Riscv.execute F im s = X ∧
    ∀ hash : Hash, (evalWithAnswerFn hash (Riscv.execute F im s)).exit ≠ .unfinished ∧
      (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ C ∧
      ((evalWithAnswerFn hash (Riscv.execute F im s)).exit = .success →
        Q ∧ (evalWithAnswerFn hash (Riscv.execute F im s)).cycles ≤ A)
def RefinesIm {α : Type} (im : Image) (fuel allCycles acceptCycles : Nat) (pre : MachineState → Prop)
    (post : α → MachineState → Prop) (program : M α) : Prop :=
  ∀ (u : MachineState) (N C A : Nat) (Q : Prop) (K : α → OracleComp HashSpec Obs), pre u →
    (∀ x t, post x t → GoodQIm im t N C Q A (K x)) →
    GoodQIm im u (N + fuel) (C + allCycles) Q (A + acceptCycles) (ccM program K)
def childWords (j : Nat) : List (BitVec 32) := childBlocks.getD j []
def childRegion : List (BitVec 32) := childBlocks.flatten
def childBase (j : Nat) : Nat := 210432 + 64 * j
def ChildCodeAt (im : Image) (j : Nat) : Prop :=
  ∀ i w, (childWords j)[i]? = some w → im.code[childBase j + i]? = some w
def ChildRegionAt (im : Image) : Prop := childRegion <+: im.code.drop 210432
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def leafO : Nat := 880
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
def w0n (k index : Nat) : Nat := hdr0 11 k index 0
def heapReg (h : Nat) : Reg :=
  match h with
  | 1 => .x9 | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def heapRegN (h : Nat) : Nat := [0,9,13,19,20,21,26,30].getD h 30
def encI (rd rs1 imm : Nat) : BitVec 32 := BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
def encS (f3 rs2 off rs1 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (off / 32 * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + off % 32 * 2 ^ 7 + 0x23)
def lvlTmpl (j l : Nat) : List (BitVec 32) :=
  [encI 10 8 (blkO l), encS 3 27 16 10] ++
    (if l ≤ 3 then [encS 2 22 24 10, encI 3 0 (heapOf l j), encS 2 3 28 10]
     else [encS 3 (heapRegN (heapOf l j)) 24 10]) ++
    (if l < 6 then [encI 12 8 (curO (l + 1) j), 0x00000073] else [0x00008067])
def childTmpl (j : Nat) : List (BitVec 32) :=
  [encI 12 8 (curO 0 j), 0x00000073, encI 11 0 64] ++ (List.range 7).flatMap (lvlTmpl j) ++
    List.replicate 19 0x00000013
def ChildTemplate : Prop := childBlocks.length = 128 ∧ ∀ j, j < 128 → childWords j = childTmpl j
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevelP (k index j : Nat) (pads sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  nodeHashP 11 k index (heapOf l j) pair.1 (pads l) pair.2
def childProg (k index j : Nat) (leaf pads sibs : Nat → Digest) : M Digest := do
  let v ← shortHash (leafBytes leaf)
  (List.range 6).foldlM (childLevelP k index j pads sibs) v
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def childWrites (j : Nat) : List Nat := (List.range 7).flatMap (stageW j)
structure ChildPre (j B k index : Nat) (leaf pads sibs : Nat → Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (childBase j)
  base8 : B % 8 = 0
  baseHi : B + 1024 ≤ MEMORY_BYTES
  t0 : u.getReg .x5 = 0
  s0 : u.getReg .x8 = BitVec.ofNat 64 B
  a0 : u.getReg .x10 = BitVec.ofNat 64 (B + leafO)
  a1 : u.getReg .x11 = BitVec.ofNat 64 128
  w0 : u.getReg .x27 = BitVec.ofNat 64 (w0n k index)
  s6 : u.getReg .x22 = BitVec.ofNat 64 index
  heaps : ∀ h, 1 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 (index + 2 ^ 32 * h)
  leafAt : ∀ i, i < 8 → DigAt u (B + leafO + 16 * i) (leaf i)
  padAt : ∀ l, l < 6 → DigAt u (B + padO l) (pads l)
  sibAt : ∀ l, l < 6 → DigAt u (B + sibO l j) (sibs l)
structure ChildPost (j B k index : Nat) (u : MachineState) (v : Digest) (t : MachineState) : Prop where
  pc : t.pc = u.getReg .x1 &&& ~~~1#64
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r
  x3 : t.getReg .x3 = BitVec.ofNat 64 (heapOf 3 j)
  a0 : t.getReg .x10 = BitVec.ofNat 64 B
  a1 : t.getReg .x11 = BitVec.ofNat 64 64
  a2 : t.getReg .x12 = BitVec.ofNat 64 (B + curO 6 j)
  node : DigAt t (B + curO 6 j) v
  hw0 : t.getMem (BitVec.ofNat 64 (B + 16)) = BitVec.ofNat 64 (w0n k index)
  hw1 : t.getMem (BitVec.ofNat 64 (B + 24)) = BitVec.ofNat 64 (hdr1 index 1)
  frame : Frame u t (fun A => ∃ off ∈ childWrites j, A = B + off)
def ChildGood (im : Image) (j : Nat) : Prop :=
  ∀ (B k index : Nat) (leaf pads sibs : Nat → Digest) (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : Digest → OracleComp HashSpec Obs),
    index < 2 ^ 32 → ChildPre j B k index leaf pads sibs u →
    (∀ v t, ChildPost j B k index u v t → GoodQIm im t N C Q A (K v)) →
    GoodQIm im u (N + 45) (C + 102) Q (A + 102) (ccM (childProg k index j leaf pads sibs) K)
def ChildRefines (im : Image) (j : Nat) : Prop :=
  ∀ (B k index : Nat) (leaf pads sibs : Nat → Digest) (P : MachineState → Prop),
    index < 2 ^ 32 → (∀ u, P u → ChildPre j B k index leaf pads sibs u) →
    RefinesIm im 45 102 102 P (fun v t => ∃ u, P u ∧ ChildPost j B k index u v t)
      (childProg k index j leaf pads sibs)
def leafFields (k index j : Nat) (ends : List Digest) (i : Nat) : Digest :=
  if i = 0 then ends.getD 0 0 else if i = 1 then ClaudeWCT.WCT9.wctHeader 6 k index 0 j else ends.getD (i - 1) 0
def sixLevels (k index j : Nat) (path : Nat → Digest) (root : Digest) : M Digest :=
  (List.range 6).foldlM (fun value l =>
    let other := path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    SigGolfCandidate.T3.nodeHash 11 k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) root
def ChildCanon : Prop :=
  ∀ (k index j : Nat) (ends : List Digest) (path : Nat → Digest), ends.length = 7 →
    childProg k index j (leafFields k index j ends) (fun _ => 0) path =
      (ClaudeWCT.WCT9.leafHash index k j ends >>= sixLevels k index j path)
def finPath (path : Fin 7 → Digest) (l : Nat) : Digest := if h : l < 7 then path ⟨l, h⟩ else 0
def PathSplit : Prop :=
  ∀ (k : Fin 9) (index j : Nat) (path : Fin 7 → Digest) (root : Digest), j < 128 →
    (List.finRange 7).foldlM (fun value level ↦ do
      let other := path level
      let pair := if j / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
      SigGolfCandidate.T3.nodeHash 11 k.val index
        (2 ^ (6 - level.val) + j / 2 ^ (level.val + 1)) pair.1 pair.2) root =
    (sixLevels k.val index j (finPath path) root >>= fun value =>
      let other := path 6
      let pair := if j / 2 ^ 6 % 2 = 0 then (value, other) else (other, value)
      SigGolfCandidate.T3.nodeHash 11 k.val index 1 pair.1 pair.2)
def rootIn (k index j : Nat) (v pad sib : Digest) : List UInt8 :=
  let pair := if bitAt j 6 = 0 then (v, sib) else (sib, v)
  blk4 pair.1 (header 11 k index 0 1) pad pair.2
def RootInput : Prop :=
  ∀ (j B k index : Nat) (u t t' : MachineState) (v pad sib : Digest),
    j < 128 → index < 2 ^ 32 → B % 8 = 0 → B + 1024 ≤ MEMORY_BYTES → ChildPost j B k index u v t →
    DigAt u (B + padO 6) pad → DigAt u (B + sibO 6 j) sib →
    (∀ A, t'.getMem A = t.getMem A) → t'.getReg .x10 = BitVec.ofNat 64 B →
    t'.getReg .x11 = BitVec.ofNat 64 64 →
    hashInput t' = toQ (pad64 (rootIn k index j v pad sib))
def ChildRefinesCanon (im : Image) (j : Nat) : Prop :=
  ∀ (B k index : Nat) (ends : List Digest) (path : Nat → Digest) (P : MachineState → Prop),
    ends.length = 7 → index < 2 ^ 32 →
    (∀ u, P u → ChildPre j B k index (leafFields k index j ends) (fun _ => 0) path u) →
    RefinesIm im 45 102 102 P (fun v t => ∃ u, P u ∧ ChildPost j B k index u v t)
      (ClaudeWCT.WCT9.leafHash index k j ends >>= sixLevels k index j path)
def AllChildren (im : Image) : Prop :=
  ChildRegionAt im → ∀ j, j < 128 → ChildGood im j ∧ ChildRefines im j ∧ ChildRefinesCanon im j
end ClaudeWCT.W9.Machine.Merkle
