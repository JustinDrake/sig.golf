import SigGolfCandidate.W9Machine.WctV3Source

set_option autoImplicit false
namespace W9Machine.Child
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
def heapReg : Nat → Reg
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | 7 => .x30
  | _ => .x0
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  length : ends.length = 7
  pc : u.pc = pcOf (L.childWord j)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (coordinateBase k)
  hashMode : u.getReg .x5 = 0
  hashInput : u.getReg .x10 = BitVec.ofNat 64 (coordinateBase k + 880)
  hashLen : u.getReg .x11 = 128
  nodeHeader : u.getReg .x27 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  indexReg : u.getReg .x22 = BitVec.ofNat 64 index
  forestPointer : u.getReg .x9 = BitVec.ofNat 64 (pairAddress k)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (coordinateBase k + 880 + 16 * i)
    (V3.leafFields k.val index j.val ends i)
  padAt : ∀ l, l < 6 → DigAt u (coordinateBase k + V3.blockOffset l + 32)
    (V3.nodePad w k.val l)
  sibAt : ∀ l, l < 7 → DigAt u (coordinateBase k + V3.siblingOffset j.val l)
    (V3.sibling w k.val j.val l)
def writes (k : Fin 9) (A : Nat) : Prop :=
  (coordinateBase k + 64 ≤ A ∧ A < coordinateBase k + 464) ∨
    (pairAddress k ≤ A ∧ A < pairAddress k + 48)
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14]
structure Post (L : Layout) (k : Fin 9) (u : MachineState)
    (pair : V3.RootPair) (t : MachineState) : Prop where
  pc : t.pc = pcOf (L.returnWord k)
  hashLen : t.getReg .x11 = 64
  left : DigAt t (pairAddress k) pair.left
  right : DigAt t (pairAddress k + 16) pair.right
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k)
def Good (L : Layout) (b : Budget) (j : Fin 128) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (ends : List Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : V3.RootPair → OracleComp HashSpec Obs),
    Pre L w index k j ends u →
    (∀ pair t, Post L k u pair t → GoodQFor L.image t N C Q A (K pair)) →
    GoodQFor L.image u (N + b.fuel) (C + b.allCycles) Q (A + b.acceptCycles)
      (ccM (V3.childProgram w index k j ends) K)
end W9Machine.Child
