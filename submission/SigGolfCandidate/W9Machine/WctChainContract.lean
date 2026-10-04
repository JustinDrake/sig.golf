import SigGolfCandidate.W9Machine.WctChildContract

set_option autoImplicit false
namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
abbrev base := coordinateBase
abbrev table := headerTable
abbrev program := V3.chainProgram
structure Pre (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  pc : u.pc = pcOf (L.chainWord rank)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (base k)
  headerReg : u.getReg .x28 = BitVec.ofNat 64 (table k + 2048)
  prefixReg : u.getReg .x31 = BitVec.ofNat 64 (V3.chainPrefix index k.val j.val)
  route : u.getReg .x4 = BitVec.ofNat 64 (index + 2 ^ 32 * j.val)
  hashMode : u.getReg .x5 = 0
  stepOne : u.getReg .x7 = 1
  stepTwo : u.getReg .x13 = 2
  hashLen : u.getReg .x11 = 64
  childPC : u.getReg .x23 = pcOf (L.childWord j)
  returnPC : u.getReg .x1 = pcOf (L.returnWord k)
  indexReg : u.getReg .x22 = BitVec.ofNat 64 index
  nodeHeader : u.getReg .x27 = BitVec.ofNat 64 (V3.nodeLow k.val index)
  forestPointer : u.getReg .x9 = BitVec.ofNat 64 (pairAddress k)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (Child.heapReg h) = BitVec.ofNat 64 h
  leafHeader : u.getMem (BitVec.ofNat 64 (table k + 456)) =
    (SigGolfCandidate.T3.header 6 k.val index 0 j.val).extractLsb' 0 64
  witness : ∀ off, off < 1024 → off % 8 = 0 →
    u.getMem (BitVec.ofNat 64 (base k + off)) =
      w.extractLsb' (8 * (V3.regionOffset k.val + off)) 64
def writes (k : Fin 9) (A : Nat) : Prop := base k + 448 ≤ A ∧ A < base k + 1024
def clobbers : List Reg := [.x3, .x10, .x11, .x12, .x14, .x25]
structure Post (L : Layout) (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (u : MachineState) (ends : List Digest) (t : MachineState) : Prop where
  length : ends.length = 7
  child : Child.Pre L w index k j ends t
  keep : ∀ r, r ∉ clobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k)
def Good (L : Layout) (rank : Fin 728) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre L w index k j rank u →
    (∀ ends t, Post L w index k j u ends t → GoodQFor L.image t N C Q A (K ends)) →
    GoodQFor L.image u (N + 89) (C + 89) Q (A + 84)
      (ccM (program w index k j rank) K)
def AllGood (L : Layout) : Prop := ∀ rank : Fin 728, Good L rank
end W9Machine.Chain
