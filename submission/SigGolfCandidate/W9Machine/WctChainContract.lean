import SigGolfCandidate.W9Machine.WctPlanFrame
import SigGolfCandidate.W9Machine.WctChainSource
import SigGolfCandidate.W9Machine.WctRootRuns
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs

namespace W9Machine.Chain
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT.W9.Machine.Merkle
def base (k : Fin 9) : Nat := 2112 + 1024 * k.val
def table (k : Fin 9) : Nat := 0xfee600 + 512 * k.val
def program (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728) :
    M (List Digest) :=
  (List.finRange 7).mapM fun t =>
    let d := ClaudeWCT.WCT9.digit rank t
    ClaudeWCT.W9.T3M.wctChainP index k.val j.val t.val (3 - d) d
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).1
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).2
      (ClaudeWCT.W9.T3M.wreveal w k.val t.val d)
structure Pre (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728)
    (u : MachineState) : Prop where
  indexBound : index < 2 ^ 31
  pc : u.pc = pcOf (chainEntries.getD rank.val 0)
  baseReg : u.getReg .x8 = BitVec.ofNat 64 (base k)
  headerReg : u.getReg .x28 = BitVec.ofNat 64 (table k + 2048)
  route : u.getReg .x4 = BitVec.ofNat 64 (hdr1 index j.val)
  hashMode : u.getReg .x5 = 0
  stepOne : u.getReg .x6 = 1
  stepTwo : u.getReg .x7 = 2
  hashLen : u.getReg .x11 = 64
  childPC : u.getReg .x23 = pcOf (childBase j.val)
  returnPC : u.getReg .x1 = pcOf (rootPc k)
  indexReg : u.getReg .x22 = BitVec.ofNat 64 index
  nodeHeader : u.getReg .x27 = BitVec.ofNat 64 (w0n k.val index)
  heaps : ∀ h, 1 ≤ h → h ≤ 7 →
    u.getReg (heapReg h) = BitVec.ofNat 64 (index + 2 ^ 32 * h)
  headers : ∀ t, t < 7 → ∀ d, d < 3 →
    u.getMem (BitVec.ofNat 64 (table k + 64 * t + 8 * d)) =
      BitVec.ofNat 64 (hdr0 5 k.val index (d + 256 * t))
  leafHeader : u.getMem (BitVec.ofNat 64 (table k + 456)) =
    BitVec.ofNat 64 (hdr0 6 k.val index 0)
  witness : ∀ off, off < 1024 → off % 8 = 0 → OrigW w u (base k + off)
def writes (k : Fin 9) (A : Nat) : Prop := base k + 448 ≤ A ∧ A < base k + 1024
structure Post (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (u : MachineState) (ends : List Digest) (t : MachineState) : Prop where
  length : ends.length = 7
  child : ChildPre j.val (base k) k.val index (leafFields k.val index j.val ends)
    (ClaudeWCT.W9.T3M.wmpad w k.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val) t
  rootPad : DigAt t (base k + padO 6) (ClaudeWCT.W9.T3M.wmpad w k.val 6)
  rootSibling : DigAt t (base k + sibO 6 j.val) (ClaudeWCT.W9.T3M.wsib w k.val j.val 6)
  keep : ∀ r, r ∉ wctChainClobbers → t.getReg r = u.getReg r
  frame : Frame u t (writes k)
def Good (rank : Fin 728) : Prop :=
  ∀ (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : List Digest → OracleComp HashSpec Obs),
    Pre w index k j rank u →
    (∀ ends t, Post w index k j u ends t → GoodQFor Frozen.image t N C Q A (K ends)) →
    GoodQFor Frozen.image u (N + 89) (C + 89) Q (A + 89)
      (ccM (program w index k j rank) K)
def AllGood : Prop := ∀ rank : Fin 728, Good rank
end W9Machine.Chain
