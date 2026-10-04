import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Keygen.Leaf
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Layer selections admissible digestSearch counterSearch decode
  attemptLimit counterLimit chainCount target Selection)
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((selections N).getD c ⟨0, []⟩).bucket * 128 + ((selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (s : MachineState) (rho : Digest) (m : Message) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def DsPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => Failed t
  | some (_, N), t => t.pc = pcOf 172 ∧ t.getReg .x5 = 0 ∧ admissible (selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCost : Nat := attemptLimit * 700 + 100
def DigestSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (rho : Digest) (m : Message), DsPre s rho m →
    TBSim image sk s dsCost (digestSearch rho m 0 attemptLimit) (DsPost s)
def csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (X : Nat) : Prop :=
  X = ENC + 16 ∨ X = ENC + 24 ∨ X = ENC + 32 ∨ (EOUT ≤ X ∧ X < EOUT + 32) ∨ (DIGITS ≤ X ∧ X < DIGITS + 64)
structure CsPre (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : (Digest × BitVec 96 × Digest)) (ret : Nat) : Prop where
  pc : s.pc = pcOf 646
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (Keygen.n4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  rR : DigAt s (ENC + 48) msg.2.2
  hpad : msg.2.1 = 0
  msg : DigAt s ENC msg.1
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  table : Search.TableOK s
def CsPost (s : MachineState) (lay : Layer) (ret : Nat) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => Failed t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, decode lay v = some ds) ∧
      (∀ i < chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ target lay
def csCost (lay : Layer) : Nat := counterLimit * (if lay = 0 then 205 else 160) + 2000
def CounterSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : (Digest × BitVec 96 × Digest)) (ret : Nat),
    CsPre s lay tree leaf msg ret →
      TBSim image sk s (csCost lay) (counterSearch lay tree leaf msg 0 counterLimit) (CsPost s lay ret)
structure Kernels (sk : BitVec 256) : Prop where
  digest : DigestSearchSpec sk
  counter : CounterSearchSpec sk
end SigGolfCandidate.T3M.Sign
