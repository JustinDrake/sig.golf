import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Keygen.Leaf

/-!
# Sign: the interface to stream E's search kernels

The sign image shares two pieces with expand (stream E, `T3M/Search/*`, `KernAt image 543`,
`DsAt image 153 543`):

* the digest search `ds_loop` (words 153..171) with `select_ok` (546..645): from word 153 with
  `I = 0`, `rho` at `DIG` and the message at `DIG + 32`, the machine refines Core's
  `digestSearch rho m 0 attemptLimit`; on success it is at `ds_done` (172) with the digest output
  `N` at `NBUF`, the selection rows at `SEL` and `admissible (selections N)`; on exhaustion it
  halts through `fail` (`Failed`);
* `counter_search` (646..1012): from its entry with the layer registers and the message digest at
  `ENC`, the machine refines `counterSearch lay tree leaf msg 0 counterLimit`; on success it returns
  with the digits as bytes at `DIGITS`; on exhaustion it halts through `fail`.

`DigestSearchSpec sk` and `CounterSearchSpec sk` are exactly what the sign proof consumes; the
costs `dsCost`, `csCost` are all-oracle bounds (E measured exact per-trial maxima 666 resp.
158 / 201 cycles). `Kernels sk` bundles both. Until E's lemmas are merged, the sign theorems take
`Kernels` as a hypothesis.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Layer selections admissible digestSearch counterSearch decode
  attemptLimit counterLimit chainCount target Selection)

/-! ## Selection rows and stored outputs -/

/-- Entry `j` of selection row `c`: `256 bucket + x_j` (the sorted leaves of coordinate `c`). -/
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((selections N).getD c ⟨0, []⟩).bucket * 128 + ((selections N).getD c ⟨0, []⟩).leaves.getD j 0

/-- The selection rows of `N` at `SEL` (row `c` at `SEL + 24 c`). -/
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)

/-- A 256-bit value stored as four little-endian doublewords at `A`. -/
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64

/-! ## The digest search (words 153..171 and `select_ok`) -/

/-- Registers the digest search may change. -/
def dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]

/-- Doublewords the digest search may change: the counter header, `NBUF`, the selection rows. -/
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)

/-- Entry of the digest search (word 153 = `ds_loop`, `I = 0`). -/
structure DsPre (s : MachineState) (rho : Digest) (m : Message) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64

/-- Exit of the digest search: `fail` on exhaustion, else `ds_done` (172) with `N`. -/
def DsPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => Failed t
  | some (_, N), t => t.pc = pcOf 172 ∧ t.getReg .x5 = 0 ∧ admissible (selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW

/-- All-oracle cycle bound of the digest search (≤ 700 cycles per trial). -/
def dsCost : Nat := attemptLimit * 700 + 100

/-- **Interface (E)**: the digest search refines `digestSearch rho m 0 attemptLimit`. -/
def DigestSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (rho : Digest) (m : Message), DsPre s rho m →
    TBSim image sk s dsCost (digestSearch rho m 0 attemptLimit) (DsPost s)

/-! ## `counter_search` (words 646..1012) -/

/-- Registers `counter_search` may change. -/
def csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]

/-- Doublewords `counter_search` may change: the encoding header and counter, `EOUT`, the digits. -/
def CsW (X : Nat) : Prop :=
  X = ENC + 16 ∨ X = ENC + 24 ∨ X = ENC + 32 ∨ (EOUT ≤ X ∧ X < EOUT + 32) ∨ (DIGITS ≤ X ∧ X < DIGITS + 64)

/-- Entry of `counter_search` (word 646), called with `ra = ret`. -/
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

/-- Exit of `counter_search`: `fail` on exhaustion, else back at `ret` with the digits at `DIGITS`
(and `s9` = the data-digit total, at most the target: layer 0 passes it on as `build_leaf`'s unused
root slot). -/
def CsPost (s : MachineState) (lay : Layer) (ret : Nat) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => Failed t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, decode lay v = some ds) ∧
      (∀ i < chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ target lay

/-- All-oracle cycle bound of `counter_search` (≤ 160 / 205 cycles per lower / top trial). -/
def csCost (lay : Layer) : Nat := counterLimit * (if lay = 0 then 205 else 160) + 2000

/-- **Interface (E)**: `counter_search` refines `counterSearch lay tree leaf msg 0 counterLimit`. -/
def CounterSearchSpec (sk : BitVec 256) : Prop :=
  ∀ (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : (Digest × BitVec 96 × Digest)) (ret : Nat),
    CsPre s lay tree leaf msg ret →
      TBSim image sk s (csCost lay) (counterSearch lay tree leaf msg 0 counterLimit) (CsPost s lay ret)

/-- Both kernel interfaces. -/
structure Kernels (sk : BitVec 256) : Prop where
  digest : DigestSearchSpec sk
  counter : CounterSearchSpec sk

end SigGolfCandidate.T3M.Sign
