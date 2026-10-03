import SigGolfCandidate.W9Machine.WctRuns

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def recoverEnds (sig : ClaudeWCT.WCT9.Signature) (index : Nat)
    (a : HashOutput) (k : Fin 9) : M (List Digest) :=
  (List.finRange 7).mapM fun i ↦
    let d := ClaudeWCT.WCT9.digit (ClaudeWCT.WCT9.rank a k) i
    ClaudeWCT.WCT9.chain index k.val (ClaudeWCT.WCT9.child a k).val i.val
      (3 - d) d ((sig.openings k).values i)
def RefinesPiece {α : Type} (L : Layout) (b : Budget) (pre : MachineState → Prop)
    (post : α → MachineState → Prop) (program : M α) : Prop :=
  ∀ (u : MachineState) (N C A : Nat) (Q : Prop)
    (K : α → OracleComp HashSpec Obs), pre u →
    (∀ x t, post x t → GoodQFor L.image t N C Q A (K x)) →
    GoodQFor L.image u (N + b.fuel) (C + b.allCycles) Q (A + b.acceptCycles)
      (ccM program K)
def ChainContract (L : Layout) (b : Budget) (sig : ClaudeWCT.WCT9.Signature)
    (index : Nat) (a : HashOutput) (k : Fin 9) (pre : MachineState → Prop)
    (post : List Digest → MachineState → Prop) : Prop :=
  RefinesPiece L b pre post (recoverEnds sig index a k)
end W9Machine
end

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def LeafContract (L : Layout) (b : Budget) (index : Nat) (k : Fin 9)
    (child : Fin 128) (ends : List Digest) (pre : MachineState → Prop)
    (post : Digest → MachineState → Prop) : Prop :=
  ends.length = 7 →
    RefinesPiece L b pre post (ClaudeWCT.WCT9.leafHash index k.val child.val ends)
end W9Machine
end

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def recoverPath (sig : ClaudeWCT.WCT9.Signature) (index : Nat) (a : HashOutput)
    (k : Fin 9) (root : Digest) : M Digest :=
  (List.finRange 7).foldlM (fun value level ↦ do
    let selected := ClaudeWCT.WCT9.child a k
    let other := (sig.openings k).path level
    let pair := if selected.val / 2 ^ level.val % 2 = 0 then
      (value, other) else (other, value)
    SigGolfCandidate.T3.nodeHash 11 k.val index
      (2 ^ (6 - level.val) + selected.val / 2 ^ (level.val + 1)) pair.1 pair.2) root
def MerkleContract (L : Layout) (b : Budget) (sig : ClaudeWCT.WCT9.Signature)
    (index : Nat) (a : HashOutput) (k : Fin 9) (root : Digest)
    (pre : MachineState → Prop) (post : Digest → MachineState → Prop) : Prop :=
  RefinesPiece L b pre post (recoverPath sig index a k root)
end W9Machine
end
