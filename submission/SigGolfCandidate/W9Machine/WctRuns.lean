import SigGolfCandidate.W9Machine.WctLayout

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
open RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M)
def wctRun (L : Layout) (p fuel : Nat) : Option Result :=
  symRun {} (L.image.code.drop p) (pcOf p) fuel
def PieceChecked (L : Layout) (p fuel : Nat) (r : Result) : Prop :=
  wctRun L p fuel = some r
def PieceSound (L : Layout) (p : Nat) (r : Result) : Prop :=
  ∀ s : MachineState, s.pc = pcOf p → (∀ o ∈ r.st.obl, o.holds s) →
    Steps L.image s r.steps r.cycles (r.toState s)
end W9Machine
