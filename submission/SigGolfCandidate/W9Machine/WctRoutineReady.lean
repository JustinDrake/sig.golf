import SigGolfCandidate.W9Machine.WctPlanGood
import SigGolfCandidate.W9Machine.WctChainControl
import SigGolfCandidate.W9Machine.WctChainSplit

section

namespace W9Machine
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem chainPiece_steps_cycles (p : ChainPiece) : p.result.steps = p.result.cycles := by
  cases p with
  | mk pc words kind => cases kind <;> rfl
theorem planFuel_le_cycles (ps : List ChainPiece) : planFuel ps ≤ planCycles ps := by
  induction ps with
  | nil => exact Nat.le_refl 0
  | cons p ps ih =>
    simp only [planFuel, planCycles, ChainPiece.totalCycles, chainPiece_steps_cycles]
    split_ifs <;> omega
theorem planCycles_eq (r : ChainRoutine) : planCycles r.pieces = r.cycles := by
  unfold ChainRoutine.cycles
  induction r.pieces with
  | nil => rfl
  | cons p ps ih => simpa only [planCycles, List.map_cons, List.sum_cons, Nat.add_comm] using congrArg (· + p.totalCycles) ih
theorem ChainRoutine.checked_cycles (r : ChainRoutine) (h : r.checked = true) : r.cycles ≤ 84 := by
  simp only [checked, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2
theorem chainRoutine_good (r : ChainRoutine) (hr : r.checked = true)
    (s : MachineState) (post : MachineState → Prop) (hready : PlanReady r.pieces s post)
    (N C A : Nat) (Q : Prop) (K : MachineState → OracleComp HashSpec Obs)
    (hK : ∀ t, post t → GoodQFor Frozen.image t N C Q A (K t)) :
    GoodQFor Frozen.image s (N + 89) (C + 89) Q (A + 84)
      (cc (chainPlan r.pieces s) K) := by
  have hc := r.checked_cycles hr
  have hp := planCycles_eq r
  have hf := planFuel_le_cycles r.pieces
  exact (chainPlan_good r.pieces s post hready N C A Q K hK).mono
    (by omega) (by omega) (fun h => ⟨h, by omega⟩)
end W9Machine
end

section



namespace W9Machine.Chain
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
structure RoutineReady (rank : Fin 728) (r : ChainRoutine) : Prop where
  guard : planGuard r.pieces {} = true
  linked : PlanLinked r.pieces
  entry : r.pieces.head?.map ChainPiece.pc = some (chainEntries.getD rank.val 0)
  queries : planQueries r.pieces {} = expectedQueries (ClaudeWCT.WCT9.codeword rank)
  endpoints : ∀ t, t < 7 → ∀ word, word < 2 →
    (terminalTrace r.pieces {}).read (traceLeafSlot t + 8 * word) =
      expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word
  cycles : planCycles r.pieces ≤ 84
def terminalChecked (r : ChainRoutine) : Bool :=
  (planQueries r.pieces {} == expectedQueries r.digits) &&
    ((List.range 7).all fun t => (List.range 2).all fun word =>
      (terminalTrace r.pieces {}).read (traceLeafSlot t + 8 * word) ==
        expectedEndpoint r.digits t word)
end W9Machine.Chain
end
