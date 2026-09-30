import SigGolfCandidate.Transport
import SigGolfCandidate.Bridge.Basic

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Transport
open OracleComp Bridge RiscvZkvm.Rv64

/-- The old instrumented execution counts exactly the queries seen by the new oracle counter. -/
theorem execute_count (i : Legacy.Riscv.Image) (n : Nat) (s : MachineState) (c : Nat) :
    countFrom (fun _ => 1) (Legacy.Riscv.execute n i s) c =
      (fun e => (e, c + e.hashCalls)) <$> Legacy.Riscv.execute n i s := by
  induction n generalizing s c with
  | zero => simp [Legacy.Riscv.execute, countFrom_pure]
  | succ n ih =>
    simp only [Legacy.Riscv.execute]
    cases hf : Legacy.Riscv.fetch i s with
    | none => simp [countFrom_pure]
    | some inst =>
      cases inst with
      | base inst =>
        cases inst <;> dsimp only
        all_goals try
          split <;> simp_all only [countFrom_pure, countFrom_map, ih, Functor.map_map, map_pure, Legacy.Riscv.Execution.charge, Nat.zero_add, Nat.add_zero] <;> rfl
        split
        · simp only [countFrom_bind, countFrom_query, bind_map_left, map_bind,
            countFrom_pure, map_pure, ih]
          congr 1
          funext a
          simp [bind_map_left, Functor.map_map, Legacy.Riscv.Execution.charge, Nat.add_assoc]
        · split <;> simp [countFrom_pure]
      | word op rd r1 r2 =>
        simp [Legacy.Riscv.ordinaryStep, countFrom_map, ih, Functor.map_map,
          Legacy.Riscv.Execution.charge]
      | sraiw rd r sh =>
        simp [Legacy.Riscv.ordinaryStep, countFrom_map, ih, Functor.map_map,
          Legacy.Riscv.Execution.charge]

theorem run_count (s : Legacy.Submission) (p : Legacy.Phase)
    (x : Legacy.Input s.sizes p) (c : Nat) :
    countFrom (fun _ => 1) (s.run p x) c =
      (fun r => (r, c + r.hashCalls)) <$> s.run p x := by
  unfold Legacy.Submission.run
  cases hs : Legacy.initialState s p x with
  | none => simp [countFrom_pure]
  | some st =>
    simp only [countFrom_bind, execute_count, bind_map_left, countFrom_pure, map_bind, map_pure]

theorem native_run_count (s : Legacy.Submission) (h : s.Admissible) (p : Legacy.Phase)
    (x : Legacy.Input s.sizes p) (c : Nat) :
    countFrom (fun _ => 1) ((submission s).run (program p) (input _ p x)) c =
      (fun r => (runResult s.sizes p r, c + r.hashCalls)) <$> s.run p x := by
  rw [← run_eq s h, countFrom_map, run_count, Functor.map_map]

end SigGolfCandidate.Transport
