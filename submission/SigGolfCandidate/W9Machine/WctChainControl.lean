import SigGolfCandidate.T3M.Verify.Mem
import SigGolfCandidate.W9Machine.WctPlanGuard
import SigGolfCandidate.W9Machine.WctPlanGood

namespace W9Machine
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def terminalTrace : List ChainPiece → ChainTrace → ChainTrace
  | [], tr => tr
  | p :: ps, tr => if p.kind = .leaf then tr else terminalTrace ps (tr.step p.kind)
def PlanLinked (ps : List ChainPiece) : Prop :=
  ∀ p ∈ ps, sliceChecked p.pc p.words = true ∧ p.checked = true
theorem chain_next_pc (p : ChainPiece) (s : MachineState) (ans : BitVec 256)
    (hl : p.kind ≠ .leaf)
    (hw : p.words.length = p.result.steps + if p.isHash then 1 else 0) :
    (if p.isHash then writeHash (p.result.toState s) ans else p.result.toState s).pc =
      pcOf p.nextPc := by
  cases p with
  | mk pc words kind =>
    cases kind with
    | head off dst chain digit =>
      simp only [ChainPiece.result, ChainPiece.isHash, headRHRel, if_true] at hw
      change (writeHash ((headRHRel .x8 _ _ pc chain digit).toState s) ans).pc = pcOf (pc + words.length)
      rw [writeHash_pc]
      change pcOf (pc + 4) + 4 = _
      rw [SigGolfCandidate.T3M.pcOf_add4]
      congr 1
      omega
    | rung digit dst =>
      cases dst <;>
        simp only [ChainPiece.result, ChainPiece.isHash, rungRRel, Option.map,
          Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true] at hw
      all_goals
        simp only [ChainPiece.isHash, if_true, writeHash_pc, ChainPiece.result,
          rungRRel, Option.map, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, if_false, if_true,
          Result.toState_pc, E.eval, ChainPiece.nextPc]
        rw [SigGolfCandidate.T3M.pcOf_add4]
        congr 1
        omega
    | copy off dst =>
      simp only [ChainPiece.result, ChainPiece.isHash, copyFHRel, Bool.false_eq_true, if_false, Nat.add_zero] at hw
      change pcOf (pc + 4) = pcOf (pc + words.length)
      rw [hw]
    | jump target => rfl
    | leaf => exact False.elim (hl rfl)
end W9Machine
