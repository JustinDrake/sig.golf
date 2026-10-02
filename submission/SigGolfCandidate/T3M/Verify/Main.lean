import SigGolfCandidate.T3M.Verify.Top
import SigGolfCandidate.T3M.Final.Pending

/-! # V3: the verify fields of F's `Pending`

* **`verify_refines : Final.VerifyRefines`** — for every message, public key and witness bytes, the organizer's run
  of the frozen verify image has the value `if verifyP then some () else none` and the hash calls of
  `countCalls (mrealize 0 (verifyP m pk w))`, as an equality of oracle computations;
* **`verify_terminates : Final.VerifyTerminates`** — under every fixed oracle the run finishes within
  `cycleBoundAll = 15404 < CYCLE_LIMIT` cycles;
* **`verify_accept_cycles : Final.VerifyAcceptCycles`** — accepting runs take at most `cycleBound = 9137 =
  verifyCycleBound` cycles. -/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify

theorem init_exists_verify (input : Legacy.Input submission.sizes .verify) :
    ∃ s, initialState submission .verify input = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩

theorem fuelBound_le : fuelBound ≤ CYCLE_LIMIT := by rw [fuelBound_eq]; unfold CYCLE_LIMIT; norm_num

/-- **Verify refinement** (`Pending.verify_refines`). -/
theorem verify_refines : Final.VerifyRefines := by
  intro m pk w
  obtain ⟨s, hs⟩ := init_exists_verify (m, pk, w)
  have hg := (verify_good (m, pk, w) s hs CYCLE_LIMIT fuelBound_le).1
  rw [ccM_Kb] at hg
  rw [run_eq submission .verify _ s hs, submission_verify, Functor.map_map]
  change _ = (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
  rw [← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT Verify.image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl

/-- **Verify termination** (`Pending.verify_terminates`), with the bound `cycleBoundAll = 15397`. -/
theorem verify_terminates : Final.VerifyTerminates := by
  intro hash m pk w
  obtain ⟨s, hs⟩ := init_exists_verify (m, pk, w)
  have hg := (verify_good (m, pk, w) s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq submission hash .verify (m, pk, w) s hs, submission_verify]
  simp only [toRunResult]
  refine ⟨?_, lt_of_le_of_lt hg.2.1 (by rw [cycleBoundAll_eq]; unfold CYCLE_LIMIT; norm_num)⟩
  simpa using hg.1

/-- **Accepting verify cycles** (`Pending.verify_accept_cycles`): at most `verifyCycleBound = 9137`. -/
theorem verify_accept_cycles : Final.VerifyAcceptCycles := by
  intro hash m pk w h
  obtain ⟨s, hs⟩ := init_exists_verify (m, pk, w)
  have hg := (verify_good (m, pk, w) s hs CYCLE_LIMIT fuelBound_le).2 hash
  rw [runWith_eq submission hash .verify (m, pk, w) s hs, submission_verify] at h ⊢
  simp only [toRunResult] at h ⊢
  have hsucc : (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT Images.verifyImage s)).exit = .success := by
    by_contra hne
    rw [if_neg hne] at h
    cases h
  have := (hg.2.2 hsucc).2
  rw [cycleBound_eq] at this
  exact this

end SigGolfCandidate.T3M
