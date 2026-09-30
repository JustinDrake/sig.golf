import SigGolfCandidate.Transport.Execution
import VCVio.EvalDist.Expectation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Transport
open OracleComp OracleComp.EvalDist RiscvZkvm.Rv64

def honestResult (r : Legacy.HonestResult) : SigGolf.HonestResult :=
  ⟨r.success, fun p => r.costs (phase p), r.verificationCycles⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] program input output sizes layout submission Legacy.Input Legacy.Output
  SigGolf.Input SigGolf.Output

theorem honest_eq (s : Legacy.Submission) (h : s.Admissible)
    (sk : Legacy.SecretKey) (m : Legacy.Message) :
    honestResult <$> s.honest sk m = (submission s).honest sk m := by
  unfold Legacy.Submission.honest SigGolf.Submission.honest
  rw [← run_eq s h .keygen sk]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro kg
  simp only [runResult, output, Option.map_id]
  cases hk : kg.value with
  | none =>
    simp [hk, honestResult, Legacy.recordCost, Function.update]
    funext p
    cases p <;> rfl
  | some key =>
    rcases key with ⟨pk, cache⟩
    simp only [hk, Option.map_some, output]
    rw [← run_eq s h .sign (sk, cache, m)]
    simp only [map_bind, bind_map_left]
    apply bind_congr
    intro sign
    simp only [runResult, output, Option.map_id]
    cases hs : sign.value with
    | none =>
      simp [hs, honestResult, Legacy.recordCost, Function.update]
      funext p
      cases p <;> rfl
    | some sig =>
      simp only [hs, Option.map_some, output]
      rw [← run_eq s h .expand (m, pk, sig)]
      simp only [map_bind, bind_map_left]
      apply bind_congr
      intro expand
      simp only [runResult, output, Option.map_id]
      cases he : expand.value with
      | none =>
        simp [he, honestResult, Legacy.recordCost, Function.update]
        funext p
        cases p <;> rfl
      | some wit =>
        simp only [he, Option.map_some, output]
        rw [← run_eq s h .verify (m, pk, wit)]
        simp only [map_bind, bind_map_left]
        apply bind_congr
        intro verify
        simp [runResult, output, honestResult, Legacy.recordCost, Function.update,
          submission, sizes, Legacy.witnessCycles, SigGolf.witnessCharge]
        funext p
        cases p <;> rfl

theorem verificationCycles (s : Legacy.Submission) (h : s.Admissible) (C : Nat)
    (hb : s.VerificationBound C) : (submission s).VerificationCycles C := by
  intro hash sk m
  rw [← honest_eq s h, evalWithAnswerFn_map]
  exact hb hash sk m

theorem termination (s : Legacy.Submission) (h : s.Admissible)
    (ht : s.Terminates) : (submission s).Termination := by
  intro hash p x
  cases p <;>
    first
    | (rw [← run_eq s h .keygen x, evalWithAnswerFn_map]; exact (ht hash .keygen x).2)
    | (rw [← run_eq s h .sign x, evalWithAnswerFn_map]; exact (ht hash .sign x).2)
    | (rw [← run_eq s h .expand x, evalWithAnswerFn_map]; exact (ht hash .expand x).2)
    | (rw [← run_eq s h .verify x, evalWithAnswerFn_map]; exact (ht hash .verify x).2)

theorem allMessages_fold (s : Legacy.Submission) (h : s.Admissible) (sk : Legacy.SecretKey)
    (messages : List Legacy.Message) (initial : Legacy.HonestSummary) :
    Legacy.HonestSummary.allSucceed <$> messages.foldlM (fun summary message => do
      let result ← s.honest sk message
      pure (⟨summary.allSucceed && result.success,
        fun p => max (summary.maxCosts p) (result.costs p)⟩ : Legacy.HonestSummary)) initial =
    messages.foldlM (fun success message => do
      let result ← (submission s).honest sk message
      pure (success && result.success)) initial.allSucceed := by
  induction messages generalizing initial with
  | nil => rfl
  | cons message rest ih =>
    simp only [List.foldlM_cons, map_bind, ← honest_eq s h, bind_map_left, bind_assoc, pure_bind]
    apply bind_congr
    intro result
    simpa only [← honest_eq s h, bind_map_left, honestResult] using
      ih (⟨initial.allSucceed && result.success,
        fun p => max (initial.maxCosts p) (result.costs p)⟩ : Legacy.HonestSummary)

theorem everyMessage_eq (s : Legacy.Submission) (h : s.Admissible) (sk : Legacy.SecretKey) :
    Legacy.HonestSummary.allSucceed <$> s.allMessages sk = (submission s).everyMessageSucceeds sk := by
  unfold Legacy.Submission.allMessages SigGolf.Submission.everyMessageSucceeds
  rw [allMessages_fold s h]
  simp only [bind_pure, bind_pure_comp, List.forIn_yield_eq_foldlM]

theorem completeness (s : Legacy.Submission) (h : s.Admissible)
    (hc : s.Complete) : (submission s).Completeness := by
  intro sk
  rw [← everyMessage_eq s h]
  simpa [SigGolf.withRandomOracle, Legacy.withRandomOracle, probOutput_map,
    SigGolf.FAILURE, Legacy.FAILURE] using hc sk

theorem workload_eq (s : Legacy.Submission) (h : s.Admissible) (sk : Legacy.SecretKey) :
    honestResult <$> s.honestWorkload sk = (do
      let m ← ($ᵗ SigGolf.Message : ProbComp SigGolf.Message)
      SigGolf.withRandomOracle ((submission s).honest sk m)) := by
  simp [Legacy.Submission.honestWorkload, ← honest_eq s h,
    SigGolf.withRandomOracle, Legacy.withRandomOracle, map_bind]

theorem compressionBudgets (s : Legacy.Submission) (h : s.Admissible)
    (hb : s.CompressionBounds) : (submission s).CompressionBudgets := by
  intro sk p budget hp
  rw [← workload_eq s h]
  simp only [OracleComp.EvalDist.expectedValue_map]
  cases p <;> simp only [SigGolf.Program.budget, Option.some.injEq, reduceCtorEq] at hp
  all_goals subst budget
  all_goals
    solve
    | (convert hb sk .keygen (by simp [Legacy.Phase.budgeted]) using 1 <;>
        simp [honestResult, phase, Legacy.Phase.budget, Legacy.BUDGET_KEYGEN,
          SigGolf.BUDGET_KEYGEN, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])
    | (convert hb sk .sign (by simp [Legacy.Phase.budgeted]) using 1 <;>
        simp [honestResult, phase, Legacy.Phase.budget, Legacy.BUDGET_SIGN,
          SigGolf.BUDGET_SIGN, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])
    | (convert hb sk .expand (by simp [Legacy.Phase.budgeted]) using 1 <;>
        simp [honestResult, phase, Legacy.Phase.budget, Legacy.BUDGET_EXPAND,
          SigGolf.BUDGET_EXPAND, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])

end SigGolfCandidate.Transport
