import SigGolfCandidate.Legacy.Security

section

namespace SigGolfCandidate.Legacy
open OracleComp
def Submission.Admissible (submission : Submission) : Prop :=
  submission.sizes.Valid ∧ ∀ phase, (submission.image phase).Valid submission.sizes submission.layout
def Submission.Terminates (submission : Submission) : Prop :=
  ∀ (hash : Hash) (phase : Phase) (input : Input submission.sizes phase),
    let result := submission.runWith hash phase input
    result.finished = true ∧ result.cycles < CYCLE_LIMIT
def Submission.Complete (submission : Submission) : Prop :=
  ∀ secretKey, 1 - FAILURE ≤ Pr[fun summary => summary.allSucceed = true |
    withRandomOracle (submission.allMessages secretKey)]
def Submission.CompressionBounds (submission : Submission) : Prop :=
  ∀ secretKey phase, phase ∈ Phase.budgeted →
    OracleComp.EvalDist.expectedValue (submission.honestWorkload secretKey)
      (fun result => ENNReal.ofReal (Real.rpow 2
        ((result.costs phase : ℝ) / (phase.budget : ℝ)))) ≤ 2
def Submission.VerificationBound (submission : Submission) (C : Nat) : Prop :=
  ∀ (hash : Hash) secretKey message,
    let result := evalWithAnswerFn hash (submission.honest secretKey message)
    result.success = true → result.verificationCycles ≤ C
structure Certificate (submission : Submission) (C : Nat) : Prop where
  admissible : submission.Admissible
  termination : submission.Terminates
  completeness : submission.Complete
  compressionBounds : submission.CompressionBounds
  security : submission.Secure
  verificationBound : submission.VerificationBound C
end SigGolfCandidate.Legacy
end

section

end
