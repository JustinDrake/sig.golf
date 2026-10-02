import SigGolfCandidate.T3M.Final.Main
import SigGolfCandidate.Transfer.Statements
import SigGolfCandidate.Transfer.Security

/-!
# The T3 certificate under the current contract

`submissionNew` is the T3 submission as a value of the current contract's `SigGolf.Submission` (the same sizes,
layout and four images, `Transfer.currentOf`); its legacy view is exactly `T3M.submission`, whose legacy certificate is
`certificate_of`. The statements transfer through the unchanged, scheme-independent `Transfer.Statements` and
`Transfer.Security` (five-layer `Transfer/Final`, rewritten for T3).
-/

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.Transfer

/-- The T3 submission under the current contract. -/
def submissionNew : SigGolf.Submission := currentOf submission

theorem legacyOf_submissionNew : legacyOf submissionNew = submission :=
  legacyOf_currentOf submission

/-- **The T3 certificate under the current contract**, from the machine and source statements. -/
theorem certificateNew_of (P : Pending) (S : SourceFacts) : SigGolf.Certificate submissionNew 9148 := by
  have hL : Legacy.Certificate (legacyOf submissionNew) 9148 := by
    rw [legacyOf_submissionNew]
    exact certificate_of P S
  have hrun : RunAgrees submissionNew := runAgrees_of_admissible submissionNew hL.admissible
  exact
    { admission := admission_of_legacy submissionNew hL.admissible
      completeness := completeness_of_legacy submissionNew hrun hL.completeness
      compressionBudgets := compressionBudgets_of_legacy submissionNew hrun hL.compressionBounds
      verificationCycles := verificationCycles_of_legacy submissionNew hrun _ hL.verificationBound
      security := security_of_legacy submissionNew hrun hL.security
      termination := termination_of_legacy submissionNew hrun hL.termination }

end SigGolfCandidate.T3M.Final
