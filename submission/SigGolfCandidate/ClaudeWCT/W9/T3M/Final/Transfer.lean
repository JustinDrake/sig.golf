import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Main
import SigGolfCandidate.Transfer.Statements
import SigGolfCandidate.Transfer.Security
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Transfer
open ClaudeWCT.W9.T3M (Images submission)
def submissionNew (I : Images) : SigGolf.Submission := currentOf (submission I)
theorem legacyOf_submissionNew (I : Images) : legacyOf (submissionNew I) = submission I :=
  legacyOf_currentOf (submission I)
theorem certificateNew_of {I : Images} (P : Pending I) (S : SourceFacts) :
    SigGolf.Certificate (submissionNew I) 7840 := by
  have hL : SigGolfCandidate.Legacy.Certificate (legacyOf (submissionNew I)) 7840 := by
    rw [legacyOf_submissionNew]
    exact certificate_of P S
  have hrun : RunAgrees (submissionNew I) := runAgrees_of_admissible (submissionNew I) hL.admissible
  exact
    { admission := admission_of_legacy (submissionNew I) hL.admissible
      completeness := completeness_of_legacy (submissionNew I) hrun hL.completeness
      compressionBudgets := compressionBudgets_of_legacy (submissionNew I) hrun hL.compressionBounds
      verificationCycles := verificationCycles_of_legacy (submissionNew I) hrun _ hL.verificationBound
      security := security_of_legacy (submissionNew I) hrun hL.security
      termination := termination_of_legacy (submissionNew I) hrun hL.termination }
end ClaudeWCT.W9.T3M.Final
