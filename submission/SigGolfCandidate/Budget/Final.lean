import SigGolfCandidate.Budget.Expand
import SigGolfCandidate.Keygen.Main
import SigGolfCandidate.Sign.Main
import SigGolfCandidate.Expand.Main

/-!
# Budget: the compression bounds of the submission

Keygen and sign are discharged by their bytecode refinements (`Keygen.keygen_run_counts`,
`Sign.sign_refines`); the expand bound is pathwise (`Budget/Expand`, `ExpandBelowSign`: on every
honest path the expand run makes at most as many compressions as the sign run), discharged by
the three refinements including `Expand.expand_refines_counts`: `submission_compressionBounds`.
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp

theorem submission_keygenRefinesCounts (sk : SecretKey) :
    RefinesCounts submission .keygen sk (keygenRef sk) :=
  ⟨some, Keygen.keygen_run_counts sk⟩

set_option maxRecDepth 100000 in
theorem submission_signRefinesCounts (sk : SecretKey) (cache : Cache) (m : Message) :
    RefinesCounts submission .sign (sk, cache, m) (signRef sk cache m) :=
  ⟨id, (Sign.sign_refines sk cache m).trans (id_map _).symm⟩

/-- The pathwise expand bound of the submission. -/
theorem submission_expandBelowSign : ExpandBelowSign submission :=
  expandBelowSign_submission Keygen.keygen_run_counts Sign.sign_refines Expand.expand_refines_counts

/-- **Compression bounds** of `SigGolfCandidate.submission` (the organizer's
`Submission.CompressionBounds`), with no hypotheses. -/
theorem submission_compressionBounds : submission.CompressionBounds :=
  submission_compressionBounds_of_counts' submission_keygenRefinesCounts submission_signRefinesCounts
    submission_expandBelowSign

end SigGolfCandidate.Budget
