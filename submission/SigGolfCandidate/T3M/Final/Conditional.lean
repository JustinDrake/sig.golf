import SigGolfCandidate.T3M.Final.Discharge
import SigGolfCandidate.T3M.Final.SourceDischarge
import SigGolfCandidate.T3M.Final.Transfer

/-!
# The T3 certificate, conditional on exactly what is not yet proved: SEC's padded-game security

Seven of `Pending`'s nine machine fields are proved (`Final/Discharge`: keygen ×2, sign ×2, verify ×3) and every
`SourceFacts` field except padded-game security comes from the checked source closure (`Final/SourceDischarge`).
So the organizer's certificate for the T3 submission at `C = 9202` needs only these three hypotheses: SEC's
`SecurityP` and stream E's two expand statements. When they are proved this becomes an unconditional
`SigGolf.Certificate submissionNew 9202`.
-/

namespace SigGolfCandidate.T3M.Final

/-- The full current-contract certificate from SEC's padded-game security and the two expand refinements. -/
theorem certificate_of_remaining (security : SecurityP) (expandRefines : ExpandRefines)
    (expandTerminates : ExpandTerminates) : SigGolf.Certificate submissionNew 9202 :=
  certificateNew_of
    { keygen_run_counts := keygen_run_counts_holds
      keygen_runWith := keygen_runWith_holds
      sign_refines := sign_refines_holds
      sign_terminates := sign_terminates_holds
      expand_refines := expandRefines
      expand_terminates := expandTerminates
      verify_refines := verify_refines_holds
      verify_terminates := verify_terminates_holds
      verify_accept_cycles := verify_accept_cycles_holds }
    (sourceFacts_of_securityP security)

/-- **The T3 certificate given only SEC's padded-game security**: every machine statement is proved (`pending_holds`)
and every other source fact comes from the checked closure. -/
theorem certificate_of_security (security : SecurityP) : SigGolf.Certificate submissionNew 9202 :=
  certificateNew_of pending_holds (sourceFacts_of_securityP security)

end SigGolfCandidate.T3M.Final
