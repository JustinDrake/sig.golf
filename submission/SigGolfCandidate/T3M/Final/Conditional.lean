import SigGolfCandidate.T3M.Final.Discharge
import SigGolfCandidate.T3M.Final.SourceDischarge
import SigGolfCandidate.T3M.Final.Transfer

/-!
# The complete T3 machine certificate and its source security premise

`pending_holds` proves all nine machine fields. `sourceFacts_of_securityP` supplies all source fields from the
checked source closure and its security argument. `certificate_of_security` therefore yields the current
organizer certificate at `C = 9235` once supplied `T3.Secc.t3_securityP`, as done in `Solution.lean`.
The more general `certificate_of_remaining` interface is retained for explicit expansion refinements.
-/

namespace SigGolfCandidate.T3M.Final

/-- The full current-contract certificate from SEC's padded-game security and the two expand refinements. -/
theorem certificate_of_remaining (security : SecurityP) (expandRefines : ExpandRefines)
    (expandTerminates : ExpandTerminates) : SigGolf.Certificate submissionNew 9235 :=
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
theorem certificate_of_security (security : SecurityP) : SigGolf.Certificate submissionNew 9235 :=
  certificateNew_of pending_holds (sourceFacts_of_securityP security)

end SigGolfCandidate.T3M.Final
