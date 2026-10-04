import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Transfer
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Discharge
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SourceDischarge

namespace ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3M (Images submission)
structure MachineFacts (I : Images) : Prop where
  admissible : (submission I).Admissible
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
theorem pending_of_machine {I : Images} (M : MachineFacts I) : Pending I where
  admissible := M.admissible
  keygen_run_counts := keygen_run_counts_holds I M.admissible
  keygen_runWith := keygen_runWith_holds I M.admissible
  sign_refines := M.sign_refines
  sign_terminates := M.sign_terminates
  expand_refines := M.expand_refines
  expand_terminates := M.expand_terminates
  verify_refines := M.verify_refines
  verify_terminates := M.verify_terminates
  verify_accept_cycles := M.verify_accept_cycles
theorem certificate_of_security {I : Images} (security : SecurityP) (M : MachineFacts I) :
    SigGolf.Certificate (submissionNew I) 7701 :=
  certificateNew_of (pending_of_machine M) (sourceFacts_of_securityP security)
end ClaudeWCT.W9.T3M.Final
