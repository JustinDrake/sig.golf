import SigGolfCandidate.W9Machine.WctChainAllGood
import SigGolfCandidate.W9Machine.WctSourceEquiv
import SigGolfCandidate.W9Machine.WctEndpoints
import SigGolfCandidate.W9Fin.Fts
import SigGolfCandidate.W9Machine.WctImageIdentity
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.Final.Assembly
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearFinal
import SigGolfCandidate.ClaudeWCT.W9.New.G6.PairFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert
import SigGolfCandidate.T3M.Sign.WctFinal

section



namespace W9Machine.Chain
theorem allGood : AllGood Frozen.layout :=
  allGood_of V3SourceEquiv.sourceEquivalent V3Endpoints.endpointsCorrect
end W9Machine.Chain
end

section



namespace W9Fin
theorem verify_final_of (I : ClaudeWCT.W9.T3M.Images)
    (hI : I.verify = SigGolfCandidate.T3M.Images.verifyImage)
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I :=
  verify_inputs'_of I hI hbridge W9Machine.Chain.allGood
theorem verify_final
    (hbridge : W9Machine.Frozen.image = SigGolfCandidate.T3M.Images.verifyImage) :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs' hbridge W9Machine.Chain.allGood
theorem verify_final_closed :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_final W9Machine.Frozen.image_eq
end W9Fin
#print axioms W9Fin.verify_final_of
#print axioms W9Fin.verify_final
#print axioms W9Fin.verify_final_closed
end

section







namespace SigGolfCandidate.Packaging
open SigGolfCandidate.T3M.Sign.Boundary (finalImages)
theorem certificate_ready :
    SigGolf.Certificate (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission) 7716 :=
  ClaudeWCT.W9.Final.certificate_of_pending (I := finalImages)
    { large_route := ClaudeWCT.W9.T3.Security.LargeCoupling.large_route_hlarge
      pair_bound := ClaudeWCT.W9.T3.Security.WPair.pair_guess_bound
      near_bound := ClaudeWCT.W9.T3.Security.CaseC.nearBound
      admissible := SigGolfCandidate.T3M.submission_admissible
      verify_refines := W9Fin.verify_final_closed.1
      verify_terminates := W9Fin.verify_final_closed.2.1
      verify_accept_cycles := W9Fin.verify_final_closed.2.2
      sign_refines := ClaudeWCT.W9.Machine.ExpandLink.sign_pending_v3.1
      sign_terminates := ClaudeWCT.W9.Machine.ExpandLink.sign_pending_v3.2
      expand_refines := ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v3.1
      expand_terminates := ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v3.2 }
end SigGolfCandidate.Packaging
end
