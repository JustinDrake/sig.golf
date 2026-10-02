import SigGolfCandidate.T3.Secc.CaseCNearTight
import SigGolfCandidate.T3.Secc.LargeCouplingCert
import SigGolfCandidate.T3.Secc.WotsSmall
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
namespace SigGolfCandidate.T3.Secc
open SigGolfCandidate.T3.Security
/-- **The T3 security theorem**: the small route (A's `Wots.small_route` on CC's `caseC_small_bound nearBound`) and
the large route (LR-34's `LargeCoupling.large_route_hlarge`), closed by `SeccClosing.securityP_of_routes`. -/
theorem t3_securityP : SigGolfCandidate.T3M.Final.SecurityP :=
  SeccClosing.securityP_of_routes (Wots.small_route (CaseC.caseC_small_bound CaseC.nearBound))
    LargeCoupling.large_route_hlarge

end SigGolfCandidate.T3.Secc
