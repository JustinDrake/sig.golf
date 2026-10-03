import SigGolfCandidate.T3M.Sign.Main
import SigGolfCandidate.T3M.Expand.Main

/-! Kernel audit of the exact 5616-byte combined-image producer roots. -/
#print axioms SigGolfCandidate.T3M.Sign.sign_refines
#print axioms SigGolfCandidate.T3M.Sign.sign_terminates
#print axioms SigGolfCandidate.T3M.Expand.expand_refines_holds
#print axioms SigGolfCandidate.T3M.Expand.expand_terminates_holds
#print axioms SigGolfCandidate.T3M.Search.digestSearch_spec
#print axioms SigGolfCandidate.T3M.Search.counterSearch_spec
