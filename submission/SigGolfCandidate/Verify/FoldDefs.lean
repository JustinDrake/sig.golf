import SigGolfCandidate.Verify.FoldRuns

namespace SigGolfCandidate.Verify

/-- The shape blocks of chunk `ci` of layer `lay` (all `2 ^ bits` blocks). -/
def layFoldOk (lay ci : Nat) : Bool := foldCheck lay ci 0 (2 ^ chBits lay ci)

end SigGolfCandidate.Verify
