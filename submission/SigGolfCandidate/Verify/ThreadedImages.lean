import SigGolfCandidate.Verify.Code

/-! The threaded checks use the actual submitted verifier image. -/
namespace SigGolfCandidate.Verify.Threaded

def chunks : List (List (BitVec 32)) := Verify.vChunks
def look (n : Nat) : Option (BitVec 32) := Verify.vlook n

end SigGolfCandidate.Verify.Threaded
