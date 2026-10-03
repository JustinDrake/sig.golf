import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Honest

namespace SphincsSecurity
open OracleComp
def payloadOf (input : HashInput) : HashInput := input.drop 32
theorem payloadOf_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : payloadOf (tweakableHashInput parameter domain payload) = payload := by
  have hlength : (tweakBytes domain ++ bytesLE 16 parameter).length = 32 := by
    simp [tweakBytes_length, bytesLE_length 16 parameter]
  simp only [payloadOf, tweakableHashInput]
  rw [← hlength, List.drop_left]
end SphincsSecurity
