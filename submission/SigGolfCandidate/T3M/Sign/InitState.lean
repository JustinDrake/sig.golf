import SigGolfCandidate.T3M.Sign.Init
import SigGolfCandidate.T3M.Submission

/-!
# The sign loader

`initialState_sign` : the organizer loads `sinit sk cache m` (kept out of `Sign/Init` so that only
`Sign/Main` imports `T3M.Submission`, i.e. the verify image).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

set_option maxRecDepth 100000 in
theorem initialState_sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (sinit sk cache m) := by
  have hv := submission_sign_valid
  unfold initialState
  rw [if_pos hv]
  simp only [submission_sign, Images.signImage, Images.signData, MachineState.writeBytesAsWords_nil,
    inputBuffers, List.foldl_cons, List.foldl_nil]
  rfl

end SigGolfCandidate.T3M.Sign
