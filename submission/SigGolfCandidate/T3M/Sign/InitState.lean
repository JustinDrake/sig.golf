import SigGolfCandidate.T3M.Sign.Init
import SigGolfCandidate.T3M.Submission

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem dataBase_sign : dataBase (submission.image .sign) = SIGN_DATA := by
  unfold dataBase; rw [show (submission.image .sign).data.length = 69632 from Images.signData_length]; rfl
set_option maxRecDepth 100000 in
theorem initialState_sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (sinit sk cache m) := by
  have hv := submission_sign_valid
  unfold initialState
  rw [if_pos hv, dataBase_sign]
  simp only [submission_sign, Images.signImage,
    inputBuffers, List.foldl_cons, List.foldl_nil]
  change some _ = some _
  congr 1
end SigGolfCandidate.T3M.Sign
