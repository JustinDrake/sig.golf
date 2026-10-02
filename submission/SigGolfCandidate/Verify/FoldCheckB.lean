import SigGolfCandidate.Verify.FoldDefs
import SigGolfCandidate.Verify.FoldCheckA
set_option Elab.async false

/-! Kernel check of the Merkle shape blocks of layers 2..4 (one declaration per layer). -/

namespace SigGolfCandidate.Verify

theorem layFoldOk_2_0 : layFoldOk 2 0 = true := by decide +kernel
theorem layFoldOk_3_0 : layFoldOk 3 0 = true := by decide +kernel
theorem layFoldOk_4_0 : layFoldOk 4 0 = true := by decide +kernel

end SigGolfCandidate.Verify
