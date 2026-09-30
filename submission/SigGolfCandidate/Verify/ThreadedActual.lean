import SigGolfCandidate.Verify.ThreadedBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SigGolfCandidate.Verify.Threaded

theorem image_eq : image = Verify.image := by
  change (⟨chunks.flatten, []⟩ : Legacy.Riscv.Image) = ⟨Images.verifyCode, Images.verifyData⟩
  rw [Verify.verifyCode_eq]
  rfl

theorem look_global_ok : LookOK Verify.image look := by
  rw [← image_eq]
  exact look_ok

#print axioms image_eq
#print axioms look_global_ok
end SigGolfCandidate.Verify.Threaded
