import SigGolfCandidate.T3M.Images.Keygen

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy
structure Images where
  sign : Riscv.Image
  expand : Riscv.Image
  verify : Riscv.Image
def submission (I : Images) : Submission where
  sizes := ⟨5456, 24264, 131072⟩
  layout := ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩
  image
    | .keygen => SigGolfCandidate.T3M.Images.keygenImage
    | .sign => I.sign
    | .expand => I.expand
    | .verify => I.verify
variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5456, 24264, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩ := rfl
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl
end ClaudeWCT.W9.T3M
