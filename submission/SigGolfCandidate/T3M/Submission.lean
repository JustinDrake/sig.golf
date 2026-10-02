import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Images.Sign
import SigGolfCandidate.T3M.Images.Expand
import SigGolfCandidate.T3M.Images.Verify

/-!
# The T3 submission (four frozen images) and its static admission

Sizes `S = 5776`, `W = 25240`, `K = 32768` and the shared layout of `t3m/images/set.txt` (message
`0x40`, secret key `0x80`, public key `0xA0`, cache `0x9000`, signature `0x7000`, witness `0x800`);
the images are the generated modules `T3M/Images/*` (frozen `.code` files, SHA-256 checked by
`t3m/lean/gen_images.py`).

Admission is proved image by image, as in the five-layer `Submission.lean`: the code list is
rewritten to its chunks (`delta` inside an equation, so no equation lemma evaluates the list),
`List.length_append` splits the length, and the kernel only counts each 256-word chunk; the layout
half reads only the data section (empty, except the verify image's 96 bytes, T3K).
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy

/-- The T3 submission. -/
def submission : Submission where
  sizes := ⟨5776, 25240, 32768⟩
  layout := ⟨0x40, 0x80, 0xA0, 0x9000, 0x7000, 0x800⟩
  image
    | .keygen => Images.keygenImage
    | .sign => Images.signImage
    | .expand => Images.expandImage
    | .verify => Images.verifyImage

@[simp] theorem submission_sizes : submission.sizes = ⟨5776, 25240, 32768⟩ := rfl
@[simp] theorem submission_layout : submission.layout = ⟨0x40, 0x80, 0xA0, 0x9000, 0x7000, 0x800⟩ := rfl
@[simp] theorem submission_keygen : submission.image .keygen = Images.keygenImage := rfl
@[simp] theorem submission_sign : submission.image .sign = Images.signImage := rfl
@[simp] theorem submission_expand : submission.image .expand = Images.expandImage := rfl
@[simp] theorem submission_verify : submission.image .verify = Images.verifyImage := rfl

/-- Proves `(submission.image phase).Valid submission.sizes submission.layout` for an image whose
code list is `code`, a concatenation of chunks. -/
local macro "image_valid " code:ident : tactic => `(tactic| (
  have hcode : $code = $code := rfl
  conv at hcode => rhs; delta $code:ident
  rw [Riscv.Image.Valid]
  refine ⟨?_, by decide +kernel⟩
  rw [Riscv.Image.byteSize, show Riscv.Image.code _ = $code from rfl, hcode]
  try simp only [List.length_append]
  decide +kernel))

theorem submission_keygen_valid :
    (submission.image .keygen).Valid submission.sizes submission.layout := by
  image_valid Images.keygenCode

theorem submission_sign_valid :
    (submission.image .sign).Valid submission.sizes submission.layout := by
  image_valid Images.signCode

theorem submission_expand_valid :
    (submission.image .expand).Valid submission.sizes submission.layout := by
  image_valid Images.expandCode

set_option maxRecDepth 200000 in
theorem submission_verify_valid :
    (submission.image .verify).Valid submission.sizes submission.layout := by
  image_valid Images.verifyCode

/-- **Static admission**: sizes, image-size limits, aligned nonoverlapping buffers. -/
theorem submission_admissible : submission.Admissible := by
  refine ⟨by unfold Sizes.Valid; decide, ?_⟩
  intro phase
  cases phase
  · exact submission_keygen_valid
  · exact submission_sign_valid
  · exact submission_expand_valid
  · exact submission_verify_valid

end SigGolfCandidate.T3M
