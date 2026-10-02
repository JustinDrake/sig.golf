import SigGolfCandidate.T3.FullCache.Fields
import SigGolfCandidate.T3.FullCache.Region

namespace SiggolfT3Mac4
open SphincsSecurity
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem decodeTag_encodeTag (tag : MacTag) : decodeTag (encodeTag tag) = tag := by
  funext i
  obtain ⟨h0,h1,h2,h3⟩ := extract_answerOfWords (tag 0) (tag 1) (tag 2) (tag 3)
  fin_cases i <;> simp only [decodeTag,encodeTag] <;> assumption

theorem encodeTag_decodeTag (tag : HashOutput) : encodeTag (decodeTag tag) = tag :=
  answerOfWords_extract tag

def tagEquiv : MacTag ≃ HashOutput where
  toFun := encodeTag
  invFun := decodeTag
  left_inv := decodeTag_encodeTag
  right_inv := encodeTag_decodeTag

theorem encodeTag_injective : Function.Injective encodeTag := tagEquiv.injective

end SiggolfT3Mac4
