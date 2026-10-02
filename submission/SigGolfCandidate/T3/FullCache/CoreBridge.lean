import SigGolfCandidate.T3.FullCache.TagCodec
import SigGolfCandidate.T3.FullCache.PayloadSeparation

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Byte-exact view of the MAC cache used by the concrete source. -/
def toCoreCache (cache : SiggolfT3Mac4.Cache) : SigGolfCandidate.T3.Cache :=
  ⟨encodeTag cache.tag,cache.region⟩

def fromCoreCache (cache : SigGolfCandidate.T3.Cache) : SiggolfT3Mac4.Cache :=
  ⟨cache.region,decodeTag cache.tag⟩

theorem fromCoreCache_toCoreCache (cache : SiggolfT3Mac4.Cache) :
    fromCoreCache (toCoreCache cache)=cache := by
  cases cache
  simp only [fromCoreCache,toCoreCache,decodeTag_encodeTag]

theorem toCoreCache_fromCoreCache (cache : SigGolfCandidate.T3.Cache) :
    toCoreCache (fromCoreCache cache)=cache := by
  cases cache
  simp only [fromCoreCache,toCoreCache,encodeTag_decodeTag]

def coreCacheEquiv : SiggolfT3Mac4.Cache ≃ SigGolfCandidate.T3.Cache where
  toFun := toCoreCache
  invFun := fromCoreCache
  left_inv := fromCoreCache_toCoreCache
  right_inv := toCoreCache_fromCoreCache

def corePayload (request : SiggolfT3Mac4.Request T3Message) : T3M (Option T3Signature) :=
  SigGolfCandidate.T3.signPayload (toCoreCache request.cache) request.message

theorem corePayload_nonMac (request : SiggolfT3Mac4.Request T3Message) :
    AllQueriesSatisfy (corePayload request) NonMac :=
  Payload.signPayload_allowed _ _

theorem privateMacKey_eq_core : privateMacKey=SigGolfCandidate.T3.privateMacKey := rfl

/-- The actual HashOutput-tag signer is exactly the four-word source signer,
for every supplied byte-representable cache and on both authentication branches. -/
theorem core_sign_eq (cache : SiggolfT3Mac4.Cache) (message : T3Message) :
    SigGolfCandidate.T3.sign (toCoreCache cache) message = sign corePayload ⟨message,cache⟩ := by
  unfold SigGolfCandidate.T3.sign SigGolfCandidate.T3.privateMac sign privateMac
  rw [privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,toCoreCache,tagRegion,regionBytes]
  apply congrArg (fun k => SigGolfCandidate.T3.privateMacKey >>= k)
  funext key
  by_cases h : macTag key (List.ofFn cache.region)=cache.tag
  · simp only [h,ne_eq,not_true_eq_false,ite_false,ite_true,corePayload,toCoreCache]
  · have he : encodeTag (macTag key (List.ofFn cache.region)) ≠ encodeTag cache.tag :=
      fun hx => h (encodeTag_injective hx)
    rw [if_pos he, if_neg h]

end SiggolfT3Mac4.Source
