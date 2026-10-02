import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation
import SigGolfCandidate.T3.FullCache.Forgery
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- The complete8190-node cache region, with16bytes per node. -/
abbrev Region := Fin 131040 → UInt8

def regionBytes (region : Region) : HashInput := List.ofFn region

def tagRegion (key : MacKey) (region : Region) : MacTag := macTag key (regionBytes region)

def tagBytes (tag : MacTag) : HashInput := (List.ofFn tag).flatMap (bytesLE 8)

theorem regionBytes_length (region : Region) : (regionBytes region).length = 131040 := by
  simp only [regionBytes, List.length_ofFn]

theorem regionBytes_injective : Function.Injective regionBytes := by
  intro a b h
  unfold regionBytes at h
  exact List.ofFn_injective h

theorem regionChunks_length (region : Region) : (chunks32 (regionBytes region)).length = 32760 := by
  rw [chunks32_length, regionBytes_length]

theorem regionChunks_injective : Function.Injective (fun region : Region => chunks32 (regionBytes region)) := by
  intro a b h
  apply regionBytes_injective
  exact chunks32_injective _ _ ((regionBytes_length a).trans (regionBytes_length b).symm)
    (by rw [regionBytes_length]; decide) h

theorem tagBytes_length (tag : MacTag) : (tagBytes tag).length = 32 := by
  simp [tagBytes, List.length_flatMap, bytesLE_length]

theorem tagBytes_injective : Function.Injective tagBytes := by
  intro a b h
  exact flatMap_bytesLE_ofFn_injective h

theorem fullCache_length (key : MacKey) (region : Region) :
    (regionBytes region ++ tagBytes (tagRegion key region)).length = 131072 := by
  rw [List.length_append, regionBytes_length, tagBytes_length]

/-- Actual full-region forged tag probability for arbitrary different regions and chosen tags. -/
theorem probEvent_region_bad_le [SampleableType MacKey] (published candidate : Region)
    (hne : candidate ≠ published) (tag tag' : MacTag) :
    Pr[fun key : MacKey => tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate = tag' |
      $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  exact probEvent_retag_bad_le (chunks32 (regionBytes published)) (chunks32 (regionBytes candidate))
    ((regionChunks_length published).trans (regionChunks_length candidate).symm)
    (fun h => hne (regionChunks_injective h).symm)
    (chunks32_lt_macPrime _) (chunks32_lt_macPrime _)
    (by rw [regionChunks_length]; decide) tag tag'

/-- The same bound on the actual32-byte serialized tag. -/
theorem probEvent_region_bad_bytes_le [SampleableType MacKey] (published candidate : Region)
    (hne : candidate ≠ published) (tag tag' : MacTag) :
    Pr[fun key : MacKey => tagBytes (tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate) = tagBytes tag' |
      $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  have he : (fun key : MacKey => tagBytes (tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate) = tagBytes tag') =
      (fun key : MacKey => tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate = tag') := by
    funext key
    exact propext ⟨fun h => tagBytes_injective h, fun h => congrArg tagBytes h⟩
  rw [he]
  exact probEvent_region_bad_le published candidate hne tag tag'

end SiggolfT3Mac4
