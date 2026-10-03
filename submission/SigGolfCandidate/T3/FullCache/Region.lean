import SigGolfCandidate.T3.FullCache.Retag
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation

section

namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option exponentiation.threshold 1024
set_option backward.isDefEq.respectTransparency false
theorem mem_badWords_of_tag_eq (xs ys : List Nat) (key : MacKey) (tag tag' : MacTag) (j : Fin 4)
    (h : macTagOf (retag key xs tag) ys j = tag' j) :
    macLowWord key j ∈ badWords xs ys (tagResidue (tag' j - tag j)) := by
  unfold macTagOf at h
  rw [macKeyWord_retag] at h
  unfold retag at h
  rw [macPadWord_mk] at h
  have hres := residue_of_tag_eq _ _ (polyMac_lt_pow _ xs) (polyMac_lt_pow _ ys) _ _ h
  unfold badWords badKeys
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, ← macKeyWord_eq]
  refine ⟨Finset.mem_univ _, ?_, hres⟩
  rw [macKeyWord_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 61)
theorem card_retag_bad_le (xs ys : List Nat) (hlen : xs.length = ys.length) (hne : xs ≠ ys)
    (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime) (tag tag' : MacTag) :
    Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'}
      ≤ (8 * (xs.length + 1)) ^ 4 * Fintype.card MacTag := by
  let f : {key : MacKey // macTagOf (retag key xs tag) ys = tag'} →
      ((j : Fin 4) → {w : BitVec 64 // w ∈ badWords xs ys (tagResidue (tag' j - tag j))}) × MacTag :=
    fun key => (fun j => ⟨macLowWord key.1 j,
      mem_badWords_of_tag_eq xs ys key.1 tag tag' j (congrFun key.2 j)⟩, macPadWord key.1)
  have hf : Function.Injective f := by
    intro k1 k2 h
    apply Subtype.ext
    have h1 : macLowWord k1.1 = macLowWord k2.1 := by
      funext j
      exact congrArg Subtype.val (congrFun (congrArg Prod.fst h) j)
    have h2 : macPadWord k1.1 = macPadWord k2.1 := congrArg Prod.snd h
    rw [← mkMacKey_words k1.1, ← mkMacKey_words k2.1, h1, h2]
  refine (Fintype.card_le_of_injective f hf).trans ?_
  rw [Fintype.card_prod, Fintype.card_pi]
  refine Nat.mul_le_mul_right _ ?_
  simp only [Fintype.card_coe]
  refine (Finset.prod_le_prod' fun j _ => card_badWords_le xs ys hlen hne hx hy _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
theorem card_tagWord : Fintype.card (BitVec 64) = 2 ^ 64 := Fintype.card_bitVec 64
theorem card_hashOutput : Fintype.card HashOutput = 2 ^ 256 := Fintype.card_bitVec hashOutputBits
theorem card_macTag : Fintype.card MacTag = (2 ^ 64) ^ 4 := by
  rw [Fintype.card_fun, card_tagWord, Fintype.card_fin]
theorem card_macKey : Fintype.card MacKey = (2 ^ 256) ^ 2 := by
  rw [Fintype.card_fun, card_hashOutput, Fintype.card_fin]
theorem probEvent_retag_bad_le [SampleableType MacKey] (xs ys : List Nat) (hlen : xs.length = ys.length)
    (hne : xs ≠ ys) (hx : ∀ x ∈ xs, x < macPrime) (hy : ∀ y ∈ ys, y < macPrime)
    (hL : xs.length + 1 ≤ 2 ^ 15) (tag tag' : MacTag) :
    Pr[fun key : MacKey => macTagOf (retag key xs tag) ys = tag' | $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, card_macKey]
  have hc := card_retag_bad_le xs ys hlen hne hx hy tag tag'
  rw [card_macTag] at hc
  have hn : Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} ≤ 2 ^ 328 := by
    refine hc.trans ?_
    calc (8 * (xs.length + 1)) ^ 4 * (2 ^ 64) ^ 4 ≤ (8 * 2 ^ 15) ^ 4 * (2 ^ 64) ^ 4 :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left 8 hL) 4)
      _ = 2 ^ 328 := by norm_num
  have hcast : ((Fintype.card {key : MacKey // macTagOf (retag key xs tag) ys = tag'} : ℕ) : ℝ≥0∞)
      ≤ (2 ^ 328 : ℝ≥0∞) := by exact_mod_cast hn
  refine ENNReal.div_le_of_le_mul (hcast.trans (le_of_eq ?_))
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
    show ((2 : ENNReal) ^ 256) ^ 2 = (2 : ENNReal) ^ 184 * 2 ^ 328 by
      rw [← pow_mul, ← pow_add],
    ← mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by finiteness), one_mul]
end SiggolfT3Mac4
end

section


namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
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
theorem probEvent_region_bad_le [SampleableType MacKey] (published candidate : Region)
    (hne : candidate ≠ published) (tag tag' : MacTag) :
    Pr[fun key : MacKey => tagRegion (retag key (chunks32 (regionBytes published)) tag) candidate = tag' |
      $ᵗ MacKey] ≤ (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  exact probEvent_retag_bad_le (chunks32 (regionBytes published)) (chunks32 (regionBytes candidate))
    ((regionChunks_length published).trans (regionChunks_length candidate).symm)
    (fun h => hne (regionChunks_injective h).symm)
    (chunks32_lt_macPrime _) (chunks32_lt_macPrime _)
    (by rw [regionChunks_length]; decide) tag tag'
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
end
