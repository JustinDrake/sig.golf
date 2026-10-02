import SigGolfCandidate.T3.FullCache.Fields
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The tag of a chunk list. -/
def macTagOf (key : MacKey) (chunks : List Nat) : MacTag :=
  fun j => BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks) + macPadWord key j

theorem macTag_eq (key : MacKey) (data : HashInput) : macTag key data = macTagOf key (chunks32 data) := rfl

/-- The key with the low words of `key` whose tag on `chunks` is `tag`. -/
def retag (key : MacKey) (chunks : List Nat) (tag : MacTag) : MacKey :=
  mkMacKey (macLowWord key) fun j => tag j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)

theorem macLowWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macLowWord (retag key chunks tag) = macLowWord key := by
  funext j; exact macLowWord_mk _ _ j

theorem macKeyWord_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) (j : Fin 4) :
    macKeyWord (retag key chunks tag) j = macKeyWord key j := by
  rw [macKeyWord_eq, macKeyWord_eq, macLowWord_retag]

theorem macTagOf_retag (key : MacKey) (chunks : List Nat) (tag : MacTag) :
    macTagOf (retag key chunks tag) chunks = tag := by
  funext j
  unfold macTagOf
  rw [macKeyWord_retag]
  unfold retag
  rw [macPadWord_mk]
  exact add_sub_cancel _ _

theorem retag_macTagOf (key : MacKey) (chunks : List Nat) : retag key chunks (macTagOf key chunks) = key := by
  unfold retag
  have hp : (fun j => macTagOf key chunks j - BitVec.ofNat 64 (polyMac (macKeyWord key j) chunks)) =
      macPadWord key := by
    funext j; unfold macTagOf; exact add_sub_cancel_left _ _
  rw [hp, mkMacKey_words]

/-- A key with the low words of `h` retags to `h` at `h`'s own tag. -/
theorem retag_mk_eq (h : MacKey) (chunks : List Nat) (pads : MacTag) :
    retag (mkMacKey (macLowWord h) pads) chunks (macTagOf h chunks) = h := by
  have hl : macLowWord (mkMacKey (macLowWord h) pads) = macLowWord h := by
    funext j; exact macLowWord_mk _ _ j
  have hk : ∀ j, macKeyWord (mkMacKey (macLowWord h) pads) j = macKeyWord h j := by
    intro j; rw [macKeyWord_eq, macKeyWord_eq, hl]
  have := retag_macTagOf h chunks
  unfold retag at this ⊢
  rw [hl]
  simp only [hk]
  exact this

/-- **The law of a retagged key.** A uniform key is a uniform key whose pads are replaced so that its tag on
`chunks` is an independent uniform tag: the published tag is uniform and independent of the low words. -/
theorem evalSPMF_uniformSample_bind_retag [SampleableType MacTag] [SampleableType MacKey] (chunks : List Nat) :
    𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (retag key chunks tag)] = 𝒮[$ᵗ MacKey] := by
  classical
  refine evalSPMF_ext fun h => ?_
  rw [probOutput_uniformSample MacKey h, probOutput_bind_eq_sum_fintype]
  have hinner : ∀ tag : MacTag,
      Pr[= h | (do let key ← $ᵗ MacKey; pure (retag key chunks tag))]
        = (if tag = macTagOf h chunks then
            (Fintype.card MacTag : ℝ≥0∞) * (Fintype.card MacKey : ℝ≥0∞)⁻¹ else 0) := by
    intro tag
    rw [bind_pure_comp, probOutput_map_eq_sum_fintype_ite]
    simp only [probOutput_uniformSample MacKey]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((Finset.univ.filter fun key : MacKey => h = retag key chunks tag).card : ℝ≥0∞)
          = if tag = macTagOf h chunks then (Fintype.card MacTag : ℝ≥0∞) else 0 := by
      by_cases ht : tag = macTagOf h chunks
      · have hset : (Finset.univ.filter fun key : MacKey => h = retag key chunks tag)
            = Finset.univ.image (fun pads : MacTag => mkMacKey (macLowWord h) pads) := by
          ext key
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hk
            refine ⟨macPadWord key, ?_⟩
            have hl : macLowWord h = macLowWord key := by rw [hk, macLowWord_retag]
            rw [hl, mkMacKey_words]
          · rintro ⟨pads, rfl⟩
            rw [ht]
            exact (retag_mk_eq h chunks pads).symm
        rw [hset, Finset.card_image_of_injective _ (fun p q hpq => by
              funext j
              have := congrArg (fun k => macPadWord k j) hpq
              simpa only [macPadWord_mk] using this),
            Finset.card_univ, if_pos ht]
      · rw [if_neg ht, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro key - rfl
        exact ht (macTagOf_retag key chunks tag).symm
    rw [hcard, ite_mul, zero_mul]
  simp_rw [hinner, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (macTagOf h chunks), if_pos (Finset.mem_univ _),
      probOutput_uniformSample MacTag, ← mul_assoc,
      ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]


end SiggolfT3Mac4
