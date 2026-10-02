import SigGolfCandidate.T3.FullCache.Retag
namespace SiggolfT3Mac4
set_option autoImplicit false
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

abbrev LowKeys := Fin 4 → BitVec 61
abbrev UnusedBits := Fin 4 → BitVec 3
abbrev Components := LowKeys × (MacTag × UnusedBits)

def joinLow (key : BitVec 61) (unused : BitVec 3) : BitVec 64 :=
  BitVec.ofNat 64 (key.toNat + 2 ^ 61 * unused.toNat)

theorem joinLow_low (key : BitVec 61) (unused : BitVec 3) :
    (joinLow key unused).extractLsb' 0 61 = key := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hk := key.isLt; have hu := unused.isLt
  omega

theorem joinLow_high (key : BitVec 61) (unused : BitVec 3) :
    (joinLow key unused).extractLsb' 61 3 = unused := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hk := key.isLt; have hu := unused.isLt
  omega

theorem joinLow_parts (word : BitVec 64) :
    joinLow (word.extractLsb' 0 61) (word.extractLsb' 61 3) = word := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinLow, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hw := word.isLt
  omega

def components (key : MacKey) : Components :=
  (fun j => (macLowWord key j).extractLsb' 0 61,
   macPadWord key, fun j => (macLowWord key j).extractLsb' 61 3)

def ofComponents (c : Components) : MacKey :=
  mkMacKey (fun j => joinLow (c.1 j) (c.2.2 j)) c.2.1

theorem ofComponents_components (key : MacKey) : ofComponents (components key) = key := by
  simp only [ofComponents, components, joinLow_parts]
  exact mkMacKey_words key

theorem components_ofComponents (c : Components) : components (ofComponents c) = c := by
  apply Prod.ext
  · funext j
    simp only [components, ofComponents, macLowWord_mk, joinLow_low]
  · apply Prod.ext
    · funext j
      simp only [components, ofComponents, macPadWord_mk]
    · funext j
      simp only [components, ofComponents, macLowWord_mk, joinLow_high]

def componentsEquiv : MacKey ≃ Components where
  toFun := components
  invFun := ofComponents
  left_inv := ofComponents_components
  right_inv := components_ofComponents

/-- Exact joint uniform law of the four61-bit keys, four64-bit pads and12unused bits,
starting from the two complete256-bit answers. -/
theorem uniform_components [SampleableType MacKey] [SampleableType Components] :
    𝒮[components <$> ($ᵗ MacKey : ProbComp MacKey)] = 𝒮[($ᵗ Components : ProbComp Components)] :=
  evalSPMF_map_bijective_uniform_cross (α := MacKey) (β := Components) components componentsEquiv.bijective

theorem components_lowKeys (key : MacKey) (j : Fin 4) :
    ((components key).1 j).toNat = macKeyWord key j := by
  rw [macKeyWord_eq]
  simp [components, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Exact published-tag plus retagged-key joint law, not only a key marginal. -/
theorem uniform_key_and_tag [SampleableType MacKey] [SampleableType MacTag] (chunks : List Nat) :
    𝒮[do let key ← $ᵗ MacKey; pure (macTagOf key chunks, key)] =
      𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (tag, retag key chunks tag)] := by
  calc
    _ = (fun key : MacKey => (macTagOf key chunks, key)) <$> 𝒮[$ᵗ MacKey] := by
      rw [bind_pure_comp, evalSPMF_map]
    _ = (fun key : MacKey => (macTagOf key chunks, key)) <$>
        𝒮[do let tag ← $ᵗ MacTag; let key ← $ᵗ MacKey; pure (retag key chunks tag)] := by
      rw [evalSPMF_uniformSample_bind_retag chunks]
    _ = _ := by
      rw [← evalSPMF_map]
      apply congrArg evalSPMF
      simp only [map_bind, map_pure, macTagOf_retag]

/-- The actually used keys and pads have the uniform product law after discarding
all12unused bits. No independent-field premise is required. -/
theorem uniform_key_pads [SampleableType MacKey] [SampleableType (LowKeys × MacTag)] :
    𝒮[(fun key : MacKey => ((components key).1, (components key).2.1)) <$> ($ᵗ MacKey)] =
      𝒮[$ᵗ (LowKeys × MacTag)] := by
  let _ : SampleableType ((LowKeys × MacTag) × UnusedBits) := SampleableType.ofFintype _
  let e : MacKey ≃ ((LowKeys × MacTag) × UnusedBits) :=
    componentsEquiv.trans (Equiv.prodAssoc LowKeys MacTag UnusedBits).symm
  have h := evalSPMF_map_bijective_uniform_cross (α := MacKey)
    (β := ((LowKeys × MacTag) × UnusedBits)) e e.bijective
  have hm := congrArg (fun law : SPMF ((LowKeys × MacTag) × UnusedBits) => Prod.fst <$> law) h
  have hm' : 𝒮[(fun key : MacKey => ((components key).1, (components key).2.1)) <$> ($ᵗ MacKey)] =
      𝒮[Prod.fst <$> ($ᵗ ((LowKeys × MacTag) × UnusedBits))] := by
    simpa only [evalSPMF_map, Functor.map_map, Function.comp_def, e, Equiv.trans_apply,
      componentsEquiv, Equiv.coe_fn_mk, Equiv.prodAssoc_symm_apply] using hm
  exact hm'.trans evalSPMF_map_fst_uniformSample_prod

end SiggolfT3Mac4
