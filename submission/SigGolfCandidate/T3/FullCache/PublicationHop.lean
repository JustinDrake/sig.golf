import SigGolfCandidate.T3.FullCache.AdaptiveHop

namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {Message Signature State : Type}

theorem publication_retag_law [SampleableType MacKey] [SampleableType MacTag] {β : Type}
    (region : Region) (next : Cache → MacKey → ProbComp β) :
    𝒮[do let key ← $ᵗ MacKey; next ⟨region, tagRegion key region⟩ key] =
      𝒮[do
        let tag ← $ᵗ MacTag
        let key ← $ᵗ MacKey
        next ⟨region, tag⟩ (retagRegion key ⟨region, tag⟩)] := by
  have hlaw := evalSPMF_uniformSample_bind_retag (chunks32 (regionBytes region))
  rw [evalSPMF_bind, ← hlaw, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind]
  apply congrArg evalSPMF
  apply bind_congr
  intro tag
  apply bind_congr
  intro key
  have ht := retagRegion_tag key (⟨region,tag⟩ : Cache)
  change tagRegion (retag key (chunks32 (regionBytes region)) tag) region = tag at ht
  rw [ht]
  rfl

theorem probEvent_bind_const_charge {X Y : Type} (mx : ProbComp X)
    (left right : X → ProbComp Y) (event : Y → Prop) (charge : ENNReal)
    (h : ∀ x, Pr[event | left x] ≤ Pr[event | right x] + charge) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right] + charge := by
  rw [probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' x,Pr[=x | mx] * (Pr[event | right x] + charge) :=
      ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = (∑' x,Pr[=x | mx] * Pr[event | right x]) + (∑' x,Pr[=x | mx]) * charge := by
      simp only [mul_add,ENNReal.tsum_add,ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)

/-- The unconditioned four-lane MAC game: publish the real tag of a uniform
512-bit key, then execute arbitrary adaptive requests. It is bounded by publishing
an independent uniform tag and authenticating only the literal published cache.
The full state, failed/repeated requests, final verification and any count event
are preserved by the continuation. -/
theorem published_authentication_hop [SampleableType MacKey] [SampleableType MacTag] {α β : Type}
    (region : Region) (world : Cache → Public State)
    (overhead : Cache → Request Message → StateT State ProbComp Unit)
    (payload : Cache → Signer Message Signature State)
    (program : Cache → OracleComp (Interaction Message Signature) α) (limit : Nat)
    (state : Cache → State)
    (cont : Cache → ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,limit < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      run (world published) (realSigner (overhead published) (payload published) key)
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      run (world published) (idealSigner (overhead published) (payload published) published)
        (program published) (state published) >>= cont published] +
      limit * ((2 : ENNReal)^184)⁻¹ := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (publication_retag_law region
    (fun published key => run (world published)
      (realSigner (overhead published) (payload published) key)
      (program published) (state published) >>= cont published))]
  apply probEvent_bind_const_charge
  intro tag
  exact authentication_hop (world ⟨region,tag⟩) (overhead ⟨region,tag⟩) (payload ⟨region,tag⟩)
    ⟨region,tag⟩ (program ⟨region,tag⟩) limit (state ⟨region,tag⟩) (cont ⟨region,tag⟩) event
    (hlong ⟨region,tag⟩)

theorem published_lifetime_authentication_hop
    [SampleableType MacKey] [SampleableType MacTag] {α β : Type}
    (region : Region) (world : Cache → Public State)
    (overhead : Cache → Request Message → StateT State ProbComp Unit)
    (payload : Cache → Signer Message Signature State)
    (program : Cache → OracleComp (Interaction Message Signature) α)
    (state : Cache → State)
    (cont : Cache → ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,2^32 < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      run (world published) (realSigner (overhead published) (payload published) key)
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      run (world published) (idealSigner (overhead published) (payload published) published)
        (program published) (state published) >>= cont published] +
      ((2 : ENNReal)^152)⁻¹ := by
  refine (published_authentication_hop region world overhead payload program (2^32) state cont event hlong).trans
    (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]

end SiggolfT3Mac4.Adaptive
