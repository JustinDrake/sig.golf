import SigGolfCandidate.T3.FullCache.CountedSigner

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Authentication hop for the explicitly interpreted T3-domain source signer.
The source request path executes the two actual private key queries before its
MAC test; public queries, complete auxiliary state and the request log persist. -/
theorem counted_source_authentication_hop
    [SampleableType MacKey] [SampleableType MacTag] {S α β : Type}
    (world : Adaptive.Public (CountState S)) (other : OtherTable) (region : Region)
    (payload : Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ request, AllQueriesSatisfy (payload request) NonMac)
    (program : Cache → OracleComp (Interaction T3Message T3Signature) α)
    (state : Cache → CountState S)
    (cont : Cache → ((α × QueryLog (Requests T3Message T3Signature)) × CountState S) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ published result,2^32 < result.1.2.length → Pr[event | cont published result] = 0) :
    Pr[event | do
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region,tagRegion key region⟩
      Adaptive.run world
        (fun request => simulateQ (tableHandler world (joinTable other key)) (sign payload request))
        (program published) (state published) >>= cont published] ≤
    Pr[event | do
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region,tag⟩
      Adaptive.run world
        (Adaptive.idealSigner keyCharge
          (fun request => simulateQ (baseHandler world other) (payload request)) published)
        (program published) (state published) >>= cont published] +
      ((2 : ENNReal)^152)⁻¹ := by
  simp_rw [sign_interpretation world other _ payload hpayload]
  exact Adaptive.published_lifetime_authentication_hop region (fun _ => world)
    (fun _ => keyCharge) (fun _ request => simulateQ (baseHandler world other) (payload request))
    program state cont event hlong

/-- The initial other-source state may itself be sampled and may contain all
paired masks, reserved seed coordinates, roots and keygen transcripts. Averaging
the complete conditional source hop spends the MAC lifetime loss only once. -/
theorem averaged_source_authentication_hop
    [SampleableType OtherTable] [SampleableType MacKey] [SampleableType MacTag] {S α β : Type}
    (world : OtherTable → Adaptive.Public (CountState S)) (region : OtherTable → Region)
    (payload : OtherTable → Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ other request, AllQueriesSatisfy (payload other request) NonMac)
    (program : OtherTable → Cache → OracleComp (Interaction T3Message T3Signature) α)
    (state : OtherTable → Cache → CountState S)
    (cont : OtherTable → Cache → ((α × QueryLog (Requests T3Message T3Signature)) × CountState S) → ProbComp β)
    (event : β → Prop)
    (hlong : ∀ other published result,2^32 < result.1.2.length → Pr[event | cont other published result] = 0) :
    Pr[event | do
      let other ← $ᵗ OtherTable
      let key ← $ᵗ MacKey
      let published : Cache := ⟨region other,tagRegion key (region other)⟩
      Adaptive.run (world other)
        (fun request => simulateQ (tableHandler (world other) (joinTable other key)) (sign (payload other) request))
        (program other published) (state other published) >>= cont other published] ≤
    Pr[event | do
      let other ← $ᵗ OtherTable
      let tag ← $ᵗ MacTag
      let published : Cache := ⟨region other,tag⟩
      Adaptive.run (world other)
        (Adaptive.idealSigner keyCharge
          (fun request => simulateQ (baseHandler (world other) other) (payload other request)) published)
        (program other published) (state other published) >>= cont other published] +
      ((2 : ENNReal)^152)⁻¹ := by
  apply Adaptive.probEvent_bind_const_charge
  intro other
  exact counted_source_authentication_hop (world other) other (region other) (payload other)
    (hpayload other) (program other) (state other) (cont other) event (hlong other)

end SiggolfT3Mac4.Source
