import SigGolfCandidate.T3.FullCache.CountedSigner
import SigGolfCandidate.T3.FullCache.RequestRun
import SigGolfCandidate.T3.FullCache.CoreBridge

section

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
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
end

section



namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3.Security
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev CoreRequest := SigGolfCandidate.T3.Security.Request
abbrev CoreRequests := SigGolfCandidate.T3.Security.Requests
abbrev CoreInteraction := SigGolfCandidate.T3.Security.LazyPrivate.Interaction
def toCoreRequest (request : Request T3Message) : CoreRequest :=
  ⟨request.message,toCoreCache request.cache⟩
def fromCoreRequest (request : CoreRequest) : Request T3Message :=
  ⟨request.message,fromCoreCache request.cache⟩
theorem toCoreRequest_fromCoreRequest (request : CoreRequest) :
    toCoreRequest (fromCoreRequest request)=request := by
  cases request
  simp only [toCoreRequest,fromCoreRequest,toCoreCache_fromCoreCache]
theorem fromCoreRequest_toCoreRequest (request : Request T3Message) :
    fromCoreRequest (toCoreRequest request)=request := by
  cases request
  simp only [toCoreRequest,fromCoreRequest,fromCoreCache_toCoreCache]
theorem entry_roundtrip (request : CoreRequest) (answer : Option T3Signature) :
    (⟨toCoreRequest (fromCoreRequest request),answer⟩ : (input : CoreRequests.Domain) × CoreRequests.Range input)=⟨request,answer⟩ := by
  exact Sigma.ext (toCoreRequest_fromCoreRequest request) HEq.rfl
def toCoreLog (log : QueryLog (Requests T3Message T3Signature)) : QueryLog CoreRequests :=
  log.map fun entry => ⟨toCoreRequest entry.1,entry.2⟩
theorem toCoreLog_length (log : QueryLog (Requests T3Message T3Signature)) :
    (toCoreLog log).length=log.length := by simp [toCoreLog]
noncomputable def interactionMap : QueryImpl CoreInteraction
    (OracleComp (Interaction T3Message T3Signature))
  | .inl input => liftM ((Interaction T3Message T3Signature).query (.inl input))
  | .inr request => liftM ((Interaction T3Message T3Signature).query (.inr (fromCoreRequest request)))
noncomputable def transport {α : Type} (program : OracleComp CoreInteraction α) :
    OracleComp (Interaction T3Message T3Signature) α := simulateQ interactionMap program
def restore {α State : Type}
    (result : (α × QueryLog (Requests T3Message T3Signature)) × State) :
    (α × QueryLog CoreRequests) × State := ((result.1.1,toCoreLog result.1.2),result.2)
theorem run_transport {α State : Type} (world : RequestHop.Public State)
    (signer : RequestHop.Signer State) (program : OracleComp CoreInteraction α) (state : State) :
    RequestHop.run world signer program state =
      restore <$> Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [RequestHop.run_public,Adaptive.run_public,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          simp only [transport,simulateQ_bind,simulateQ_spec_query,interactionMap]
          rw [RequestHop.run_request,Adaptive.run_request,map_bind,toCoreRequest_fromCoreRequest]
          apply bind_congr
          intro head
          rw [ih]
          simp only [Functor.map_map,Function.comp_def,restore,toCoreLog,List.map_cons,
            toCoreRequest_fromCoreRequest,entry_roundtrip]
          rfl
theorem run_transport_bind {α β State : Type} (world : RequestHop.Public State)
    (signer : RequestHop.Signer State) (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]
end SiggolfT3Mac4.Source
end
