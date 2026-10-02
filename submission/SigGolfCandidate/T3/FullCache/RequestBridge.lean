import SigGolfCandidate.T3.FullCache.RequestRun
import SigGolfCandidate.T3.FullCache.CoreBridge
import SigGolfCandidate.T3.FullCache.CountedHop

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

/-- The complete source log and auxiliary state survive the request/cache bijection. -/
theorem run_transport_bind {α β State : Type} (world : RequestHop.Public State)
    (signer : RequestHop.Signer State) (program : OracleComp CoreInteraction α) (state : State)
    (cont : ((α × QueryLog CoreRequests) × State) → ProbComp β) :
    RequestHop.run world signer program state >>= cont =
      Adaptive.run world (fun request => signer (toCoreRequest request))
        (transport program) state >>= fun result => cont (restore result) := by
  rw [run_transport,bind_map_left]

end SiggolfT3Mac4.Source
