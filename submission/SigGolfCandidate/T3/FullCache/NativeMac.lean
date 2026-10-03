import SigGolfCandidate.T3.FullCache.RequestBridge

namespace SigGolfCandidate.T3.Security.CacheAuthentication
open OracleComp OracleSpec SphincsSecurity
@[irreducible] noncomputable def regionFintype : Fintype Region := by
  classical
  exact inferInstance
abbrev MacTable := SiggolfT3Mac4.MacKey
@[irreducible] noncomputable def macTableSampler : SampleableType MacTable := by
  classical
  exact SampleableType.ofFintype _
end SigGolfCandidate.T3.Security.CacheAuthentication
namespace SigGolfCandidate.T3.Security.MacGame
open OracleComp OracleSpec ENNReal CacheAuthentication
open SiggolfT3Mac4 (MacKey encodeTag decodeTag tagRegion)
open SiggolfT3Mac4.Adaptive (retagRegion)
open SiggolfT3Mac4.Source (keyCoordinate toCoreCache fromCoreCache toCoreRequest fromCoreRequest)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType MacTable := macTableSampler
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
variable {State : Type}
abbrev NonMac := SiggolfT3Mac4.Source.NonMac
def tagAt (key : MacTable) (region : Region) : HashOutput := encodeTag (tagRegion key region)
def retag (key : MacTable) (published : T3.Cache) : MacTable := retagRegion key (fromCoreCache published)
noncomputable def sourceHandler (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    QueryImpl T3.Spec (StateT State ProbComp)
  | .inl input => base (.inl input)
  | .inr coordinate => do
      let answer ← base (.inr coordinate)
      if coordinate=keyCoordinate 0 then pure (key 0)
      else if coordinate=keyCoordinate 1 then pure (key 1) else pure answer
theorem sourceHandler_agrees (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable)
    (input : T3.Spec.Domain) (h : NonMac input) : sourceHandler base key input=base input := by
  cases input with
  | inl input => rfl
  | inr coordinate => simp only [sourceHandler,h.1,h.2,ite_false,bind_pure]
theorem simulate_no_mac {α : Type} (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable)
    (program : M α) (h : AllQueriesSatisfy program NonMac) :
    simulateQ (sourceHandler base key) program=simulateQ base program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,
        sourceHandler_agrees base key input hinput]
      exact congrArg (fun continuation => base input >>= continuation) (funext fun answer => ih answer (htail answer))
theorem payload_no_mac (cache : T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac :=
  SiggolfT3Mac4.Source.Payload.signPayload_allowed cache message
noncomputable def overhead (base : QueryImpl T3.Spec (StateT State ProbComp)) : StateT State ProbComp Unit := do
  let _ ← base (.inr (keyCoordinate 0))
  let _ ← base (.inr (keyCoordinate 1))
  pure ()
noncomputable def realSigner (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    RequestHop.Signer State := fun request =>
  SiggolfT3Mac4.Adaptive.realSigner (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request)) key (fromCoreRequest request)
noncomputable def idealSigner (base : QueryImpl T3.Spec (StateT State ProbComp)) (published : T3.Cache) :
    RequestHop.Signer State := fun request =>
  SiggolfT3Mac4.Adaptive.idealSigner (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (fromCoreRequest request)
theorem source_key_eq (base : QueryImpl T3.Spec (StateT State ProbComp)) (key : MacTable) :
    simulateQ (sourceHandler base key) privateMacKey =
      (do let _ ← overhead base; pure key) := by
  rw [← SiggolfT3Mac4.Source.privateMacKey_eq_core]
  unfold SiggolfT3Mac4.Source.privateMacKey privateHash
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,sourceHandler]
  simp only [ite_true,SiggolfT3Mac4.Source.keyCoordinate_zero_ne_one,
    Ne.symm SiggolfT3Mac4.Source.keyCoordinate_zero_ne_one,ite_false,bind_assoc,pure_bind]
  rw [SiggolfT3Mac4.Source.key_cases]
  simp only [overhead,bind_assoc,pure_bind]
theorem source_signer_eq (base : QueryImpl T3.Spec (StateT State ProbComp))
    (key : MacTable) (request : Request) :
    simulateQ (sourceHandler base key) (sign request.cache request.message)=realSigner base key request := by
  rw [← SiggolfT3Mac4.Source.toCoreCache_fromCoreCache request.cache,
    SiggolfT3Mac4.Source.core_sign_eq]
  unfold SiggolfT3Mac4.Source.sign SiggolfT3Mac4.Source.privateMac
  rw [SiggolfT3Mac4.Source.privateMacKey_eq_core]
  simp only [bind_assoc,pure_bind,simulateQ_bind,source_key_eq,bind_assoc,pure_bind]
  change (overhead base >>= fun _ => _)=_
  unfold realSigner SiggolfT3Mac4.Adaptive.realSigner
  apply congrArg (fun next => overhead base >>= next)
  funext ignored
  simp only [SiggolfT3Mac4.Source.toCoreCache_fromCoreCache,
    fromCoreRequest,fromCoreCache]
  split_ifs
  · exact simulate_no_mac base key _ (SiggolfT3Mac4.Source.corePayload_nonMac _)
  · rfl
theorem authentication_hop {α β : Type} (world : RequestHop.Public State)
    (base : QueryImpl T3.Spec (StateT State ProbComp)) (published : T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog Requests) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result,limit < result.1.2.length → Pr[event | cont result]=0) :
    Pr[event | ($ᵗ MacTable : ProbComp _) >>= fun key =>
      RequestHop.run world (realSigner base (retag key published)) program state >>= cont] ≤
      Pr[event | RequestHop.run world (idealSigner base published) program state >>= cont]+
        limit*((2 : ENNReal)^184)⁻¹ := by
  have hr := @SiggolfT3Mac4.Source.run_transport_bind α β State
  simp only [hr]
  simp only [realSigner,idealSigner,retag,SiggolfT3Mac4.Source.fromCoreRequest_toCoreRequest]
  exact SiggolfT3Mac4.Adaptive.authentication_hop world (fun _ => overhead base)
    (fun request => simulateQ base (SiggolfT3Mac4.Source.corePayload request))
    (fromCoreCache published) (SiggolfT3Mac4.Source.transport program) limit state
    (fun result => cont (SiggolfT3Mac4.Source.restore result)) event
    (fun result hlong' => hlong _ (by simpa only [SiggolfT3Mac4.Source.restore,
      SiggolfT3Mac4.Source.toCoreLog_length] using hlong'))
noncomputable local instance : SampleableType SiggolfT3Mac4.MacTag := SampleableType.ofFintype _
theorem encoded_uniform_bind {α : Type} (next : HashOutput → ProbComp α) :
    𝒮[do let tag ← ($ᵗ SiggolfT3Mac4.MacTag : ProbComp _); next (encodeTag tag)] =
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] := by
  have h := evalSPMF_map_bijective_uniform_cross (α := SiggolfT3Mac4.MacTag)
    (β := HashOutput) encodeTag SiggolfT3Mac4.tagEquiv.bijective
  rw [← bind_map_left,evalSPMF_bind,h,← evalSPMF_bind]
theorem refresh_published {α : Type} (region : Region) (next : HashOutput → MacTable → ProbComp α) :
    𝒮[do let key ← ($ᵗ MacTable : ProbComp _); next (tagAt key region) key] =
      𝒮[do
        let tag ← ($ᵗ HashOutput : ProbComp _)
        let key ← ($ᵗ MacTable : ProbComp _)
        next tag (retag key ⟨tag,region⟩)] := by
  have h := SiggolfT3Mac4.Adaptive.publication_retag_law region
    (fun published key => next (encodeTag published.tag) key)
  have he := encoded_uniform_bind (fun tag => do
    let key ← ($ᵗ MacTable : ProbComp _)
    next tag (retag key ⟨tag,region⟩))
  simp only [retag,fromCoreCache,SiggolfT3Mac4.decodeTag_encodeTag] at he
  exact h.trans he
theorem sample_mac_at_bind {α : Type} (region : Region) (next : HashOutput → ProbComp α) :
    𝒮[do let key ← ($ᵗ MacTable : ProbComp _); next (tagAt key region)] =
      𝒮[do let tag ← ($ᵗ HashOutput : ProbComp _); next tag] := by
  rw [refresh_published region (fun tag _ => next tag)]
  apply evalSPMF_bind_congr'
  intro tag
  apply evalSPMF_ext
  intro result
  change Pr[=result | ($ᵗ MacTable : ProbComp _) >>= fun _ => next tag]=Pr[=result | next tag]
  rw [probOutput_bind_const]
  simp
end SigGolfCandidate.T3.Security.MacGame
