import SigGolfCandidate.T3.FullCache.Retag
import SigGolfCandidate.T3.FullCache.Region
import SigGolfCandidate.T3.Core

section

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
theorem uniform_components [SampleableType MacKey] [SampleableType Components] :
    𝒮[components <$> ($ᵗ MacKey : ProbComp MacKey)] = 𝒮[($ᵗ Components : ProbComp Components)] :=
  evalSPMF_map_bijective_uniform_cross (α := MacKey) (β := Components) components componentsEquiv.bijective
theorem components_lowKeys (key : MacKey) (j : Fin 4) :
    ((components key).1 j).toNat = macKeyWord key j := by
  rw [macKeyWord_eq]
  simp [components, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
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
end

section


namespace SiggolfT3Mac4
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option Elab.async false
structure Cache where
  region : Region
  tag : MacTag
structure Request (Message : Type) where
  message : Message
  cache : Cache
abbrev Requests (Message Signature : Type) := Request Message →ₒ Option Signature
abbrev Interaction (Message Signature : Type) := SphincsSecurity.OracleWorld + Requests Message Signature
end SiggolfT3Mac4
namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Message Signature State : Type}
abbrev Public (State : Type) := QueryImpl SphincsSecurity.OracleWorld (StateT State ProbComp)
abbrev Signer (Message Signature State : Type) := Request Message → StateT State ProbComp (Option Signature)
noncomputable def run {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (program : OracleComp (Interaction Message Signature) α) (state : State) :
    ProbComp ((α × QueryLog (Requests Message Signature)) × State) :=
  OracleComp.recOn program (fun value state => pure ((value,[]),state))
    (fun input _ ih state => match input with
      | .inl input => do
          let result ← (world input).run state
          ih result.1 result.2
      | .inr request => do
          let result ← (signer request).run state
          (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$> ih result.1 result.2) state
theorem run_pure {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (value : α) (state : State) : run world signer (pure value) state=pure ((value,[]),state) := rfl
theorem run_public {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (input : SphincsSecurity.OracleWorld.Domain)
    (next : SphincsSecurity.OracleWorld.Range input → OracleComp (Interaction Message Signature) α)
    (state : State) :
    run world signer (liftM ((Interaction Message Signature).query (.inl input)) >>= next) state=
      (do let result ← (world input).run state; run world signer (next result.1) result.2) := rfl
theorem run_request {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (request : Request Message) (next : Option Signature → OracleComp (Interaction Message Signature) α)
    (state : State) :
    run world signer (liftM ((Interaction Message Signature).query (.inr request)) >>= next) state=
      (do
        let result ← (signer request).run state
        (fun tail => ((tail.1.1,⟨request,result.1⟩::tail.1.2),tail.2)) <$>
          run world signer (next result.1) result.2) := rfl
theorem erasure {α : Type} (world : Public State) (signer : Signer Message Signature State)
    (program : OracleComp (Interaction Message Signature) α) (state : State) :
    (fun result => (result.1.1,result.2)) <$> run world signer program state=
      (simulateQ (world+signer) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [run_public,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          exact bind_congr fun result => ih result.1 result.2
      | inr request =>
          rw [run_request,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,map_bind]
          apply bind_congr
          intro result
          simpa only [Functor.map_map,Function.comp_def] using ih result.1 result.2
theorem probEvent_bind_le_add_bind {α β γ : Type} (mx : ProbComp α)
    (left right : α → ProbComp β) (badRun : α → ProbComp γ)
    (event : β → Prop) (bad : γ → Prop)
    (hle : ∀ value ∈ support mx,Pr[event | left value] ≤
      Pr[event | right value]+Pr[bad | badRun value]) :
    Pr[event | mx >>= left] ≤ Pr[event | mx >>= right]+Pr[bad | mx >>= badRun] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hv : value ∈ support mx
  · rw [← mul_add]
    exact mul_le_mul' le_rfl (hle value hv)
  · simp [probOutput_eq_zero_of_not_mem_support hv]
def BadIn (bad : Request Message → Prop) (limit : Nat) (log : QueryLog (Requests Message Signature)) : Prop :=
  ∃ entry ∈ log.take limit,bad entry.1
theorem identical_until_bad {α β : Type} (world : Public State) (bad : Request Message → Prop)
    (left right : Signer Message Signature State) (hagree : ∀ request,¬bad request → left request=right request)
    (program : OracleComp (Interaction Message Signature) α) :
    ∀ (limit : Nat) (state : State) (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β)
      (event : β → Prop),
      (∀ result,limit < result.1.2.length → Pr[event | cont result]=0) →
      Pr[event | run world left program state >>= cont] ≤
        Pr[event | run world right program state >>= cont]+
          Pr[fun result => BadIn bad limit result.1.2 | run world right program state] := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      intro limit state cont event _
      exact le_self_add
  | query_bind input next ih =>
      intro limit state cont event hlong
      cases input with
      | inl input =>
          rw [run_public,run_public,bind_assoc,bind_assoc]
          apply probEvent_bind_le_add_bind
          intro result _
          exact ih result.1 limit result.2 cont event hlong
      | inr request =>
          by_cases hbad : bad request
          · cases limit with
            | zero =>
                refine le_trans (le_of_eq ?_) zero_le
                rw [probEvent_eq_zero_iff]
                intro value hv
                rw [run_request,bind_assoc,mem_support_bind_iff] at hv
                obtain ⟨head,_,hv⟩ := hv
                rw [bind_map_left,mem_support_bind_iff] at hv
                obtain ⟨tail,_,hv⟩ := hv
                have hz := hlong ((tail.1.1,⟨request,head.1⟩::tail.1.2),tail.2) (by simp)
                rw [probEvent_eq_zero_iff] at hz
                exact hz value hv
            | succ limit =>
                have hone : Pr[fun result => BadIn bad (limit+1) result.1.2 |
                    run world right (liftM ((Interaction Message Signature).query (.inr request)) >>= next) state]=1 := by
                  rw [probEvent_eq_one_iff]
                  refine ⟨by simp,?_⟩
                  intro result hr
                  rw [run_request,mem_support_bind_iff] at hr
                  obtain ⟨head,_,hr⟩ := hr
                  rw [support_map] at hr
                  obtain ⟨tail,_,rfl⟩ := hr
                  exact ⟨⟨request,head.1⟩,by simp,hbad⟩
                exact probEvent_le_one.trans (hone.symm.le.trans le_add_self)
          · rw [run_request,run_request,hagree request hbad,bind_assoc,bind_assoc]
            apply probEvent_bind_le_add_bind
            intro head _
            rw [bind_map_left,bind_map_left,probEvent_map]
            refine (ih head.1 (limit-1) head.2 _ event (fun result hr => hlong _ (by simp;omega))).trans
              (add_le_add le_rfl (probEvent_mono fun result _ hr => ?_))
            obtain ⟨entry,he,hbadEntry⟩ := hr
            cases limit with
            | zero => simp at he
            | succ limit =>
                simp only [Nat.add_sub_cancel] at he
                exact ⟨entry,by simp [he],hbadEntry⟩
end SiggolfT3Mac4.Adaptive
end

section

namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {Message Signature : Type}
def retagRegion (key : MacKey) (published : Cache) : MacKey :=
  retag key (chunks32 (regionBytes published.region)) published.tag
def BadRequest (published : Cache) (key : MacKey) (request : Request Message) : Prop :=
  request.cache.region ≠ published.region ∧
    tagRegion (retagRegion key published) request.cache.region = request.cache.tag
theorem retagRegion_tag (key : MacKey) (published : Cache) :
    tagRegion (retagRegion key published) published.region = published.tag :=
  macTagOf_retag key (chunks32 (regionBytes published.region)) published.tag
theorem request_bad_bound [SampleableType MacKey] (published : Cache) (request : Request Message) :
    Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] ≤
      (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  by_cases hne : request.cache.region ≠ published.region
  · exact (probEvent_mono fun _ _ h => h.2).trans
      (probEvent_region_bad_le published.region request.cache.region hne published.tag request.cache.tag)
  · have hz : Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro key _ h
      exact hne h.1
    rw [hz]
    exact zero_le
theorem list_events_bound {X Y : Type} (mx : ProbComp X) (entries : List Y)
    (event : Y → X → Prop) (cap : ENNReal) (hc : ∀ entry ∈ entries,Pr[event entry | mx] ≤ cap) :
    Pr[fun x => ∃ entry ∈ entries,event entry x | mx] ≤ entries.length*cap := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      calc
        _ = Pr[fun x => event entry x ∨ ∃ entry ∈ entries,event entry x | mx] := by
          apply probEvent_ext
          intro x _
          simp
        _ ≤ Pr[event entry | mx]+Pr[fun x => ∃ entry ∈ entries,event entry x | mx] :=
          probEvent_or_le _ _ _
        _ ≤ cap+entries.length*cap :=
          add_le_add (hc entry (by simp)) (ih fun entry he => hc entry (by simp [he]))
        _ = _ := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          rw [add_comm]
theorem independent_log_bad_bound [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature))
    (limit : Nat) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) limit (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      limit*((2 : ENNReal)^184)⁻¹ := by
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  rw [probEvent_bind_bind_swap,probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' x,Pr[=x | mx]*(limit*((2 : ENNReal)^184)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul' le_rfl
      rw [bind_pure_comp,probEvent_map]
      exact (list_events_bound ($ᵗ MacKey) ((logOf x).take limit)
        (fun entry key => BadRequest published key entry.1) _
        (fun entry _ => request_bad_bound published entry.1)).trans
        (mul_le_mul' (by exact_mod_cast List.length_take_le _ _) le_rfl)
    _ = (∑' x,Pr[=x | mx])*(limit*((2 : ENNReal)^184)⁻¹) := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_of_le_one_left zero_le tsum_probOutput_le_one
theorem lifetime_mac_charge [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature)) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) (2^32) (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      ((2 : ENNReal)^152)⁻¹ := by
  refine (independent_log_bad_bound published mx logOf (2^32)).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SiggolfT3Mac4.Adaptive
end

section

namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
variable {Message Signature State : Type}
noncomputable def realSigner (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (key : MacKey) : Signer Message Signature State :=
  fun request => do
    let _ ← overhead request
    if tagRegion key request.cache.region = request.cache.tag then payload request else pure none
noncomputable def idealSigner (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache) : Signer Message Signature State :=
  fun request => do
    let _ ← overhead request
    if request.cache = published then payload request else pure none
theorem signer_agrees (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache) (key : MacKey)
    (request : Request Message) (hgood : ¬BadRequest published key request) :
    realSigner overhead payload (retagRegion key published) request =
      idealSigner overhead payload published request := by
  unfold realSigner idealSigner
  apply congrArg (fun continuation => overhead request >>= continuation)
  funext answer
  by_cases hr : request.cache.region = published.region
  · rw [hr, retagRegion_tag]
    by_cases ht : published.tag = request.cache.tag
    · have he : request.cache = published := by
        cases request with
        | mk message cache => cases cache; cases published; cases hr; cases ht; rfl
      rw [if_pos ht, if_pos he]
    · have he : request.cache ≠ published := fun he => ht (congrArg Cache.tag he).symm
      rw [if_neg ht, if_neg he]
  · have ht : tagRegion (retagRegion key published) request.cache.region ≠ request.cache.tag :=
      fun ht => hgood ⟨hr,ht⟩
    have he : request.cache ≠ published := fun he => hr (congrArg Cache.region he)
    rw [if_neg ht,if_neg he]
theorem authentication_hop [SampleableType MacKey] {α β : Type}
    (world : Public State) (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache)
    (program : OracleComp (Interaction Message Signature) α) (limit : Nat) (state : State)
    (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result, limit < result.1.2.length → Pr[event | cont result] = 0) :
    Pr[event | ($ᵗ MacKey : ProbComp _) >>= fun key =>
      run world (realSigner overhead payload (retagRegion key published)) program state >>= cont] ≤
      Pr[event | run world (idealSigner overhead payload published) program state >>= cont] +
        limit * ((2 : ENNReal)^184)⁻¹ := by
  have h := probEvent_bind_le_add_bind ($ᵗ MacKey : ProbComp _)
    (fun key => run world (realSigner overhead payload (retagRegion key published)) program state >>= cont)
    (fun _ => run world (idealSigner overhead payload published) program state >>= cont)
    (fun key => (fun result => (key,result)) <$> run world (idealSigner overhead payload published) program state)
    event (fun result => BadIn (BadRequest published result.1) limit result.2.1.2) (by
      intro key _
      rw [probEvent_map]
      exact identical_until_bad world (BadRequest published key) _ _
        (signer_agrees overhead payload published key) program limit state cont event hlong)
  rw [probEvent_bind_const] at h
  simp only [probFailure_eq_zero,tsub_zero,one_mul] at h
  exact h.trans (add_le_add le_rfl
    (independent_log_bad_bound published
      (run world (idealSigner overhead payload published) program state) (fun result => result.1.2) limit))
theorem lifetime_authentication_hop [SampleableType MacKey] {α β : Type}
    (world : Public State) (overhead : Request Message → StateT State ProbComp Unit)
    (payload : Signer Message Signature State) (published : Cache)
    (program : OracleComp (Interaction Message Signature) α) (state : State)
    (cont : ((α × QueryLog (Requests Message Signature)) × State) → ProbComp β) (event : β → Prop)
    (hlong : ∀ result, 2^32 < result.1.2.length → Pr[event | cont result] = 0) :
    Pr[event | ($ᵗ MacKey : ProbComp _) >>= fun key =>
      run world (realSigner overhead payload (retagRegion key published)) program state >>= cont] ≤
      Pr[event | run world (idealSigner overhead payload published) program state >>= cont] +
        ((2 : ENNReal)^152)⁻¹ := by
  refine (authentication_hop world overhead payload published program (2^32) state cont event hlong).trans
    (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SiggolfT3Mac4.Adaptive
end

section

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
end

section


namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev T3Coordinate := SigGolfCandidate.T3.Coordinate
def keyTweak (i : Fin 2) : BitVec 128 := SigGolfCandidate.T3.header 14 0 0 0 i.val
def keyCoordinate (i : Fin 2) : T3Coordinate := .inl (keyTweak i)
theorem keyCoordinate_injective : Function.Injective keyCoordinate := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    norm_num [keyCoordinate,keyTweak,SigGolfCandidate.T3.header,SigGolfCandidate.T3.packedNodeTag] at h ⊢
  all_goals have h' := congrArg BitVec.toNat h; norm_num at h'
theorem keyCoordinate_zero_ne_one : keyCoordinate 0 ≠ keyCoordinate 1 := by
  intro h
  have := keyCoordinate_injective h
  exact (by decide : (0 : Fin 2) ≠ 1) this
abbrev OtherCoordinate := {c : T3Coordinate // c ≠ keyCoordinate 0 ∧ c ≠ keyCoordinate 1}
abbrev OtherTable := OtherCoordinate → HashOutput
abbrev FullTable := T3Coordinate → HashOutput
noncomputable def joinTable (other : OtherTable) (key : MacKey) : FullTable := fun c => by
  classical
  exact if h0 : c = keyCoordinate 0 then key 0 else
    if h1 : c = keyCoordinate 1 then key 1 else other ⟨c,h0,h1⟩
theorem joinTable_key (other : OtherTable) (key : MacKey) (i : Fin 2) :
    joinTable other key (keyCoordinate i) = key i := by
  fin_cases i
  · simp [joinTable]
  · simp [joinTable,Ne.symm keyCoordinate_zero_ne_one]
theorem joinTable_other (other : OtherTable) (key : MacKey) (c : OtherCoordinate) :
    joinTable other key c = other c := by
  simp [joinTable,c.property.1,c.property.2]
noncomputable def tableEquiv : (OtherTable × MacKey) ≃ FullTable where
  toFun tables := joinTable tables.1 tables.2
  invFun table := ((fun c => table c),fun i => table (keyCoordinate i))
  left_inv tables := by
    apply Prod.ext
    · funext c; exact joinTable_other tables.1 tables.2 c
    · funext i; exact joinTable_key tables.1 tables.2 i
  right_inv table := by
    funext c
    classical
    unfold joinTable
    dsimp only
    split_ifs with h0 h1
    · rw [h0]
    · rw [h1]
    · rfl
theorem uniform_product {A B : Type} [Finite A] [Finite B]
    [SampleableType A] [SampleableType B] [SampleableType (A × B)] :
    𝒮[do let a ← ($ᵗ A : ProbComp _); let b ← $ᵗ B; pure (a,b)] = 𝒮[$ᵗ (A × B)] := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  apply evalSPMF_ext
  rintro ⟨a,b⟩
  change Pr[=(a,b) | do let x ← ($ᵗ A : ProbComp _); let y ← $ᵗ B; pure (id x,id y)] = _
  rw [probOutput_bind_bind_prod_mk_eq_mul' _ _ id id a b]
  simp only [id_map,probOutput_uniformSample,Nat.card_eq_fintype_card,Fintype.card_prod,Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
theorem uniform_table_split [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)] :
    𝒮[do
      let other ← ($ᵗ OtherTable : ProbComp _)
      let key ← $ᵗ MacKey
      pure (joinTable other key)] = 𝒮[$ᵗ FullTable] := by
  have h := congrArg (Functor.map tableEquiv) (uniform_product (A := OtherTable) (B := MacKey))
  simp only [← evalSPMF_map,map_bind,map_pure] at h
  exact h.trans (evalSPMF_map_bijective_uniform_cross (α := OtherTable × MacKey) (β := FullTable)
    tableEquiv tableEquiv.bijective)
theorem uniform_table_split_bind [SampleableType OtherTable] [SampleableType MacKey]
    [SampleableType FullTable] [SampleableType (OtherTable × MacKey)]
    {α : Type} (next : FullTable → ProbComp α) :
    𝒮[do let table ← ($ᵗ FullTable : ProbComp _); next table] =
      𝒮[do
        let other ← ($ᵗ OtherTable : ProbComp _)
        let key ← $ᵗ MacKey
        next (joinTable other key)] := by
  rw [evalSPMF_bind,← uniform_table_split,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]
end SiggolfT3Mac4.Source
end
