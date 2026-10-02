import SigGolfCandidate.T3.FullCache.AdaptiveForgery

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

/-- A four-lane MAC signer, with exactly the same key-independent bookkeeping
before the MAC test in both games. The state may include a full HASH counter. -/
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

/-- An adaptive authentication hop retaining the complete request log and handler
state. No assumption bounds the adversary's program syntactically: over-limit
transcripts need only receive zero score in the continuation. -/
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
