import SigGolfCandidate.T3.Gate6.NativeCache

namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def acceptedWeight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) : ENNReal :=
  expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
    (fun answer => (decoder answer).elim 0 payoff)

theorem uniform_decoder_weight {β : Type} (decoder : HashOutput → Option β)
    (payoff : β → ENNReal) (rejected : ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => (decoder answer).elim rejected payoff)=
      acceptedWeight decoder payoff+failMass decoder*rejected := by
  classical
  have hp (answer : HashOutput) :
      (decoder answer).elim rejected payoff=(decoder answer).elim 0 payoff+
        (if decoder answer=none then 1 else 0)*rejected := by
    cases decoder answer <;> simp
  simp_rw [hp]
  rw [expectedValue_add,expectedValue_mul_const,expectedValue_ite_one]
  have hf : failMass decoder=Pr[fun answer : HashOutput => decoder answer=none |
      ($ᵗ HashOutput : ProbComp HashOutput)] := failMass_eq_probEvent decoder
  rw [← hf]
  rfl

def CachedTrialScoresBound {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal) (price : ENNReal)
    (counter bound : Nat) (cache : RCache) : Prop :=
  ∀ c,counter ≤ c → c < bound → ∀ answer,cache (inputs c)=some answer →
    (decoder answer).elim 0 weight ≤ price

theorem expected_publicSearch_completed_le_of_cached_scores {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value,payoff (result counter value)=weight value)
    (price : ENNReal) (hstep : acceptedWeight decoder weight+failMass decoder*price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right,left < bound → right < bound → inputs left=inputs right → left=right) :
    ∀ fuel counter,counter+fuel ≤ bound → ∀ cache : RCache,
      CachedTrialScoresBound inputs decoder weight price counter bound cache →
      expectedValue (roRun secret
        (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim price payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero => intro counter _ cache _;simp [searchLoop,publicProgram]
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [publicSearch_succ,roRun_bind,roRun_publicQuery,expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hp := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq,hc]
          simp only [expectedValue_pure]
          cases hd : decoder answer with
          | none =>
              exact ih (counter+1) (by omega) cache
                (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
          | some value =>
              simpa only [roRun_pure,expectedValue_pure,Option.elim_some,hweight,hd] using hp
      | none =>
          rw [expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter+1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c)=some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = acceptedWeight decoder weight+failMass decoder*price :=
              uniform_decoder_weight decoder weight price
            _ ≤ price := hstep

theorem digestTrial_nonce_injective {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat}
    (he : digestTrial rho message counter=digestTrial rho' message' counter') : rho=rho' := by
  have h := pad64_inj_of_length (by simp [digestInput,SphincsSecurity.bytesLE_length]) he
  exact (digestInput_injective h).1

/-- The exact new decoder over the existing T3 digest-trial domain. -/
noncomputable def decode (answer : HashOutput) : Option HashOutput :=
  if DigestAccepted answer then some answer else none
noncomputable def search (rho : Digest) (message : Message) (fuel : Nat) : M (Option (BitVec 32 × HashOutput)) :=
  publicProgram (searchLoop (digestTrial rho message) decode
    (fun c output => pure (BitVec.ofNat 32 c,output)) fuel 0)
noncomputable def hit (mark : MarkedLabel) (output : HashOutput) : ENNReal :=
  if (digestRecord output).1=mark then 1 else 0
noncomputable def completedScore (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) : ENNReal :=
  found.elim (1/2^59) (fun value => hit mark value.2)

theorem acceptance_le_one : acceptance≤1 := by
  rw [← digest_acceptance_exact]
  exact probEvent_le_one

theorem decoder_failure : failMass decode=1-acceptance := by
  rw [failMass_eq_probEvent]
  change Pr[fun output : HashOutput => decode output=none | ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have he : (fun output => decode output=none)=(fun output => ¬DigestAccepted output) := by
    funext output
    simp [decode]
  rw [he]
  have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) DigestAccepted
  rw [probFailure_of_liftM_PMF,tsub_zero,digest_acceptance_exact,add_comm] at h
  exact ENNReal.eq_sub_of_add_eq' (by simp) h

theorem accepted_hit (mark : MarkedLabel) : acceptedWeight decode (hit mark)=acceptance/2^59 := by
  unfold acceptedWeight
  have he (output : HashOutput) : (decode output).elim 0 (hit mark)=
      if DigestAccepted output ∧ (digestRecord output).1=mark then 1 else 0 := by
    simp only [decode,hit]
    split_ifs <;> simp_all [hit]
  simp_rw [he]
  rw [expectedValue_ite_one]
  exact digest_mark_joint_exact mark

theorem completedScore_le_one (mark : MarkedLabel) (found : Option (BitVec 32 × HashOutput)) :
    completedScore mark found≤1 := by
  cases found with
  | none => norm_num [completedScore]
  | some value => unfold completedScore hit;simp only [Option.elim_some];split_ifs <;> norm_num

noncomputable def CachedHit (rho : Digest) (message : Message) (fuel : Nat)
    (cache : RCache) (mark : MarkedLabel) : Prop :=
  ∃ c,c<fuel ∧ ∃ output,cache (digestTrial rho message c)=some output ∧
    Cache.Matches mark output

/-- Exhaustion receives its uniform completion inside the same search recurrence. -/
theorem completed_search_no_cached_hit (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel)
    (hno : ¬CachedHit rho message fuel cache mark) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤1/2^59 := by
  unfold search completedScore
  apply expected_publicSearch_completed_le_of_cached_scores secret (digestTrial rho message) decode
    (fun c output => (BitVec.ofNat 32 c,output)) (fun found => hit mark found.2)
    (hit mark) (fun _ _ => rfl) (1/2^59) _ fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (lt_of_lt_of_le hl hlimit)
      (lt_of_lt_of_le hr hlimit) he) fuel 0 (by omega) cache
  · intro c hc hf output ha
    by_cases hadm : DigestAccepted output
    · have hnot : (digestRecord output).1≠mark := fun ht => hno ⟨c,hf,output,ha,hadm,ht⟩
      simp [decode,hadm,hit,hnot]
    · simp [decode,hadm]
  · rw [accepted_hit,decoder_failure]
    calc
      _ = (acceptance+(1-acceptance))*(1/2^59) := by simp only [div_eq_mul_inv,one_mul];ring
      _ = 1/2^59 := by rw [add_tsub_cancel_of_le acceptance_le_one,one_mul]
      _ ≤ _ := le_rfl

theorem completed_search_cached_event (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (roRun secret (search rho message fuel) cache)
      (fun result => completedScore mark result.1)≤
      1/2^59+if CachedHit rho message fuel cache mark then 1 else 0 := by
  by_cases h : CachedHit rho message fuel cache mark
  · rw [if_pos h]
    exact (expectedValue_le_of_le _ fun _ => completedScore_le_one mark _).trans (le_add_left le_rfl)
  · rw [if_neg h,add_zero]
    exact completed_search_no_cached_hit secret rho message fuel hlimit cache mark h

noncomputable def cachedNonces (message : Message) (fuel : Nat) (cache : RCache)
    (mark : MarkedLabel) : Finset Digest := Finset.univ.filter fun rho => CachedHit rho message fuel cache mark

theorem cachedNonces_card_le_count (message : Message) (fuel : Nat) (cache : RCache) (mark : MarkedLabel) :
    ((cachedNonces message fuel cache mark).card : ENNReal)≤NativeCache.count mark cache := by
  classical
  let nonces := cachedNonces message fuel cache mark
  have hw : ∀ rho : nonces,∃ counter,counter<fuel ∧ ∃ output,
      cache (digestTrial rho.val message counter)=some output ∧ Cache.Matches mark output := by
    intro rho
    exact (Finset.mem_filter.mp rho.property).2
  choose counter hc output ha htarget using hw
  let inputs (rho : nonces) := digestTrial rho.val message (counter rho)
  have hinj : Function.Injective inputs := by
    intro left right he
    exact Subtype.ext (digestTrial_nonce_injective he)
  have hentry (rho : nonces) : NativeCache.entry mark cache (inputs rho)=1 := by
    simp only [NativeCache.entry,inputs,ha,Option.elim_some,htarget,if_true]
  calc
    _ = ∑ rho : nonces,NativeCache.entry mark cache (inputs rho) := by
      simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,nonces]
    _ ≤ ∑' input,NativeCache.entry mark cache input := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comp_le_tsum_of_injective hinj (NativeCache.entry mark cache))
    _ = _ := rfl

/-- Exact-domain fresh-nonce source search bound, including exhausted searches. -/
theorem uniform_nonce_completed_point (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      1/(2 : ENNReal)^59+NativeCache.count mark cache/(2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        1/(2 : ENNReal)^59+if CachedHit rho message fuel cache mark then 1 else 0) :=
      expectedValue_mono _ fun rho => completed_search_cached_event secret rho message fuel hlimit cache mark
    _ = 1/(2 : ENNReal)^59+(cachedNonces message fuel cache mark).card/(2 : ENNReal)^128 := by
      rw [expectedValue_add,expectedValue_const (by simp),expectedValue_ite_one,probEvent_uniformSample]
      simp only [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat,cachedNonces]
    _ ≤ _ := add_le_add le_rfl (ENNReal.div_le_div_right (cachedNonces_card_le_count message fuel cache mark) _)

theorem uniform_nonce_completed_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (search rho message fuel) cache) (fun result => completedScore mark result.1) ≤
      (17/16 : ENNReal)/(2 : ENNReal)^59 :=
  (uniform_nonce_completed_point secret message fuel hlimit cache mark).trans
    (NativeCache.clean_point_bound_arithmetic cache hfinite q hsize hq hclean mark)

end SigGolfResearch.Gate6.NativeSearch
#print axioms SigGolfResearch.Gate6.NativeSearch.uniform_nonce_completed_cap
