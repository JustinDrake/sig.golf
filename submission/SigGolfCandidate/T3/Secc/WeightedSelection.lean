import SigGolfCandidate.T3.BPORS

/-! Weighted fresh/cached selection for the actual digest rejection search.
The payoff may depend on all leaf bits, not merely on index/bucket labels.
This is the local kernel needed by a future-coverage forecast. -/

namespace SigGolfCandidate.T3.Sampling.WeightedSelection
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (searchLoop failMass failMass_eq_probEvent)
open DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def cacheEntry {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) (cache : RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => (decoder answer).elim 0 weight)

noncomputable def cacheWeight {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) (cache : RCache) : ENNReal :=
  ∑' input, cacheEntry decoder weight cache input

noncomputable def trialWeight {β : Type} (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (weight : β → ENNReal)
    (bound : Nat) (cache : RCache) : ENNReal :=
  ∑ counter : Fin bound, cacheEntry decoder weight cache (inputs counter)

theorem cacheWeight_empty {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) : cacheWeight decoder weight ∅ = 0 := by
  simp [cacheWeight, cacheEntry]

theorem cacheWeight_cacheQuery {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) (cache : RCache) (input : HashInput) (answer : HashOutput)
    (hfresh : cache input = none) :
    cacheWeight decoder weight (cache.cacheQuery input answer) =
      cacheWeight decoder weight cache + (decoder answer).elim 0 weight := by
  unfold cacheWeight
  rw [ENNReal.tsum_eq_add_tsum_ite
      (f := cacheEntry decoder weight (cache.cacheQuery input answer)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := cacheEntry decoder weight cache) input]
  simp only [cacheEntry, QueryCache.cacheQuery_self, hfresh, Option.elim_none,
    Option.elim_some, zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other = input
  · simp [heq]
  · simp only [heq, if_false, QueryCache.cacheQuery_of_ne cache answer heq]

/-- A fresh public row adds exactly its uniform accepted weight to the cache
moment, regardless of how the query input was chosen from the previous state. -/
theorem fresh_cache_growth {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) (cache : RCache) (input : HashInput)
    (hfresh : cache input = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => cacheWeight decoder weight (cache.cacheQuery input answer)) =
      cacheWeight decoder weight cache + acceptedWeight decoder weight := by
  simp_rw [cacheWeight_cacheQuery decoder weight cache input _ hfresh]
  rw [expectedValue_add, expectedValue_const (by simp)]
  rfl

theorem failMass_le_one {β : Type} (decoder : HashOutput → Option β) :
    failMass decoder ≤ 1 := by
  rw [failMass_eq_probEvent]
  exact probEvent_le_one

theorem price_add_cache {β : Type} (decoder : HashOutput → Option β)
    (weight : β → ENNReal) (price extra : ENNReal)
    (hprice : acceptedWeight decoder weight + failMass decoder * price ≤ price) :
    acceptedWeight decoder weight + failMass decoder * (price + extra) ≤ price + extra := by
  rw [mul_add, ← add_assoc]
  apply add_le_add hprice
  simpa only [one_mul] using (mul_le_mul' (failMass_le_one decoder) (le_refl extra))

/-- Cached accepted trials contribute their actual payoff. Unlike the older
label-only cap, this retains every leaf-dependent target-match weight. -/
theorem search_weight_le_fresh_add_cached {β γ : Type} (secret : BitVec 256)
    (inputs : Nat → HashInput) (decoder : HashOutput → Option β)
    (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value, payoff (result counter value) = weight value)
    (price : ENNReal)
    (hprice : acceptedWeight decoder weight + failMass decoder * price ≤ price)
    (bound : Nat)
    (hinj : ∀ left right, left < bound → right < bound → inputs left = inputs right → left = right)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ bound) (cache : RCache) :
    expectedValue (roRun secret
      (publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
      (fun output => output.1.elim 0 payoff) ≤
      price + trialWeight inputs decoder weight bound cache := by
  apply expected_publicSearch_le_of_cached_scores secret inputs decoder result payoff weight hweight
    (price + trialWeight inputs decoder weight bound cache)
    (price_add_cache decoder weight price _ hprice) bound hinj fuel counter hlimit cache
  intro c _ hc answer ha
  have hterm : cacheEntry decoder weight cache (inputs c) ≤
      trialWeight inputs decoder weight bound cache := by
    exact Finset.single_le_sum
      (f := fun i : Fin bound => cacheEntry decoder weight cache (inputs i))
      (fun _ _ => bot_le) (Finset.mem_univ (⟨c, hc⟩ : Fin bound))
  have hscore : (decoder answer).elim 0 weight ≤
      trialWeight inputs decoder weight bound cache := by
    simpa only [cacheEntry, ha, Option.elim_some] using hterm
  exact hscore.trans le_add_self

theorem acceptanceProbability_ne_zero : acceptanceProbability ≠ 0 := by
  rw [DigestCounting.acceptanceProbability_eq_p0]
  norm_num [DigestCounting.p0]

theorem acceptanceProbability_ne_top : acceptanceProbability ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) digest_acceptanceProbability_le_one

noncomputable def freshPrice (weight : HashOutput → ENNReal) : ENNReal :=
  acceptedWeight digestDecode weight / acceptanceProbability

theorem freshPrice_step (weight : HashOutput → ENNReal) :
    acceptedWeight digestDecode weight + failMass digestDecode * freshPrice weight =
      freshPrice weight := by
  have hcancel : acceptanceProbability * freshPrice weight = acceptedWeight digestDecode weight := by
    unfold freshPrice
    rw [div_eq_mul_inv, mul_left_comm,
      ENNReal.mul_inv_cancel acceptanceProbability_ne_zero acceptanceProbability_ne_top, mul_one]
  rw [digest_failMass, ← hcancel, ← add_mul,
    add_tsub_cancel_of_le digest_acceptanceProbability_le_one, one_mul]

theorem digest_weight_le (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (weight : HashOutput → ENNReal) :
    expectedValue (roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => result.1.elim 0 (fun found => weight found.2)) ≤
      freshPrice weight + trialWeight (digestTrial rho message) digestDecode weight fuel cache := by
  rw [digestSearch_public]
  exact search_weight_le_fresh_add_cached secret (digestTrial rho message) digestDecode
    (fun c output => (BitVec.ofNat 32 c, output)) (fun found => weight found.2) weight
    (fun _ _ => rfl) (freshPrice weight) (freshPrice_step weight).le fuel
    (fun _ _ hl hr he => digestTrial_injective rho message (hl.trans_le hlimit) (hr.trans_le hlimit) he)
    fuel 0 (by omega) cache

theorem digest_nonce_trials_injective (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32) :
    Function.Injective (fun point : Digest × Fin fuel => digestTrial point.1 message point.2.val) := by
  intro left right heq
  dsimp only at heq
  have hrho := digestTrial_nonce_injective heq
  apply Prod.ext hrho
  apply Fin.ext
  rw [hrho] at heq
  exact digestTrial_injective right.1 message (left.2.isLt.trans_le hlimit)
    (right.2.isLt.trans_le hlimit) heq

theorem nonce_trialWeight_le (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2^32)
    (cache : RCache) (weight : HashOutput → ENNReal) :
    expectedValue ($ᵗ Digest : ProbComp Digest)
      (fun rho => trialWeight (digestTrial rho message) digestDecode weight fuel cache) ≤
      cacheWeight digestDecode weight cache / (2 : ENNReal)^128 := by
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage trialWeight
  simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  simpa only [tsum_fintype, Fintype.sum_prod_type, cacheWeight] using
    ENNReal.tsum_comp_le_tsum_of_injective (digest_nonce_trials_injective message fuel hlimit)
      (cacheEntry digestDecode weight cache)

/-- Exact fresh accepted-draw price plus a weighted cache-reuse term, for any
leaf-sensitive payoff, under the source's actual uniform nonce and search. -/
theorem uniform_nonce_digest_weight_le (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2^32) (cache : RCache) (weight : HashOutput → ENNReal) :
    expectedValue (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
      roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => result.1.elim 0 (fun found => weight found.2)) ≤
      freshPrice weight + cacheWeight digestDecode weight cache / (2 : ENNReal)^128 := by
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => freshPrice weight + trialWeight (digestTrial rho message) digestDecode weight fuel cache) :=
      expectedValue_mono _ (fun rho => digest_weight_le secret rho message fuel hlimit cache weight)
    _ = freshPrice weight + expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => trialWeight (digestTrial rho message) digestDecode weight fuel cache) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
    _ ≤ _ := add_le_add le_rfl (nonce_trialWeight_le message fuel hlimit cache weight)

end SigGolfCandidate.T3.Sampling.WeightedSelection
