import SigGolfCandidate.T3.BPORS
import SigGolfCandidate.T3.Gate6.BPORSPrefix

section

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
  norm_num [DigestCounting.p0, SigGolfResearch.Gate6.Budget.p0]
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
end

section

namespace SigGolfCandidate.T3.Security.LazyPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem payloadForNonce_weight_le (cache : T3.Cache) (rho : Digest) (message : Message)
    (state : State) (weight : HashOutput → ENNReal) :
    expectedValue (run (payloadRecordForNonce cache rho message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
        (fun result => result.1.elim 0 (fun found => weight found.2)) := by
  rw [payloadRecordForNonce, run_bind, expectedValue_bind, run_digestSearch, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [run_bind, expectedValue_bind, run_pure, expectedValue_pure, Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem payload_weight_le (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message)) = none) (weight : HashOutput → ENNReal) :
    expectedValue (run (payloadRecord cache message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      freshPrice weight + cacheWeight Sampling.digestDecode weight state.2 / (2 : ENNReal)^128 := by
  rw [payloadRecord, run_bind, run_privateNonce_fresh message state hfresh]
  simp only [bind_assoc, pure_bind, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
        expectedValue (Sampling.roRun 0
          (digestSearch (output.extractLsb' 0 128) message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2))) :=
      expectedValue_mono _ fun output => payloadForNonce_weight_le cache _ message
        (state.1.cacheQuery (.inr (.inl message)) output, state.2) weight
    _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2))) :=
      uniform_hash_low_expectation (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2)))
    _ ≤ _ := by
      rw [← expectedValue_bind]
      exact uniform_nonce_digest_weight_le 0 message attemptLimit (by decide) state.2 weight
theorem signing_weight_le (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message)) = none) (weight : HashOutput → ENNReal) :
    expectedValue (run (signingRecord cache message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      freshPrice weight + cacheWeight Sampling.digestDecode weight state.2 / (2 : ENNReal)^128 := by
  rw [signingRecord, run_bind, expectedValue_bind]
  apply expectedValue_le_of_support
  intro result hresult
  have hp := privateMac_preserves_nonce cache.region message state result hresult
  split_ifs with htag
  · simp only [run_pure, expectedValue_pure, Option.elim_none]
    exact bot_le
  · have h := payload_weight_le cache message result.2 (hp.1.trans hfresh) weight
    rw [hp.2] at h
    exact h
end SigGolfCandidate.T3.Security.LazyPrivate
end

section

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
noncomputable def score (values : Source → Value) (target : Target → Value) : ENNReal :=
  ∑ embedding : Target ↪ Source,
    if (fun slot => values (embedding slot)) = target then 1 else 0
theorem score_card (values : Source → Value) (target : Target → Value) :
    score values target =
      (Fintype.card {embedding : Target ↪ Source //
        (fun slot => values (embedding slot)) = target} : ENNReal) := by
  classical
  simp [score, Fintype.card_subtype]
theorem one_le_score (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) (hcovered : ∀ slot, ∃ source, values source = target slot) :
    1 ≤ score values target := by
  classical
  choose chosen hchosen using hcovered
  let embedding : Target ↪ Source := ⟨chosen, fun first second heq =>
    hinj ((hchosen first).symm.trans ((congrArg values heq).trans (hchosen second)))⟩
  have hmatch : (fun slot => values (embedding slot)) = target := funext hchosen
  have h := Finset.single_le_sum
    (f := fun e : Target ↪ Source =>
      if (fun slot => values (e slot)) = target then (1 : ENNReal) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ embedding)
  simpa only [hmatch, if_true, score] using h
theorem average_score (values : Source → Value) :
    finiteAverage (fun target : Target → Value => score values target) =
      ((Fintype.card Source).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal) ^ Fintype.card Target := by
  classical
  unfold finiteAverage score
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fun, Nat.cast_pow]
noncomputable def matchingEquiv (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) :
    {embedding : Target ↪ Source // (fun slot => values (embedding slot)) = target} ≃
      (∀ slot : Target, {source : Source // values source = target slot}) where
  toFun embedding slot := ⟨embedding.val slot, congrFun embedding.property slot⟩
  invFun choices := ⟨⟨fun slot => (choices slot).val,
    fun first second heq => hinj ((choices first).property.symm.trans
      ((congrArg values heq).trans (choices second).property))⟩,
    funext (fun slot => (choices slot).property)⟩
  left_inv embedding := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    rfl
  right_inv choices := by
    funext slot
    rfl
theorem score_eq_fibers (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) :
    score values target =
      ∏ slot, (Fintype.card {source : Source // values source = target slot} : ENNReal) := by
  rw [score_card, Fintype.card_congr (matchingEquiv values target hinj),
    Fintype.card_pi, Nat.cast_prod]
def fiberSumEquiv (oldValues : Source → Value) (newValues : New → Value) (value : Value) :
    {source : Source ⊕ New // Sum.elim oldValues newValues source = value} ≃
      ({source : Source // oldValues source = value} ⊕
        {source : New // newValues source = value}) where
  toFun source := match source with
    | ⟨.inl source, h⟩ => .inl ⟨source, h⟩
    | ⟨.inr source, h⟩ => .inr ⟨source, h⟩
  invFun source := match source with
    | .inl source => ⟨.inl source.val, source.property⟩
    | .inr source => ⟨.inr source.val, source.property⟩
  left_inv source := by rcases source with ⟨source, h⟩; cases source <;> rfl
  right_inv source := by cases source <;> rfl
theorem fiber_card_sum (oldValues : Source → Value) (newValues : New → Value) (value : Value) :
    (Fintype.card {source : Source ⊕ New // Sum.elim oldValues newValues source = value} : ENNReal) =
      (Fintype.card {source : Source // oldValues source = value} : ENNReal) +
        (Fintype.card {source : New // newValues source = value} : ENNReal) := by
  rw [Fintype.card_congr (fiberSumEquiv oldValues newValues value), Fintype.card_sum, Nat.cast_add]
theorem score_sum (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) (hinj : Function.Injective target) :
    score (Sum.elim oldValues newValues) target =
      ∑ selected : Finset Target,
        score oldValues (fun slot : selected => target slot.val) *
          score newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) := by
  classical
  rw [score_eq_fibers _ _ hinj]
  simp_rw [fiber_card_sum]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro selected _
  have hold : Function.Injective (fun slot : selected => target slot.val) :=
    fun first second h => Subtype.ext (hinj h)
  have hnew : Function.Injective (fun slot : (selectedᶜ : Finset Target) => target slot.val) :=
    fun first second h => Subtype.ext (hinj h)
  rw [score_eq_fibers oldValues (fun slot : selected => target slot.val) hold,
    score_eq_fibers newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) hnew]
  exact congrArg₂ (fun a b : ENNReal => a * b)
    (Finset.prod_coe_sort selected
      (fun slot => (Fintype.card {source : Source // oldValues source = target slot} : ENNReal))).symm
    (Finset.prod_coe_sort (selectedᶜ : Finset Target)
      (fun slot => (Fintype.card {source : New // newValues source = target slot} : ENNReal))).symm
theorem three_opening_average (records : Nat) (values : Fin records × Fin 3 → Fin 128) :
    finiteAverage (fun target : Fin 3 → Fin 128 => score values target) =
      ((3 * records).descFactorial 3 : ENNReal) / (128 : ENNReal)^3 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, Nat.cast_ofNat] using
    (average_score (Target := Fin 3) values)
theorem two_opening_average (records : Nat) (values : Fin records × Fin 3 → Fin 128) :
    finiteAverage (fun target : Fin 2 → Fin 128 => score values target) =
      ((3 * records).descFactorial 2 : ENNReal) / (128 : ENNReal)^2 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, Nat.cast_ofNat] using
    (average_score (Target := Fin 2) values)
end SigGolfCandidate.T3.BPORS.InjectiveCover
end

section

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
abbrev SplitEmbedding := Σ selected : Finset Target,
  (selected ↪ Source) × ((selectedᶜ : Finset Target) ↪ New)
noncomputable def oldSlots (embedding : Target ↪ Source ⊕ New) : Finset Target :=
  Finset.univ.filter fun slot => (embedding slot).isLeft
theorem mem_oldSlots (embedding : Target ↪ Source ⊕ New) (slot : Target) :
    slot ∈ oldSlots embedding ↔ (embedding slot).isLeft := by simp [oldSlots]
noncomputable def splitOld (embedding : Target ↪ Source ⊕ New) : oldSlots embedding ↪ Source where
  toFun slot := (embedding slot.val).getLeft ((mem_oldSlots embedding slot.val).mp slot.property)
  inj' := by
    intro first second h
    apply Subtype.ext
    apply embedding.injective
    have he := congrArg (Sum.inl (β := New)) h
    simpa only [Sum.inl_getLeft] using he
noncomputable def splitNew (embedding : Target ↪ Source ⊕ New) :
    ((oldSlots embedding)ᶜ : Finset Target) ↪ New where
  toFun slot := (embedding slot.val).getRight (Sum.not_isLeft.mp
    (fun h => (Finset.mem_compl.mp slot.property) ((mem_oldSlots embedding slot.val).mpr h)))
  inj' := by
    intro first second h
    apply Subtype.ext
    apply embedding.injective
    have he := congrArg (Sum.inr (α := Source)) h
    simpa only [Sum.inr_getRight] using he
noncomputable def splitEmbedding (embedding : Target ↪ Source ⊕ New) :
    SplitEmbedding (Target := Target) (Source := Source) (New := New) :=
  ⟨oldSlots embedding, splitOld embedding, splitNew embedding⟩
noncomputable def mergeEmbedding (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    Target ↪ Source ⊕ New where
  toFun slot := if h : slot ∈ parts.1 then .inl (parts.2.1 ⟨slot, h⟩)
    else .inr (parts.2.2 ⟨slot, Finset.mem_compl.mpr h⟩)
  inj' := by
    intro first second heq
    dsimp only at heq
    split_ifs at heq with hfirst hsecond hsecond
    · exact congrArg Subtype.val (parts.2.1.injective (Sum.inl.inj heq))
    · exact congrArg Subtype.val (parts.2.2.injective (Sum.inr.inj heq))
theorem oldSlots_merge (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    oldSlots (mergeEmbedding parts) = parts.1 := by
  ext slot
  by_cases h : slot ∈ parts.1 <;> simp [oldSlots, mergeEmbedding, h]
theorem merge_split (embedding : Target ↪ Source ⊕ New) :
    mergeEmbedding (splitEmbedding embedding) = embedding := by
  apply Function.Embedding.ext
  intro slot
  by_cases h : slot ∈ oldSlots embedding
  · simp only [mergeEmbedding, splitEmbedding, Function.Embedding.coeFn_mk, h,
      dite_true, splitOld, Sum.inl_getLeft]
  · simp only [mergeEmbedding, splitEmbedding, Function.Embedding.coeFn_mk, h,
      dite_false, splitNew, Sum.inr_getRight]
theorem merge_injective : Function.Injective
    (mergeEmbedding (Target := Target) (Source := Source) (New := New)) := by
  rintro ⟨left, oldLeft, newLeft⟩ ⟨right, oldRight, newRight⟩ heq
  have hsets : left = right := by
    have h := congrArg oldSlots heq
    simpa only [oldSlots_merge] using h
  subst right
  have hold : oldLeft = oldRight := by
    apply Function.Embedding.ext
    intro slot
    have h := congrArg (fun e : Target ↪ Source ⊕ New => e slot.val) heq
    simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, slot.property, dite_true,
      Sum.inl.injEq] using h
  have hnew : newLeft = newRight := by
    apply Function.Embedding.ext
    intro slot
    have h := congrArg (fun e : Target ↪ Source ⊕ New => e slot.val) heq
    simpa only [mergeEmbedding, Function.Embedding.coeFn_mk,
      Finset.mem_compl.mp slot.property, dite_false, Sum.inr.injEq] using h
  subst oldRight
  subst newRight
  rfl
noncomputable def sumEmbeddingEquiv :
    SplitEmbedding (Target := Target) (Source := Source) (New := New) ≃
      (Target ↪ Source ⊕ New) :=
  Equiv.ofBijective mergeEmbedding ⟨merge_injective, fun embedding =>
    ⟨splitEmbedding embedding, merge_split embedding⟩⟩
theorem merge_matches (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value)
    (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    (fun slot => Sum.elim oldValues newValues (mergeEmbedding parts slot)) = target ↔
      ((fun slot : parts.1 => oldValues (parts.2.1 slot)) = (fun slot => target slot.val) ∧
       (fun slot : (parts.1ᶜ : Finset Target) => newValues (parts.2.2 slot)) =
         (fun slot => target slot.val)) := by
  constructor
  · intro h
    constructor
    · funext slot
      have heq := congrFun h slot.val
      simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, slot.property, dite_true,
        Sum.elim_inl] using heq
    · funext slot
      have heq := congrFun h slot.val
      simpa only [mergeEmbedding, Function.Embedding.coeFn_mk,
        Finset.mem_compl.mp slot.property, dite_false, Sum.elim_inr] using heq
  · rintro ⟨hold, hnew⟩
    funext slot
    by_cases h : slot ∈ parts.1
    · simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, h, dite_true, Sum.elim_inl] using
        congrFun hold ⟨slot, h⟩
    · simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, h, dite_false, Sum.elim_inr] using
        congrFun hnew ⟨slot, Finset.mem_compl.mpr h⟩
theorem score_sum_all (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score (Sum.elim oldValues newValues) target =
      ∑ selected : Finset Target,
        score oldValues (fun slot : selected => target slot.val) *
          score newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) := by
  classical
  rw [score, ← (sumEmbeddingEquiv (Target := Target) (Source := Source) (New := New)).sum_comp]
  change (∑ parts : SplitEmbedding (Target := Target) (Source := Source) (New := New),
    if (fun slot => Sum.elim oldValues newValues (mergeEmbedding parts slot)) = target then
      (1 : ENNReal) else 0) = _
  simp_rw [merge_matches]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, score, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro old _
  apply Finset.sum_congr rfl
  intro fresh _
  split_ifs <;> simp_all
end SigGolfCandidate.T3.BPORS.InjectiveCover
end

section

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]
theorem score_source_le (embed : Source ↪ New) (oldValues : Source → Value)
    (newValues : New → Value) (target : Target → Value)
    (hvalues : ∀ source, newValues (embed source) = oldValues source) :
    score oldValues target ≤ score newValues target := by
  classical
  let liftMatch :
      {e : Target ↪ Source // (fun slot => oldValues (e slot)) = target} →
      {e : Target ↪ New // (fun slot => newValues (e slot)) = target} := fun e =>
    ⟨e.val.trans embed, funext (fun slot => (hvalues (e.val slot)).trans (congrFun e.property slot))⟩
  have hinj : Function.Injective liftMatch := by
    intro first second h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    apply embed.injective
    exact congrArg (fun e => e.val slot) h
  rw [score_card, score_card]
  exact_mod_cast Fintype.card_le_of_injective liftMatch hinj
theorem score_append_mono (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score oldValues target ≤ score (Sum.elim oldValues newValues) target :=
  score_source_le Function.Embedding.inl oldValues (Sum.elim oldValues newValues) target (fun _ => rfl)
theorem score_ne_top (values : Source → Value) (target : Target → Value) :
    score values target ≠ ⊤ := by
  rw [score_card]
  exact ENNReal.natCast_ne_top _
noncomputable def increment (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) : ENNReal :=
  score (Sum.elim oldValues newValues) target - score oldValues target
theorem before_add_increment (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score oldValues target + increment oldValues newValues target =
      score (Sum.elim oldValues newValues) target :=
  add_tsub_cancel_of_le (score_append_mono oldValues newValues target)
theorem finiteAverage_add {A : Type} [Fintype A] (first second : A → ENNReal) :
    finiteAverage (fun x => first x + second x) = finiteAverage first + finiteAverage second := by
  simp only [finiteAverage, Finset.sum_add_distrib, div_eq_mul_inv, add_mul]
theorem average_increment [Nonempty Value] (oldValues : Source → Value)
    (newValues : New → Value) :
    finiteAverage (fun target : Target → Value => increment oldValues newValues target) =
      (((Fintype.card Source + Fintype.card New).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal)^Fintype.card Target) -
      (((Fintype.card Source).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal)^Fintype.card Target) := by
  have hsum : finiteAverage (fun target : Target → Value => score oldValues target) +
      finiteAverage (fun target : Target → Value => increment oldValues newValues target) =
        finiteAverage (fun target : Target → Value => score (Sum.elim oldValues newValues) target) := by
    rw [← finiteAverage_add]
    congr 1
    funext target
    exact before_add_increment oldValues newValues target
  have hcard : (Fintype.card Value : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfinite : finiteAverage (fun target : Target → Value => score oldValues target) ≠ ⊤ := by
    rw [average_score]
    exact ENNReal.div_ne_top (by finiteness) (pow_ne_zero _ hcard)
  have heq := congrArg (fun value => value -
      finiteAverage (fun target : Target → Value => score oldValues target)) hsum
  rw [ENNReal.add_sub_cancel_left hfinite] at heq
  simpa only [average_score, Fintype.card_sum] using heq
noncomputable def selectionGain (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (output : HashOutput) : ENNReal :=
  if eligible output then increment oldValues (newValues output) target else 0
noncomputable def afterSelection (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (selected : Option HashOutput) : ENNReal :=
  selected.elim (score oldValues target) (fun output =>
    if eligible output then score (Sum.elim oldValues (newValues output)) target
    else score oldValues target)
theorem afterSelection_eq (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (selected : Option HashOutput) :
    afterSelection oldValues newValues target eligible selected =
      score oldValues target + selected.elim 0 (selectionGain oldValues newValues target eligible) := by
  cases selected with
  | none => simp only [afterSelection, Option.elim_none, add_zero]
  | some output =>
      simp only [afterSelection, selectionGain, Option.elim_some]
      cases h : eligible output with
      | false => simp only [h, Bool.false_eq_true, if_false, add_zero]
      | true =>
          simp only [h, if_true]
          exact (before_add_increment oldValues (newValues output) target).symm
theorem signing_update_le (cache : T3.Cache) (message : Message)
    (state : Security.LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl message)) = none)
    (oldValues : Source → Value) (newValues : HashOutput → New → Value)
    (target : Target → Value) (eligible : HashOutput → Bool) :
    expectedValue (Security.LazyPrivate.run (Security.signingRecord cache message) state)
      (fun result => afterSelection oldValues newValues target eligible result.1.2) ≤
      score oldValues target +
        (freshPrice (selectionGain oldValues newValues target eligible) +
          cacheWeight Sampling.digestDecode (selectionGain oldValues newValues target eligible) state.2 /
            (2 : ENNReal)^128) := by
  simp_rw [afterSelection_eq]
  rw [expectedValue_add]
  apply add_le_add
  · exact expectedValue_le_of_le _ (fun _ => le_rfl)
  · exact Security.LazyPrivate.signing_weight_le cache message state hfresh
      (selectionGain oldValues newValues target eligible)
end SigGolfCandidate.T3.BPORS.InjectiveCover
end

section

namespace SigGolfCandidate.T3.DigestSampling
open OracleComp ENNReal
open SigGolfResearch.Gate6
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
def rawRecordViewEquiv : RawRecord ≃ RawView × (Padding × Unused) where
  toFun r := ((r.1.1,fun c => (r.1.2 c,r.2.1 c)),r.2.2)
  invFun r := ((r.1.1,fun c => (r.1.2 c).1),(fun c => (r.1.2 c).2,r.2))
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def gateCoordinatesEquiv : HashOutput ≃ RawView × (Padding × Unused) :=
  (Equiv.ofBijective digestRecord digestRecord_bijective).trans rawRecordViewEquiv
theorem gateCoordinates_view (output : HashOutput) :
    (gateCoordinatesEquiv output).1=rawView output := rfl
theorem gateCoordinates_gate (output : HashOutput) :
    digestGate output=true ↔ (gateCoordinatesEquiv output).2.1=0 := by
  change digestGate output=true ↔ (digestRecord output).2.2.1=0
  rw [digestGate,decide_eq_true_eq,digestRecord_gate_zero]
theorem finiteAverage_div {α : Type} [Fintype α] (f : α → ENNReal) (d : ENNReal) :
    BPORS.finiteAverage (fun x => f x/d)=BPORS.finiteAverage f/d := by
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring
theorem average_gate_weight (payoff : RawView → ENNReal) :
    BPORS.finiteAverage (fun output : HashOutput =>
      if digestGate output=true then payoff (rawView output) else 0)=
        BPORS.finiteAverage payoff/8 := by
  have he (output : HashOutput) :
      (if digestGate output=true then payoff (rawView output) else 0)=
        (if (gateCoordinatesEquiv output).2.1=0 then payoff (gateCoordinatesEquiv output).1 else 0) := by
    simp only [gateCoordinates_view,gateCoordinates_gate]
  simp_rw [he]
  rw [BPORS.finiteAverage_equiv gateCoordinatesEquiv
    (fun p => if p.2.1=0 then payoff p.1 else 0),BPORS.finiteAverage_pair]
  have hi (view : RawView) : BPORS.finiteAverage
      (fun suffix : Padding × Unused => if suffix.1=0 then payoff view else 0)=payoff view/8 := by
    rw [BPORS.finiteAverage_pair]
    change BPORS.finiteAverage (fun gate : Padding =>
      BPORS.finiteAverage (fun _ : Unused => if gate=0 then payoff view else 0))=_
    simp_rw [BPORS.History.finiteAverage_constant]
    unfold BPORS.finiteAverage
    simp [Padding]
  simp_rw [hi]
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro view _
  ring
end SigGolfCandidate.T3.DigestSampling
end

section


namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def outIdx (x : HashOutput) : Fin (2 ^ 31) := (rawView x).1
def outBucket (x : HashOutput) (c : Fin 7) : Fin 16 := ((rawView x).2 c).1
def outLeaves (x : HashOutput) (c : Fin 7) : Fin 3 → Fin 128 := ((rawView x).2 c).2
def label (x : HashOutput) : BPORS.History.Proposal := (outIdx x, fun c => outBucket x c)
def labels (X : List HashOutput) : List BPORS.History.Proposal := X.map label
theorem labels_append (X Y : List HashOutput) : labels (X ++ Y) = labels X ++ labels Y := List.map_append
abbrev Slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Type :=
  {s : Fin X.length × Fin 3 // outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b}
def slotValue (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) (s : Slot X i c b) : Fin 128 :=
  outLeaves (X.get s.1.1) c s.1.2
noncomputable def coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : ENNReal :=
  BPORS.InjectiveCover.score (slotValue X i c b) target
noncomputable def score (X : List HashOutput) (N : HashOutput) : ENNReal :=
  if digestGate N=true then
    ∏ c : Fin 7, coordScore X (outIdx N) c (outBucket N c) (outLeaves N c) else 0
def CoordCovered (X : List HashOutput) (N : HashOutput) (c : Fin 7) : Prop :=
  ∀ j, ∃ s : Slot X (outIdx N) c (outBucket N c), slotValue X (outIdx N) c (outBucket N c) s = outLeaves N c j
theorem one_le_score (X : List HashOutput) (N : HashOutput)
    (hinj : ∀ c, Function.Injective (outLeaves N c)) (hgate : digestGate N=true)
    (hcov : ∀ c, CoordCovered X N c) : 1 ≤ score X N := by
  simp only [score,hgate,if_true]
  apply Finset.one_le_prod''
  intro c
  exact BPORS.InjectiveCover.one_le_score _ _ (hinj c) (hcov c)
def slotEmbed (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Slot X i c b ↪ Slot (X ++ Y) i c b where
  toFun s := ⟨(Fin.castLE (by simp) s.1.1, s.1.2), by
    have h := s.2
    simp only [List.get_eq_getElem, Fin.val_castLE] at h ⊢
    rw [List.getElem_append_left s.1.1.isLt]
    exact h⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    have h1 := congrArg (fun u : Slot (X ++ Y) i c b => u.1) h
    simp only [Prod.mk.injEq] at h1
    exact Prod.ext (Fin.castLE_injective _ h1.1) h1.2
theorem coordScore_append_mono (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) : coordScore X i c b target ≤ coordScore (X ++ Y) i c b target := by
  unfold coordScore
  apply BPORS.InjectiveCover.score_source_le (slotEmbed X Y i c b)
  intro s
  simp only [slotValue, slotEmbed, Function.Embedding.coeFn_mk, List.get_eq_getElem, Fin.val_castLE]
  rw [List.getElem_append_left s.1.1.isLt]
theorem score_append_mono (X Y : List HashOutput) (N : HashOutput) : score X N ≤ score (X ++ Y) N := by
  unfold score
  split_ifs with hg
  · exact Finset.prod_le_prod' fun c _ => coordScore_append_mono X Y _ c _ _
  · exact le_rfl
noncomputable def hits (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) : Nat :=
  (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b).card
theorem card_slot (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    Fintype.card (Slot X i c b) = 3 * hits X i c b := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter fun s : Fin X.length × Fin 3 =>
      outIdx (X.get s.1) = i ∧ outBucket (X.get s.1) c = b) =
      (Finset.univ.filter fun k : Fin X.length => outIdx (X.get k) = i ∧ outBucket (X.get k) c = b) ×ˢ
        (Finset.univ : Finset (Fin 3)) := by
    ext s
    simp
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, hits, Nat.mul_comm]
theorem hits_eq_count (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    hits X i c b = ((BPORS.History.atIndex i (labels X)).map fun row => row c).count b := by
  induction X with
  | nil => simp [hits, labels, BPORS.History.atIndex]
  | cons x X ih =>
      have hsplit : hits (x :: X) i c b =
          (if outIdx x = i ∧ outBucket x c = b then 1 else 0) + hits X i c b := by
        unfold hits
        rw [Finset.card_filter, Finset.card_filter]
        exact Fin.sum_univ_succ (n := X.length) _
      rw [hsplit, ih]
      simp only [labels, List.map_cons, BPORS.History.atIndex_cons, label]
      by_cases hi : outIdx x = i
      · simp only [hi, if_true, true_and, List.map_cons, List.count_cons]
        by_cases hb : outBucket x c = b
        · simp [hb, Nat.add_comm]
        · simp [hb]
      · simp [hi]
theorem average_coordScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) :
    BPORS.finiteAverage (fun target : Fin 3 → Fin 128 => coordScore X i c b target) =
      BPORS.bucketMass ((BPORS.History.atIndex i (labels X)).map fun row => row c) b / 128 ^ 3 := by
  unfold coordScore
  rw [BPORS.InjectiveCover.average_score, card_slot, hits_eq_count, BPORS.bucketMass]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
theorem average_coordinate (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) :
    BPORS.finiteAverage (fun d : Fin 16 × (Fin 3 → Fin 128) => coordScore X i c d.1 d.2) =
      BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) / 128 ^ 3 := by
  rw [BPORS.finiteAverage_pair]
  simp_rw [average_coordScore]
  unfold BPORS.finiteAverage BPORS.coordinateEnvelope
  simp only [Fintype.card_fin, Nat.cast_ofNat, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring
theorem average_at_index (X : List HashOutput) (i : Fin (2 ^ 31)) :
    BPORS.finiteAverage (fun v : Fin 7 → Fin 16 × (Fin 3 → Fin 128) =>
        ∏ c : Fin 7, coordScore X i c (v c).1 (v c).2)/8 =
      BPORS.History.wordEnvelope (BPORS.History.atIndex i (labels X)) := by
  rw [BPORS.finiteAverage_product 7
    (fun c (d : Fin 16 × (Fin 3 → Fin 128)) => coordScore X i c d.1 d.2)]
  simp_rw [average_coordinate]
  unfold BPORS.History.wordEnvelope
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv]
theorem average_score (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => score X N) = BPORS.History.fullPrice (labels X) / 2 ^ 128 := by
  change BPORS.finiteAverage (fun N : HashOutput => if digestGate N=true then
    (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2) (rawView N) else 0)=_
  rw [average_gate_weight (fun p : RawView => ∏ c : Fin 7, coordScore X p.1 c (p.2 c).1 (p.2 c).2),
    BPORS.finiteAverage_pair,←finiteAverage_div]
  simp_rw [average_at_index]
  unfold BPORS.finiteAverage BPORS.History.fullPrice
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (2 ^ 97 : ENNReal), mul_assoc]
  congr 1
  rw [show (2 : ENNReal) ^ 128 = 2 ^ 97 * 2 ^ 31 by rw [← pow_add]]
  rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
end SigGolfCandidate.T3.Security.CaseC
end
