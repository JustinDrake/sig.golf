import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessagePrehit
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeUniform
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedDigestRate
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeWeightedOriginRace
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FreshDigestHazard
import SigGolfCandidate.SphincsSecurity.Proof.Fts.RawSigningMomentBound

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_4 : SampleableType Randomness := Concrete.randomnessSampleableType
theorem uniform_randomness_messageInput_cacheHit_eq_count
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Pr[fun randomness : Randomness => ∃ output,
      cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output |
      ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSet cache key.parameter key.root message
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2), ⟨randomness.1, rfl⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, hcached, randomness, hinput⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCount cache key.parameter key.root message := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCount, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]
noncomputable def messageInputMissProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun randomness : Randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none | ($ᵗ Randomness : ProbComp Randomness)]
theorem messageInputMissProbability_eq_count (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageInputMissProbability key message cache =
      1 - cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let miss : Randomness → Prop := fun randomness => cache (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness)) = none
  have hnot : Pr[fun randomness => ¬ miss randomness | ($ᵗ Randomness : ProbComp Randomness)] =
      cachedMessageEntryCount cache key.parameter key.root message * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    apply Eq.trans ?_ (uniform_randomness_messageInput_cacheHit_eq_count key message cache)
    apply probEvent_congr'
    · intro randomness _
      exact Option.ne_none_iff_exists'
    · rfl
  have h := probEvent_compl ($ᵗ Randomness : ProbComp Randomness) miss
  rw [probFailure_of_liftM_PMF, tsub_zero] at h
  have heq := ENNReal.eq_sub_of_add_eq probEvent_ne_top h
  rw [hnot] at heq
  exact heq
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem cachedMessageEntryCount_cacheQuery_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (input : HashInput) (output : HashOutput) :
    cachedMessageEntryCount (cache.cacheQuery input output) parameter root message ≤
      cachedMessageEntryCount cache parameter root message + 1 := by
  have hsubset : cachedMessageInputSet (cache.cacheQuery input output) parameter root message ⊆
      insert ⟨input, output⟩ (cachedMessageInputSet cache parameter root message) := by
    intro entry hentry
    rcases QueryCache.toSet_cacheQuery_subset_insert cache input output hentry.1 with heq | hold
    · exact Or.inl heq
    · exact Or.inr ⟨hold, hentry.2⟩
  exact (ENat.toENNReal_mono (Set.encard_le_encard hsubset)).trans
    (by simpa only [cachedMessageEntryCount, ENat.toENNReal_add, ENat.toENNReal_one] using
      ENat.toENNReal_mono (Set.encard_insert_le (cachedMessageInputSet cache parameter root message) ⟨input, output⟩))
theorem randomOracle_cachedMessageEntryCount_le (parameter : PublicParameter) (root : Digest) (message : Message)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : result ∈ support ((randomOracle input).run cache)) :
    cachedMessageEntryCount result.2 parameter root message ≤ cachedMessageEntryCount cache parameter root message + 1 := by
  cases hc : cache input with
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact cachedMessageEntryCount_cacheQuery_le parameter root message cache input output
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact le_self_add
namespace Concrete
theorem signAttempt_cachedMessageEntryCount_le (key : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache)) :
    cachedMessageEntryCount result.2 key.parameter key.root message ≤ cachedMessageEntryCount cache key.parameter key.root message + 1 := by
  rw [simulateQ_signAttempt_run_eq, mem_support_bind_iff] at hr
  obtain ⟨oracleResult, horacle, hpure⟩ := hr
  simp only [mem_support_pure_iff] at hpure
  subst result
  exact randomOracle_cachedMessageEntryCount_le key.parameter key.root message
    (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) cache oracleResult horacle
end Concrete
end SphincsSecurity
end

section






namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_6 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop
theorem probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec) (hreference : reference ≤ cache) :
    messageInputMissProbability key message cache * Concrete.admissibleProbability ≤
      Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] := by
  rw [signDigestAttemptPrefix]
  apply mul_le_probEvent_bind
  · exact le_rfl
  · intro randomness _ hmiss
    have hrefMiss : reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none := by
      cases hc : reference (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => rfl
      | some output => simpa only [hmiss, reduceCtorEq] using hreference hc
    rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
      probEvent_bind_pure_comp]
    change Concrete.admissibleProbability ≤
      Pr[fun result => reference (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache]
    simpa only [hrefMiss, true_and] using (probEvent_signAttempt_fresh_success_eq key message randomness cache hmiss).ge
theorem digestAttemptExpectation_mul_message_rate_le_freshSelection
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hreference : reference ≤ cache) (budget rate : ENNReal)
    (hrate : rate ≤ (1 - budget * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * Concrete.admissibleProbability)
    (hbudget : cachedMessageEntryCount cache key.parameter key.root message + (attempts : ENNReal) ≤ budget) :
    digestAttemptExpectation attempts key message cache * rate ≤
      Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
  induction attempts generalizing cache with
  | zero => simp only [digestAttemptExpectation, zero_mul]; exact zero_le
  | succ attempts ih =>
      rw [digestAttemptExpectation, add_mul, one_mul, ← ENNReal.tsum_mul_right, probEvent_signDigestLoop_fresh_recurrence]
      apply add_le_add
      · apply hrate.trans (le_trans ?_ (probEvent_signDigestAttemptPrefix_fresh_ge_messageMiss key message reference cache hreference))
        rw [messageInputMissProbability_eq_count]
        exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (le_self_add.trans hbudget) le_rfl) _) le_rfl
      · apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
        · by_cases hnone : result.2.1 = none
          · rw [if_pos hnone, if_pos hnone, mul_assoc]
            apply mul_le_mul' le_rfl
            apply ih result.2.2 (hreference.trans (signDigestAttemptPrefix_cache_le key message cache result hr))
            have hgrowth := signAttempt_cachedMessageEntryCount_le key message result.1 cache result.2
              (signDigestAttemptPrefix_support_attempt key message cache result hr)
            calc
              _ ≤ (cachedMessageEntryCount cache key.parameter key.root message + 1) + (attempts : ENNReal) :=
                add_le_add hgrowth le_rfl
              _ = cachedMessageEntryCount cache key.parameter key.root message + ((attempts + 1 : Nat) : ENNReal) := by
                push_cast; ring
              _ ≤ _ := hbudget
          · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
        · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]
noncomputable def messageDigestFreshRate (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  (1 - (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
    ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) * Concrete.admissibleProbability
noncomputable def messageDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ / messageDigestFreshRate key message cache
theorem messageDigestFreshRate_ge_budget (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    (1 - ((q + digestAttemptLimit : Nat) : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      Concrete.admissibleProbability ≤ messageDigestFreshRate key message cache := by
  unfold messageDigestFreshRate
  rw [Nat.cast_add]
  exact mul_le_mul' (tsub_le_tsub_left (mul_le_mul' (add_le_add
    ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl) le_rfl) _) le_rfl
theorem messageDigestFreshRate_ne_zero (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache ≠ 0 := by
  apply ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ?_) (messageDigestFreshRate_ge_budget key message cache q hcache))
  apply digestRaceSuccessRate_ne_zero_of_budget_lt
  norm_num [digestAttemptLimit, randomnessBits] at *
  omega
theorem messageDigestFreshRate_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    messageDigestFreshRate key message cache ≠ ⊤ := by
  unfold messageDigestFreshRate
  exact ENNReal.mul_ne_top (by finiteness) admissibleProbability_ne_top
theorem messageDigestReuseWeight_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≤ digestReuseWeight q :=
  ENNReal.div_le_div_left (messageDigestFreshRate_ge_budget key message cache q hcache) _
theorem messageDigestReuseWeight_ne_top (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestReuseWeight key message cache ≠ ⊤ :=
  ne_top_of_le_ne_top (digestReuseWeight_ne_top q hq) (messageDigestReuseWeight_le key message cache q hcache)
theorem exactDigestReuseWeight_le_fresh_mul_messageReuseWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache := by
  have hcancel : messageDigestFreshRate key message cache * messageDigestReuseWeight key message cache =
      ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
    unfold messageDigestReuseWeight
    rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel
      (messageDigestFreshRate_ne_zero key message cache q hq hcache) (messageDigestFreshRate_ne_top key message cache), mul_one]
  have h := mul_le_mul' (digestAttemptExpectation_mul_message_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
    (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal))
    (messageDigestFreshRate key message cache) le_rfl le_rfl) (le_refl (messageDigestReuseWeight key message cache))
  rw [mul_assoc, hcancel] at h
  exact h
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def normalizedMessageReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  messageDigestReuseWeight key message cache /
    (1 + cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * messageDigestReuseWeight key message cache)
theorem normalizedMessageReuseWeight_eq_inv (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache =
      (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) +
        messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))⁻¹ := by
  let count := cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
  let reuse := messageDigestReuseWeight key message cache
  have hreuseTop : reuse ≠ ⊤ := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hreuseZero : reuse ≠ 0 := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (by finiteness))
      (ENNReal.inv_ne_zero.mpr (messageDigestFreshRate_ne_top key message cache))
  have hinv : reuse⁻¹ = messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) := by
    unfold reuse messageDigestReuseWeight
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (by finiteness)))
      (Or.inl (ENNReal.inv_ne_top.mpr (by positivity))), inv_inv, inv_inv, mul_comm]
  have hfactor : 1 + count * reuse = reuse * (count + reuse⁻¹) := by
    rw [mul_add, ENNReal.mul_inv_cancel hreuseZero hreuseTop]
    ring
  change reuse * (1 + count * reuse)⁻¹ = _
  rw [hfactor, ENNReal.mul_inv (Or.inl hreuseZero) (Or.inl hreuseTop), ← mul_assoc,
    ENNReal.mul_inv_cancel hreuseZero hreuseTop, one_mul, hinv]
theorem exactDigestReuseWeight_le_normalizedMessage (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    exactDigestReuseWeight key message cache ≤ normalizedMessageReuseWeight key message cache := by
  have hcount : cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness)
      ((cachedMessageEntryCountWhere_le_enncard cache key.parameter key.root message (fun _ => True)).trans hcache)
  have hreuse := messageDigestReuseWeight_ne_top key message cache q hq hcache
  have hmass : freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache ≤ 1 :=
    le_self_add.trans_eq (freshSelection_add_count_exactWeight_add_exhaustion key message cache)
  unfold normalizedMessageReuseWeight
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ = exactDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by ring
    _ ≤ freshDigestSelectionProbability key message cache * messageDigestReuseWeight key message cache +
        (cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache :=
      add_le_add (exactDigestReuseWeight_le_fresh_mul_messageReuseWeight key message cache q hq hcache) le_rfl
    _ = (freshDigestSelectionProbability key message cache +
        cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache) *
          messageDigestReuseWeight key message cache := by rw [add_mul]
    _ ≤ _ := mul_le_of_le_one_left' hmass
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def messageAdmissibleDeficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  cachedMessageEntryCount cache key.parameter key.root message * admissibleProbability -
    cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True)
theorem messageDigestFreshRate_balance (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal) +
      (cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)) *
        admissibleProbability = ((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability := by
  let count := cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal)
  let space : ENNReal := (2 ^ randomnessBits : Nat)
  let admissible : ENNReal := admissibleProbability
  have hcount : count ≤ space := by
    apply (add_le_add ((cachedMessageEntryCount_le_enncard cache key.parameter key.root message).trans hcache) le_rfl).trans
    change (q : ENNReal) + (digestAttemptLimit : ENNReal) ≤ ((2 ^ randomnessBits : Nat) : ENNReal)
    rw [← Nat.cast_add]
    exact_mod_cast (show q + digestAttemptLimit ≤ 2 ^ randomnessBits by norm_num [digestAttemptLimit, randomnessBits] at *; omega)
  have hzero : space ≠ 0 := by dsimp only [space]; positivity
  have htop : space ≠ ⊤ := by dsimp only [space]; finiteness
  have hfraction : count * space⁻¹ ≤ 1 :=
    (mul_le_mul' hcount le_rfl).trans_eq (ENNReal.mul_inv_cancel hzero htop)
  have hcancel : (count * space⁻¹) * (space * admissible) = count * admissible := by
    rw [mul_assoc, ← mul_assoc space⁻¹, ENNReal.inv_mul_cancel hzero htop, one_mul]
  change ((1 - count * space⁻¹) * admissible) * space + count * admissible = _
  calc
    _ = ((1 - count * space⁻¹) + count * space⁻¹) * (space * admissible) := by rw [← hcancel]; ring
    _ = space * admissible := by rw [tsub_add_cancel_of_le hfraction, one_mul]
theorem normalizedMessageReuseWeight_le_deficit (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q) :
    normalizedMessageReuseWeight key message cache ≤
      ((((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability) - ((digestAttemptLimit : ENNReal) * admissibleProbability +
        messageAdmissibleDeficit key message cache))⁻¹ := by
  rw [normalizedMessageReuseWeight_eq_inv key message cache q hq hcache]
  apply ENNReal.inv_le_inv.mpr
  apply tsub_le_iff_left.mpr
  rw [← messageDigestFreshRate_balance key message cache q hq hcache, add_mul]
  have hcount : cachedMessageEntryCount cache key.parameter key.root message * admissibleProbability ≤
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) + messageAdmissibleDeficit key message cache :=
    le_add_tsub
  have h := add_le_add (add_le_add (le_refl (messageDigestFreshRate key message cache * ((2 ^ randomnessBits : Nat) : ENNReal))) hcount)
    (le_refl ((digestAttemptLimit : ENNReal) * admissibleProbability))
  convert h using 1 <;> first | rfl | ring
theorem normalizedMessageReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    normalizedMessageReuseWeight key message cache ≤
      (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹ := by
  apply (normalizedMessageReuseWeight_le_deficit key message cache q hq hcache).trans
  apply (ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (add_le_add le_rfl hdeficit) _)).trans
  have hp := admissibleProbability_ne_top
  have hlow := (ENNReal.toReal_le_toReal (by simp) hp).mpr admissibleProbability_ge
  have hhigh := (ENNReal.toReal_le_toReal hp (by simp)).mpr admissibleProbability_le
  rw [ENNReal.toReal_inv] at hlow hhigh
  norm_num at hlow hhigh
  have hsmall : (digestAttemptLimit : ENNReal) * admissibleProbability + ((2 ^ 83 : Nat) : ENNReal) <
      ((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, digestAttemptLimit, randomnessBits]
    push_cast
    nlinarith
  apply (ENNReal.toReal_le_toReal (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hsmall))) (by
    exact ENNReal.mul_ne_top (by finiteness) (ENNReal.inv_ne_top.mpr (mul_ne_zero (by simp) admissibleProbability_pos)))).mp
  rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hsmall.le (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, digestAttemptLimit, randomnessBits]
  push_cast
  set x := admissibleProbability.toReal
  have hx : 0 < x := by linarith
  rw [inv_le_iff_one_le_mul₀ (by nlinarith)]
  have hax : 0 < (2 : ℝ) ^ 128 * x := by positivity
  have hy : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 128 * x) = 1 := inv_mul_cancel₀ hax.ne'
  have hypos : 0 < ((2 : ℝ) ^ 128 * x)⁻¹ := inv_pos.mpr hax
  have h1 : (2 : ℝ) ^ 128 * x - (2 ^ 20 * x + 2 ^ 83) ≥ 2 ^ 128 * x * (1024 / 1025) := by nlinarith
  norm_num at hy hypos h1 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 hypos.le]
theorem exactDigestReuseWeight_le_near_uniform_of_deficit
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (q : Nat) (hq : q ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ q)
    (hdeficit : messageAdmissibleDeficit key message cache ≤ ((2 ^ 83 : Nat) : ENNReal)) :
    exactDigestReuseWeight key message cache ≤
      (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹ :=
  (exactDigestReuseWeight_le_normalizedMessage key message cache q hq hcache).trans
    (normalizedMessageReuseWeight_le_near_uniform_of_deficit key message cache q hq hcache hdeficit)
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem cachedMessageEntryCount_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    cachedMessageEntryCount cache parameter root message ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCount_le_enncard cache parameter root message)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
theorem cachedMessageEntryCountWhere_ne_top_of_finite (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere cache parameter root message P ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedMessageEntryCountWhere_le_enncard cache parameter root message P)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness
noncomputable def messageDeficitScore (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) : ℝ :=
  (cachedMessageEntryCount cache parameter root message).toReal * Concrete.admissibleProbability.toReal -
    (cachedMessageEntryCountWhere cache parameter root message (fun _ => True)).toReal
theorem messageDeficitScore_of_no_inputs (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hcount : cachedMessageEntryCount cache parameter root message = 0) :
    messageDeficitScore parameter root message cache ≤ 0 := by
  simp only [messageDeficitScore, hcount, ENNReal.toReal_zero, zero_mul, zero_sub]
  exact neg_nonpos.mpr ENNReal.toReal_nonneg
theorem messageDeficitScore_ofReal_eq (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    ENNReal.ofReal (messageDeficitScore key.parameter key.root message cache) =
      Concrete.messageAdmissibleDeficit key message cache := by
  have hcount := cachedMessageEntryCount_ne_top_of_finite key.parameter key.root message cache hfinite
  have hadmissible := cachedMessageEntryCountWhere_ne_top_of_finite key.parameter key.root message cache hfinite (fun _ => True)
  rw [messageDeficitScore, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcount, ENNReal.ofReal_toReal hadmissible,
    ENNReal.ofReal_toReal Concrete.admissibleProbability_ne_top]
  rfl
end SphincsSecurity
end

section


namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def positiveScoreMoment (score : ℝ) (power : Nat) : ENNReal :=
  ENNReal.ofReal (max score 0 ^ power)
theorem positiveScoreMoment_ne_top (score : ℝ) (power : Nat) : positiveScoreMoment score power ≠ ⊤ := by
  exact ENNReal.ofReal_ne_top
theorem positiveScoreMoment_zero_of_nonpos (score : ℝ) (hscore : score ≤ 0) (power : Nat) (hpower : power ≠ 0) :
    positiveScoreMoment score power = 0 := by
  simp [positiveScoreMoment, max_eq_right hscore, zero_pow hpower]
end SphincsSecurity
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) : ENNReal :=
  ∑ message : Message, positiveScoreMoment (messageDeficitScore parameter root message cache) power
theorem positiveScoreMoment_le_messageDeficitMoment (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (power : Nat) (message : Message) :
    positiveScoreMoment (messageDeficitScore parameter root message cache) power ≤
      messageDeficitMoment parameter root cache power := by
  unfold messageDeficitMoment
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun message : Message => positiveScoreMoment (messageDeficitScore parameter root message cache) power)
    (fun _ _ => zero_le) (Finset.mem_univ message)
theorem messageDeficitMoment_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hcount : ∀ message, cachedMessageEntryCount cache parameter root message = 0)
    (power : Nat) (hpower : power ≠ 0) : messageDeficitMoment parameter root cache power = 0 := by
  apply Finset.sum_eq_zero
  intro message _
  exact positiveScoreMoment_zero_of_nonpos _
    (messageDeficitScore_of_no_inputs parameter root message cache (hcount message)) power hpower
end SphincsSecurity
end

section


namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def MessageDeficitExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∃ message, ((2 ^ 83 : Nat) : ENNReal) < Concrete.messageAdmissibleDeficit key message cache
theorem positiveScoreMoment_eq_pow_ofReal (score : ℝ) (power : Nat) :
    positiveScoreMoment score power = ENNReal.ofReal score ^ power := by
  rw [positiveScoreMoment, ENNReal.ofReal_pow (le_max_right _ _)]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show 0 ≤ ENNReal.ofReal score from zero_le)]
theorem cachedMessageEntryCount_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none)
    (message : Message) : cachedMessageEntryCount cache parameter root message = 0 := by
  have hempty : cachedMessageInputSet cache parameter root message = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨input, answer⟩ ⟨hcached, randomness, hinput⟩
    change cache input = some answer at hcached
    have h := hnone (Concrete.messageDigestPayload root message randomness)
    rw [← hinput, hcached] at h
    cases h
  simp only [cachedMessageEntryCount, hempty, Set.encard_empty, ENat.toENNReal_zero]
end SphincsSecurity
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem TargetShapeValid.empty (remaining : Finset IndexGroup) : TargetShapeValid ∅ remaining := by
  constructor <;> intro group hgroup <;> exact (Finset.notMem_empty group hgroup).elim
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def nearUniformDigestReuseWeight : ENNReal :=
  (1025 / 1024 : ENNReal) * (((2 ^ randomnessBits : Nat) : ENNReal) * admissibleProbability)⁻¹
theorem exactDigestReuseWeight_le_near_uniform_of_clean_cache (key : SecretKey) (cache : QueryCache HashSpec)
    (cap : Nat) (hcap : cap ≤ 2 ^ 127) (hcache : QueryCache.enncard cache ≤ cap)
    (hclean : ¬ MessageDeficitExceptional key cache) (message : Message) :
    exactDigestReuseWeight key message cache ≤ nearUniformDigestReuseWeight :=
  exactDigestReuseWeight_le_near_uniform_of_deficit key message cache cap hcap hcache
    (le_of_not_gt (fun h => hclean ⟨message, h⟩))
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open ENNReal
theorem reuseRawEnvelope_le_binomialAverage (key : SecretKey) (reuse rate : ENNReal)
    (hrate : rate ≤ 1) (queries signatures bound : Nat) (state : CoverLogState)
    (remaining : Finset IndexGroup) (hdegree : remaining.card ≤ bound)
    (hprob : ∀ index : Index,
      (Fintype.card Index : ENNReal)⁻¹ + reuse *
        (cachedIndexMultiplicity key.parameter state.1 index +
          (queries : ENNReal) * cachedIndexRate + bound + signatures) ≤ rate) :
    reuseRawEnvelope key reuse queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage rate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) := by
  apply (reuseRawEnvelope_query_shift_le key reuse queries signatures bound state ∅ remaining
    (TargetShapeValid.empty _) (by simpa only [Finset.card_empty, Nat.zero_add] using hdegree)).trans
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexSigning_iterate_power_le_binomialAverage hrate signatures (hprob index) _ remaining.card
noncomputable def targetProposalOverhead : ENNReal := 49185 / 32768
noncomputable def targetProposalIndexRate : ENNReal :=
  targetProposalOverhead * (Fintype.card Index : ENNReal)⁻¹
theorem targetProposalIndexRate_le_one : targetProposalIndexRate ≤ 1 := by
  unfold targetProposalIndexRate targetProposalOverhead
  norm_num only [Index, totalHeight, Fintype.card_fin]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, Index, totalHeight]
theorem targetProposalRate_of_cache_bound (cache : ENNReal) (spent queries signatures bound : Nat)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit) (hbound : bound ≤ 15)
    (hcache : cache ≤ (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) :
    (Fintype.card Index : ENNReal)⁻¹ + nearUniformDigestReuseWeight *
      (cache + (queries : ENNReal) * cachedIndexRate + bound + signatures) ≤
        targetProposalIndexRate := by
  have hsize : cache + (queries : ENNReal) * cachedIndexRate + bound + signatures ≤
      ((2 ^ 127 : Nat) : ENNReal) * cachedIndexRate +
        ((2 ^ 72 : Nat) : ENNReal) + 15 + signatureLimit := by
    calc
      _ ≤ (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal) +
          (queries : ENNReal) * cachedIndexRate + bound + signatures := by
        gcongr
      _ = ((spent + queries : Nat) : ENNReal) * cachedIndexRate +
          ((2 ^ 72 : Nat) : ENNReal) + bound + signatures := by
        push_cast
        ring
      _ ≤ _ := by
        exact add_le_add
          (add_le_add (add_le_add (mul_le_mul' (Nat.cast_le.mpr hqueries) le_rfl) le_rfl)
            (by exact_mod_cast hbound)) (Nat.cast_le.mpr hsignatures)
  apply (add_le_add le_rfl (mul_le_mul' le_rfl hsize)).trans
  unfold nearUniformDigestReuseWeight targetProposalIndexRate targetProposalOverhead cachedIndexRate
  have hp := admissibleProbability_ne_top
  have hlow := (ENNReal.toReal_le_toReal (by simp) hp).mpr admissibleProbability_ge
  have hhigh := (ENNReal.toReal_le_toReal hp (by simp)).mpr admissibleProbability_le
  rw [ENNReal.toReal_inv] at hlow hhigh
  norm_num at hlow hhigh
  have hpos : admissibleProbability ≠ 0 := admissibleProbability_pos
  norm_num only [Index, totalHeight, Fintype.card_fin, signatureLimit, randomnessBits]
  have hprod : ((2 : ENNReal) ^ 128 * admissibleProbability) ≠ 0 := mul_ne_zero (by simp) hpos
  have hprodTop : ((2 : ENNReal) ^ 128 * admissibleProbability) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hp
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  set x := admissibleProbability.toReal
  have hx : 0 < x := by linarith
  have hinv : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 128 * x) = 1 := inv_mul_cancel₀ (by positivity)
  have hinvpos : 0 < ((2 : ℝ) ^ 128 * x)⁻¹ := by positivity
  have hsmall : ((2 : ℝ) ^ 128 * x)⁻¹ * (2 ^ 72 + 15 + 2 ^ 32) ≤ 3 / 10 ^ 14 := by
    rw [mul_comm, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  norm_num at hinv hinvpos hsmall ⊢
  nlinarith [mul_pos hinvpos hx]
theorem reuseRawEnvelope_le_proposalIndexAverage (key : SecretKey)
    (spent queries signatures bound : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 15)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage targetProposalIndexRate signatures (fun count =>
        (((signingSlotsAtIndex (observedOptionalSigningViews
          (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal) + count) ^
          remaining.card) :=
  reuseRawEnvelope_le_binomialAverage key nearUniformDigestReuseWeight targetProposalIndexRate
    targetProposalIndexRate_le_one queries signatures bound state remaining hdegree
    (fun index => targetProposalRate_of_cache_bound _ spent queries signatures bound hqueries hsignatures hbound (hcache index))
theorem proposalIndexAverage_le_uniformAverage (signatures proposals degree : Nat)
    {signings consumed : ENNReal} (hcounts : signings ≤ consumed)
    (hroom : targetProposalOverhead * signatures + degree ≤ ((proposals + 1 : Nat) : ENNReal)) :
    binomialAverage targetProposalIndexRate signatures (fun count => (signings + count) ^ degree) ≤
      binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals (fun count => (consumed + count) ^ degree) := by
  apply binomialAverage_shifted_power_le_of_room targetProposalIndexRate_le_one
    (by norm_num [Index, totalHeight]) hcounts signatures proposals degree (mass := targetProposalOverhead * signatures)
  · unfold targetProposalIndexRate
    exact le_of_eq (by ring)
  · exact hroom
theorem reuseRawEnvelope_le_uniformProposalAverage (key : SecretKey)
    (spent queries signatures bound proposals : Nat) (state : CoverLogState) (remaining : Finset IndexGroup)
    (consumed : Index → Nat) (hqueries : spent + queries ≤ 2 ^ 127) (hsignatures : signatures ≤ signatureLimit)
    (hdegree : remaining.card ≤ bound) (hbound : bound ≤ 15)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * cachedIndexRate + ((2 ^ 72 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed index)
    (hroom : targetProposalOverhead * signatures + remaining.card ≤ ((proposals + 1 : Nat) : ENNReal)) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries signatures state ∅ remaining ≤
      ∑ index : Index, binomialAverage (Fintype.card Index : ENNReal)⁻¹ proposals
        (fun count => ((consumed index : ENNReal) + count) ^ remaining.card) := by
  apply (reuseRawEnvelope_le_proposalIndexAverage key spent queries signatures bound state remaining
    hqueries hsignatures hdegree hbound hcache).trans
  apply Finset.sum_le_sum
  intro index _
  exact proposalIndexAverage_le_uniformAverage signatures proposals remaining.card
    (Nat.cast_le.mpr (hcounts index)) hroom
end SphincsSecurity.Concrete
end
