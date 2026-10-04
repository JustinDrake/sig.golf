import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CacheMessageWeight
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeRace
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedDigestRate
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestLoopRecord
import SigGolfCandidate.SphincsSecurity.Proof.Fts.NormalizedTargetMatches
import SigGolfCandidate.SphincsSecurity.Proof.Fts.NormalizedTargetCacheQuery
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetSigningMatchFactors
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeSignerView
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SignerDigestSource
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TerminalCache

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
def successfulSignerInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : ENNReal :=
  match result.1.1, result.1.2 with
  | some signature, some view => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)) view
  | _, _ => 0
noncomputable def cachedSignerInputWeight (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) : ENNReal :=
  match before input with
  | none => 0
  | some output =>
      if (∃ randomness, input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ∧
          Admissible (truncateMessageDigest output) then weight input (hashOutputFewTimeView output) else 0
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cachedSignerInputWeight_le_cacheMessageEntryWeight (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : HashInput → FewTimeView → ENNReal) (input : HashInput) :
    cachedSignerInputWeight key message before weight input ≤ cacheMessageEntryWeight key.parameter weight before input := by
  unfold cachedSignerInputWeight cacheMessageEntryWeight
  cases before input with
  | none => exact le_rfl
  | some output =>
      simp only
      split_ifs with hsource htarget
      · exact le_rfl
      · obtain ⟨randomness, heq⟩ := hsource.1
        exact (htarget ⟨⟨messageDigestPayload key.root message randomness, heq.symm⟩, hsource.2⟩).elim
      · exact bot_le
      · exact le_rfl
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
def onlyInputCache (cache : QueryCache HashSpec) (target : HashInput) :
    QueryCache HashSpec :=
  fun input => if input = target then cache input else none
theorem onlyInputCache_le (cache : QueryCache HashSpec) (target : HashInput) :
    onlyInputCache cache target ≤ cache := by
  intro input output hcached
  by_cases hinput : input = target
  · simpa [onlyInputCache, hinput] using hcached
  · simp [onlyInputCache, hinput] at hcached
theorem cachedMessageEntryCountWhere_onlyInput_le_one
    (cache : QueryCache HashSpec) (target : HashInput)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (onlyInputCache cache target) parameter root message P ≤ 1 := by
  have hsubsingleton :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).Subsingleton := by
    rintro ⟨leftInput, leftOutput⟩ hleft ⟨rightInput, rightOutput⟩ hright
    have hleftInput : leftInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hleft
    have hrightInput : rightInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hright
    subst leftInput
    subst rightInput
    have houtputs : leftOutput = rightOutput := by
      apply Option.some.inj
      exact hleft.1.1.symm.trans hright.1.1
    subst rightOutput
    rfl
  have hencard :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.2 hsubsingleton
  simpa only [cachedMessageEntryCountWhere, ENat.toENNReal_one] using
    ENat.toENNReal_mono hencard
end SphincsSecurity
end

section





namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
def selectedLoopInputWeight (key : SecretKey) (message : Message)
    (weight : HashInput → FewTimeView → ENNReal) (result : DigestLoopRecord) : ENNReal :=
  match result.1 with
  | none => 0
  | some (randomness, index, leaves) => weight
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness))
      (selectedFewTimeView index leaves)
theorem probEvent_signDigestLoop_fixedPrehit_le_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (input : HashInput) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView (onlyInputCache cache input) key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] ≤
      exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message
    (onlyInputCache cache input) cache (onlyInputCache_le cache input), cachedDigestAttemptRate_eq_count]
  calc
    _ = cachedMessageEntryCountWhere (onlyInputCache cache input) key.parameter key.root message P *
        exactDigestReuseWeight key message cache := by unfold exactDigestReuseWeight; ring
    _ ≤ 1 * exactDigestReuseWeight key message cache := mul_le_mul'
      (cachedMessageEntryCountWhere_onlyInput_le_one cache input key.parameter key.root message P) le_rfl
    _ = _ := one_mul _
theorem selectedLoopInputWeight_le_fresh_add_prehit
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (result : DigestLoopRecord)
    (hresult : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)) :
    selectedLoopInputWeight key message weight result ≤
      (∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
      (∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
        cachedSignerInputWeight key message before weight input else 0) := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp only [selectedLoopInputWeight]; exact bot_le
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
      let view := selectedFewTimeView index leaves
      change weight input view ≤ _
      cases hbefore : before input with
      | none =>
          have hfresh : FreshSelectedView before key message (· = view) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, hbefore, rfl⟩
          apply (hweight input view).trans
          apply le_trans ?_ le_self_add
          exact (le_of_eq (if_pos hfresh).symm).trans (ENNReal.le_tsum view)
      | some output =>
          have hattempt := signDigestLoop_initial_cached_result digestAttemptLimit key message randomness
            index leaves before after output hbefore hresult
          have hview : view = hashOutputFewTimeView output := signAttemptResultOfOutput_view output index leaves hattempt
          have hadmissible : Admissible (truncateMessageDigest output) :=
            (signAttemptResultOfOutput_ne_none_iff output).mp (by rw [hattempt]; exact Option.some_ne_none _)
          have hsource : cachedSignerInputWeight key message before weight input = weight input view := by
            simp only [cachedSignerInputWeight, hbefore]
            rw [if_pos ⟨⟨randomness, rfl⟩, hadmissible⟩, ← hview]
          have hprehit : PrehitSelectedView (onlyInputCache before input) key message (fun _ => True)
              (some (randomness, index, leaves), after) := by
            refine ⟨randomness, index, leaves, rfl, output, ?_, hattempt, trivial⟩
            simpa [onlyInputCache, input] using hbefore
          apply le_trans ?_ (le_add_left le_rfl)
          rw [← hsource]
          exact (le_of_eq (if_pos hprehit).symm).trans (ENNReal.le_tsum input)
theorem expected_selectedLoopInputWeight_le_exactReuse
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message weight result) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before := by
  have hexpect {α : Type} (event : α → DigestLoopRecord → Prop) (value : α → ENNReal) :
      (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ∑' index, if event index result then value index else 0) =
      ∑' index, Pr[event index | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * value index := by
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro index
    rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro result
    split_ifs <;> simp
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        ((∑' view, if FreshSelectedView before key message (· = view) result then uniformWeight view else 0) +
          ∑' input, if PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) result then
            cachedSignerInputWeight key message before weight input else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
      · exact mul_le_mul' le_rfl (selectedLoopInputWeight_le_fresh_add_prehit key message before weight uniformWeight hweight result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' view, Pr[FreshSelectedView before key message (· = view) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] * uniformWeight view) +
        ∑' input, Pr[PrehitSelectedView (onlyInputCache before input) key message (fun _ => True) |
          (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
            cachedSignerInputWeight key message before weight input := by
      simp only [mul_add, ENNReal.tsum_add, hexpect]
    _ ≤ (∑' view, (freshDigestSelectionProbability key message before *
          Pr[= view | signerViewSample]) * uniformWeight view) +
        ∑' input, exactDigestReuseWeight key message before * cachedSignerInputWeight key message before weight input := by
      apply add_le_add
      · apply ENNReal.tsum_le_tsum
        intro view
        apply mul_le_mul' _ le_rfl
        exact le_of_eq (by
          simpa only [probEvent_eq_eq_probOutput, freshDigestSelectionProbability] using
            (probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform digestAttemptLimit key message before before (· = view)
              (onlyRejectedNewMessageEntries_self before key message)))
      · exact ENNReal.tsum_le_tsum (fun input => mul_le_mul'
          (probEvent_signDigestLoop_fixedPrehit_le_exactWeight key message before input (fun _ => True)) le_rfl)
    _ = _ := by simp only [mul_assoc, ENNReal.tsum_mul_left]; rw [mul_comm (exactDigestReuseWeight key message before)]
theorem expected_freshSelectedLoopInputWeight_le (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (weight : FewTimeView → ENNReal) :
    (∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
      selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * weight source := by
  have hzero (input : HashInput) : cachedSignerInputWeight key message before
      (fun input source => if before input = none then weight source else 0) input = 0 := by
    unfold cachedSignerInputWeight
    cases hc : before input with
    | none => rfl
    | some output => simp only [hc, reduceCtorEq, if_false, ite_self]
  have hbound := expected_selectedLoopInputWeight_le_exactReuse key message before
    (fun input source => if before input = none then weight source else 0) weight (by
      intro input source
      split_ifs; exact le_rfl; exact bot_le)
  simpa only [hzero, tsum_zero, zero_mul, add_zero] using hbound
def DigestCompletionConsistent (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  result.1.2 = selectedLoopView? loop ∧
    ∀ signature, result.1.1 = some signature →
      ∃ index leaves, loop.1 = some (signature.randomness, index, leaves)
theorem successfulSignerInputWeight_le_selectedLoopInputWeight
    (key : SecretKey) (message : Message) (weight : HashInput → FewTimeView → ENNReal)
    (loop : DigestLoopRecord) (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : DigestCompletionConsistent loop result) :
    successfulSignerInputWeight key message weight result ≤ selectedLoopInputWeight key message weight loop := by
  cases hs : result.1.1 with
  | none => simp only [successfulSignerInputWeight, hs]; exact bot_le
  | some signature =>
      obtain ⟨index, leaves, hloop⟩ := hconsistent.2 signature hs
      simp only [successfulSignerInputWeight, hs, hconsistent.1, selectedLoopView?, hloop,
        Option.map_some, selectedLoopInputWeight, le_refl]
theorem expected_digestCompletion_cost_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal)
    (weight : HashInput → FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤ selectedLoopInputWeight key message weight loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop := by
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro loop
  by_cases hl : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before)
  · apply mul_le_mul' le_rfl
    calc
      _ ≤ ∑' result, Pr[= result | finish loop] * selectedLoopInputWeight key message weight loop := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : result ∈ support (finish loop)
        · exact mul_le_mul' le_rfl (hcost loop hl result hr)
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [probOutput_eq_zero_of_not_mem_support hl, zero_mul, zero_mul]
theorem expected_digestCompletion_successfulInputWeight_le_selected {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      ∑' loop, Pr[= loop | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before] *
        selectedLoopInputWeight key message weight loop :=
  expected_digestCompletion_cost_le_selected key message before finish
    (fun result => successfulSignerInputWeight key message weight (record result)) weight
    (fun loop hl result hr => successfulSignerInputWeight_le_selectedLoopInputWeight
      key message weight loop (record result) (hconsistent loop hl result hr))
theorem expected_digestCompletion_freshCost_le {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α) (cost : α → ENNReal) (weight : FewTimeView → ENNReal)
    (hcost : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), cost result ≤
        selectedLoopInputWeight key message (fun input source => if before input = none then weight source else 0) loop) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] * cost result) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * weight source :=
  (expected_digestCompletion_cost_le_selected key message before finish cost _ hcost).trans
    (expected_freshSelectedLoopInputWeight_le key message before weight)
theorem expected_digestCompletion_successfulInputWeight_le_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      (∑' input, cachedSignerInputWeight key message before weight input) * exactDigestReuseWeight key message before :=
  (expected_digestCompletion_successfulInputWeight_le_selected key message before finish record hconsistent weight).trans
    (expected_selectedLoopInputWeight_le_exactReuse key message before weight uniformWeight hweight)
theorem expected_digestCompletion_successfulInputWeight_le_allMessage {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hconsistent : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionConsistent loop (record result))
    (weight : HashInput → FewTimeView → ENNReal) (uniformWeight : FewTimeView → ENNReal)
    (hweight : ∀ input view, weight input view ≤ uniformWeight view)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      successfulSignerInputWeight key message weight (record result)) ≤
      freshDigestSelectionProbability key message before *
        (∑' view, Pr[= view | signerViewSample] * uniformWeight view) +
      cacheMessageWeight key.parameter weight before * reuse :=
  (expected_digestCompletion_successfulInputWeight_le_exactReuse key message before finish record hconsistent
    weight uniformWeight hweight).trans (add_le_add le_rfl (mul_le_mul'
      (ENNReal.tsum_le_tsum (cachedSignerInputWeight_le_cacheMessageEntryWeight key message before weight)) hreuse))
end SphincsSecurity.Concrete
end

section


set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem normalizedSourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset IndexGroup)
    (hdisjoint : Disjoint left right) :
    normalizedSourceSubsetMatch target source left * normalizedSourceSubsetMatch target source right =
      normalizedSourceSubsetMatch target source (left ∪ right) := by
  unfold normalizedSourceSubsetMatch
  rw [Finset.card_union_of_disjoint hdisjoint, pow_add, ← sourceSubsetMatch_mul, Nat.cast_mul]
  ring
theorem normalizedSourceSubsetMatch_singletons (target source : FewTimeView) (required : Finset IndexGroup) :
    (∏ tree ∈ required, normalizedSourceSubsetMatch target source {tree}) = normalizedSourceSubsetMatch target source required := by
  simp only [normalizedSourceSubsetMatch, sourceSubsetMatch, Finset.card_singleton, pow_one,
    Finset.prod_singleton, Finset.prod_mul_distrib, Finset.prod_const, Nat.cast_prod]
noncomputable def targetCacheArrivalPolynomial (cached : Fin m → ENNReal) (groups : Fin m → Finset IndexGroup)
    (target source : FewTimeView) : ENNReal :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
      ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot
theorem targetCacheProduct_add_arrival (cached : Fin m → ENNReal) (groups : Fin m → Finset IndexGroup)
    (target source : FewTimeView) :
    (∏ slot : Fin m, cached slot) + targetCacheArrivalPolynomial cached groups target source =
      ∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot)) := by
  rw [show (∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot))) =
    ∏ slot : Fin m, (normalizedSourceSubsetMatch target source (groups slot) + cached slot) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul, targetCacheArrivalPolynomial]
theorem targetLogProduct_insert_expansion (logged : IndexGroup → ENNReal) (required : Finset IndexGroup) (target source : FewTimeView) :
    (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
      ∑ selected ∈ required.powerset, normalizedSourceSubsetMatch target source selected *
        ∏ tree ∈ required \ selected, logged tree := by
  rw [show (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
    ∏ tree ∈ required, (normalizedSourceSubsetMatch target source {tree} + logged tree) by simp only [add_comm]]
  rw [Finset.prod_add]
  simp only [normalizedSourceSubsetMatch_singletons]
noncomputable def targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : IndexGroup → ENNReal)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (target source : FewTimeView) : ENNReal :=
  targetCacheArrivalPolynomial cached groups target source *
    ∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})
theorem expected_targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : IndexGroup → ENNReal)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (target : FewTimeView)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required) :
    (∑' source, Pr[= source | signerViewSample] *
      targetMixedGrowthPolynomial cached logged groups required target source) =
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          ∑ trees ∈ required.powerset,
            signerRate target (selected.biUnion groups ∪ trees) *
              ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
                ∏ tree ∈ required \ trees, logged tree) := by
  simp only [targetMixedGrowthPolynomial, targetCacheArrivalPolynomial, targetLogProduct_insert_expansion]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro trees htrees
  have hselectedNonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  have hpair : (selected : Set (Fin m)).PairwiseDisjoint groups := fun i _ j _ hij => hdisjoint hij
  have hsep : Disjoint (selected.biUnion groups) trees := by
    rw [Finset.disjoint_biUnion_left]
    intro slot _
    exact (hremaining slot).mono_right (Finset.mem_powerset.mp htrees)
  have hpoint (source : FewTimeView) :
      (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
        (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
          (normalizedSourceSubsetMatch target source trees * ∏ tree ∈ required \ trees, logged tree) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups ∪ trees) *
        ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) * ∏ tree ∈ required \ trees, logged tree) := by
    rw [normalizedSourceSubsetMatch_prod target source groups selected hpair, ← normalizedSourceSubsetMatch_mul target source _ _ hsep]
    ring
  simp only [hpoint, ← mul_assoc, ENNReal.tsum_mul_right]
  rfl
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) : ENNReal :=
  ∑ selected ∈ required.powerset.erase ∅, normalizedSourceSubsetMatch target source selected *
    normalizedTargetLogProduct key cache log payload target (required \ selected)
theorem normalizedTargetLogProduct_add_increment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) :
    normalizedTargetLogProduct key cache log payload target required + normalizedTargetLogIncrement key cache log payload target required source =
      ∏ tree ∈ required, (normalizedTargetLogMatch key cache log payload target tree + normalizedSourceSubsetMatch target source {tree}) := by
  rw [targetLogProduct_insert_expansion, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset required)]
  simp only [normalizedSourceSubsetMatch, Finset.card_empty, pow_zero, sourceSubsetMatch,
    Finset.prod_empty, Nat.cast_one, one_mul, Finset.sdiff_empty, normalizedTargetLogIncrement, normalizedTargetLogProduct]
theorem normalizedTargetLogProduct_append_none (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none) :
    normalizedTargetLogProduct key after (log ++ [entry]) payload target required =
      normalizedTargetLogProduct key before log payload target required := by
  apply Finset.prod_congr rfl
  intro tree _
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero,
    eligibleSigningViews_cache_stable key before after log payload hcache hsigned] at hstep
  exact congrArg (fun count : Nat => coverNormalization * (count : ENNReal)) hstep
theorem expected_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    (∑' source, Pr[= source | signerViewSample] * normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        signerRate target selected * normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  simp only [normalizedTargetLogIncrement, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  rfl
theorem cached_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    cacheMessageWeight key.parameter (fun input source => if input = tweakableHashInput key.parameter .message payload then 0
      else normalizedTargetLogIncrement key cache log payload target required source) cache =
      ∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  have hpoint (input : HashInput) (source : FewTimeView) :
      (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedSourceSubsetMatch target source selected) *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
    unfold normalizedTargetLogIncrement
    split_ifs <;> simp only [zero_mul, Finset.sum_const_zero]
  simp only [hpoint, cacheMessageWeight_sum, cacheMessageWeight_mul_right, normalizedCachedTargetSubsetMatch_eq_weight]
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem signDigestLoop_selected_cached_output (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before)) :
    ∃ output, after (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = selectedFewTimeView index leaves := by
  have hreplay := replayRom_of_mem_support (signDigestLoop attempts key message) before
    (some (randomness, index, leaves)) after hloop (fromCache after) (agreesWithFn_fromCache after)
  have hgood := successfulDigestLoop_of_mem_support (fromCache after) key message attempts randomness index leaves
    before after after hreplay le_rfl (agreesWithFn_fromCache after)
  obtain ⟨_, digest, heval, hadmissible, hindex, hleaves, hcached⟩ := hgood.extract
  obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp (CachedRun.messageDigest_cached hcached)
  have hdigest : digest = truncateMessageDigest output := by
    rw [← heval]
    change truncateMessageDigest (fromCache after (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness))) = truncateMessageDigest output
    rw [agreesWithFn_fromCache after houtput]
  refine ⟨output, houtput, hdigest ▸ hadmissible, ?_⟩
  simp only [hashOutputFewTimeView, fullDigestView, selectedFewTimeView, ← hdigest, hindex, hleaves]
theorem signAfterDigest_message_cache_eq (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (before after : QueryCache HashSpec) (signature : Option Signature)
    (hfinish : (signature, after) ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAfterDigest key randomness index leaves)).run before)) (payload : HashInput) :
    after (tweakableHashInput key.parameter .message payload) = before (tweakableHashInput key.parameter .message payload) := by
  cases hbefore : before (tweakableHashInput key.parameter .message payload) with
  | none => exact signAfterDigest_cache_message_none key randomness index leaves before after signature hfinish payload hbefore
  | some output =>
      have hcache : before ≤ after :=
        (replay_of_mem_support (signAfterDigest key randomness index leaves) before signature after hfinish
          (fromCache after) (agreesWithFn_fromCache after)).1
      exact hcache hbefore
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signWithView
def DigestCompletionPreservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  DigestCompletionConsistent loop result ∧ messageAnswers key.parameter result.2 = messageAnswers key.parameter loop.2
theorem digestCompletion_successful_cached_output (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (signature : Signature) (hs : result.1.1 = some signature) :
    ∃ output, result.2 (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message signature.randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ result.1.2 = some (hashOutputFewTimeView output) := by
  obtain ⟨index, leaves, hselected⟩ := hcompletion.1.2 signature hs
  have hloop' : (some (signature.randomness, index, leaves), loop.2) ∈ support
      ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before) := by
    have heq : loop = (some (signature.randomness, index, leaves), loop.2) := Prod.ext hselected rfl
    rwa [← heq]
  obtain ⟨output, hcached, hadmissible, hview⟩ := signDigestLoop_selected_cached_output
    digestAttemptLimit key message before loop.2 signature.randomness index leaves hloop'
  refine ⟨output, ?_, hadmissible, ?_⟩
  · exact (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).trans hcached
  · simp only [hcompletion.1.1, selectedLoopView?, hselected, Option.map_some, ← hview]
noncomputable def originalDigestCompletion (key : SecretKey) (loop : DigestLoopRecord) :
    ProbComp ((Option Signature × Option FewTimeView) × QueryCache HashSpec) :=
  match loop.1 with
  | none => pure ((none, none), loop.2)
  | some (randomness, index, leaves) =>
      (fun result => ((result.1, some (selectedFewTimeView index leaves)), result.2)) <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2
theorem signWithView_run_eq_digestCompletion (key : SecretKey) (message : Message) (before : QueryCache HashSpec) :
    (simulateQ romImpl (signWithView key message)).run before =
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= originalDigestCompletion key := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro loop
  cases hl : loop.1 with
  | none => simp only [originalDigestCompletion, hl, simulateQ_pure, StateT.run_pure]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        simulateQ_romImpl_liftM, map_eq_bind_pure_comp]
      rfl
theorem originalDigestCompletion_preservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hr : result ∈ support (originalDigestCompletion key loop)) :
    DigestCompletionPreservesMessages key loop result := by
  cases hl : loop.1 with
  | none =>
      have heq : result = ((none, none), loop.2) := by
        simpa only [originalDigestCompletion, hl, support_pure, Set.mem_singleton_iff] using hr
      subst result
      simp only [DigestCompletionPreservesMessages, DigestCompletionConsistent, selectedLoopView?, hl,
        Option.map_none, reduceCtorEq, false_implies, implies_true, and_self]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, support_map] at hr
      obtain ⟨⟨signature, after⟩, hfinish, rfl⟩ := hr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [selectedLoopView?, hl, Option.map_some]
      · intro successful hs
        have hfinish' : (some successful, after) ∈ support
            ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2) := by
          rwa [← hs]
        have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loop.2 after successful hfinish'
        exact ⟨index, leaves, by simpa only [hrandomness] using hl⟩
      · funext payload
        exact signAfterDigest_message_cache_eq key randomness index leaves loop.2 after signature hfinish payload
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem digestCompletion_normalizedTargetLogProduct_le_input
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message (fun input source =>
          if input = tweakableHashInput key.parameter .message payload then 0
          else normalizedTargetLogIncrement key before log payload target required source) result := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have hproject : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩]) payload target required := by
    unfold normalizedTargetLogProduct normalizedTargetLogMatch
    rw [hcompletion.2]
  rw [hproject]
  cases hs : result.1.1 with
  | none =>
      rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
        (by simp [eligibleSigningView?])]
      simp only [successfulSignerInputWeight, hs, add_zero, le_refl]
  | some signature =>
      obtain ⟨output, houtput, _, hview⟩ := digestCompletion_successful_cached_output key message before loop hloop result hcompletion signature hs
      have hcached : loop.2 (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message signature.randomness)) = some output :=
        (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).symm.trans houtput
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
          (by simp [eligibleSigningView?, hsame])]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        simp only [successfulSignerInputWeight, hs, hview, if_neg hinput]
        rw [normalizedTargetLogProduct_add_increment]
        apply Finset.prod_le_prod'
        intro tree _
        exact normalizedTargetLogMatch_le_of_eligibleView key before loop.2 log ⟨message, some signature⟩ payload target
          (hashOutputFewTimeView output) tree hcache hsigned (Or.inr (by
            simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, hcached]))
theorem expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetLogProduct key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
          (∑ selected ∈ required.powerset.erase ∅,
            signerRate target selected * normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * reuse := by
  let computation := (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  have hweight (input : HashInput) (source : FewTimeView) :
      weight input source ≤ normalizedTargetLogIncrement key before log payload target required source := by
    unfold weight
    split_ifs; exact bot_le; exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (normalizedTargetLogProduct key before log payload target required + successfulSignerInputWeight key message weight (record result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · change result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨loop, hl, hf⟩ := hr
        exact mul_le_mul' le_rfl (digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required
          hsigned loop hl (record result) (hcompletion loop hl result hf))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        ∑' result, Pr[= result | computation] * successfulSignerInputWeight key message weight (record result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ _ := by
      have hbound := (expected_digestCompletion_successfulInputWeight_le_allMessage key message before finish record
        (fun loop hl result hr => (hcompletion loop hl result hr).1) weight _ hweight reuse hreuse).trans
          (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)
      simp only [weight, expected_normalizedTargetLogIncrement, cached_normalizedTargetLogIncrement] at hbound
      simpa only [add_assoc, computation, weight] using add_le_add
        (le_refl (normalizedTargetLogProduct key before log payload target required)) hbound
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cacheMessageWeight_of_no_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after)
    (hnoNew : ∀ input output, before input = none → MessageHashInput parameter input → after input = some output →
      ¬ Admissible (truncateMessageDigest output)) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  have hzero : cacheMessageWeight parameter (fun input source => if before input = none then weight input source else 0) after = 0 := by
    unfold cacheMessageWeight
    apply ENNReal.tsum_eq_zero.mpr
    intro input
    unfold cacheMessageEntryWeight
    cases houtput : after input with
    | none => rfl
    | some output =>
        simp only
        by_cases hgood : MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output)
        · rw [if_pos hgood]
          by_cases hfresh : before input = none
          · exact (hnoNew input output hfresh hgood.1 houtput hgood.2).elim
          · simp only [hfresh, if_false]
        · simp only [hgood, if_false]
  rw [hzero, add_zero]
theorem cacheMessageWeight_of_single_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : MessageHashInput parameter input) (hafter : after input = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (hunique : ∀ other answer, before other = none → MessageHashInput parameter other → after other = some answer →
      Admissible (truncateMessageDigest answer) → other = input) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before + weight input (hashOutputFewTimeView output) := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  congr 1
  unfold cacheMessageWeight
  rw [tsum_eq_single input]
  · simp only [cacheMessageEntryWeight, hafter, hmessage, hadmissible, and_self, if_true, hfresh]
  · intro other hne
    unfold cacheMessageEntryWeight
    cases hanswer : after other with
    | none => rfl
    | some answer =>
        simp only
        by_cases hgood : MessageHashInput parameter other ∧ Admissible (truncateMessageDigest answer)
        · rw [if_pos hgood]
          by_cases hbefore : before other = none
          · exact (hne (hunique other answer hbefore hgood.1 hanswer hgood.2)).elim
          · simp only [hbefore, if_false]
        · simp only [hgood, if_false]
end SphincsSecurity.Concrete
end

section



set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem signDigestLoop_new_payload_eq_selected (attempts : Nat) (key : SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hloop : (some (randomness, index, leaves), after) ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run before))
    (payload : HashInput) (output : HashOutput)
    (hbefore : before (tweakableHashInput key.parameter .message payload) = none)
    (hafter : after (tweakableHashInput key.parameter .message payload) = some output)
    (hadmissible : Admissible (truncateMessageDigest output)) :
    payload = messageDigestPayload key.root message randomness := by
  obtain ⟨selected, selectedIndex, selectedLeaves, hselected, hpayload⟩ := signDigestLoop_new_admissible_selected attempts key message
    before after (some (randomness, index, leaves)) hloop payload output hbefore hafter hadmissible
  have hrandomness : randomness = selected := congrArg Prod.fst (Option.some.inj hselected)
  exact hpayload.trans (congrArg _ hrandomness.symm)
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def targetMixedSigningGrowth (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) : ENNReal :=
  (normalizedTargetCacheProduct key.parameter after (tweakableHashInput key.parameter .message payload) target groups -
    normalizedTargetCacheProduct key.parameter before (tweakableHashInput key.parameter .message payload) target groups) *
      normalizedTargetLogProduct key after log payload target required
noncomputable def newTargetMixedGrowthWeight (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup) (source : FewTimeView) : ENNReal :=
  targetMixedGrowthPolynomial
    (fun slot => normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot))
    (normalizedTargetLogMatch key before log payload target) groups required target source
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem signDigestLoop_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight loop.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  obtain ⟨selected, after⟩ := loop
  cases selected with
  | none =>
      simp only [selectedLoopInputWeight, add_zero]
      apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
      intro input output hfresh hmessage hafter hadmissible
      obtain ⟨payload, rfl⟩ := hmessage
      obtain ⟨_, _, _, hselected, _⟩ := signDigestLoop_new_admissible_selected digestAttemptLimit key message
        before after none hloop payload output hfresh hafter hadmissible
      contradiction
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · obtain ⟨output, houtput, hadmissible, hview⟩ := signDigestLoop_selected_cached_output digestAttemptLimit key message
          before after randomness index leaves hloop
        simp only [selectedLoopInputWeight, hfresh, if_true]
        rw [← hview]
        apply cacheMessageWeight_of_single_new key.parameter weight before after hcache _ output hfresh
          ⟨messageDigestPayload key.root message randomness, rfl⟩ houtput hadmissible
        intro other answer hbefore hmessage hafter hgood
        obtain ⟨payload, rfl⟩ := hmessage
        exact congrArg (tweakableHashInput key.parameter .message)
          (signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after randomness index leaves hloop
            payload answer hbefore hafter hgood)
      · simp only [selectedLoopInputWeight, if_neg hfresh, add_zero]
        apply cacheMessageWeight_of_no_new key.parameter weight before after hcache
        intro input output hbefore hmessage hafter hadmissible
        obtain ⟨payload, rfl⟩ := hmessage
        have hpayload := signDigestLoop_new_payload_eq_selected digestAttemptLimit key message before after
          randomness index leaves hloop payload output hbefore hafter hadmissible
        exact hfresh (hpayload ▸ hbefore)
theorem digestCompletion_cacheMessageWeight_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) (weight : HashInput → FewTimeView → ENNReal) :
    cacheMessageWeight key.parameter weight result.2 = cacheMessageWeight key.parameter weight before +
      selectedLoopInputWeight key message (fun input source => if before input = none then weight input source else 0) loop := by
  rw [cacheMessageWeight_messageAnswers_congr key.parameter result.2 loop.2 hcompletion.2]
  exact signDigestLoop_cacheMessageWeight_eq key message before loop hloop weight
theorem digestCompletion_targetCacheProduct_le_of_fresh (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (targetInput : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) :
    normalizedTargetCacheProduct key.parameter result.2 targetInput target groups ≤
      normalizedTargetCacheProduct key.parameter before targetInput target groups +
        targetCacheArrivalPolynomial (fun slot => normalizedCachedTargetSubsetMatch key.parameter before targetInput target (groups slot))
          groups target (selectedFewTimeView index leaves) := by
  unfold normalizedTargetCacheProduct
  rw [targetCacheProduct_add_arrival]
  apply Finset.prod_le_prod'
  intro slot _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
  apply add_le_add le_rfl
  split_ifs; exact bot_le; exact le_rfl
theorem digestCompletion_targetLogProduct_le_view (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves)) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      ∏ tree ∈ required, (normalizedTargetLogMatch key before log payload target tree +
        normalizedSourceSubsetMatch target (selectedFewTimeView index leaves) {tree}) := by
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  calc
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message weight result :=
      digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required hsigned loop hloop result hcompletion
    _ ≤ normalizedTargetLogProduct key before log payload target required + selectedLoopInputWeight key message weight loop :=
      add_le_add le_rfl (successfulSignerInputWeight_le_selectedLoopInputWeight key message weight loop result hcompletion.1)
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        normalizedTargetLogIncrement key before log payload target required (selectedFewTimeView index leaves) := by
      apply add_le_add le_rfl
      simp only [selectedLoopInputWeight, hselected, weight]
      split_ifs; exact bot_le; exact le_rfl
    _ = _ := normalizedTargetLogProduct_add_increment key before log payload target required (selectedFewTimeView index leaves)
theorem digestCompletion_targetMixedGrowth_le_freshInput (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    targetMixedSigningGrowth key before result.2 (log ++ [⟨message, result.1.1⟩]) payload target groups required ≤
      selectedLoopInputWeight key message (fun input source => if before input = none then
        newTargetMixedGrowthWeight key before log payload target groups required source else 0) loop := by
  by_cases hnew : ∃ randomness index leaves, loop.1 = some (randomness, index, leaves) ∧
      before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
  · obtain ⟨randomness, index, leaves, hselected, hfresh⟩ := hnew
    have hproduct := digestCompletion_targetCacheProduct_le_of_fresh key message before loop hloop result hcompletion
      randomness index leaves hselected hfresh (tweakableHashInput key.parameter .message payload) target groups
    have hlog := digestCompletion_targetLogProduct_le_view key message before log payload target required hsigned loop hloop result hcompletion
      randomness index leaves hselected
    simp only [selectedLoopInputWeight, hselected, hfresh, if_true]
    exact mul_le_mul' (tsub_le_iff_right.mpr (hproduct.trans_eq (add_comm _ _))) hlog
  · have hzero (weight : HashInput → FewTimeView → ENNReal) : selectedLoopInputWeight key message
        (fun input source => if before input = none then weight input source else 0) loop = 0 := by
      cases hs : loop.1 with
      | none => simp only [selectedLoopInputWeight, hs]
      | some selected =>
          obtain ⟨randomness, index, leaves⟩ := selected
          have hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) ≠ none :=
            fun hc => hnew ⟨randomness, index, leaves, hs, hc⟩
          simp only [selectedLoopInputWeight, hs, if_neg hfresh]
    have hcounts (slot : Fin m) : normalizedCachedTargetSubsetMatch key.parameter result.2
        (tweakableHashInput key.parameter .message payload) target (groups slot) =
        normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target (groups slot) := by
      simp only [normalizedCachedTargetSubsetMatch_eq_weight]
      rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion, hzero, add_zero]
    simp only [targetMixedSigningGrowth, normalizedTargetCacheProduct, hcounts, tsub_self, zero_mul, zero_le]
theorem expected_digestCompletion_targetMixedGrowth_le_freshMass {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (groups : Fin m → Finset IndexGroup) (required : Finset IndexGroup)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      targetMixedSigningGrowth key before (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target groups required) ≤
      freshDigestSelectionProbability key message before *
        ∑' source, Pr[= source | signerViewSample] * newTargetMixedGrowthWeight key before log payload target groups required source :=
  expected_digestCompletion_freshCost_le key message before finish _ _ (fun loop hl result hr =>
    digestCompletion_targetMixedGrowth_le_freshInput key message before log payload target groups required hsigned
      loop hl (record result) (hcompletion loop hl result hr))
end SphincsSecurity.Concrete
end
