import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeTargetCompletion
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestAttemptExpectation

section


namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem probEvent_completeOption_eq {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop) :
    Pr[P | comp >>= fun result => (selected result).elim fallback pure] =
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => selected result = none | comp] * Pr[P | fallback] := by
  rw [probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite comp (fun result => ∃ value, selected result = some value ∧ P value),
    probEvent_eq_tsum_ite comp (fun result => selected result = none),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  cases selected result with
  | none => simp [Option.elim]
  | some value => simp [Option.elim, probEvent_pure, mul_ite]
theorem probEvent_selectedOption_le_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0)
    (hcomplete : Pr[P | comp >>= fun result => (selected result).elim fallback pure] ≤
      Pr[P | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] ≤
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hmass : Pr[fun result => selected result ≠ none | comp] +
      Pr[fun result => selected result = none | comp] = 1 := by
    simpa only [not_not, hfail, tsub_zero] using
      probEvent_compl comp (fun result => selected result ≠ none)
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result = none | comp] * Pr[P | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[P | comp >>= fun result => (selected result).elim fallback pure] :=
      (probEvent_completeOption_eq comp selected fallback P).symm
    _ ≤ Pr[P | fallback] := hcomplete
    _ = _ := by rw [← add_mul, hmass, one_mul]
theorem probEvent_selectedOption_eq_mass_mul {α β : Type} (comp : ProbComp α)
    (selected : α → Option β) (fallback : ProbComp β) (P : β → Prop)
    (hfail : Pr[⊥ | comp] = 0) (hfallback : Pr[⊥ | fallback] = 0)
    (hcomplete : ∀ Q : β → Prop,
      Pr[Q | comp >>= fun result => (selected result).elim fallback pure] ≤ Pr[Q | fallback]) :
    Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] * Pr[P | fallback] := by
  have hparts :
      Pr[fun result => ∃ value, selected result = some value ∧ P value | comp] +
        Pr[fun result => ∃ value, selected result = some value ∧ ¬ P value | comp] =
      Pr[fun result => selected result ≠ none | comp] := by
    simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro result
    cases selected result with
    | none => simp
    | some value => by_cases hP : P value <;> simp [hP]
  have hfallbackMass : Pr[P | fallback] + Pr[fun value => ¬ P value | fallback] = 1 := by
    simpa only [hfallback, tsub_zero] using probEvent_compl fallback P
  apply le_antisymm (probEvent_selectedOption_le_mass_mul comp selected fallback P hfail (hcomplete P))
  apply ENNReal.le_of_add_le_add_right (a :=
    Pr[fun result => selected result ≠ none | comp] * Pr[fun value => ¬ P value | fallback])
    (ENNReal.mul_ne_top probEvent_ne_top probEvent_ne_top)
  calc
    _ = Pr[fun result => selected result ≠ none | comp] := by
      rw [← mul_add, hfallbackMass, mul_one]
    _ = _ := hparts.symm
    _ ≤ _ := add_le_add le_rfl (probEvent_selectedOption_le_mass_mul comp selected fallback
      (fun value => ¬ P value) hfail (hcomplete _))
theorem freshSelectedLoopView?_satisfies_iff
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    (∃ view, freshSelectedLoopView? referenceCache key message result = some view ∧ P view) ↔
      FreshSelectedView referenceCache key message P result := by
  cases hresult : result.1 with
  | none => simp [freshSelectedLoopView?, FreshSelectedView, hresult]
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      by_cases hfresh : referenceCache (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message randomness)) = none
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]
      · simp [freshSelectedLoopView?, FreshSelectedView, hresult, hfresh]
theorem completeFreshSelectedLoopView_eq_elim
    (referenceCache : QueryCache HashSpec) (key : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    completeFreshSelectedLoopView referenceCache key message result =
      (freshSelectedLoopView? referenceCache key message result).elim
        signerViewSample pure := by
  unfold completeFreshSelectedLoopView
  cases freshSelectedLoopView? referenceCache key message result <;> rfl
theorem probEvent_signDigestLoop_freshSelected_eq_mass_mul_uniform
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache key message) :
    Pr[FreshSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      Pr[fun result => freshSelectedLoopView? referenceCache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] *
          Pr[P | signerViewSample] := by
  have h := probEvent_selectedOption_eq_mass_mul
    ((simulateQ romImpl (signDigestLoop attempts key message)).run workingCache)
    (freshSelectedLoopView? referenceCache key message) signerViewSample P
    (by simp) probFailure_signerViewSample (by
      intro Q
      simpa only [funext (completeFreshSelectedLoopView_eq_elim referenceCache key message)] using
        (probEvent_completeFreshSelectedLoopView_le_uniform attempts key message
          referenceCache workingCache Q hinvariant))
  simpa only [freshSelectedLoopView?_satisfies_iff] using h
noncomputable def freshDigestSelectionProbability
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
    (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]
theorem freshDigestSelectionProbability_le_one
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache ≤ 1 := probEvent_le_one
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix
private theorem probEvent_digestContinuation_prehit_eq
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) (result : DigestAttemptResult)
    (hr : result ∈ support (signDigestAttemptPrefix key message workingCache)) :
    Pr[PrehitSelectedView referenceCache key message P |
      signDigestLoopContinuation attempts key message result.1 result.2] =
      (if FavorablePrehitAttempt referenceCache key message P result then 1 else 0) +
        (if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
          (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0) := by
  cases hresult : result.2.1 with
  | none =>
      have hnot : ¬ FavorablePrehitAttempt referenceCache key message P result := by
        rintro ⟨output, hc, ha, _⟩
        have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
        exact ha (heq.symm.trans hresult)
      simp only [signDigestLoopContinuation, hresult, if_true, if_neg hnot, zero_add]
  | some selected =>
      obtain ⟨index, leaves⟩ := selected
      have hiff : PrehitSelectedView referenceCache key message P
          (some (result.1, index, leaves), result.2.2) ↔ FavorablePrehitAttempt referenceCache key message P result := by
        constructor
        · rintro ⟨randomness, foundIndex, foundLeaves, hfound, output, hc, ho, hP⟩
          have hfirst := congrArg Prod.fst (Option.some.inj hfound)
          refine ⟨output, ?_, ?_, hP⟩
          · rw [hfirst]
            exact hc
          · rw [ho]
            exact Option.some_ne_none _
        · rintro ⟨output, hc, _, hP⟩
          have heq := signDigestAttemptPrefix_cached_result key message workingCache result output hr (hreference hc)
          exact ⟨result.1, index, leaves, rfl, output, hc, heq.symm.trans hresult, hP⟩
      simp only [signDigestLoopContinuation, hresult, probEvent_pure, Option.some_ne_none, if_false, add_zero, hiff]
theorem probEvent_signDigestLoop_prehit_recurrence
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop (attempts + 1) key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P +
        ∑' result, Pr[= result | signDigestAttemptPrefix key message workingCache] *
          if result.2.1 = none then Pr[PrehitSelectedView referenceCache key message P |
            (simulateQ romImpl (signDigestLoop attempts key message)).run result.2.2] else 0 := by
  rw [signDigestLoop_run_succ_eq_attemptPrefix, probEvent_bind_eq_tsum,
    ← probEvent_signDigestAttemptPrefix_favorablePrehit_eq referenceCache workingCache key message P,
    probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
  · rw [probEvent_digestContinuation_prehit_eq attempts key message referenceCache workingCache hreference P result hr]
    split_ifs <;> ring
  · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, ite_self, zero_add]
theorem probEvent_signDigestLoop_prehit_eq_rate_mul_attempts
    (attempts : Nat) (key : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (hreference : referenceCache ≤ workingCache)
    (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView referenceCache key message P |
      (simulateQ romImpl (signDigestLoop attempts key message)).run workingCache] =
      cachedDigestAttemptRate key message referenceCache P * digestAttemptExpectation attempts key message workingCache := by
  induction attempts generalizing workingCache with
  | zero =>
      simp [signDigestLoop, PrehitSelectedView, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_prehit_recurrence attempts key message referenceCache workingCache hreference P,
        digestAttemptExpectation, mul_add, mul_one, ← ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message workingCache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, ih result.2.2
            (hreference.trans (signDigestAttemptPrefix_cache_le key message workingCache result hr))]
          ring
        · simp only [if_neg hnone, mul_zero]
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul, mul_zero]
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
private theorem digestSelection_partition (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result)
    (hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)) :
    (if freshSelectedLoopView? cache key message result ≠ none then (1 : ENNReal) else 0) +
      (if PrehitSelectedView cache key message (fun _ => True) result then 1 else 0) +
      (if result.1 = none then 1 else 0) = 1 := by
  obtain ⟨selected, after⟩ := result
  cases selected with
  | none => simp [freshSelectedLoopView?, PrehitSelectedView]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      cases hc : cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) with
      | none => simp [freshSelectedLoopView?, PrehitSelectedView, hc]
      | some output =>
          have hp : PrehitSelectedView cache key message (fun _ => True) (some (randomness, index, leaves), after) :=
            ⟨randomness, index, leaves, rfl, output, hc,
              signDigestLoop_initial_cached_result attempts key message randomness index leaves cache after output hc hr, trivial⟩
          simp only [freshSelectedLoopView?, hc, Option.some_ne_none, if_false, ne_eq, not_true_eq_false, hp,
            if_true, zero_add, add_zero]
theorem probEvent_signDigestLoop_selection_mass (attempts : Nat) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    Pr[fun result => freshSelectedLoopView? cache key message result ≠ none |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[PrehitSelectedView cache key message (fun _ => True) |
        (simulateQ romImpl (signDigestLoop attempts key message)).run cache] +
      Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] = 1 := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  calc
    _ = ∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] := by
      apply tsum_congr
      intro result
      by_cases hr : result ∈ support ((simulateQ romImpl (signDigestLoop attempts key message)).run cache)
      · have h := congrArg (fun value => Pr[= result | (simulateQ romImpl (signDigestLoop attempts key message)).run cache] * value)
          (digestSelection_partition attempts key message cache result hr)
        simpa only [mul_add, mul_ite, mul_one, mul_zero] using h
      · simp only [probOutput_eq_zero_of_not_mem_support hr, ite_self, zero_add]
    _ = 1 := tsum_probOutput_of_liftM_PMF _
noncomputable def digestExhaustionProbability (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  Pr[fun result => result.1 = none | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache]
theorem freshSelection_add_cachedAttempts_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedDigestAttemptRate key message cache (fun _ => True) * digestAttemptExpectation digestAttemptLimit key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := probEvent_signDigestLoop_selection_mass digestAttemptLimit key message cache
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl] at h
  exact h
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_3 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signAttempt signDigestAttemptPrefix
theorem cachedDigestAttemptRate_eq_count (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    cachedDigestAttemptRate key message cache P =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ := by
  let hit : Randomness → Prop := fun randomness => ∃ output,
    cache (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = some output ∧
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output)
  let targets : Finset Randomness := Finset.univ.filter hit
  let fiber := cachedMessageInputSetWhere cache key.parameter key.root message P
  let embedding : (targets : Set Randomness) ↪ fiber :=
    ⟨fun randomness =>
      ⟨⟨tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness.1),
          Classical.choose (Finset.mem_filter.mp randomness.2).2⟩,
        ⟨⟨(Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).1, ⟨randomness.1, rfl⟩⟩,
          (Classical.choose_spec (Finset.mem_filter.mp randomness.2).2).2⟩⟩,
      fun left right heq => Subtype.ext <|
        (messageDigestPayload_injective key.root <|
          (tweakableHashInput_injective key.parameter (by trivial) (by trivial) <|
            congrArg (fun entry : fiber => entry.1.1) heq).2).2⟩
  have hsurjective : Function.Surjective embedding := by
    rintro ⟨⟨input, output⟩, ⟨hcached, randomness, hinput⟩, hadmissible, hP⟩
    change input = tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness) at hinput
    subst input
    have hh : hit randomness := ⟨output, hcached, hadmissible, hP⟩
    let target : (targets : Set Randomness) := ⟨randomness, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    refine ⟨target, Subtype.ext ?_⟩
    have hout := Option.some.inj ((Classical.choose_spec (Finset.mem_filter.mp target.2).2).1.symm.trans hcached)
    exact Sigma.ext (by rfl) (heq_of_eq hout)
  have hcard : (targets.card : ENNReal) = cachedMessageEntryCountWhere cache key.parameter key.root message P := by
    have h := Set.encard_congr (Equiv.ofBijective embedding ⟨embedding.injective, hsurjective⟩)
    simpa only [cachedMessageEntryCountWhere, fiber, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe] using
      congrArg ENat.toENNReal h
  rw [cachedDigestAttemptRate, probEvent_uniformSample, card_randomness, div_eq_mul_inv]
  change (targets.card : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹ = _
  rw [hcard]
noncomputable def exactDigestReuseWeight (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) : ENNReal :=
  digestAttemptExpectation digestAttemptLimit key message cache * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹
theorem probEvent_signDigestLoop_prehit_eq_count_mul_exactWeight
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) (P : FewTimeView → Prop) :
    Pr[PrehitSelectedView cache key message P |
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] =
      cachedMessageEntryCountWhere cache key.parameter key.root message P * exactDigestReuseWeight key message cache := by
  rw [probEvent_signDigestLoop_prehit_eq_rate_mul_attempts digestAttemptLimit key message cache cache le_rfl,
    cachedDigestAttemptRate_eq_count, exactDigestReuseWeight]
  ring
theorem freshSelection_add_count_exactWeight_add_exhaustion (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    freshDigestSelectionProbability key message cache +
      cachedMessageEntryCountWhere cache key.parameter key.root message (fun _ => True) * exactDigestReuseWeight key message cache +
      digestExhaustionProbability key message cache = 1 := by
  have h := freshSelection_add_cachedAttempts_add_exhaustion key message cache
  rw [cachedDigestAttemptRate_eq_count] at h
  unfold exactDigestReuseWeight
  convert h using 1; ring
end SphincsSecurity.Concrete
end
