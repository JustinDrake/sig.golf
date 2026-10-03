import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeProbability
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeLoop
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeSignerView
import SigGolfCandidate.SphincsSecurity.Proof.Fts.AdmissibleCount

section


set_option autoImplicit true
namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity_1 {α : Type} [Fintype α] [Nonempty α] : SampleableType α :=
  SampleableType.ofFintype α
theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    𝒮[(do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right))] =
      𝒮[($ᵗ (α × β) : ProbComp (α × β))] := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]
def listToFunction (count : Nat) (values : List FewTimeView) : Fin count → FewTimeView :=
  fun position => values.getD position.val default
@[simp]
theorem listToFunction_ofFn (values : Fin count → FewTimeView) :
    listToFunction count (List.ofFn values) = values := by
  funext position
  simp [listToFunction, List.getD]
end SphincsSecurity.Concrete
end

section





namespace SphincsSecurity.Concrete
open OracleComp OracleSpec ENNReal
abbrev HashOutputRest :=
  DigestUnusedBits × BitVec (hashOutputBits - messageDigestBits)
def reorderHashOutputCoordinates :
    (HashOutputRest × FewTimeView) ≃ HashOutputCoordinates where
  toFun value := ((value.2, value.1.1), value.1.2)
  invFun value := ((value.1.2, value.2), value.1.1)
  left_inv _ := rfl
  right_inv _ := rfl
set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutputCoordinates_bind_reordered {Result : Type}
    (continuation : HashOutputCoordinates → ProbComp Result) :
    𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
      𝒮[($ᵗ HashOutputRest : ProbComp HashOutputRest) >>= fun rest =>
        ($ᵗ FewTimeView : ProbComp FewTimeView) >>= fun view =>
          continuation ((view, rest.1), rest.2)] := by
  let paired : ProbComp (HashOutputRest × FewTimeView) := do
    let rest ← $ᵗ HashOutputRest
    let view ← $ᵗ FewTimeView
    pure (rest, view)
  have hpaired :
      𝒮[paired] = 𝒮[($ᵗ (HashOutputRest × FewTimeView) :
        ProbComp (HashOutputRest × FewTimeView))] := by
    exact evalDist_independent_uniform_pair
  have hreordered :
      𝒮[reorderHashOutputCoordinates <$> paired] =
        𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] := by
    calc
      𝒮[reorderHashOutputCoordinates <$> paired] =
          reorderHashOutputCoordinates <$> 𝒮[paired] := by rw [evalSPMF_map]
      _ = reorderHashOutputCoordinates <$>
          𝒮[($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [hpaired]
      _ = 𝒮[reorderHashOutputCoordinates <$>
          ($ᵗ (HashOutputRest × FewTimeView) :
            ProbComp (HashOutputRest × FewTimeView))] := by rw [evalSPMF_map]
      _ = 𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
        evalSPMF_map_bijective_uniform_cross
          (α := HashOutputRest × FewTimeView) (β := HashOutputCoordinates)
          (reorderHashOutputCoordinates : HashOutputRest × FewTimeView →
            HashOutputCoordinates)
          reorderHashOutputCoordinates.bijective
  calc
    𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>= continuation] =
        𝒮[(reorderHashOutputCoordinates <$> paired) >>= continuation] := by
      rw [evalSPMF_bind, ← hreordered, ← evalSPMF_bind]
    _ = _ := by
      simp only [paired, map_eq_bind_pure_comp, bind_assoc, pure_bind,
        reorderHashOutputCoordinates, Function.comp_apply]
      rfl
abbrev AdmissibleView := {view : FewTimeView // AdmissibleLeaves view.2}
def admissibleViewEquiv : AdmissibleView ≃ Index × {leaves : IndexGroup → FtsLeaf // AdmissibleLeaves leaves} where
  toFun view := (view.1.1, ⟨view.1.2, view.2⟩)
  invFun value := ⟨(value.1, value.2.1), value.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem card_admissibleView :
    (Fintype.card AdmissibleView : ENNReal) = admissibleProbability * Fintype.card FewTimeView := by
  rw [Fintype.card_congr admissibleViewEquiv, Fintype.card_prod, Fintype.card_subtype, Nat.cast_mul,
    card_admissibleLeaves_eq_mul, Fintype.card_prod, Nat.cast_mul]
  ring
instance : Nonempty AdmissibleView := by
  apply Fintype.card_pos_iff.mp
  have h : (Fintype.card AdmissibleView : ENNReal) ≠ 0 := by
    rw [card_admissibleView]
    exact mul_ne_zero admissibleProbability_pos (by simp)
  exact Nat.pos_of_ne_zero (by exact_mod_cast h)
noncomputable instance : SampleableType AdmissibleView := SampleableType.ofFintype AdmissibleView
noncomputable irreducible_def signerViewSample : ProbComp FewTimeView :=
  Subtype.val <$> ($ᵗ AdmissibleView : ProbComp AdmissibleView)
theorem probOutput_signerViewSample (view : FewTimeView) :
    Pr[= view | signerViewSample] =
      if AdmissibleLeaves view.2 then (admissibleProbability * Fintype.card FewTimeView)⁻¹ else 0 := by
  rw [signerViewSample_def]
  split_ifs with hview
  · rw [show view = (⟨view, hview⟩ : AdmissibleView).val from rfl,
      probOutput_map_injective _ Subtype.val_injective, probOutput_uniformSample, card_admissibleView]
  · rw [probOutput_map_eq_tsum_ite]
    apply ENNReal.tsum_eq_zero.mpr
    intro other
    rw [if_neg]
    rintro rfl
    exact hview other.2
theorem probFailure_signerViewSample : Pr[⊥ | signerViewSample] = 0 := by
  rw [signerViewSample_def, probFailure_map]
  exact probFailure_uniformSample AdmissibleView
theorem probEvent_signerView_index (index : Index) :
    Pr[fun view : FewTimeView => view.1 = index | signerViewSample] = (Fintype.card Index : ENNReal)⁻¹ := by
  classical
  rw [probEvent_eq_tsum_ite, tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single index (fun other _ hother =>
    Finset.sum_eq_zero (fun leaves _ => if_neg hother)) (fun h => (h (Finset.mem_univ _)).elim)]
  simp only [if_true, probOutput_signerViewSample]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_admissibleLeaves_eq_mul]
  have hcard : (Fintype.card FewTimeView : ENNReal) =
      (Fintype.card Index : ENNReal) * Fintype.card (IndexGroup → FtsLeaf) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  rw [hcard, ENNReal.mul_inv (Or.inl admissibleProbability_pos) (Or.inl admissibleProbability_ne_top),
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  calc
    _ = (admissibleProbability * admissibleProbability⁻¹) *
        ((Fintype.card (IndexGroup → FtsLeaf) : ENNReal) * (Fintype.card (IndexGroup → FtsLeaf) : ENNReal)⁻¹) *
          (Fintype.card Index : ENNReal)⁻¹ := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel admissibleProbability_pos admissibleProbability_ne_top,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, one_mul]
theorem probOutput_uniformFewTimeView (view : FewTimeView) :
    Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] = (Fintype.card FewTimeView : ENNReal)⁻¹ :=
  probOutput_uniformSample FewTimeView view
theorem probOutput_uniformFewTimeView_admissible (view : FewTimeView) :
    (if AdmissibleLeaves view.2 then Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] else 0) =
      admissibleProbability * Pr[= view | signerViewSample] := by
  rw [probOutput_signerViewSample, probOutput_uniformFewTimeView]
  split_ifs
  · rw [ENNReal.mul_inv (Or.inl admissibleProbability_pos) (Or.inl admissibleProbability_ne_top), ← mul_assoc,
      ENNReal.mul_inv_cancel admissibleProbability_pos admissibleProbability_ne_top, one_mul]
  · rw [mul_zero]
theorem probEvent_uniformFewTimeView_admissible (P : FewTimeView → Prop) :
    Pr[fun view => AdmissibleLeaves view.2 ∧ P view | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      admissibleProbability * Pr[P | signerViewSample] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro view
  by_cases hP : P view
  · by_cases hadm : AdmissibleLeaves view.2
    · simp only [hP, hadm, and_self, if_true]
      have h := probOutput_uniformFewTimeView_admissible view
      rw [if_pos hadm] at h
      exact h
    · have h := probOutput_uniformFewTimeView_admissible view
      rw [if_neg hadm] at h
      simp only [hP, hadm, and_true, if_false, if_true]
      exact h
  · simp [hP]
theorem probEvent_uniformFewTimeView_admissible_eq :
    Pr[fun view => AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] = admissibleProbability := by
  have h := probEvent_uniformFewTimeView_admissible (fun _ => True)
  simp only [and_true] at h
  rw [h]
  simp
theorem probEvent_uniformFewTimeView_not_admissible :
    Pr[fun view => ¬ AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] =
      1 - admissibleProbability := by
  have hc := probEvent_compl ($ᵗ FewTimeView : ProbComp FewTimeView) (fun view => AdmissibleLeaves view.2)
  rw [probEvent_uniformFewTimeView_admissible_eq] at hc
  simp only [probFailure_uniformSample, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq admissibleProbability_ne_top ((add_comm _ _).trans hc)
theorem probEvent_uniformFewTimeView_bind_le {α : Type} (g : FewTimeView → ProbComp α) (Q : α → Prop)
    (P : FewTimeView → Prop) [DecidablePred P] (bound : ENNReal) (hbound : Pr[P | signerViewSample] ≤ bound)
    (hadmissible : ∀ view, AdmissibleLeaves view.2 → Pr[Q | g view] ≤ if P view then 1 else 0)
    (hrejected : ∀ view, ¬ AdmissibleLeaves view.2 → Pr[Q | g view] ≤ bound) :
    Pr[Q | ($ᵗ FewTimeView : ProbComp FewTimeView) >>= g] ≤ bound := by
  classical
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' view, Pr[= view | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ((if AdmissibleLeaves view.2 ∧ P view then 1 else 0) + (if AdmissibleLeaves view.2 then 0 else bound)) := by
      apply ENNReal.tsum_le_tsum
      intro view
      apply mul_le_mul' le_rfl
      by_cases h : AdmissibleLeaves view.2
      · simpa [h] using hadmissible view h
      · simpa [h] using hrejected view h
    _ = Pr[fun view => AdmissibleLeaves view.2 ∧ P view | ($ᵗ FewTimeView : ProbComp FewTimeView)] +
        Pr[fun view => ¬ AdmissibleLeaves view.2 | ($ᵗ FewTimeView : ProbComp FewTimeView)] * bound := by
      simp only [mul_add, ENNReal.tsum_add]
      congr 1
      · rw [probEvent_eq_tsum_ite]
        apply tsum_congr
        intro view
        split_ifs <;> simp
      · rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
        apply tsum_congr
        intro view
        split_ifs <;> simp
    _ ≤ admissibleProbability * bound + (1 - admissibleProbability) * bound := by
      rw [probEvent_uniformFewTimeView_admissible, probEvent_uniformFewTimeView_not_admissible]
      gcongr
    _ = bound := by
      rw [← add_mul, add_tsub_cancel_of_le admissibleProbability_le_one, one_mul]
set_option maxRecDepth 100000 in
theorem probEvent_uniformHashOutput_view (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput => P (hashOutputFewTimeView output) | ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  let coordinates : HashOutput → FewTimeView × DigestUnusedBits := fun output =>
    digestCoordinates (truncateMessageDigest output)
  calc
    Pr[fun output : HashOutput => P (hashOutputFewTimeView output) | ($ᵗ HashOutput : ProbComp HashOutput)] =
        Pr[fun value => P value.1 | coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[fun value => P value.1 |
        ($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (by
        simpa only [coordinates] using evalDist_hashOutput_digestCoordinates_uniform)
    _ = Pr[P | Prod.fst <$> ($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] := by
      rw [probEvent_map]
      rfl
    _ = _ := probEvent_congr' (fun _ _ => Iff.rfl) evalSPMF_map_fst_uniformSample_prod
theorem probEvent_uniformHashOutput_admissible_view
    (P : FewTimeView → Prop) :
    Pr[fun output : HashOutput =>
      signAttemptResultOfOutput output ≠ none ∧ P (hashOutputFewTimeView output) |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
      admissibleProbability * Pr[P | signerViewSample] := by
  rw [← probEvent_uniformFewTimeView_admissible, ← probEvent_uniformHashOutput_view]
  congr 1
  funext output
  rw [signAttemptResultOfOutput_ne_none_iff, admissible_iff_view]
def OnlyRejectedNewMessageEntries (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) : Prop :=
  ∀ randomness output,
    referenceCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none →
    workingCache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = some output →
    signAttemptResultOfOutput output = none
theorem onlyRejectedNewMessageEntries_self (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) :
    OnlyRejectedNewMessageEntries cache cache secretKey message := by
  intro randomness output hmiss hhit
  rw [hmiss] at hhit
  simp at hhit
theorem onlyRejectedNewMessageEntries_cacheRejected
    (referenceCache workingCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (output : HashOutput)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message)
    (hrejected : signAttemptResultOfOutput output = none) :
    OnlyRejectedNewMessageEntries referenceCache
      (workingCache.cacheQuery
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled)) output)
      secretKey message := by
  intro randomness found hreferenceFound hfound
  let foundInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : foundInput = sampledInput
  · have hfound' : some output = some found := by
      calc
        some output =
            (workingCache.cacheQuery sampledInput output) sampledInput := by
              rw [QueryCache.cacheQuery_self]
        _ = (workingCache.cacheQuery sampledInput output) foundInput := by rw [hsame]
        _ = some found := by simpa only [foundInput, sampledInput] using hfound
    rw [← Option.some.inj hfound']
    exact hrejected
  · have hworking : workingCache foundInput = some found := by
      rw [QueryCache.cacheQuery_of_ne workingCache output hsame] at hfound
      simpa only [foundInput, sampledInput] using hfound
    exact hinvariant randomness found hreferenceFound hworking
set_option maxRecDepth 100000 in
theorem onlyRejectedNewMessageEntries_of_failed_attempt
    (referenceCache beforeCache afterCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (sampled : Randomness)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache beforeCache secretKey message)
    (hmem : (none, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message sampled)).run beforeCache)) :
    OnlyRejectedNewMessageEntries referenceCache afterCache secretKey message := by
  intro randomness output hreference hafter
  let target := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)
  let sampledInput := tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message sampled)
  by_cases hsame : target = sampledInput
  · apply Eq.symm
    have hafterSampled : afterCache sampledInput = some output := by
      change afterCache target = some output at hafter
      rw [← hsame]
      exact hafter
    change afterCache
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message sampled)) = some output at hafterSampled
    exact signAttempt_result_of_cached secretKey message sampled beforeCache afterCache
      none output hafterSampled hmem
  · by_cases hbefore : beforeCache target = none
    · change beforeCache
        (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none at hbefore
      change (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) ≠
        tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message sampled) at hsame
      have hnone := signAttempt_cache_other_none secretKey message sampled beforeCache afterCache
        none hmem _ hbefore hsame
      rw [hnone] at hafter
      simp at hafter
    · obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp hbefore
      have hmemWorld : (none, afterCache) ∈ support
          ((simulateQ romImpl
            (liftM (signAttempt secretKey message sampled :
              OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
                OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))).run
              beforeCache) := by
        rw [simulateQ_romImpl_liftM]
        exact hmem
      have hle : beforeCache ≤ afterCache :=
        simulateQ_romImpl_cache_le
          (liftM (signAttempt secretKey message sampled :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
              OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
          beforeCache (none, afterCache) hmemWorld
      have heq : prior = output := Option.some.inj ((hle hprior).symm.trans hafter)
      rw [← heq]
      exact hinvariant randomness prior hreference hprior
def FreshSelectedView (referenceCache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (P : FewTimeView → Prop)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Prop :=
  ∃ randomness index leaves,
    result.1 = some (randomness, index, leaves)
      ∧ referenceCache (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)) = none
      ∧ P (selectedFewTimeView index leaves)
end SphincsSecurity.Concrete
end
