import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ConcreteTargetShapeQuery
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FreshTargetShapeAverage
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetIndexEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedTargetIncrement
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestCompletionCacheGrowth

section





namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
theorem expected_uniformFewTimeView_eq_leafAverage (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target) =
      (Fintype.card Index : ENNReal)⁻¹ * ∑ index : Index, leafAverage (fun leaves => f (index, leaves)) := by
  simp only [probOutput_uniformFewTimeView, tsum_fintype, Fintype.sum_prod_type, leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro leaves _
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  ring
theorem expected_signerViewSample_le (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | signerViewSample] * f target) ≤
      admissibleProbability⁻¹ * ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro target
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  have h := probOutput_uniformFewTimeView_admissible target
  have hle : admissibleProbability * Pr[= target | signerViewSample] ≤
      Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
    rw [← h]
    split_ifs <;> simp
  calc
    Pr[= target | signerViewSample] =
        admissibleProbability⁻¹ * (admissibleProbability * Pr[= target | signerViewSample]) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel admissibleProbability_pos admissibleProbability_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hle
theorem expected_fresh_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card := by
  rw [expected_uniformFewTimeView_eq_leafAverage]
  apply mul_le_mul' le_rfl
  rw [← targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
  calc
    _ ≤ ∑ index : Index, targetShapeEnvelope (constRate (Fintype.card Index : ENNReal)⁻¹) reuse (constRate cachedIndexRate)
        queries signings (liftTargetIndexVector (indexPowerMoments key cache log index)) groups remaining := by
      apply Finset.sum_le_sum
      intro index _
      have hfubini := leafAverage_targetShapeEnvelope_le (L := FtsLeaf)
        (F := fun leaves => targetShapeMoments key cache log payload (index, leaves))
        (rate := fun leaves => signerRate (index, leaves)) (arrival := fun leaves => arrivalRate (index, leaves)) reuse
        (targetShapeMoments_shapeLocal key cache log payload index) (signerRate_local index) (arrivalRate_local index)
        (fun coords hne => leafAverage_signerRate_le index coords hne)
        (fun coords hne => leafAverage_arrivalRate_le index coords hne) queries signings groups remaining hvalid
      refine hfubini.trans ?_
      exact targetShapeEnvelope_mono _ _ _ queries signings
        (averagedShape_targetShapeMoments_le key cache log payload hfresh hsigned index) groups remaining hvalid
    _ = _ := by
      have hsum : liftTargetIndexVector (targetIndexMoments key cache log) =
          fun G R => ∑' index : Index, liftTargetIndexVector (indexPowerMoments key cache log index) G R := by
        funext G R
        simp only [liftTargetIndexVector, targetIndexMoments, indexPowerMoments, tsum_fintype]
      rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]
theorem targetShapeMoments_cacheQuery_self_vector (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload target =
      targetShapeMoments key before log payload target := by
  funext groups remaining
  exact targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining _ output hfresh hsigned (Or.inr rfl)
theorem expected_cacheQuery_freshTargetEnvelope_le (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        targetShapeEnvelope (signerRate (hashOutputFewTimeView output)) reuse (arrivalRate (hashOutputFewTimeView output))
          queries signings
          (targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload
            (hashOutputFewTimeView output)) groups remaining else 0)) ≤
      (Fintype.card Index : ENNReal)⁻¹ *
        targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
          (targetIndexMoments key before log) groups.card remaining.card := by
  simp only [targetShapeMoments_cacheQuery_self_vector key before log payload _ _ hfresh hsigned]
  exact (expected_uniformHashOutput_admissible_weight_le_uniform
    (fun target => targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
      (targetShapeMoments key before log payload target) groups remaining)).trans
    (expected_fresh_targetShapeEnvelope_le key before log payload hfresh hsigned reuse queries signings groups remaining hvalid)
theorem expected_signer_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | signerViewSample] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card) :=
  (expected_signerViewSample_le _).trans (mul_le_mul' le_rfl
    (expected_fresh_targetShapeEnvelope_le key cache log payload hfresh hsigned reuse queries signings groups remaining hvalid))
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem cacheMessageWeight_exclude_fresh (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (hfresh : cache targetInput = none) (weight : FewTimeView → ENNReal) :
    cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else weight source) cache =
      cacheMessageWeight parameter (fun _ source => weight source) cache := by
  unfold cacheMessageWeight
  apply tsum_congr
  intro input
  by_cases heq : input = targetInput
  · subst input
    simp only [cacheMessageEntryWeight, hfresh]
  · unfold cacheMessageEntryWeight
    cases cache input <;> simp only [heq, if_false]
theorem targetShapeMoments_fresh_payload_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (first second : HashInput)
    (hfirst : cache (tweakableHashInput key.parameter .message first) = none)
    (hsecond : cache (tweakableHashInput key.parameter .message second) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (target : FewTimeView) :
    targetShapeMoments key cache log first target = targetShapeMoments key cache log second target := by
  funext groups remaining
  unfold targetShapeMoments normalizedTargetLogProduct normalizedTargetLogMatch
  simp only [normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hfirst,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hsecond,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log first hfirst hsigned,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log second hsecond hsigned]
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def newTargetEnvelopeCharge (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  cacheMessageWeight key.parameter (fun input target => if before input = none then
    targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
      (targetShapeMoments key after log (payloadOf input) target) groups remaining else 0) after
theorem newTargetEnvelopeCharge_of_no_new (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hnone : ∀ payload output, before (tweakableHashInput key.parameter .message payload) = none →
      after (tweakableHashInput key.parameter .message payload) = some output → ¬ Admissible (truncateMessageDigest output)) :
    newTargetEnvelopeCharge key before after log reuse queries signings groups remaining = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro input
  unfold cacheMessageEntryWeight
  cases houtput : after input with
  | none => rfl
  | some output =>
      simp only
      split_ifs with hgood hfresh
      · obtain ⟨payload, rfl⟩ := hgood.1
        exact (hnone payload output hfresh houtput hgood.2).elim
      · rfl
      · rfl
end SphincsSecurity.Concrete
end

section





namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop
theorem digestCompletion_new_targetShapeMoments_eq (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hselected : loop.1 = some (randomness, index, leaves))
    (hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none)
    (target : FewTimeView) :
    targetShapeMoments key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target =
      targetShapeMoments key before log (messageDigestPayload key.root message randomness) target := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have heligible : eligibleSigningView? (messageAnswers key.parameter loop.2) key.root
      (messageDigestPayload key.root message randomness) ⟨message, result.1.1⟩ = none := by
    cases hs : result.1.1 with
    | none => simp [eligibleSigningView?]
    | some signature =>
        obtain ⟨otherIndex, otherLeaves, hother⟩ := hcompletion.1.2 signature hs
        have hr : signature.randomness = randomness := congrArg Prod.fst (Option.some.inj (hother.symm.trans hselected))
        simp [eligibleSigningView?, hr]
  have hlog (required : Finset IndexGroup) :
      normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) (messageDigestPayload key.root message randomness) target required =
        normalizedTargetLogProduct key before log (messageDigestPayload key.root message randomness) target required := by
    have heq : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩])
        (messageDigestPayload key.root message randomness) target required := by
      unfold normalizedTargetLogProduct normalizedTargetLogMatch
      rw [hcompletion.2]
    rw [heq]
    exact normalizedTargetLogProduct_append_none key before loop.2 log _ _ target required hcache hsigned heligible
  funext groups remaining
  unfold targetShapeMoments
  rw [hlog]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion]
  simp only [selectedLoopInputWeight, hselected, hfresh, if_true, add_zero]
theorem digestCompletion_newTargetEnvelopeCharge_eq_selected
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) reuse queries signings groups remaining =
      selectedLoopInputWeight key message (fun input target => if before input = none then
        targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
          (targetShapeMoments key before log (payloadOf input) target) groups remaining else 0) loop := by
  unfold newTargetEnvelopeCharge
  rw [digestCompletion_cacheMessageWeight_eq key message before loop hloop result hcompletion,
    cacheMessageWeight_fresh_restriction, zero_add]
  cases hs : loop.1 with
  | none => simp only [selectedLoopInputWeight, hs]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
      · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput]
        rw [digestCompletion_new_targetShapeMoments_eq key message before loop hloop result hcompletion
          log hsigned randomness index leaves hs hfresh]
      · simp only [selectedLoopInputWeight, hs, if_neg hfresh]
theorem expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining) ≤
      freshDigestSelectionProbability key message before *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key before log) groups.card remaining.card)) := by
  by_cases hexists : ∃ payload, before (tweakableHashInput key.parameter .message payload) = none
  · obtain ⟨reference, hreference⟩ := hexists
    let weight := fun source => targetShapeEnvelope (signerRate source) reuse (arrivalRate source) queries signings
      (targetShapeMoments key before log reference source) groups remaining
    have hbound := expected_digestCompletion_freshCost_le key message before finish
      (fun result => newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining) weight (by
          intro loop hl result hr
          rw [digestCompletion_newTargetEnvelopeCharge_eq_selected key message before loop hl (record result)
            (hcompletion loop hl result hr) log hsigned]
          cases hs : loop.1 with
          | none => simp only [selectedLoopInputWeight, hs, le_refl]
          | some selected =>
              obtain ⟨randomness, index, leaves⟩ := selected
              by_cases hfresh : before (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) = none
              · simp only [selectedLoopInputWeight, hs, hfresh, if_true, payloadOf_tweakableHashInput, weight]
                rw [targetShapeMoments_fresh_payload_eq key before log _ reference hfresh hreference hsigned]
              · simp only [selectedLoopInputWeight, hs, if_neg hfresh, le_refl])
    exact hbound.trans (mul_le_mul' le_rfl
      (expected_signer_targetShapeEnvelope_le key before log reference hreference hsigned
        reuse queries signings groups remaining hvalid))
  · have hzero (result : α) : newTargetEnvelopeCharge key before (record result).2 (log ++ [⟨message, (record result).1.1⟩])
        reuse queries signings groups remaining = 0 :=
      newTargetEnvelopeCharge_of_no_new key before (record result).2 _ reuse queries signings groups remaining
        (fun payload _ hfresh _ _ => hexists ⟨payload, hfresh⟩)
    simp only [hzero, mul_zero, tsum_zero, zero_le]
end SphincsSecurity.Concrete
end
