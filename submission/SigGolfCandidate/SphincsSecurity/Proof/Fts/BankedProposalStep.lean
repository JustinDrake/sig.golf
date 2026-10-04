import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CacheMessageWeight
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ReuseRawEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestCompletionNewTarget
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ExactTargetShapeSigning
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeContinuation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalProposalExecution

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def certificateBankCount (bank : HashInput → Bool) : ENNReal :=
  ∑' input, if bank input then 1 else 0
theorem certificateBankCount_empty : certificateBankCount (fun _ => false) = 0 := by
  simp [certificateBankCount]
theorem one_le_certificateBankCount (bank : HashInput → Bool) (input : HashInput) (hbank : bank input = true) :
    1 ≤ certificateBankCount bank := by
  have h := ENNReal.le_tsum (f := fun input => if bank input then (1 : ENNReal) else 0) input
  simpa only [certificateBankCount, hbank, if_true] using h
noncomputable def bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) : ENNReal :=
  ∑' input, if bank input then 1 else if stopped then 0 else
    cacheMessageEntryWeight parameter weight cache input
theorem bankedCacheWeight_mono (parameter : PublicParameter)
    (first second : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hle : ∀ input target, first input target ≤ second input target) :
    bankedCacheWeight parameter first bank stopped cache ≤ bankedCacheWeight parameter second bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · unfold cacheMessageEntryWeight
    cases cache input
    · exact le_rfl
    · simp only
      split_ifs
      · exact hle input _
      · exact le_rfl
theorem bankedCacheWeight_discard_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank stopped cache ≤ bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases bank input <;> cases stopped <;> simp
theorem certificateBankCount_le_bankedCacheWeight (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec) :
    certificateBankCount bank ≤ bankedCacheWeight parameter weight bank stopped cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  split_ifs <;> first | exact le_rfl | exact zero_le
theorem bankedCacheWeight_stopped (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank true cache = certificateBankCount bank := by
  simp only [bankedCacheWeight, certificateBankCount, if_true]
theorem bankedCacheWeight_live (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (cache : QueryCache HashSpec) :
    bankedCacheWeight parameter weight bank false cache = certificateBankCount bank +
      cacheMessageWeight parameter (fun input target => if bank input then 0 else weight input target) cache := by
  rw [bankedCacheWeight, certificateBankCount, cacheMessageWeight, ← ENNReal.tsum_add]
  apply tsum_congr
  intro input
  cases hbank : bank input <;> cases hcache : cache input <;>
    simp [cacheMessageEntryWeight, hbank, hcache]
theorem bankedCacheWeight_bank_le (parameter : PublicParameter)
    (weight : HashInput → FewTimeView → ENNReal) (bank completed : HashInput → Bool)
    (stopped : Bool) (cache : QueryCache HashSpec)
    (hcompleted : ∀ input, completed input = true →
      1 ≤ cacheMessageEntryWeight parameter weight cache input) :
    bankedCacheWeight parameter weight (fun input => bank input || completed input) stopped cache ≤
      bankedCacheWeight parameter weight bank false cache := by
  apply ENNReal.tsum_le_tsum
  intro input
  cases hbank : bank input <;> cases hcomplete : completed input <;>
    simp only [hbank, hcomplete, Bool.false_or, Bool.true_or, Bool.false_eq_true, if_true, if_false, le_refl]
  · cases stopped <;> simp
  · exact hcompleted input hcomplete
theorem expected_bankedCacheWeight_step_le_of_split {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hsplit : ∀ result ∈ support computation, ∀ value : HashInput → FewTimeView → ENNReal,
      cacheMessageWeight parameter value (after result) = cacheMessageWeight parameter value before +
        cacheMessageWeight parameter (fun input target => if before input = none then value input target else 0) (after result))
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge := by
  let pending := fun result input target => if bank input then 0 else weight result input target
  have hstep (result : α) (hr : result ∈ support computation) :
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result) ≤
      certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
        cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
          (after result) := by
    apply (bankedCacheWeight_bank_le parameter (weight result) bank (completed result) (stopped result)
      (after result) (hcompleted result hr)).trans
    rw [bankedCacheWeight_live, hsplit result hr (pending result), ← add_assoc]
    apply add_le_add le_rfl
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    split_ifs <;> first | exact le_rfl | exact zero_le
  have hold' : (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) ≤
      cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before := by
    rw [expected_cacheMessageWeight]
    apply cacheMessageWeight_mono
    intro input target
    dsimp only [pending]
    cases hb : bank input
    · simpa only [hb, Bool.false_eq_true, if_false] using hold input target
    · simp only [if_true, mul_zero, tsum_zero, le_refl]
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (certificateBankCount bank + cacheMessageWeight parameter (pending result) before +
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · exact mul_le_mul' le_rfl (hstep result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | computation]) * certificateBankCount bank +
        (∑' result, Pr[= result | computation] * cacheMessageWeight parameter (pending result) before) +
        (∑' result, Pr[= result | computation] *
          cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
            (after result)) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ certificateBankCount bank +
        cacheMessageWeight parameter (fun input target => if bank input then 0 else initial input target) before + charge :=
      add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hold') hnew
    _ = _ := by rw [bankedCacheWeight_live]
theorem expected_bankedCacheWeight_step_le {α : Type} (parameter : PublicParameter)
    (computation : ProbComp α) (before : QueryCache HashSpec) (after : α → QueryCache HashSpec)
    (weight : α → HashInput → FewTimeView → ENNReal)
    (initial : HashInput → FewTimeView → ENNReal) (bank : HashInput → Bool)
    (completed : α → HashInput → Bool) (stopped : α → Bool) (charge : ENNReal)
    (hcache : ∀ result ∈ support computation, before ≤ after result)
    (hcompleted : ∀ result ∈ support computation, ∀ input, completed result input = true →
      1 ≤ cacheMessageEntryWeight parameter (weight result) (after result) input)
    (hold : ∀ input target, (∑' result, Pr[= result | computation] * weight result input target) ≤ initial input target)
    (hnew : (∑' result, Pr[= result | computation] *
      cacheMessageWeight parameter (fun input target => if before input = none then weight result input target else 0)
        (after result)) ≤ charge) :
    (∑' result, Pr[= result | computation] *
      bankedCacheWeight parameter (weight result) (fun input => bank input || completed result input)
        (stopped result) (after result)) ≤ bankedCacheWeight parameter initial bank false before + charge :=
  expected_bankedCacheWeight_step_le_of_split parameter computation before after weight initial bank completed stopped charge
    (fun result hr value => cacheMessageWeight_of_le parameter value before (after result) (hcache result hr))
    hcompleted hold hnew
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem newTargetEnvelopeCharge_cacheQuery (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    newTargetEnvelopeCharge key before (before.cacheQuery input output) log reuse queries signings groups remaining =
      if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        targetShapeEnvelope (signerRate (hashOutputFewTimeView output)) reuse (arrivalRate (hashOutputFewTimeView output))
          queries signings
          (targetShapeMoments key (before.cacheQuery input output) log (payloadOf input) (hashOutputFewTimeView output)) groups remaining else 0 := by
  unfold newTargetEnvelopeCharge
  rw [cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh,
    cacheMessageWeight_fresh_restriction, zero_add]
  simp only [hfresh, if_true]
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_signWithView_newTargetEnvelopeCharge_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) reuse queries signings groups remaining) ≤
        freshDigestSelectionProbability key message before *
          (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
            targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
              (targetIndexMoments key before log) groups.card remaining.card)) := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log hsigned reuse queries signings groups remaining hvalid
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def freshWorldTargetHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => if MessageHashInput parameter input ∧ cache input = none then 1 else 0
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
noncomputable abbrev reuseNewTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (before : QueryCache HashSpec) (after : CoverLogState) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  newTargetEnvelopeCharge key before after.1 after.2 reuse budget signatures groups remaining
theorem expected_randomOracle_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 (.inr input) : ENNReal) *
        ((Fintype.card Index : ENNReal)⁻¹ *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (state.1.cacheQuery input output, state.2) groups remaining) ≤ _
    simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge_cacheQuery key state.1 state.2 _ _ _ groups remaining input _ hfresh]
    by_cases hmessage : MessageHashInput key.parameter input
    · obtain ⟨payload, rfl⟩ := hmessage
      simp only [show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
        true_and, payloadOf_tweakableHashInput, freshWorldTargetHashCost, hfresh, and_self, if_true, Nat.cast_one, one_mul]
      refine (expected_cacheQuery_freshTargetEnvelope_le key state.1 state.2 payload hfresh hsigned _ _ _ groups remaining hvalid).trans_eq ?_
      unfold reuseRawEnvelope observedRawIndexShapeVector
      rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
    · simp only [hmessage, false_and, if_false, mul_zero, tsum_zero, zero_le]
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    rw [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction]
    exact zero_le
theorem expected_logTraced_world_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
        ((Fintype.card Index : ENNReal)⁻¹ *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseNewTarget_le key reuse budget signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction, mul_zero, tsum_zero, zero_le]
theorem expected_logTraced_sign_reuseNewTarget_le_mass_mul (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      freshDigestSelectionProbability key message state.1 *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state groups remaining)) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  have heq := congrArg (fun computation : ProbComp (Option Signature × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) hrun
  rw [tsum_probOutput_map_mul] at heq
  have h := expected_signWithView_newTargetEnvelopeCharge_le_mass_mul key message state.1 state.2 hsigned
    reuse budget signatures groups remaining hvalid
  refine heq.le.trans (h.trans_eq ?_)
  unfold reuseRawEnvelope observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def signingExecutionHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => digestAttemptLimit
end SphincsSecurity.Concrete
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
noncomputable def reuseTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (signerRate target) reuse (arrivalRate target) budget signatures
    (observedTargetShapeVector key payload target state)
theorem reuseTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    reuseTargetEnvelope key reuse smaller payload target signatures state groups remaining ≤
      reuseTargetEnvelope key reuse larger payload target signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ signatures _ hbudget groups remaining hvalid
theorem expected_randomOracle_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + 1) payload target signatures state groups remaining := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    unfold reuseTargetEnvelope
    rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
    exact targetShapeEnvelope_mono _ _ _ budget signatures
      (fun G R hv => expected_fresh_targetShape_le key payload target state.1 state.2 input hfresh hsigned G R hv)
      groups remaining hvalid
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact reuseTargetEnvelope_budget_mono key reuse payload target signatures state (Nat.le_succ _) groups remaining hvalid
theorem expected_logTraced_world_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) payload target signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseTarget_le key reuse budget payload target signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
theorem expected_logTraced_sign_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse budget payload target (signatures + 1) state groups remaining := by
  unfold reuseTargetEnvelope
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ budget signatures
    (fun G R hv => expected_logTraced_sign_targetShape_le_of_exactReuse key reuse payload target state hsigned message hreuse G R hv)
      groups remaining hvalid).trans
    (targetShapeEnvelope_signing_le _ _ _ budget signatures _ groups remaining hvalid)
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable
def TargetCoveredOn (key : SecretKey) (required : Finset IndexGroup) (state : CoverLogState)
    (payload : HashInput) (target : FewTimeView) : Prop :=
  ∀ tree ∈ required, 0 < targetTreeMatchCount
    (eligibleSigningViews (messageAnswers key.parameter state.1) key.root payload state.2) target tree
def TargetCertificateAt (key : SecretKey) (required : Finset IndexGroup) (state : CoverLogState)
    (input : HashInput) : Prop :=
  ∃ output, state.1 input = some output ∧ MessageHashInput key.parameter input ∧
    Admissible (truncateMessageDigest output) ∧
      TargetCoveredOn key required state (payloadOf input) (hashOutputFewTimeView output)
noncomputable def completedTargetBank (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) : HashInput → Bool :=
  fun input => bank input || decide (TargetCertificateAt key required state input)
noncomputable def targetCertificateScale (required : Finset IndexGroup) : ENNReal :=
  coverScale ^ required.card
noncomputable def targetCertificateForecast (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput) (target : FewTimeView) : ENNReal :=
  reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required *
    targetCertificateScale required
noncomputable def bankedTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) : ENNReal :=
  bankedCacheWeight key.parameter (targetCertificateForecast key reuse budget signatures required state) bank stopped state.1
noncomputable def targetCreationMultiplier (key : SecretKey) (cache : QueryCache HashSpec) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl input => freshWorldTargetHashCost key.parameter cache input
  | .inr message => admissibleProbability⁻¹ * freshDigestSelectionProbability key message cache
theorem targetCreationMultiplier_sign_le (key : SecretKey) (cache : QueryCache HashSpec) (message : Message) :
    targetCreationMultiplier key cache (.inr message) ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by
  calc
    _ ≤ (2142 : ENNReal) * 1 :=
      mul_le_mul' admissibleProbability_inv_le (freshDigestSelectionProbability_le_one key message cache)
    _ ≤ _ := by
      rw [mul_one]
      exact_mod_cast (show 2142 ≤ 2 ^ ftsTreeHeight by decide)
noncomputable def targetCreationPrice (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) : ENNReal :=
  (Fintype.card Index : ENNReal)⁻¹ *
    reuseRawEnvelope key reuse budget signatures state ∅ required * targetCertificateScale required
theorem bankedTargetEnvelope_initial (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState)
    (hnone : ∀ input, MessageHashInput key.parameter input → state.1 input = none) :
    bankedTargetEnvelope key reuse budget signatures required state (fun _ => false) false = 0 := by
  rw [bankedTargetEnvelope, bankedCacheWeight_live, certificateBankCount_empty, zero_add]
  exact cacheMessageWeight_of_no_message key.parameter _ state.1 hnone
theorem bankedTargetEnvelope_stopped (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) :
    bankedTargetEnvelope key reuse budget signatures required state bank true = certificateBankCount bank :=
  bankedCacheWeight_stopped _ _ _ _
theorem targetCreationMultiplier_sign_mul_price (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (message : Message) :
    targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state =
      freshDigestSelectionProbability key message state.1 *
        (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required)) *
          targetCertificateScale required := by
  unfold targetCreationMultiplier targetCreationPrice
  ring
theorem completedTargetBank_of_certificate (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) (input : HashInput)
    (hcovered : TargetCertificateAt key required state input) :
    completedTargetBank key required state bank input = true := by
  simp only [completedTargetBank, hcovered, decide_true, Bool.or_true]
theorem normalizedTargetLogProduct_ge_of_coveredOn (key : SecretKey) (required : Finset IndexGroup)
    (state : CoverLogState) (payload : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state payload target) :
    coverNormalization ^ required.card ≤
      normalizedTargetLogProduct key state.1 state.2 payload target required := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro tree htree
  apply le_mul_of_one_le_right'
  exact_mod_cast Nat.succ_le_iff.mpr (hcovered tree htree)
theorem one_le_targetCertificateForecast_of_covered (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state (payloadOf input) target) :
    1 ≤ targetCertificateForecast key reuse budget signatures required state input target := by
  have hmoment := normalizedTargetLogProduct_ge_of_coveredOn key required state (payloadOf input) target hcovered
  have hforecast : coverNormalization ^ required.card ≤
      reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required := by
    apply hmoment.trans
    simpa only [reuseTargetEnvelope, observedTargetShapeVector, targetShapeMoments, Finset.prod_empty, one_mul] using
      (le_targetShapeEnvelope (signerRate target) reuse (arrivalRate target)
        budget signatures (observedTargetShapeVector key (payloadOf input) target state) ∅ required)
  unfold targetCertificateForecast targetCertificateScale
  calc
    (1 : ENNReal) = coverNormalization ^ required.card * coverScale ^ required.card := by
      rw [← mul_pow, coverNormalization_mul_coverScale, one_pow]
    _ ≤ _ := mul_le_mul' hforecast le_rfl
theorem one_le_targetCertificateEntry_of_certificate (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (input : HashInput)
    (hcertificate : TargetCertificateAt key required state input) :
    1 ≤ cacheMessageEntryWeight key.parameter
      (targetCertificateForecast key reuse budget signatures required state) state.1 input := by
  obtain ⟨output, houtput, hmessage, hadmissible, hcovered⟩ := hcertificate
  simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
  exact one_le_targetCertificateForecast_of_covered key reuse budget signatures required state input _ hcovered
private theorem empty_targetShapeValid (required : Finset IndexGroup) : TargetShapeValid ∅ required := by
  constructor <;> simp
theorem targetCreationPrice_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    targetCreationPrice key reuse smaller signatures required state ≤
      targetCreationPrice key reuse larger signatures required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact targetShapeEnvelope_queries_mono _ _ _ _ _ hbudget ∅ required (empty_targetShapeValid required)
theorem targetCreationPrice_signatures_mono (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) {smaller larger : Nat} (hsignatures : smaller ≤ larger) :
    targetCreationPrice key reuse budget smaller required state ≤
      targetCreationPrice key reuse budget larger required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact Function.monotone_iterate_of_id_le
    (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning (constRate (Fintype.card Index : ENNReal)⁻¹) reuse f from
      fun _ _ _ => (le_self_add).trans le_self_add)
    hsignatures _ ∅ required
theorem bankedTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool)
    {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    bankedTargetEnvelope key reuse smaller signatures required state bank stopped ≤
      bankedTargetEnvelope key reuse larger signatures required state bank stopped := by
  apply bankedCacheWeight_mono
  intro input target
  exact mul_le_mul' (reuseTargetEnvelope_budget_mono key reuse (payloadOf input) target signatures state
    hbudget ∅ required (empty_targetShapeValid required)) le_rfl
theorem newTargetCertificateForecast_eq (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (before : QueryCache HashSpec) (after : CoverLogState) :
    cacheMessageWeight key.parameter (fun input target => if before input = none then
      targetCertificateForecast key reuse budget signatures required after input target else 0) after.1 =
      reuseNewTargetEnvelope key reuse budget signatures before after ∅ required * targetCertificateScale required := by
  unfold reuseNewTargetEnvelope newTargetEnvelopeCharge
  rw [← cacheMessageWeight_mul_right]
  apply congrArg (fun weight => cacheMessageWeight key.parameter weight after.1)
  funext input target
  by_cases hfresh : before input = none
  · simp only [hfresh, if_true, targetCertificateForecast]
    rfl
  · simp only [hfresh, if_false, zero_mul]
theorem expected_logTraced_world_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : (OracleWorld + SigningSpec).Range (.inl input) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) signatures required state bank false +
        (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
          ((Fintype.card Index : ENNReal)⁻¹ *
            reuseRawEnvelope key reuse budget signatures state ∅ required) * targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inl input) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_world_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state input hsigned ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_world_reuseNewTarget_le key reuse budget signatures state input hsigned
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))
theorem expected_logTraced_sign_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : (OracleWorld + SigningSpec).Range (.inr message) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        freshDigestSelectionProbability key message state.1 *
          (admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required)) *
            targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_sign_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state hsigned message hreuse ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_sign_reuseNewTarget_le_mass_mul key reuse budget signatures state hsigned message
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
def proposalRecordLogState (input : (OracleWorld + SigningSpec).Domain) (log : QueryLog SigningSpec)
    (record : ProposalExecutionRecord input) : CoverLogState :=
  (record.cache, log ++ signingLogFragment input record.output)
private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl
private theorem expected_pmf_mono_of_support {α : Type} (law : PMF α) (first second : α → ENNReal)
    (hle : ∀ result ∈ law.support, first result ≤ second result) :
    (∑' result, Pr[= result | law] * first result) ≤ ∑' result, Pr[= result | law] * second result := by
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (hle result hr)
  · have hp : Pr[= result | law] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]
theorem originalAdversaryPMFImpl_run (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    (originalAdversaryPMFImpl key input).run cache =
      (liftM ((unloggedMappedAdversaryImpl key input).run cache) : PMF _) := by
  rw [originalAdversaryPMFImpl, pmfSumImpl_eq_lift_add, originalAdversaryImpl_split]
  rfl
theorem expected_originalProposalRecord_logged (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CoverLogState) (weight : CoverLogState → ENNReal) :
    (∑' record, Pr[= record | originalProposalRecord key input state.1] *
      weight (proposalRecordLogState input state.2 record)) =
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * weight result.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have h := congrArg (fun computation : PMF ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] * weight (result.2, state.2 ++ signingLogFragment input result.1))
      (originalProposalRecord_project key input state.1)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, originalAdversaryPMFImpl_run, expected_pmfLift] at h
  exact h
theorem originalProposalRecord_world_hashCalls (key : SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inl input))
    (hr : record ∈ (originalProposalRecord key (.inl input) cache).support) :
    record.trace.hashCalls = signingExecutionHashCost (.inl input) := by
  rw [originalProposalRecord, PMF.mem_support_map_iff] at hr
  obtain ⟨result, _, rfl⟩ := hr
  cases input with
  | inl sample => rfl
  | inr input => rfl
noncomputable def bankedProposalRecordValue (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool)
    (input : (OracleWorld + SigningSpec).Domain) (record : ProposalExecutionRecord input) (stopped : Bool) : ENNReal :=
  let after := proposalRecordLogState input state.2 record
  bankedTargetEnvelope key reuse (budget - record.trace.hashCalls) signatures required after
    (completedTargetBank key required after bank) stopped
theorem expected_originalProposalRecord_world_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : ProposalExecutionRecord (.inl input) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcost : signingExecutionHashCost (.inl input) ≤ budget) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse budget signatures required state := by
  let afterBudget := budget - signingExecutionHashCost (.inl input)
  let weight := fun current => bankedTargetEnvelope key reuse afterBudget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_world_bankedTarget_le key reuse afterBudget signatures required state bank input
    (fun _ => false) hsigned
  have hrestore : afterBudget + signingExecutionHashCost (.inl input) = budget := Nat.sub_add_cancel hcost
  rw [hrestore] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
        weight (proposalRecordLogState (.inl input) state.2 record) := by
      apply expected_pmf_mono_of_support
      intro record hr
      have hc := originalProposalRecord_world_hashCalls key input state.1 record hr
      dsimp only [bankedProposalRecordValue, weight, afterBudget]
      rw [hc]
      exact bankedCacheWeight_discard_le _ _ _ _ _
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inl input) state weight
    _ ≤ bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse afterBudget signatures required state := by
      simpa only [targetCreationMultiplier, targetCreationPrice, mul_assoc] using hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_budget_mono key reuse signatures required state (Nat.sub_le _ _)))
theorem expected_originalProposalRecord_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state := by
  let weight := fun current => bankedTargetEnvelope key reuse budget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_sign_bankedTarget_le key reuse budget signatures required state bank message
    (fun _ => false) hsigned hreuse
  rw [← targetCreationMultiplier_sign_mul_price] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
        weight (proposalRecordLogState (.inr message) state.2 record) := by
      apply ENNReal.tsum_le_tsum
      intro record
      apply mul_le_mul' le_rfl
      exact (bankedCacheWeight_discard_le _ _ _ _ _).trans
        (bankedTargetEnvelope_budget_mono key reuse signatures required _ _ false (Nat.sub_le _ _))
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inr message) state weight
    _ ≤ bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state := hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_signatures_mono key reuse budget required state (Nat.le_succ _)))
theorem expected_coupled_bankedProposalRecord_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset IndexGroup)
    (state : CoverLogState) (bank : HashInput → Bool) (input : (OracleWorld + SigningSpec).Domain)
    (law : PMF α) (record : α → ProposalExecutionRecord input) (stopped : α → Bool) (bound : ENNReal)
    (hrecord : law.map record = originalProposalRecord key input state.1)
    (hbound : (∑' result, Pr[= result | originalProposalRecord key input state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank input result false) ≤ bound) :
    (∑' result, Pr[= result | law] *
      bankedProposalRecordValue key reuse budget signatures required state bank input (record result) (stopped result)) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        bankedProposalRecordValue key reuse budget signatures required state bank input (record result) false := by
      apply ENNReal.tsum_le_tsum
      intro result
      exact mul_le_mul' le_rfl (bankedCacheWeight_discard_le _ _ _ _ _)
    _ = ∑' result, Pr[= result | originalProposalRecord key input state.1] *
        bankedProposalRecordValue key reuse budget signatures required state bank input result false := by
      rw [← hrecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    _ ≤ bound := hbound
theorem expected_lengthBridge_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset IndexGroup) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : Nat × ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | recordLengthBridge (originalProposalRecord key (.inr message) state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) result.2 (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state :=
  expected_coupled_bankedProposalRecord_le key reuse budget signatures required state bank (.inr message)
    _ Prod.snd stopped _ (recordLengthBridge_record _ _ _ _)
    (expected_originalProposalRecord_sign_banked_le key reuse budget signatures required state bank message
      (fun _ => false) hsigned hreuse)
end SphincsSecurity.Concrete
end
