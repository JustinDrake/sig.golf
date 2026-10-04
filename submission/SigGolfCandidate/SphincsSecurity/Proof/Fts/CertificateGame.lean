import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateMonitor
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FreshDigestHazard
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryMessageCost
import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalProposalExecution
import SigGolfCandidate.SphincsSecurity.Proof.Base.RomQueryChargeBind
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificatePathBudget
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsProbeCanonicalChargeGame

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
theorem expected_certificateLengthImpl_potential_le (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcache, _⟩, hvalid, hcost⟩ := hdata
    rw [certificateMonitorCharge, if_pos hactive]
    cases input with
    | inl world =>
        rw [certificateLengthImpl_world_run, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inl world) state 0 _ hactive,
          signingLogFragment, List.append_nil]
        have hcost' : signingExecutionHashCost (.inl world) ≤ budget - state.2.spent := by
          cases world <;> exact hcost
        have h := expected_originalProposalRecord_world_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - state.2.log.length) required
          (certificateMonitorCoverState state) state.2.bank world
          (fun record => (certificateMonitorUpdate key budget required stopAfter (.inl world) state 0 record).stopped)
          hsigned hcost'
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
    | inr message =>
        rw [certificateLengthImpl_sign_run, if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [certificateMonitorPotential_advance_active key budget required stopAfter (.inr message) state _ _ hactive,
          signingLogFragment, List.length_append, List.length_singleton]
        have hremaining : signatureLimit - (state.2.log.length + 1) + 1 = signatureLimit - state.2.log.length := by
          change state.2.log.length < signatureLimit at hvalid
          omega
        have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache key state.1 state.2.spent
          hcache.spent_le hcache.cache_le hcache.no_deficit message
        have h := expected_lengthBridge_sign_banked_le key nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - (state.2.log.length + 1)) required
          (certificateMonitorCoverState state) state.2.bank message
          (fun result => (certificateMonitorUpdate key budget required stopAfter (.inr message) state result.1 result.2).stopped)
          hsigned hreuse
        rw [hremaining] at h
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hlive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero, certificateLengthImpl_inactive_run key budget required stopAfter input state hactive,
      ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [certificateMonitorPotential, bankedTargetEnvelope_stopped]
    rw [ENNReal.tsum_mul_right]
    have hmass : (∑' record, Pr[= record | originalProposalRecord key input state.1]) = 1 := by
      simp only [PMF.probOutput_eq_apply, PMF.tsum_coe]
    rw [hmass, one_mul]
    exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _
theorem expected_certificateLengthImpl_of_advance_constant (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (value : ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = value) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) = value := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split <;> rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] <;>
    simp only [hadvance, ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
theorem expected_certificateLengthImpl_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationCost) =
      state.2.creationCost + certificateMonitorCharge key budget required input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationCost) _ (certificateMonitorUpdate_creationCost key budget required stopAfter input state)
theorem expected_certificateLengthImpl_creationMass (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * result.2.2.creationMass) =
      state.2.creationMass + certificateMonitorMass key budget input state :=
  expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
    (fun current => current.2.creationMass) _ (certificateMonitorUpdate_creationMass key budget required stopAfter input state)
noncomputable def expectedCertificateCharge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) α) : CertificateMonitorState → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => charge input state +
      ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
        next result.1 result.2) computation
@[simp] theorem expectedCertificateCharge_pure {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (value : α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (pure value) state = 0 := rfl
theorem expectedCertificateCharge_query_bind {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter charge (OracleSpec.query input >>= next) state =
      charge input state +
        ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
          expectedCertificateCharge key budget required stopAfter charge (next result.1) result.2 := rfl
theorem expected_certificate_accumulator {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (counter : CertificateMonitorState → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state,
      (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
        counter state + charge input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * counter result.2) =
      counter state + expectedCertificateCharge key budget required stopAfter charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      simp_rw [ih, mul_add, ENNReal.tsum_add]
      rw [hstep, add_assoc]
theorem expected_certificate_creationCost {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationCost)
    (certificateMonitorCharge key budget required) (expected_certificateLengthImpl_creationCost key budget required stopAfter)
    computation state
theorem expected_certificate_creationMass {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] * result.2.2.creationMass) =
      state.2.creationMass + expectedCertificateCharge key budget required stopAfter (certificateMonitorMass key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.creationMass)
    (certificateMonitorMass key budget) (expected_certificateLengthImpl_creationMass key budget required stopAfter)
    computation state
theorem expected_certificate_potential_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateMonitorPotential key budget required result.2) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
      expectedCertificateCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedCertificateCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            (certificateMonitorPotential key budget required result.2 +
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2) :=
          ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)
        _ = (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
            certificateMonitorPotential key budget required result.2) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 := by simp only [mul_add, ENNReal.tsum_add]
        _ ≤ (certificateMonitorPotential key budget required state + certificateMonitorCharge key budget required input state) +
            ∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
              expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required)
                (next result.1) result.2 :=
          add_le_add (expected_certificateLengthImpl_potential_le key budget required stopAfter input state) le_rfl
        _ = _ := by rw [add_assoc]
theorem expected_certificate_count_le_initial_add_charge {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      certificateBankCount result.2.2.bank) ≤
      certificateMonitorPotential key budget required state +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorCharge key budget required) computation state := by
  apply le_trans ?_ (expected_certificate_potential_le_initial_add_charge key budget required stopAfter computation state)
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)
theorem expected_certificate_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationCost := by
  rw [expected_certificate_creationCost]
  have h := expected_certificate_count_le_initial_add_charge key budget required stopAfter computation
    (cache, initialCertificateMonitor spent stopped)
  rw [certificateMonitorPotential_initial key budget spent required cache stopped hnone, zero_add] at h
  simpa only [initialCertificateMonitor, zero_add] using h
theorem expected_certificateProposal_count_le_creationCost {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationCost := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hcount := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank) hmap
  have hcost := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationCost) hmap
  rw [tsum_probOutput_map_mul] at hcount hcost
  simp only [Prod.map] at hcount hcost
  rw [hcount, hcost]
  exact expected_certificate_count_le_creationCost key budget spent required stopAfter computation cache stopped hnone
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signAttempt signDigestAttemptPrefix signDigestLoop
theorem probEvent_signDigestAttemptPrefix_fresh_le_admissibility
    (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[FreshDigestAttempt reference key message | signDigestAttemptPrefix key message cache] ≤
      admissibleProbability := by
  rw [signDigestAttemptPrefix]
  apply probEvent_bind_le_of_forall_le
  intro randomness _
  rw [show (fun result => pure (randomness, result)) = pure ∘ fun result => (randomness, result) from rfl,
    probEvent_bind_pure_comp]
  change Pr[fun result => reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none ∧ result.1 ≠ none |
      (simulateQ (randomOracle : QueryImpl HashSpec _) (signAttempt key message randomness)).run cache] ≤ _
  by_cases href : reference (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)) = none
  · simp only [href, true_and]
    cases hc : cache (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness)) with
    | none => exact (probEvent_signAttempt_fresh_success_eq key message randomness cache hc).le
    | some output =>
        apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
        intro result hr hsuccess
        have hle : cache ≤ result.2 :=
          simulateQ_romImpl_cache_le (liftM (signAttempt key message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache result (by
              rw [simulateQ_romImpl_liftM]
              exact hr)
        exact hsuccess ((signAttempt_result_of_cached key message randomness cache result.2 result.1 output
          (hle hc) hr).trans (hinvariant randomness output href hc))
  · apply le_of_eq_of_le (probEvent_eq_zero ?_) zero_le
    intro result _ hevent
    exact href hevent.1
theorem probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility
    (attempts : Nat) (key : SecretKey) (message : Message) (reference cache : QueryCache HashSpec)
    (hinvariant : OnlyRejectedNewMessageEntries reference cache key message) :
    Pr[fun result => freshSelectedLoopView? reference key message result ≠ none |
      (simulateQ romImpl (signDigestLoop attempts key message)).run cache] ≤
      digestAttemptExpectation attempts key message cache * admissibleProbability := by
  induction attempts generalizing cache with
  | zero => simp [signDigestLoop, freshSelectedLoopView?, digestAttemptExpectation]
  | succ attempts ih =>
      rw [probEvent_signDigestLoop_fresh_recurrence, digestAttemptExpectation, add_mul, one_mul,
        ← ENNReal.tsum_mul_right]
      apply add_le_add (probEvent_signDigestAttemptPrefix_fresh_le_admissibility key message reference cache hinvariant)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (signDigestAttemptPrefix key message cache)
      · by_cases hnone : result.2.1 = none
        · rw [if_pos hnone, if_pos hnone, mul_assoc]
          apply mul_le_mul' le_rfl
          apply ih
          apply onlyRejectedNewMessageEntries_of_failed_attempt reference cache result.2.2 key message result.1 hinvariant
          have heq : result.2 = (none, result.2.2) := Prod.ext hnone rfl
          rw [← heq]
          exact signDigestAttemptPrefix_support_attempt key message cache result hr
        · simp only [if_neg hnone, mul_zero, zero_mul, le_refl]
      · simp only [probOutput_eq_zero_of_not_mem_support hr, zero_mul, le_refl]
end SphincsSecurity.Concrete
end

section





set_option autoImplicit true
namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
theorem expectedQueryCharge_lift_unif_eq_zero
    (charge : QueryCache HashSpec → HashInput → ENNReal)
    (computation : OracleComp unifSpec α) (cache : QueryCache HashSpec) :
    expectedQueryCharge charge (liftM computation : OracleComp OracleWorld α) cache = 0 := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      rw [liftM_bind]
      change expectedQueryCharge charge
        ((liftM (OracleWorld.query (.inl query)) : OracleComp OracleWorld _) >>= fun answer => liftM (next answer)) cache = 0
      rw [expectedQueryCharge_query_bind]
      simp only [hashQueryCharge, Sum.elim_inl, ih, mul_zero, tsum_zero, zero_add]
end SphincsSecurity
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
noncomputable local instance instSampleableTypeRandomness_7 : SampleableType Randomness := Concrete.randomnessSampleableType
attribute [local irreducible] signDigestLoop signAttempt signWithView
set_option backward.isDefEq.respectTransparency false
theorem expectedQueryCharge_messageDigest_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (messageDigest key.parameter key.root message randomness : OracleComp HashSpec MessageDigest)) cache = 1 := by
  change expectedQueryCharge (messageHashCharge key.parameter)
    ((liftM (OracleWorld.query (.inr (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message randomness)))) : OracleComp OracleWorld HashOutput) >>=
      fun answer => pure (truncateMessageDigest answer)) cache = 1
  rw [expectedQueryCharge_query_bind]
  simp only [expectedQueryCharge_pure, mul_zero, tsum_zero, add_zero, hashQueryCharge, Sum.elim_inr,
    messageHashCharge, if_pos (show FtsProbeSimulation.MessageHashInput key.parameter
      (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)) from ⟨_, rfl⟩)]
theorem expectedQueryCharge_signAttempt_message (key : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter)
      (liftM (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) cache = 1 := by
  rw [signAttempt, liftM_bind, expectedQueryCharge_bind, expectedQueryCharge_messageDigest_message]
  conv_lhs =>
    arg 2
    tactic =>
      apply ENNReal.tsum_eq_zero.mpr
      intro result
      split_ifs <;> simp
  exact add_zero 1
theorem expectedQueryCharge_signDigestLoop_message (attempts : Nat) (key : SecretKey)
    (message : Message) (cache : QueryCache HashSpec) :
    expectedQueryCharge (messageHashCharge key.parameter) (signDigestLoop attempts key message) cache =
      digestAttemptExpectation attempts key message cache := by
  induction attempts generalizing cache with
  | zero => simp only [signDigestLoop, expectedQueryCharge_pure, digestAttemptExpectation]
  | succ attempts ih =>
      have hsample : (simulateQ romImpl (liftM sampleRandomness)).run cache =
          (fun randomness => (randomness, cache)) <$> sampleRandomness :=
        roSim.run_liftM (hashSpec := HashSpec)
          (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) sampleRandomness cache
      rw [signDigestLoop, expectedQueryCharge_bind, expectedQueryCharge_lift_unif_eq_zero, zero_add,
        hsample, sampleRandomness_eq, tsum_probOutput_map_mul, digestAttemptExpectation,
        signDigestAttemptPrefix, tsum_probOutput_bind_mul]
      simp_rw [expectedQueryCharge_bind, expectedQueryCharge_signAttempt_message,
        mul_add, ENNReal.tsum_add, mul_one, tsum_probOutput_of_liftM_PMF]
      congr 1
      apply tsum_congr
      intro randomness
      rw [simulateQ_romImpl_liftM]
      congr 1
      rw [tsum_probOutput_bind_mul]
      apply tsum_congr
      intro result
      simp only [tsum_probOutput_pure_mul]
      cases result.1 <;> simp [ih]
theorem freshDigestSelection_mass_le_messageCharge (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    admissibleProbability⁻¹ * freshDigestSelectionProbability key message cache ≤
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  have h := probEvent_signDigestLoop_fresh_le_attempts_mul_admissibility digestAttemptLimit key message cache cache
    (onlyRejectedNewMessageEntries_self cache key message)
  have hscaled := mul_le_mul' (le_refl admissibleProbability⁻¹) h
  have hscalar : admissibleProbability⁻¹ *
      (digestAttemptExpectation digestAttemptLimit key message cache * admissibleProbability) =
      digestAttemptExpectation digestAttemptLimit key message cache := by
    rw [mul_left_comm, ENNReal.inv_mul_cancel admissibleProbability_pos admissibleProbability_ne_top, mul_one]
  rw [hscalar] at hscaled
  apply hscaled.trans
  rw [signWithView, expectedQueryCharge_bind, expectedQueryCharge_signDigestLoop_message]
  exact le_self_add
private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl
theorem expected_originalProposalRecord_sign_messageCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) cache] *
      record.trace.messageCalls.length) =
      expectedQueryCharge (messageHashCharge key.parameter) (signWithView key message) cache := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  have h := congrArg (fun law : PMF (TracedSigningRecord SigningBoundaryTrace) =>
    ∑' result, Pr[= result | law] * (result.1.2.messageCalls.length : ENNReal))
    (completedSigningRecord_forget (signingBoundaryTrace key.parameter) key message cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, expected_pmfLift] at h
  change _ = expectedBoundaryMessageCalls key.parameter (signWithView key message) cache at h
  exact h.trans (expectedBoundaryMessageCalls_eq_queryCharge key.parameter (signWithView key message) cache)
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageHashCharge)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_originalProposalRecord_world_messageCalls (key : SecretKey)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) cache] *
      record.trace.messageCalls.length) = hashQueryCharge (messageHashCharge key.parameter) cache input := by
  rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
  simp only [signingBoundaryTrace_messageCalls key.parameter input _ cache,
    ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
theorem targetCreationMultiplier_le_expected_messageCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    targetCreationMultiplier key cache input ≤
      ∑' record, Pr[= record | originalProposalRecord key input cache] * record.trace.messageCalls.length := by
  cases input with
  | inl world =>
      rw [expected_originalProposalRecord_world_messageCalls, targetCreationMultiplier]
      cases world with
      | inl sample => simp only [freshWorldTargetHashCost, Nat.cast_zero, hashQueryCharge, Sum.elim_inl, le_refl]
      | inr input =>
          by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input <;>
            simp [freshWorldTargetHashCost, hashQueryCharge, messageHashCharge, hmessage]
          split_ifs <;> norm_num
  | inr message =>
      rw [expected_originalProposalRecord_sign_messageCalls]
      simpa only [targetCreationMultiplier, FtsLeaf, Fintype.card_fin] using
        freshDigestSelection_mass_le_messageCharge key message cache
noncomputable def certificateMonitorMessageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    ∑' record, Pr[= record | originalProposalRecord key input state.1] * record.trace.messageCalls.length
  else 0
theorem certificateMonitorMass_le_messageCharge (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    certificateMonitorMass key budget input state ≤ certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · simpa only [certificateMonitorMass, certificateMonitorMessageCharge, if_pos hactive] using
      targetCreationMultiplier_le_expected_messageCalls key input state.1
  · simp only [certificateMonitorMass, certificateMonitorMessageCharge, if_neg hactive, le_refl]
theorem expected_certificateLengthImpl_of_record_function (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (counter : CertificateMonitorState → ENNReal) (weight : ProposalExecutionRecord input → ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) = weight record) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] * counter result.2) =
      ∑' record, Pr[= record | originalProposalRecord key input state.1] * weight record := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
      ∑' record, Pr[= record | law] * weight record)
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
    exact h
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
theorem expected_certificateLengthImpl_messageCalls (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      result.2.2.messageCalls) = state.2.messageCalls + certificateMonitorMessageCharge key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [expected_certificateLengthImpl_of_record_function key budget required stopAfter input state
        (fun current => current.2.messageCalls)
        (fun record => (state.2.messageCalls : ENNReal) + record.trace.messageCalls.length)
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_messageCalls key budget required stopAfter input state length record hactive, Nat.cast_add])]
    simp only [certificateMonitorMessageCharge, if_pos hactive, mul_add, ENNReal.tsum_add,
      ENNReal.tsum_mul_right, PMF.probOutput_eq_apply, PMF.tsum_coe, one_mul]
  · rw [expected_certificateLengthImpl_of_advance_constant key budget required stopAfter input state
        (fun current => current.2.messageCalls) state.2.messageCalls
        (fun length record => by simp only [originalProposalAdvance,
          certificateMonitorUpdate_inactive key budget required stopAfter input state length record hactive])]
    simp only [certificateMonitorMessageCharge, if_neg hactive, add_zero]
theorem expected_certificate_messageCalls {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      result.2.2.messageCalls) = state.2.messageCalls +
        expectedCertificateCharge key budget required stopAfter (certificateMonitorMessageCharge key budget) computation state :=
  expected_certificate_accumulator key budget required stopAfter (fun current => current.2.messageCalls)
    (certificateMonitorMessageCharge key budget) (expected_certificateLengthImpl_messageCalls key budget required stopAfter)
    computation state
theorem expectedCertificateCharge_mono {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (first second : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hle : ∀ input state, first input state ≤ second input state)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : CertificateMonitorState) :
    expectedCertificateCharge key budget required stopAfter first computation state ≤
      expectedCertificateCharge key budget required stopAfter second computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [expectedCertificateCharge_pure, le_refl]
  | query_bind input next ih =>
      rw [expectedCertificateCharge_query_bind, expectedCertificateCharge_query_bind]
      exact add_le_add (hle input state) (ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2))
theorem expected_certificate_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run
        (cache, initialCertificateMonitor spent stopped)] * result.2.2.messageCalls := by
  rw [expected_certificate_creationMass, expected_certificate_messageCalls]
  simp only [initialCertificateMonitor, Nat.cast_zero, zero_add]
  exact expectedCertificateCharge_mono key budget required stopAfter _ _
    (certificateMonitorMass_le_messageCharge key budget) computation _
theorem expected_certificateProposal_creationMass_le_messageCalls {α : Type} (key : SecretKey) (budget spent : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (stopped : Bool) :
    (∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run
        ([], cache, initialCertificateMonitor spent stopped)] * result.2.2.2.messageCalls := by
  have hmap := simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    ([], cache, initialCertificateMonitor spent stopped)
  have hmass := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * result.2.2.creationMass) hmap
  have hcalls := congrArg (fun law : PMF (α × CertificateMonitorState) =>
    ∑' result, Pr[= result | law] * (result.2.2.messageCalls : ENNReal)) hmap
  rw [tsum_probOutput_map_mul] at hmass hcalls
  simp only [Prod.map] at hmass hcalls
  rw [hmass, hcalls]
  exact expected_certificate_creationMass_le_messageCalls key budget spent required stopAfter computation cache stopped
end SphincsSecurity.Concrete
end

section




set_option autoImplicit true
namespace SphincsSecurity.Concrete.OtsProbeSimulation
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
theorem simulateQ_unloggedMapped_eq_expanded (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (unloggedMappedAdversaryImpl secretKey) computation =
      simulateQ romImpl (simulateQ (expandedAdversaryImpl secretKey) computation) := by
  have hhandler : unloggedMappedAdversaryImpl secretKey = romImpl ∘ₛ expandedAdversaryImpl secretKey := by
    funext input
    exact unloggedMappedAdversaryImpl_eq_simulateQ_expanded secretKey input
  rw [hhandler, QueryImpl.simulateQ_compose]
end SphincsSecurity.Concrete.OtsProbeSimulation
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (RetainedRestResult retainedGameRestComputation)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
private theorem simulateQ_romImpl_sampling_bind_run {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld α) >>= next)).run cache =
      computation >>= fun value => (simulateQ romImpl (next value)).run cache := by
  rw [simulateQ_bind, StateT.run_bind,
    show simulateQ romImpl (liftM computation : OracleComp OracleWorld α) =
      simulateQ (unifFwdImpl HashSpec) computation from QueryImpl.simulateQ_add_liftM_left _ _ computation,
    unifFwdImpl.simulateQ_run, bind_map_left]
theorem keygen_cache_message_none (generated : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hg : generated ∈ support ((simulateQ romImpl scheme.keygen).run ∅)) :
    ∀ input, FtsProbeSimulation.MessageHashInput generated.1.2.parameter input → generated.2 input = none := by
  change generated ∈ support ((simulateQ romImpl keygen).run ∅) at hg
  rw [keygen, simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨parameter, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨otsSecret, _, hg⟩ := hg
  rw [simulateQ_romImpl_sampling_bind_run, mem_support_bind_iff] at hg
  obtain ⟨ftsSecret, _, hg⟩ := hg
  rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM, mem_support_bind_iff] at hg
  obtain ⟨root, hroot, hg⟩ := hg
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hg
  subst generated
  rintro input ⟨payload, rfl⟩
  exact keygenTable_cache_message_none parameter (otsSecret topLayer rootTree)
    root.1 root.2 hroot payload
abbrev CertificateGameResult := RetainedRestResult × (List Index × CertificateMonitorState)
noncomputable def certificateGame (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) : PMF CertificateGameResult := do
  let generated ← (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)
  let key := generated.1.1.2
  (simulateQ (certificateProposalImpl key budget required (stopAfter key))
    (retainedGameRestComputation adversary generated.1.1.1)).run
      ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped)
theorem certificateGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult)
    (hr : result ∈ (certificateGame adversary q required stopAfter stopped).support) :
    result.2.2.2.spent ≤ q ∧ result.2.2.2.creationMass ≤ q := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hgenerated, hr⟩ := hr
  rw [probCompLift_support] at hgenerated
  have hwhole : HashQueryBound (scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2)
      ∅ q := (hasHashQueryBound_iff scheme adversary q).mp hbound
  have hkeygen := boundaryRun_bind_query_bound 0 scheme.keygen
    (fun keys => gameRest scheme adversary keys.1 keys.2) q ∅ hwhole generated hgenerated
  have hrest := hkeygen.2
  rw [OtsProbeSimulation.gameRest_eq_map_retained, hashQueryBound_map_iff] at hrest
  have hcost := certificateProposal_run_cost_le generated.1.1.2 q required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) (q - generated.1.2.hashCalls)
    ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped) hrest result hr
  simp only [initialCertificateMonitor, zero_add] at hcost
  exact ⟨by omega, hcost.2.trans (Nat.cast_le.mpr (Nat.sub_le _ _))⟩
theorem expected_certificateGame_creationMass_le_messageCalls (adversary : Adversary)
    (budget : Nat) (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationMass) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.messageCalls := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  exact mul_le_mul' le_rfl (expected_certificateProposal_creationMass_le_messageCalls generated.1.1.2 budget
    generated.1.2.hashCalls required (stopAfter generated.1.1.2)
    (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped)
theorem expected_certificateGame_count_le_creationCost (adversary : Adversary)
    (budget : Nat) (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    (∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] *
        certificateBankCount result.2.2.2.bank) ≤
      ∑' result, Pr[= result | certificateGame adversary budget required stopAfter stopped] * result.2.2.2.creationCost := by
  rw [certificateGame, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro generated
  by_cases hg : generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
  · have hgenerated := hg
    rw [probCompLift_support] at hgenerated
    have hkeygen : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
      rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
      exact ⟨generated, hgenerated, rfl⟩
    have hnone := keygen_cache_message_none (generated.1.1, generated.2) hkeygen
    exact mul_le_mul' le_rfl (expected_certificateProposal_count_le_creationCost generated.1.1.2 budget
      generated.1.2.hashCalls required (stopAfter generated.1.1.2)
      (retainedGameRestComputation adversary generated.1.1.1) generated.2 stopped
      hnone)
  · have hzero : Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] = 0 := by
      rw [PMF.probOutput_eq_apply]
      exact (PMF.apply_eq_zero_iff _ _).mpr hg
    rw [hzero, zero_mul, zero_mul]
end SphincsSecurity.Concrete
end
