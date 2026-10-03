import SigGolfCandidate.T3.Nonbinary.EncodingCounts
import SigGolfCandidate.T3.FullCache.NativeMac
import SigGolfCandidate.T3.FullCache.RequestRun
import SigGolfCandidate.T3.SearchCost
import SigGolfCandidate.T3.FullCache.ExpansionCost
import SigGolfCandidate.T3.FullCache.SourcePrelude
import SigGolfCandidate.T3.Gate6.SourceBudget
import SigGolfCandidate.T3.Gate6.NearCoverage
import SigGolfCandidate.T3.Gate6.Sampling
import SigGolfCandidate.T3.Gate6.DigestCounting
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FiniteGraphReplay
import SigGolfCandidate.SphincsSecurity.Proof.Fts.AdaptiveHiddenHazard
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FiniteHashWorld
import SigGolfCandidate.SphincsSecurity.Proof.Residual.ResidualProbeCompletion
import SigGolfCandidate.SphincsSecurity.Completeness.Octopus.Tuples
import SigGolfCandidate.SphincsSecurity.Proof.Event.TruncatedCharge
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexHashMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ProposalQueryProjection
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TerminalProposalWord
import SigGolfCandidate.T3.Proofs
import Mathlib.RingTheory.Polynomial.Pochhammer
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
import SigGolfCandidate.SphincsSecurity.Proof.Base.BinomialMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalVariance
import SigGolfCandidate.Budget.Numeric
import Mathlib.Tactic
import SigGolfCandidate.Budget.Octopus.Tuples
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.EvalDist.Bool
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Replay
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ProposalPrefixExponential


/-! CacheAuthentication: base T3 replay and authentication security interfaces. -/
section



end

/-! AuthenticationHop: base T3 replay and authentication security interfaces. -/
section





end


namespace SigGolfCandidate.T3.Security.ProposalOverflow
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open BPORS.Adaptive
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

noncomputable def tailBase : ENNReal := 4097 / 4096
noncomputable def tailMoment : ENNReal := 4195328 / 4194303

theorem tailBase_one_le : 1 ≤ tailBase := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold tailBase; finiteness)).mp
  norm_num [tailBase, ENNReal.toReal_div]
theorem tailMoment_one_le : 1 ≤ tailMoment := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold tailMoment; finiteness)).mp
  norm_num [tailMoment, ENNReal.toReal_div]

theorem acceptance_le_one : (1024/1025 : ENNReal) ≤ 1 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem tailMoment_eq : tailMoment =
    (1024/1025 : ENNReal) * tailBase / (1 - (1 - 1024/1025) * tailBase) := by
  have hrem : (1 - (1024/1025 : ENNReal)).toReal = 1 - (1024/1025 : ENNReal).toReal := by
    rw [ENNReal.toReal_sub_of_le acceptance_le_one (by finiteness), ENNReal.toReal_one]
  have hlt : (1 - (1024/1025 : ENNReal)) * tailBase < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold tailBase; finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, hrem]
    norm_num [tailBase, ENNReal.toReal_div]
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold tailMoment; finiteness)
    (ENNReal.div_ne_top (by unfold tailBase; finiteness) (tsub_pos_iff_lt.mpr hlt).ne')).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hlt.le (by finiteness)]
  simp only [ENNReal.toReal_mul, hrem]
  norm_num [tailMoment, tailBase, ENNReal.toReal_div]

theorem block_moment :
    expectedValue (proposalBlockLength (1024/1025) (by norm_num) acceptance_le_one)
      (fun length => tailBase ^ length) = tailMoment := by
  simp only [expectedValue, PMF.probOutput_eq_apply]
  rw [proposalBlockLength_power_moment, ← tailMoment_eq]

/-- The initial exponential potential for the contract's full signing limit.
No large powers are evaluated: the comparison is proved using logarithm bounds. -/
theorem initial_bound :
    tailMoment ^ (2^32) / tailBase ^ BPORS.Numeric.proposalLength ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  let z : ℝ := 4097 / 4096
  let m : ℝ := 4195328 / 4194303
  have hz : 0 < z := by norm_num [z]
  have hm : 0 < m := by norm_num [m]
  have hlog : (2^32 : ℝ) * Real.log m -
      BPORS.Numeric.proposalLength * Real.log z ≤ -700 * Real.log 2 := by
    have hu := Real.log_le_sub_one_of_pos hm
    have hl := Real.one_sub_inv_le_log_of_pos hz
    have ht := Real.log_two_lt_d9
    norm_num [m, z, BPORS.Numeric.proposalLength] at hu hl ⊢
    linarith
  have hreal : m ^ (2^32 : Nat) / z ^ BPORS.Numeric.proposalLength ≤ (2 : ℝ)⁻¹ ^ 700 := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_inv]
    push_cast
    nlinarith only [hlog]
  have hfinite : tailMoment ^ (2^32 : Nat) / tailBase ^ BPORS.Numeric.proposalLength ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact ENNReal.pow_ne_top (by unfold tailMoment; finiteness)
    · exact pow_ne_zero _ (by norm_num [tailBase])
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  simpa only [tailBase, tailMoment, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, m, z] using hreal

variable {ι State Label : Type} {spec : OracleSpec ι}

/-- The potential reserves one geometric moment for each remaining active request. -/
noncomputable def weight (remaining : State → Nat) (state : List Label × State) : ENNReal :=
  tailBase ^ state.1.length * tailMoment ^ remaining state.2

theorem query_weight (model : ProposalModel spec State Label) (haccept : model.accept = 1024/1025)
    (remaining : State → Nat) (input : spec.Domain) (state : List Label × State)
    (hactive : model.active input state.2 = true → 0 < remaining state.2)
    (hadvance : ∀ outcome, remaining (model.advance input state.2 outcome) =
      if model.active input state.2 then remaining state.2 - 1 else remaining state.2) :
    expectedValue ((model.traced input).run state) (fun result => weight remaining result.2) =
      weight remaining state := by
  simp only [ProposalModel.traced, proposalRecordImpl, StateT.run_mk]
  by_cases ha : model.active input state.2 = true
  · rw [if_pos ha, ← PMF.monad_map_eq_map, expectedValue_map]
    simp only [weight, List.length_append, List.length_singleton, hadvance, ha, if_true]
    have hp := hactive ha
    have he : remaining state.2 = (remaining state.2 - 1) + 1 := by omega
    have hproject := congrArg
      (fun law : PMF Nat => expectedValue law (fun length => tailBase ^ length))
      (recordLengthBridge_length (model.record input state.2) model.accept model.positive model.lt_one.le)
    rw [← recordProposalBridge_length_record (model.record input state.2)
      (model.rejected input state.2) model.accept model.positive model.lt_one.le] at hproject
    simp only [← PMF.monad_map_eq_map, expectedValue_map, Function.comp_def] at hproject
    have hmoment : expectedValue
        (recordProposalBridge (model.record input state.2) (model.rejected input state.2)
          model.accept model.positive model.lt_one.le)
        (fun result => tailBase ^ (result.1.length + 1)) = tailMoment := by
      rw [hproject]
      simp only [expectedValue, PMF.probOutput_eq_apply]
      rw [proposalBlockLength_power_moment, haccept, ← tailMoment_eq]
    calc
      _ = expectedValue
          (recordProposalBridge (model.record input state.2) (model.rejected input state.2)
            model.accept model.positive model.lt_one.le)
          (fun result => tailBase ^ (result.1.length + 1)) *
          (tailBase ^ state.1.length * tailMoment ^ (remaining state.2 - 1)) := by
        rw [← expectedValue_mul_const]
        congr 1
        funext result
        rw [Nat.add_assoc, pow_add]
        ring
      _ = weight remaining state := by
        rw [hmoment]
        conv_rhs => rw [weight, he, pow_succ]
        ring
  · rw [if_neg ha, ← PMF.monad_map_eq_map, expectedValue_map]
    simp only [weight, hadvance, ha, if_false]
    exact expectedValue_const (by simp) _

theorem weight_dominates_overflow (remaining : State → Nat)
    (state : List Label × State) (cap : Nat) (hbad : cap < state.1.length) :
    1 ≤ weight remaining state / tailBase ^ cap := by
  have hnz : tailBase ^ cap ≠ 0 := pow_ne_zero _ (by norm_num [tailBase])
  have hfin : tailBase ^ cap ≠ ⊤ := ENNReal.pow_ne_top (by unfold tailBase; finiteness)
  calc
    1 = tailBase ^ cap / tailBase ^ cap := (ENNReal.div_self hnz hfin).symm
    _ ≤ _ := ENNReal.div_le_div_right (calc
      tailBase ^ cap ≤ tailBase ^ state.1.length := pow_le_pow_right₀ tailBase_one_le hbad.le
      _ ≤ weight remaining state := by
        unfold weight
        exact le_mul_of_one_le_right' (one_le_pow₀ tailMoment_one_le)) _

/-- Counts every active request while retaining the full, untruncated trace. -/
noncomputable def counted (model : ProposalModel spec State Label) :
    ProposalModel spec (Nat × State) Label where
  Outcome := model.Outcome
  record input state := model.record input state.2
  response := model.response
  advance input state outcome :=
    (state.1 + if model.active input state.2 then 1 else 0,
      model.advance input state.2 outcome)
  label := model.label
  active input state := model.active input state.2
  base := model.base
  accept := model.accept
  positive := model.positive
  lt_one := model.lt_one
  cap input state ha point := model.cap input state.2 ha point

noncomputable def killedWeight (limit : Nat) (state : List Label × (Nat × State)) : ENNReal :=
  if state.2.1 ≤ limit then weight (fun current : Nat × State => limit - current.1) state else 0

theorem counted_query_weight (model : ProposalModel spec State Label) (haccept : model.accept = 1024/1025)
    (limit : Nat) (input : spec.Domain) (state : List Label × (Nat × State)) :
    expectedValue (((counted model).traced input).run state)
      (fun result => killedWeight limit result.2) ≤ killedWeight limit state := by
  by_cases ha : model.active input state.2.2 = true
  · by_cases hroom : state.2.1 < limit
    · have hrewrite : expectedValue (((counted model).traced input).run state)
          (fun result => killedWeight limit result.2) =
        expectedValue (((counted model).traced input).run state)
          (fun result => weight (fun current : Nat × State => limit-current.1) result.2) := by
        simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, if_true,
          ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, show state.2.1+1 ≤ limit by omega]
      rw [hrewrite, query_weight (counted model) haccept _ input state
        (fun _ => by omega) (fun _ => by simp only [counted, ha, if_true]; omega)]
      simp [killedWeight, Nat.le_of_lt hroom]
    · have hnext : ¬state.2.1 + 1 ≤ limit := by omega
      simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, if_true,
        ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, hnext, if_false]
      rw [expectedValue_const (by simp)]
      exact bot_le
  · simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk, ha, Bool.false_eq_true, if_false,
      ← PMF.monad_map_eq_map, expectedValue_map, killedWeight, Nat.add_zero, weight]
    rw [expectedValue_const (by simp)]

attribute [local irreducible] ProposalModel.traced counted

/-- Killing the potential after the lifetime cap avoids assuming an adversary
respects that cap on losing executions. Requests are never suppressed. -/

theorem counted_execution_weight {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (limit : Nat)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    expectedValue ((simulateQ (counted model).traced computation).run state)
      (fun result => killedWeight limit result.2) ≤ killedWeight limit state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, expectedValue, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind]
      apply le_trans ?_ (counted_query_weight model haccept limit input state)
      apply expectedValue_mono
      intro middle
      exact ih middle.1 middle.2

theorem counted_overflow_bound {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (limit cap : Nat)
    (computation : OracleComp spec Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ limit ∧ cap < result.2.1.length |
      (simulateQ (counted model).traced computation).run ([], 0, state)] ≤
      tailMoment ^ limit / tailBase ^ cap := by
  classical
  rw [← expectedValue_ite_one]
  calc
    _ ≤ expectedValue ((simulateQ (counted model).traced computation).run ([],0,state))
        (fun result => killedWeight limit result.2 / tailBase ^ cap) := by
      apply expectedValue_mono
      intro result
      split
      · rename_i h
        rw [killedWeight, if_pos h.1]
        exact weight_dominates_overflow _ _ cap h.2
      · exact bot_le
    _ = expectedValue ((simulateQ (counted model).traced computation).run ([],0,state))
        (fun result => killedWeight limit result.2) / tailBase ^ cap := by
      simp only [div_eq_mul_inv, expectedValue_mul_const]
    _ ≤ killedWeight limit ([], (0, state)) / tailBase ^ cap :=
      ENNReal.div_le_div_right (counted_execution_weight model haccept limit computation ([],0,state)) _
    _ = _ := by simp [killedWeight, weight]

theorem full_trace_overflow_bound {Result : Type} (model : ProposalModel spec State Label)
    (haccept : model.accept = 1024/1025) (computation : OracleComp spec Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted model).traced computation).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  (counted_overflow_bound model haccept _ _ computation state).trans initial_bound

attribute [local semireducible] ProposalModel.traced counted

theorem counted_rejected (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : Nat × State) :
    (counted model).rejected input state = model.rejected input state.2 := rfl

/-- Counting is a pure observation: dropping it preserves the entire proposal
word as well as the responses and private/public state. -/
theorem counted_query_trace_erasure (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => (current.1,current.2.2)) <$>
      (((counted model).traced input).run state) =
      (model.traced input).run (state.1,state.2.2) := by
  simp only [ProposalModel.traced, proposalRecordImpl, StateT.run_mk]
  change PMF.map _ (if model.active input state.2.2 then _ else _) = _
  by_cases ha : model.active input state.2.2 = true
  · simp only [ha, if_true, PMF.map_comp, counted_rejected, counted]
    rfl
  · simp only [ha, Bool.false_eq_true, if_false, PMF.map_comp, counted]
    rfl

theorem counted_trace_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => (current.1,current.2.2)) <$>
      (simulateQ (counted model).traced computation).run state =
      (simulateQ model.traced computation).run (state.1,state.2.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (fun current => (current.1,current.2.2))
    (counted_query_trace_erasure model) computation state

theorem counted_source_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × (Nat × State)) :
    Prod.map id (fun current => current.2.2) <$>
      (simulateQ (counted model).traced computation).run state =
      (simulateQ model.original computation).run state.2.2 := by
  have h := congrArg (fun law => Prod.map id Prod.snd <$> law)
    (counted_trace_erasure model computation state)
  rw [model.traced_erasure] at h
  change (fun a : Result × (List Label × (Nat × State)) => (a.1,a.2.2.2)) <$> _ = _
  simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq] using h

/-- Specialization to the concrete adaptive signing model on base T3. The event
retains the lifetime-cap premise; closing it against the game log is separate. -/
theorem signing_trace_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced program).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  full_trace_overflow_bound (LazyPrivate.proposalModel budget hbudget) rfl program state

theorem signing_trace_erasure {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Prod.map id (fun current => current.2.2) <$>
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced program).run ([],0,state) =
      (liftM (LazyPrivate.run (simulateQ LazyPrivate.interactionSource program) state) :
        PMF (Result × LazyPrivate.State)) := by
  rw [counted_source_erasure, LazyPrivate.proposal_execution_erasure]

def logFragment : (input : LazyPrivate.Interaction.Domain) →
    LazyPrivate.Interaction.Range input → QueryLog Requests
  | .inl _, _ => []
  | .inr request, response => [⟨request,response⟩]

def logging : QueryImpl LazyPrivate.Interaction
    (WriterT (QueryLog Requests) (OracleComp LazyPrivate.Interaction)) :=
  QueryImpl.withTraceAppend (fun input => LazyPrivate.Interaction.query input) logFragment

def logged {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    OracleComp LazyPrivate.Interaction (Result × QueryLog Requests) :=
  (simulateQ logging program).run

theorem logged_pure {Result : Type} (value : Result) : logged (pure value) = pure (value,[]) := rfl

theorem logged_query_bind {Result : Type} (input : LazyPrivate.Interaction.Domain)
    (next : LazyPrivate.Interaction.Range input → OracleComp LazyPrivate.Interaction Result) :
    logged (LazyPrivate.Interaction.query input >>= next) = (do
      let response ← LazyPrivate.Interaction.query input
      let result ← logged (next response)
      pure (result.1, logFragment input response ++ result.2)) := by
  simp [logged, logging, QueryImpl.withTraceAppend_apply]

theorem counted_query_count (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × (Nat × State))
    (result : spec.Range input × (List Label × (Nat × State)))
    (hr : result ∈ (((counted model).traced input).run state).support) :
    result.2.2.1 = state.2.1 + if model.active input state.2.2 then 1 else 0 := by
  simp only [ProposalModel.traced, proposalRecordImpl, counted, StateT.run_mk] at hr
  by_cases ha : model.active input state.2.2 = true
  · simp only [ha, if_true, PMF.support_map, Set.mem_image] at hr
    obtain ⟨outcome, _, rfl⟩ := hr
    simp only [ha, Bool.false_eq_true, if_true, if_false]
  · simp only [ha, Bool.false_eq_true, if_false, PMF.support_map, Set.mem_image] at hr
    obtain ⟨outcome, _, rfl⟩ := hr
    simp only [ha, Bool.false_eq_true, if_true, if_false]

theorem signing_count_le_fragment (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State))
    (result : LazyPrivate.Interaction.Range input × (List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State)))
    (hr : result ∈ (((counted (LazyPrivate.proposalModel budget hbudget)).traced input).run state).support) :
    result.2.2.1 ≤ state.2.1 + (logFragment input result.1).length := by
  rw [counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [LazyPrivate.proposalModel, LazyPrivate.interactionActive, logFragment]
  | inr request => simp only [logFragment, List.length_singleton]; split <;> omega

/-- Failed and repeated requests count too, exactly as in the source game log.
The active-request counter is bounded by this log on every supported execution. -/
theorem signing_count_le_log {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State))
    (result : (Result × QueryLog Requests) × (List DigestSampling.IndexBuckets × (Nat × LazyPrivate.State)))
    (hr : result ∈ ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
      (logged program)).run state).support) :
    result.2.2.1 ≤ state.2.1 + result.1.2.length := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [logged_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [logged_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      have hstep := signing_count_le_fragment budget hbudget input state middle hm
      rw [simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨last, hl, hr⟩ := hr
      have hrest := ih middle.1 middle.2 last hl
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp only [List.length_append]
      omega

theorem signing_log_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
        (logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow budget hbudget (logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
      (logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (counted (LazyPrivate.proposalModel budget hbudget)).traced
        (logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]

/-- Overflow in the existing, unmodified concrete proposal model, restricted
only by the source game's actual signing-log limit. -/
theorem source_proposal_overflow {Result : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : LazyPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (LazyPrivate.proposalModel budget hbudget).traced (logged program)).run ([],state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← counted_trace_erasure (LazyPrivate.proposalModel budget hbudget) (logged program) ([],0,state),
    probEvent_map]
  exact signing_log_overflow budget hbudget program state

/-- The logging adapter is exactly the writer used by `Security.game`, including
failed signing responses. It does not change the game or its freshness relation. -/
theorem logged_source {Result : Type} (program : OracleComp LazyPrivate.Interaction Result) :
    simulateQ LazyPrivate.interactionSource (logged program) =
      (simulateQ
        ((fun input => liftM (forwardWorld input) :
          QueryImpl SphincsSecurity.OracleWorld (WriterT (QueryLog Requests) M)) + signingOracle)
        program).run := by
  rw [logged, QueryImpl.simulateQ_writerTMapBase_run]
  congr 2
  funext input
  cases input <;>
    simp [QueryImpl.writerTMapBase, logging, QueryImpl.withTraceAppend_apply,
      logFragment, LazyPrivate.interactionSource, signingOracle]
  · rfl
  · apply WriterT.ext
    simp

end SigGolfCandidate.T3.Security.ProposalOverflow




/-! Authored module: QuerySpace. -/
section
/-! Injective finite coordinates for the base T3 source's public searches.
These are source query identities, independent of any security reduction. -/
namespace SigGolfCandidate.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem encodingInput_injective {lay lay' : Layer} {tree tree' leaf leaf' : Nat}
    {message message' : Digest × BitVec 96 × Digest} {counter counter' : BitVec 32}
    (ht : tree < 2^40) (ht' : tree' < 2^40)
    (hl : leaf < 2^32) (hl' : leaf' < 2^32)
    (he : encodingInput lay tree leaf message counter =
      encodingInput lay' tree' leaf' message' counter') :
    lay=lay' ∧ tree=tree' ∧ leaf=leaf' ∧ message=message' ∧ counter=counter' := by
  unfold encodingInput at he
  obtain ⟨hh,hr⟩ := List.append_inj he
    (by simp only [List.length_append,List.length_replicate,bytesLE_length])
  obtain ⟨hh,hp⟩ := List.append_inj hh (by simp only [List.length_append,bytesLE_length])
  obtain ⟨hh,hc⟩ := List.append_inj hh (by simp only [List.length_append,bytesLE_length])
  obtain ⟨hm,hh⟩ := List.append_inj hh (by simp only [bytesLE_length])
  have hhead := header_injective (by decide : 4<256) (by have := lay.isLt; omega)
    ht (by decide : 0<2^32) hl (by decide : 4<256) (by have := lay'.isLt; omega)
    ht' (by decide : 0<2^32) hl' (bytesLE_injective hh)
  exact ⟨Fin.ext hhead.2.1,hhead.2.2.1,hhead.2.2.2.2,
    Prod.ext (bytesLE_injective hm) (Prod.ext (bytesLE_injective hp) (bytesLE_injective hr)),
    bytesLE_injective hc⟩

theorem encodingTrial_coordinates {lay lay' : Layer} {tree tree' leaf leaf' : Nat}
    {message message' : Digest × BitVec 96 × Digest} {counter counter' : Nat}
    (ht : tree < 2^40) (ht' : tree' < 2^40)
    (hl : leaf < 2^32) (hl' : leaf' < 2^32)
    (hc : counter < 2^32) (hc' : counter' < 2^32)
    (he : encodingTrial lay tree leaf message counter =
      encodingTrial lay' tree' leaf' message' counter') :
    lay=lay' ∧ tree=tree' ∧ leaf=leaf' ∧ message=message' ∧ counter=counter' := by
  have he := pad64_inj_of_length (by simp [encodingInput,bytesLE_length]) he
  obtain ⟨a,b,c,d,e⟩ := encodingInput_injective ht ht' hl hl' he
  refine ⟨a,b,c,d,?_⟩
  have e := congrArg BitVec.toNat e
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc'] using e

theorem digestTrial_coordinates {rho rho' : Digest} {message message' : Message}
    {counter counter' : Nat} (hc : counter<2^32) (hc' : counter'<2^32)
    (he : digestTrial rho message counter=digestTrial rho' message' counter') :
    rho=rho' ∧ message=message' ∧ counter=counter' := by
  have he := pad64_inj_of_length (by simp [digestInput,bytesLE_length]) he
  obtain ⟨a,b,c⟩ := digestInput_injective he
  refine ⟨a,b,?_⟩
  have c := congrArg BitVec.toNat c
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc,Nat.mod_eq_of_lt hc'] using c

def queryHeader (input : HashInput) : HashInput := (input.drop 16).take 16

/-- The tag byte survives every other header field, including out-of-range
addresses. Domain separation therefore needs no address-range assumption. -/
theorem header_tag (tag lay tree position index : Nat) :
    ((header tag lay tree position index).toNat/256)%256=tag%256 := by
  rw [header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0<256)
  have hw := nodeWord_lt tag position index
  norm_num only [Nat.reducePow] at *
  split_ifs <;> omega

theorem header_ne_of_tag {tag tag' lay lay' tree tree' position position' index index' : Nat}
    (h : tag%256 ≠ tag'%256) :
    header tag lay tree position index ≠ header tag' lay' tree' position' index' := by
  intro he
  have ht := congrArg (fun h : BitVec 128 => (h.toNat/256)%256) he
  exact h (by simpa only [header_tag] using ht)

theorem header_layer (tag lay tree position index : Nat) :
    ((header tag lay tree position index).toNat/65536)%256=lay%256 := by
  rw [header_toNat]
  have ht := Nat.mod_lt tag (by decide : 0<256)
  have hl := Nat.mod_lt lay (by decide : 0<256)
  have hw := nodeWord_lt tag position index
  norm_num only [Nat.reducePow] at *
  split_ifs <;> omega

theorem header_ne_of_layer {tag tag' lay lay' tree tree' position position' index index' : Nat}
    (h : lay%256 ≠ lay'%256) :
    header tag lay tree position index ≠ header tag' lay' tree' position' index' := by
  intro he
  have hl := congrArg (fun h : BitVec 128 => (h.toNat/65536)%256) he
  exact h (by simpa only [header_layer] using hl)

theorem queryHeader_padded (front back : HashInput) (hprefix : front.length=16)
    (h : BitVec 128) : queryHeader (pad64 (front ++ bytesLE 16 h ++ back))=bytesLE 16 h := by
  simp [queryHeader,pad64,List.append_assoc,hprefix,bytesLE_length]

/-- Uniform tag separation for public or privately realized source buffers. -/
theorem padded_headers_ne (leftPrefix rightPrefix leftSuffix rightSuffix : HashInput)
    (hl : leftPrefix.length=16) (hr : rightPrefix.length=16)
    (tag tag' lay lay' tree tree' position position' index index' : Nat)
    (htags : tag%256 ≠ tag'%256) :
    pad64 (leftPrefix ++ bytesLE 16 (header tag lay tree position index) ++ leftSuffix) ≠
      pad64 (rightPrefix ++ bytesLE 16 (header tag' lay' tree' position' index') ++ rightSuffix) := by
  intro he
  have he := congrArg queryHeader he
  rw [queryHeader_padded _ _ hl,queryHeader_padded _ _ hr] at he
  exact header_ne_of_tag htags (bytesLE_injective he)

@[simp] theorem queryHeader_encoding (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest)
    (counter : Nat) : queryHeader (encodingTrial lay tree leaf message counter) =
      bytesLE 16 (header 4 lay.val tree 0 leaf) := by
  simp [queryHeader,encodingTrial,encodingInput,pad64,List.append_assoc,bytesLE_length]

@[simp] theorem queryHeader_digest (rho : Digest) (message : Message) (counter : Nat) :
    queryHeader (digestTrial rho message counter) =
      bytesLE 16 (header 12 0 0 0 (BitVec.ofNat 32 counter).toNat) := by
  simp [queryHeader,digestTrial,digestInput,pad64,List.append_assoc,bytesLE_length]

theorem encodingTrial_ne_digestTrial (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest)
    (counter : Nat) (rho : Digest) (msg : Message) (ctr : Nat)
    (ht : tree<2^40) (hl : leaf<2^32) :
    encodingTrial lay tree leaf message counter ≠ digestTrial rho msg ctr := by
  intro he
  have he := congrArg queryHeader he
  simp only [queryHeader_encoding,queryHeader_digest] at he
  have hh := header_injective (by decide : 4<256) (by have := lay.isLt; omega)
    ht (by decide : 0<2^32) hl (by decide : 12<256) (by decide : 0<256)
    (by decide : 0<2^40) (by decide : 0<2^32) (BitVec.ofNat 32 ctr).isLt
    (bytesLE_injective he)
  omega

abbrev EncodingFamily := Layer × Fin (2^31) × Fin 4096 × (Digest × BitVec 96 × Digest)
abbrev DigestFamily := Digest × Message
abbrev EncodingKey := EncodingFamily × Fin (2^22)
abbrev DigestKey := DigestFamily × Fin (2^20)
abbrev SearchKey := EncodingKey ⊕ DigestKey

def encodingQuery (key : EncodingKey) : HashInput :=
  encodingTrial key.1.1 key.1.2.1 key.1.2.2.1 key.1.2.2.2 key.2

def digestQuery (key : DigestKey) : HashInput := digestTrial key.1.1 key.1.2 key.2

def searchQuery : SearchKey → HashInput := Sum.elim encodingQuery digestQuery

theorem encodingQuery_injective : Function.Injective encodingQuery := by
  rintro ⟨⟨lay,tree,leaf,message⟩,counter⟩ ⟨⟨lay',tree',leaf',message'⟩,counter'⟩ he
  obtain ⟨a,b,c,d,e⟩ := encodingTrial_coordinates
    (by have := tree.isLt; omega) (by have := tree'.isLt; omega)
    (by have := leaf.isLt; omega) (by have := leaf'.isLt; omega)
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have b := Fin.ext b
  have c := Fin.ext c
  have e := Fin.ext e
  cases a; cases b; cases c; cases d; cases e; rfl

theorem digestQuery_injective : Function.Injective digestQuery := by
  rintro ⟨⟨rho,msg⟩,counter⟩ ⟨⟨rho',msg'⟩,counter'⟩ he
  obtain ⟨a,b,c⟩ := digestTrial_coordinates
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have c := Fin.ext c
  cases a; cases b; cases c; rfl

theorem searchQuery_injective : Function.Injective searchQuery := by
  intro left right he
  cases left with
  | inl l =>
    cases right with
    | inl r => exact congrArg Sum.inl (encodingQuery_injective he)
    | inr r => exact False.elim (encodingTrial_ne_digestTrial l.1.1 l.1.2.1 l.1.2.2.1
        l.1.2.2.2 l.2 r.1.1 r.1.2 r.2 (by have := l.1.2.1.isLt; omega)
        (by have := l.1.2.2.1.isLt; omega) he)
  | inr l =>
    cases right with
    | inl r => exact False.elim (encodingTrial_ne_digestTrial r.1.1 r.1.2.1 r.1.2.2.1
        r.1.2.2.2 r.2 l.1.1 l.1.2 l.2 (by have := r.1.2.1.isLt; omega)
        (by have := r.1.2.2.1.isLt; omega) he.symm)
    | inr r => exact congrArg Sum.inr (digestQuery_injective he)

end SigGolfCandidate.T3.QuerySpace

end

/-! Authored module: Presampling. -/
section
namespace SigGolfCandidate.T3.Presampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open QuerySpace
abbrev HashInput := SphincsSecurity.HashInput
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[irreducible] noncomputable def tableSampler : SampleableType (SearchKey → HashOutput) :=
  Derivation.outputSampler SearchKey
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler

noncomputable def preparedCache (outputs : SearchKey → HashOutput) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ searchQuery outputs

theorem preparedCache_apply (outputs : SearchKey → HashOutput) (key : SearchKey) :
    preparedCache outputs (searchQuery key)=some (outputs key) :=
  cacheTable_apply ∅ searchQuery searchQuery_injective outputs key

/-- Every public search input can be presampled, while all other source queries
continue to use the same consistent random oracle. This holds for any program,
including programs that choose search families from earlier oracle answers. -/
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (SearchKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' (preparedCache outputs)] := by
  let : SampleableType (SearchKey → SphincsSecurity.HashOutput) := tableSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (SearchKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) searchQuery)
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) searchQuery)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec)) (queryTable (R := SphincsSecurity.HashOutput) searchQuery))
  rw [evalDist_presample_computation (realize secret program) preparation ∅,hprep,
    evalSPMF_bind,evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput) searchQuery searchQuery_injective
      ∅ (fun _ => rfl)]
  simp only [evalSPMF_map,bind_map_left]
  rw [evalSPMF_bind]
  congr 1

noncomputable def tableAnswers (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) : Correctness.Answers
  | .inl (.inr input) => (preparedCache outputs input).getD (fallback (.inl (.inr input)))
  | .inl (.inl input) => fallback (.inl (.inl input))
  | .inr input => fallback (.inr input)

theorem tableAnswers_apply (outputs : SearchKey → HashOutput) (fallback : Correctness.Answers)
    (key : SearchKey) : tableAnswers outputs fallback (.inl (.inr (searchQuery key)))=outputs key := by
  simp only [tableAnswers,preparedCache_apply,Option.getD_some]

theorem eval_shortHash (answers : Correctness.Answers) (input : HashInput) :
    evalWithAnswerFn answers (shortHash input) =
      (answers (.inl (.inr (pad64 input)))).extractLsb' 0 128 := rfl

theorem eval_digest (answers : Correctness.Answers) (rho : Digest) (message : Message)
    (counter : BitVec 32) : evalWithAnswerFn answers (digest rho message counter) =
      answers (.inl (.inr (pad64 (digestInput rho message counter)))) := rfl

theorem uniform_table_forall {J : Type} [Fintype J] [DecidableEq J] [SampleableType (J → HashOutput)]
    (p : HashOutput → Prop) :
    Pr[fun outputs : J → HashOutput => ∀ j,p (outputs j) | ($ᵗ (J → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  classical
  rw [probEvent_uniformSample,probEvent_uniformSample]
  have hc : (Finset.univ.filter fun outputs : J → HashOutput => ∀ j,p (outputs j)).card =
      (Finset.univ.filter p).card ^ Fintype.card J := by
    rw [← Fintype.card_subtype,Fintype.card_congr
      (Equiv.subtypePiEquivPi (p := fun (_ : J) (x : HashOutput) => p x)),Fintype.card_pi]
    simp only [Fintype.card_subtype,Finset.prod_const,Finset.card_univ]
  rw [hc,Fintype.card_fun,Nat.cast_pow,Nat.cast_pow]
  simp only [div_eq_mul_inv,mul_pow,ENNReal.inv_pow]

theorem uniform_table_restriction_failure {J : Type} [Fintype J]
    [DecidableEq J] [SampleableType (J → HashOutput)] (e : J → SearchKey) (he : Function.Injective e)
    (p : HashOutput → Prop) :
    Pr[fun outputs : SearchKey → HashOutput => ∀ j,p (outputs (e j)) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  have h := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
  have hp := congrArg (fun law => probEvent law (fun outputs : J → HashOutput => ∀ j,p (outputs j))) h
  simpa only [probEvent_evalSPMF,bind_pure_comp,probEvent_map,Function.comp_def,uniform_table_forall] using hp

theorem counterSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : EncodingFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit)=none ↔
    ∀ c : Fin (2^22), Sampling.encodingDecode family.1 (outputs (.inl (family,c)))=none := by
  rw [Correctness.counterSearch_none_iff]
  have hv (c : Nat) (hc : c<counterLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (shortHash (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
          (BitVec.ofNat 32 (0+c)))) = (outputs (.inl (family,⟨c,hc⟩))).extractLsb' 0 128 := by
    rw [eval_shortHash]
    have hinput : pad64 (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
        (BitVec.ofNat 32 (0+c))) = searchQuery (.inl (family,⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inl,encodingQuery,Sampling.encodingTrial,Nat.zero_add]
    rw [hinput,tableAnswers_apply]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩

theorem digestSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : DigestFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (digestSearch family.1 family.2 0 attemptLimit)=none ↔
    ∀ c : Fin (2^20), Sampling.digestDecode (outputs (.inr (family,c)))=none := by
  rw [Correctness.digestSearch_none_iff]
  have hv (c : Nat) (hc : c<attemptLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (digest family.1 family.2 (BitVec.ofNat 32 (0+c))) = outputs (.inr (family,⟨c,hc⟩)) := by
    rw [eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        searchQuery (.inr (family,⟨c,hc⟩)) := by
      simp only [searchQuery,Sum.elim_inr,digestQuery,Sampling.digestTrial,Nat.zero_add]
    rw [hinput,tableAnswers_apply]
  have hd (value : HashOutput) : Sampling.digestDecode value=none ↔ digestAdmissible value=false := by
    simp [Sampling.digestDecode]
  constructor
  · intro h c
    rw [hd]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)

theorem counterSearch_table_failure (fallback : Correctness.Answers) (family : EncodingFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (Sampling.encodingDecode family.1)^counterLimit := by
  simp_rw [counterSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2^22) => .inl (family,c))
    (fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)) (fun x => Sampling.encodingDecode family.1 x=none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent,Fintype.card_fin,counterLimit,
    HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h

theorem digestSearch_table_failure (fallback : Correctness.Answers) (family : DigestFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (digestSearch family.1 family.2 0 attemptLimit)=none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass Sampling.digestDecode^attemptLimit := by
  simp_rw [digestSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2^20) => .inr (family,c))
    (fun _ _ h => congrArg Prod.snd (Sum.inr.inj h)) (fun x => Sampling.digestDecode x=none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent,Fintype.card_fin,attemptLimit,
    HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits] using h

end SigGolfCandidate.T3.Presampling

end

/-! Authored module: DigestCounting. -/
section
/-! Exact fresh BPORS digest acceptance for cap 124. This file counts the
source rejection predicate; it does not assert any adaptive security coupling. -/
noncomputable section


end

end

/-! Authored module: CorrectnessAdapters. -/
section
/-! Generic names for the base source's already verified forest factorization.
The frozen source programs and their query formats are unchanged. -/
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The exact forest loop in `signPayload`, definitionally equal to `forestRows`. -/
def signForest (index : Nat) (chosen : List Selection) :
    M (List Digest × List Digest × List Digest) :=
  (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])

theorem eval_signForest (answers : Answers) (index : Nat) (chosen : List Selection) :
    evalWithAnswerFn answers (signForest index chosen)=
      (forestOpenPrefix answers index chosen 7,forestProofPrefix answers index chosen 7,
        forestRoots answers index 7) :=
  eval_forestRows answers index chosen

/-- The fixed-size projections emitted by the source signer. -/
def assembledSignature (rho : Digest) (state : List Digest × List Digest × List Digest)
    (pieces : List Pieces) : Signature :=
  ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (pieces.getD lay.val ([],[]))⟩

@[simp] theorem assembledSignature_rho (rho : Digest)
    (state : List Digest × List Digest × List Digest) (pieces : List Pieces) :
    (assembledSignature rho state pieces).rho=rho := rfl

theorem signPayload_eq (cache : Cache) (message : Message) : signPayload cache message=(do
    let rho ← privateNonce message
    let some (_,output) ← digestSearch rho message 0 attemptLimit | pure none
    let state ← signForest (output.toNat%2^31) (selections output)
    let root ← forestPk (output.toNat%2^31) state.2.2
    let some pieces ← signLayers cache (output.toNat%2^31) 4 (root, 0, 0) | pure none
    pure (some (assembledSignature rho state pieces))) := rfl

theorem assembled_forest_recovery (answers : Answers) (rho : Digest) (output : HashOutput)
    (pieces : List Pieces) (hadm : admissible (selections output)=true) :
    evalWithAnswerFn answers (recoverFts
      (assembledSignature rho (evalWithAnswerFn answers
        (signForest (output.toNat%2^31) (selections output))) pieces)
      (output.toNat%2^31) (selections output))=
      some (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
        (forestRoots answers (output.toNat%2^31) 7))) := by
  rw [eval_signForest]
  exact recoverFts_from_signer_lists answers _ (output.toNat%2^31) output hadm
    (fun _ => rfl) (fun _ => rfl)

end SigGolfCandidate.T3.Correctness

end

/-! Authored module: Budgets. -/
section
namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- A finite family containing every encoding address reachable by the signer. -/
abbrev EncodingFamily := Layer × Fin (2^31) × Fin 4096 × (Digest × BitVec 96 × Digest)
abbrev DigestFamily := Digest × Message

def EncodingSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : EncodingFamily, ∃ found,
    evalWithAnswerFn answers (counterSearch family.1 family.2.1.val
      family.2.2.1.val family.2.2.2 0 counterLimit)=some found

def DigestSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : DigestFamily, ∃ found,
    evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=some found

def SearchesSucceed (answers : Answers) : Prop :=
  DigestSearchesSucceed answers ∧ EncodingSearchesSucceed answers

set_option exponentiation.threshold 600 in
theorem encodingFamily_card : Fintype.card EncodingFamily=2^397 := by
  norm_num [EncodingFamily,Layer,Fintype.card_prod,Fintype.card_bitVec]

theorem digestFamily_card : Fintype.card DigestFamily=2^384 := by
  calc
    Fintype.card DigestFamily = (2 : Nat)^128 * (2 : Nat)^256 := by
      simp only [DigestFamily,Digest,Message,Fintype.card_prod,Fintype.card_bitVec]
    _ = (2 : Nat)^(128+256) := (pow_add (2 : Nat) 128 256).symm
    _ = (2 : Nat)^384 := rfl

theorem route_tree_bound (index : Nat) (lay : Layer) (hindex : index < 2^31) :
    (route index lay).2 < 2^31 := by
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hindex

theorem route_leaf_4096 (index : Nat) (lay : Layer) : (route index lay).1 < 4096 := by
  have h := route_leaf_bound index lay
  fin_cases lay <;> norm_num [height] at h ⊢ <;> omega

theorem encodingSearchesSucceed_at_route (answers : Answers)
    (hgood : EncodingSearchesSucceed answers) (index : Nat) (hindex : index < 2^31)
    (lay : Layer) (message : Digest × BitVec 96 × Digest) : ∃ found,
    evalWithAnswerFn answers (counterSearch lay (route index lay).2
      (route index lay).1 message 0 counterLimit)=some found := by
  exact hgood (lay,⟨_,route_tree_bound index lay hindex⟩,
    ⟨_,route_leaf_4096 index lay⟩,message)

/-- The layer signer has no failure exit other than its bounded encoding searches. -/
theorem signLayers_succeeds (answers : Answers) (cache : Cache) (index : Nat)
    (hindex : index < 2^31) (hgood : EncodingSearchesSucceed answers) :
    ∀ n message, ∃ pieces,
      evalWithAnswerFn answers (signLayers cache index n message)=some pieces := by
  intro n
  induction n with
  | zero => intro message;exact ⟨[],rfl⟩
  | succ n ih =>
      intro message
      obtain ⟨⟨counter,digits⟩,hs⟩ :=
        encodingSearchesSucceed_at_route answers hgood index hindex (Fin.ofNat 4 n) message
      simp only [signLayers,evalWithAnswerFn_bind,hs]
      by_cases hn : n=0
      · simp only [hn,ite_true,evalWithAnswerFn_bind,evalWithAnswerFn_pure]
        exact ⟨_,rfl⟩
      · simp only [hn,ite_false,evalWithAnswerFn_bind]
        obtain ⟨previous,hp⟩ := ih
          (((((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits)).1).getD
            (height (Fin.ofNat 4 n) - 1) []).getD 0 0, 0, (((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits)).1).getD
            (height (Fin.ofNat 4 n) - 1) []).getD 1 0))
        simp only [hp,evalWithAnswerFn_pure]
        exact ⟨_,rfl⟩

theorem signPayload_succeeds (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceed answers) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message),message)
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)),0,0)
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

def SigningComplete (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (sign keys.2 message)=some sig ∧
    evalWithAnswerFn answers (expand message keys.1 sig)=some w ∧
    evalWithAnswerFn answers (verify message keys.1 w)=true

theorem signing_complete_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceed answers) :
    SigningComplete answers keys := by
  intro message
  obtain ⟨sig,hs⟩ := signPayload_succeeds answers keys.2 message hgood
  have hs' : evalWithAnswerFn answers (sign keys.2 message)=some sig := by
    rw [sign_valid_cache answers keys message hkeys.2.2]
    exact hs
  obtain ⟨w,he⟩ := signPayload_expands answers keys.2 message sig hkeys.2.1 hs
  rw [← hkeys.1] at he
  exact ⟨sig,w,hs',he,expand_implies_verify answers message keys.1 sig w he⟩

/-- A single finite family of successful searches suffices for every message,
including the nonce and intermediate roots chosen from the same oracle. -/
theorem honest_signing_complete_of_searches (answers : Answers) (hgood : SearchesSucceed answers) :
    SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_searches answers _ (keygen_correct answers) hgood

def RealizedSigningComplete (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (realize secret (sign keys.2 message))=some sig ∧
    evalWithAnswerFn answers (realize secret (expand message keys.1 sig))=some w ∧
    evalWithAnswerFn answers (realize secret (verify message keys.1 w))=true

theorem realized_honest_signing_complete_of_searches
    (answers : QueryImpl SphincsSecurity.OracleWorld Id) (secret : BitVec 256)
    (hgood : SearchesSucceed (answers.compose (realHandler secret))) :
    RealizedSigningComplete answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningComplete
  simp only [realize_eval]
  exact honest_signing_complete_of_searches (answers.compose (realHandler secret)) hgood

end SigGolfCandidate.T3.Correctness

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass failMass_eq_probEvent)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Exact one-trial encoding acceptance probability, as a real number. -/
noncomputable def encodingRate (lay : Layer) : ℝ := (EncodingCounting.acceptedCount lay : ℝ)/2^128

theorem encodingRate_bounds (lay : Layer) : 1/4096 ≤ encodingRate lay ∧ encodingRate lay ≤ 1 := by
  fin_cases lay <;> norm_num [encodingRate,EncodingCounting.acceptedCount]

theorem encodingRate_cast (lay : Layer) :
    ENNReal.ofReal (encodingRate lay)=(EncodingCounting.acceptedCount lay : ENNReal)/2^128 := by
  rw [encodingRate,ENNReal.ofReal_div_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num)]
  simp

theorem failMass_eq_one_sub_accept {β : Type} (decoder : HashOutput → Option β) :
    failMass decoder=1-Pr[fun answer => (decoder answer).isSome | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  classical
  rw [failMass_eq_probEvent]
  have h := Sampling.probEvent_not (fun answer => (decoder answer).isSome)
  simp only [probEvent_uniformSample] at h ⊢
  simpa only [HashOutput,SphincsSecurity.HashOutput,SphincsSecurity.hashOutputBits,
    Bool.not_eq_true,Option.isSome_eq_false_iff,Option.isNone_iff_eq_none] using h

theorem encoding_failMass (lay : Layer) :
    failMass (Sampling.encodingDecode lay)=ENNReal.ofReal (1-encodingRate lay) := by
  rw [failMass_eq_one_sub_accept,EncodingCounting.encoding_uniform_probability,← encodingRate_cast]
  rw [ENNReal.ofReal_sub 1 (by linarith [(encodingRate_bounds lay).1])]
  simp

/-- Elementary exponential tail estimate, keeping large trial counts symbolic. -/
theorem rejection_power_le (p : ℝ) (hp : p ≤ 1) (trials bits : Nat)
    (h : bits * Real.log 2 ≤ trials*p) : (1-p)^trials ≤ 1/(2 : ℝ)^bits := by
  calc
    (1-p)^trials ≤ (Real.exp (-p))^trials :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) _
    _ = Real.exp (-(trials*p)) := by rw [← Real.exp_nat_mul];congr 1;ring
    _ ≤ Real.exp (-(bits*Real.log 2)) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/(2 : ℝ)^bits := by
      rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num)]
      simp [one_div]

@[simp] theorem ofReal_inv_two_pow (n : Nat) :
    ENNReal.ofReal (1/(2 : ℝ)^n)=1/(2 : ENNReal)^n := by
  rw [ENNReal.ofReal_div_of_pos (show 0 < (2 : ℝ)^n by positivity),
    ENNReal.ofReal_one,ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),ENNReal.ofReal_ofNat]

theorem encoding_failure_power (lay : Layer) :
    failMass (Sampling.encodingDecode lay)^counterLimit ≤ 1/(2 : ENNReal)^1024 := by
  rw [encoding_failMass,← ENNReal.ofReal_pow (by linarith [(encodingRate_bounds lay).2])]
  have hreal := rejection_power_le (encodingRate lay) (encodingRate_bounds lay).2 counterLimit 1024
    (by have hl := Real.log_two_lt_d9;have hp := (encodingRate_bounds lay).1
        change (1024 : ℝ)*Real.log 2 ≤ 4194304*encodingRate lay
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast

/-- One actual source counter-search call in a fresh random-oracle cache. -/
theorem counterSearch_failure_le (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (cache : Sampling.RCache)
    (hfresh : ∀ c,0 ≤ c → c < 2^32 → cache (Sampling.encodingTrial lay tree leaf message c)=none) :
    Pr[fun result => result.1=none |
      Sampling.roRun secret (counterSearch lay tree leaf message 0 counterLimit) cache] ≤
      1/(2 : ENNReal)^1024 := by
  exact (Sampling.counterSearch_failure secret lay tree leaf message counterLimit 0
    (by decide) cache hfresh).trans (encoding_failure_power lay)

/-- Digest arithmetic is separated from the exact cap124 count. -/
theorem digest_failure_power_of_acceptance (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    failMass Sampling.digestDecode^attemptLimit ≤ 1/(2 : ENNReal)^450 := by
  have hm : failMass Sampling.digestDecode=ENNReal.ofReal (1-p) := by
    rw [failMass_eq_one_sub_accept,haccept,ENNReal.ofReal_sub 1 (by linarith)]
    simp
  rw [hm,← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le p hp1 attemptLimit 450
    (by have hl := Real.log_two_lt_d9
        change (450 : ℝ)*Real.log 2 ≤ 1048576*p
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast

open Correctness

def DigestFailed (family : DigestFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=none

def EncodingFailed (family : EncodingFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (counterSearch family.1 family.2.1.val
    family.2.2.1.val family.2.2.2 0 counterLimit)=none

theorem incomplete_implies_failed_search (answers : Answers)
    (h : ¬SigningComplete answers (evalWithAnswerFn answers keygen)) :
    (∃ family,DigestFailed family answers) ∨ (∃ family,EncodingFailed family answers) := by
  classical
  by_contra hnone
  obtain ⟨hd,he⟩ := not_or.mp hnone
  apply h
  apply honest_signing_complete_of_searches
  constructor
  · intro family
    cases hx : evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit) with
    | none => exact False.elim (hd ⟨family,hx⟩)
    | some found => exact ⟨found,rfl⟩
  · intro family
    cases hx : evalWithAnswerFn answers (counterSearch family.1 family.2.1.val
      family.2.2.1.val family.2.2.2 0 counterLimit) with
    | none => exact False.elim (he ⟨family,hx⟩)
    | some found => exact ⟨found,rfl⟩

theorem finite_family_failure_le {ι α : Type} [Fintype ι]
    (law : ProbComp α) (event : ι → α → Prop) (δ : ENNReal)
    (h : ∀ i,Pr[event i | law] ≤ δ) :
    Pr[fun value => ∃ i,event i value | law] ≤ (Fintype.card ι : ENNReal)*δ := by
  classical
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset ι) law event
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset ι)) (fun i _ => h i)
  have hu' : Pr[fun value => ∃ i,event i value | law] ≤
      ∑ i : ι,Pr[event i | law] := by
    simpa only [Finset.mem_univ,true_and] using hu
  exact hu'.trans (hb.trans_eq (by simp))

/-- Global all-message completeness via a finite family union bound. The law's
per-family marginals remain explicit for the presampling/ROM instantiation. -/
theorem signing_incomplete_probability_le (law : ProbComp Answers) (digestFail encodingFail : ENNReal)
    (hd : ∀ family,Pr[DigestFailed family | law] ≤ digestFail)
    (he : ∀ family,Pr[EncodingFailed family | law] ≤ encodingFail) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      (2 : ENNReal)^384*digestFail+(2 : ENNReal)^397*encodingFail := by
  have hm := probEvent_mono (mx := law) (fun answers _ => incomplete_implies_failed_search answers)
  have hd' := finite_family_failure_le law DigestFailed digestFail hd
  have he' := finite_family_failure_le law EncodingFailed encodingFail he
  rw [digestFamily_card,Nat.cast_pow,Nat.cast_ofNat] at hd'
  rw [encodingFamily_card,Nat.cast_pow,Nat.cast_ofNat] at he'
  exact hm.trans ((probEvent_or_le law _ _).trans (add_le_add hd' he'))

theorem signing_incomplete_probability_small (law : ProbComp Answers)
    (hd : ∀ family,Pr[DigestFailed family | law] ≤ 1/(2 : ENNReal)^450)
    (he : ∀ family,Pr[EncodingFailed family | law] ≤ 1/(2 : ENNReal)^1024) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      1/(2 : ENNReal)^65 := by
  refine (signing_incomplete_probability_le law _ _ hd he).trans ?_
  have hreal : (2 : ℝ)^384*(1/2^450)+2^397*(1/2^1024) ≤ 1/2^65 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^384*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^397*(1/2^1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^384 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast

end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- For a fixed message, the digest union needs only cover the private nonce. -/
def SearchesSucceedFor (answers : Answers) (message : Message) : Prop :=
  (∀ rho : Digest, ∃ found,
    evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed answers

theorem signPayload_succeedsFor (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message))
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)),0,0)
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem signing_complete_for_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig : Signature, ∃ w : Witness,
      evalWithAnswerFn answers (sign keys.2 message)=some sig ∧
      evalWithAnswerFn answers (expand message keys.1 sig)=some w ∧
      evalWithAnswerFn answers (verify message keys.1 w)=true := by
  obtain ⟨sig,hs⟩ := signPayload_succeedsFor answers keys.2 message hgood
  have hs' : evalWithAnswerFn answers (sign keys.2 message)=some sig := by
    rw [sign_valid_cache answers keys message hkeys.2.2]
    exact hs
  obtain ⟨w,he⟩ := signPayload_expands answers keys.2 message sig hkeys.2.1 hs
  rw [← hkeys.1] at he
  exact ⟨sig,w,hs',he,expand_implies_verify answers message keys.1 sig w he⟩
end SigGolfCandidate.T3.Correctness

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Correctness
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler

def zeroAnswers : Answers := fun q => by
  rcases q with (input | input) | input
  · exact (0 : Fin (input+1))
  · exact (0 : HashOutput)
  · exact (0 : HashOutput)

def SearchAgreement (outputs : QuerySpace.SearchKey → HashOutput) (answers : Answers) : Prop :=
  ∀ key,answers (.inl (.inr (QuerySpace.searchQuery key)))=outputs key

def tableGood (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  SearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)

theorem counterSearch_none_agreement (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : EncodingFamily) :
    evalWithAnswerFn answers
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit)=none ↔
    ∀ c : Fin (2^22), Sampling.encodingDecode family.1 (outputs (.inl (family,c)))=none := by
  rw [counterSearch_none_iff]
  have hv (c : Nat) (hc : c<counterLimit) :
      evalWithAnswerFn answers
        (shortHash (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
          (BitVec.ofNat 32 (0+c)))) = (outputs (.inl (family,⟨c,hc⟩))).extractLsb' 0 128 := by
    rw [Presampling.eval_shortHash]
    have hinput : pad64 (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
        (BitVec.ofNat 32 (0+c))) = QuerySpace.searchQuery (.inl (family,⟨c,hc⟩)) := by
      simp only [QuerySpace.searchQuery,Sum.elim_inl,QuerySpace.encodingQuery,Sampling.encodingTrial,Nat.zero_add]
    rw [hinput,hagree]

  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c,hc⟩

theorem digestSearch_none_agreement (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    evalWithAnswerFn answers (digestSearch family.1 family.2 0 attemptLimit)=none ↔
    ∀ c : Fin (2^20), Sampling.digestDecode (outputs (.inr (family,c)))=none := by
  rw [digestSearch_none_iff]
  have hv (c : Nat) (hc : c<attemptLimit) :
      evalWithAnswerFn answers (digest family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        outputs (.inr (family,⟨c,hc⟩)) := by
    rw [Presampling.eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0+c))) =
        QuerySpace.searchQuery (.inr (family,⟨c,hc⟩)) := by
      simp only [QuerySpace.searchQuery,Sum.elim_inr,QuerySpace.digestQuery,Sampling.digestTrial,Nat.zero_add]
    rw [hinput,hagree]

  have hd (value : HashOutput) : Sampling.digestDecode value=none ↔ digestAdmissible value=false := by
    simp [Sampling.digestDecode]
  constructor
  · intro h c
    rw [hd]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (hd _).mp (h ⟨c,hc⟩)

theorem tableGood_iff_searchesSucceed (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGood outputs ↔ SearchesSucceed answers := by
  unfold tableGood SearchesSucceed DigestSearchesSucceed EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers family).trans
      (digestSearch_none_agreement outputs answers hagree family).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)

theorem tableGood_searchesSucceed (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGood outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceed answers := (tableGood_iff_searchesSucceed outputs answers hagree).mp hgood

theorem tableGood_fallback_iff (outputs : QuerySpace.SearchKey → HashOutput) (fallback : Answers) :
    tableGood outputs ↔ SearchesSucceed (Presampling.tableAnswers outputs fallback) :=
  tableGood_iff_searchesSucceed outputs _ (Presampling.tableAnswers_apply outputs fallback)

theorem not_searchesSucceed_iff (answers : Answers) :
    ¬ SearchesSucceed answers ↔
      (∃ family,DigestFailed family answers) ∨ (∃ family,EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceed,DigestSearchesSucceed,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]

theorem tableGood_failure_le (digestFail encodingFail : ENNReal)
    (hd : failMass Sampling.digestDecode^attemptLimit ≤ digestFail)
    (he : ∀ lay,failMass (Sampling.encodingDecode lay)^counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^384*digestFail+(2 : ENNReal)^397*encodingFail := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun family outputs => DigestFailed family (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun family => (Presampling.digestSearch_table_failure zeroAnswers family).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [digestFamily_card,Nat.cast_pow,Nat.cast_ofNat] at hd'
  rw [encodingFamily_card,Nat.cast_pow,Nat.cast_ofNat] at he'
  simp only [tableGood,not_searchesSucceed_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')

theorem tableGood_failure_small_of_acceptance (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^65 := by
  refine (tableGood_failure_le _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ)^384*(1/2^450)+2^397*(1/2^1024) ≤ 1/2^65 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^384*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^397*(1/2^1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^384 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast

def tableGoodFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  SearchesSucceedFor (Presampling.tableAnswers outputs zeroAnswers) message

theorem tableGoodFor_iff_searchesSucceedFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGoodFor message outputs ↔ SearchesSucceedFor answers message := by
  unfold tableGoodFor SearchesSucceedFor EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro rho
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers (rho,message)).trans
      (digestSearch_none_agreement outputs answers hagree (rho,message)).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)

theorem tableGoodFor_searchesSucceedFor (message : Message) (outputs : QuerySpace.SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGoodFor message outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceedFor answers message := (tableGoodFor_iff_searchesSucceedFor message outputs answers hagree).mp hgood

theorem not_searchesSucceedFor_iff (answers : Answers) (message : Message) :
    ¬ SearchesSucceedFor answers message ↔
      (∃ rho : Digest,DigestFailed (rho,message) answers) ∨ (∃ family,EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceedFor,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]

theorem tableGoodFor_failure_le (message : Message) (digestFail encodingFail : ENNReal)
    (hd : failMass Sampling.digestDecode^attemptLimit ≤ digestFail)
    (he : ∀ lay,failMass (Sampling.encodingDecode lay)^counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^128*digestFail+(2 : ENNReal)^397*encodingFail := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (rho : Digest) outputs => DigestFailed (rho,message) (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun rho => (Presampling.digestSearch_table_failure zeroAnswers (rho,message)).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at hd'
  rw [encodingFamily_card,Nat.cast_pow,Nat.cast_ofNat] at he'
  simp only [tableGoodFor,not_searchesSucceedFor_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')

theorem tableGoodFor_failure_small_of_acceptance (message : Message) (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^321 := by
  refine (tableGoodFor_failure_le message _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ)^128*(1/2^450)+2^397*(1/2^1024) ≤ 1/2^321 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^128*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^397*(1/2^1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^128 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast

end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def encodingEnvelopeReal (lay : Layer) : ℝ :=
  ![(BaseAudit.b1 : ℝ),(BaseAudit.b2 : ℝ),(BaseAudit.b3 : ℝ),(BaseAudit.b4 : ℝ)] lay
noncomputable def encodingEnvelope (lay : Layer) : ENNReal := ENNReal.ofReal (encodingEnvelopeReal lay)

theorem encodingEnvelopeReal_ge_one (lay : Layer) : 1 ≤ encodingEnvelopeReal lay := by
  fin_cases lay <;> norm_num [encodingEnvelopeReal,BaseAudit.b1,BaseAudit.b2,BaseAudit.b3,BaseAudit.b4]

theorem encodingEnvelope_ge_one (lay : Layer) : 1 ≤ encodingEnvelope lay := by
  simpa only [encodingEnvelope,ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (encodingEnvelopeReal_ge_one lay)

theorem signing_z_le : SigGolfCandidate.Budget.zOf 131072 ≤ ENNReal.ofReal (BaseAudit.zU : ℝ) := by
  unfold SigGolfCandidate.Budget.zOf
  apply ENNReal.ofReal_le_ofReal
  convert SigGolfCandidate.Budget.rpow_two_inv_le 131072 (by decide) using 1 <;>
    norm_num [BaseAudit.zU]

theorem encoding_step_real (lay : Layer) :
    (BaseAudit.zU : ℝ)*((1-encodingRate lay)*encodingEnvelopeReal lay+encodingRate lay) ≤
      encodingEnvelopeReal lay := by
  fin_cases lay <;> norm_num [encodingRate,EncodingCounting.acceptedCount,encodingEnvelopeReal,
    BaseAudit.zU,BaseAudit.b1,BaseAudit.b2,BaseAudit.b3,BaseAudit.b4]

theorem encoding_moment_step (lay : Layer) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass (Sampling.encodingDecode lay)*encodingEnvelope lay+
        (1-failMass (Sampling.encodingDecode lay))) ≤ encodingEnvelope lay := by
  have hp0 : 0 ≤ encodingRate lay := by linarith [(encodingRate_bounds lay).1]
  have hp1 : 0 ≤ 1-encodingRate lay := by linarith [(encodingRate_bounds lay).2]
  have hb0 : 0 ≤ encodingEnvelopeReal lay := by linarith [encodingEnvelopeReal_ge_one lay]
  have hz0 : 0 ≤ (BaseAudit.zU : ℝ) := by norm_num [BaseAudit.zU]
  have hs : 1-(1-encodingRate lay)=encodingRate lay := by ring
  rw [encoding_failMass,← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 hp1,
    hs,encodingEnvelope]
  calc
    _ ≤ ENNReal.ofReal (BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1-encodingRate lay)*ENNReal.ofReal (encodingEnvelopeReal lay)+
        ENNReal.ofReal (encodingRate lay)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((BaseAudit.zU : ℝ)*
        ((1-encodingRate lay)*encodingEnvelopeReal lay+encodingRate lay)) := by
      rw [← ENNReal.ofReal_mul hp1,← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (encoding_step_real lay)

theorem V_counterSearch_fresh (secret : BitVec 256) (lay : Layer)
    (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (fuel counter : Nat)
    (hlimit : counter+fuel ≤ 2^32) (cache : Sampling.RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (Sampling.encodingTrial lay tree leaf message c)=none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (counterSearch lay tree leaf message counter fuel) cache ≤ encodingEnvelope lay :=
  Sampling.V_counterSearch secret _ _ (encodingEnvelope_ge_one lay)
    lay tree leaf message (encoding_moment_step lay) fuel counter hlimit cache hfresh
end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.b0 : ℝ)

theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope,← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.b0]

theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    failMass Sampling.digestDecode=ENNReal.ofReal (1-(DigestCounting.p0 : ℝ)) := by
  rw [failMass_eq_one_sub_accept,haccept,
    ENNReal.ofReal_sub 1 (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0])]
  simp

theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass Sampling.digestDecode*digestEnvelope+(1-failMass Sampling.digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (DigestCounting.p0 : ℝ) := by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]
  have hp1 : 0 ≤ 1-(DigestCounting.p0 : ℝ) := by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]
  have hb0 : 0 ≤ (BaseAudit.b0 : ℝ) := by norm_num [BaseAudit.b0]
  have hz0 : 0 ≤ (BaseAudit.zU : ℝ) := by norm_num [BaseAudit.zU]
  have hs : 1-(1-(DigestCounting.p0 : ℝ))=(DigestCounting.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept,← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1,hs,digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (BaseAudit.zU : ℝ) *
      (ENNReal.ofReal (1-(DigestCounting.p0 : ℝ))*ENNReal.ofReal (BaseAudit.b0 : ℝ)+
        ENNReal.ofReal (DigestCounting.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((BaseAudit.zU : ℝ)*
        ((1-(DigestCounting.p0 : ℝ))*(BaseAudit.b0 : ℝ)+(DigestCounting.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1,← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by apply ENNReal.ofReal_le_ofReal;norm_num [BaseAudit.zU,DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0,BaseAudit.b0]

theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter+fuel ≤ 2^32) (cache : Sampling.RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (Sampling.digestTrial rho message c)=none)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal (DigestCounting.p0 : ℝ)) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh

end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler

theorem digest_failure_power :
    failMass Sampling.digestDecode^attemptLimit ≤ 1/(2 : ENNReal)^450 :=
  digest_failure_power_of_acceptance (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0

theorem tableGood_failure_small :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^65 :=
  tableGood_failure_small_of_acceptance (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0

theorem tableGoodFor_failure_small (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^321 :=
  tableGoodFor_failure_small_of_acceptance message (DigestCounting.p0 : ℝ)
    (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) (by norm_num [DigestCounting.p0,SigGolfResearch.Gate6.Budget.p0]) DigestCounting.digest_probability_eq_p0

theorem tableGoodFor_failure_128 (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^128 := by
  refine (tableGoodFor_failure_small message).trans ?_
  simp only [one_div,ENNReal.inv_le_inv]
  exact pow_le_pow_right₀ (by norm_num) (by decide)

theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass Sampling.digestDecode*digestEnvelope+(1-failMass Sampling.digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance DigestCounting.digest_probability_eq_p0

theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter+fuel ≤ 2^32) (cache : Sampling.RCache)
    (hfresh : ∀ c,counter ≤ c → c < 2^32 → cache (Sampling.digestTrial rho message c)=none) :
    Sampling.V secret (SigGolfCandidate.Budget.zOf 131072)
      (digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    DigestCounting.digest_probability_eq_p0
end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Sampling Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev signingZ : ENNReal := SigGolfCandidate.Budget.zOf 131072

def EncodingFreshBelow (n : Nat) (cache : RCache) : Prop :=
  ∀ lay : Layer,lay.val<n → ∀ tree leaf message c,c<2^32 →
    cache (encodingTrial lay tree leaf message c)=none

def AllSearchesFresh (cache : RCache) : Prop :=
  (∀ rho message c,c<2^32 → cache (digestTrial rho message c)=none) ∧ EncodingFreshBelow 4 cache

/-- Precisely the source-stage preservation obligations used by the moment
composition. Every premise concerns actual reachable random-oracle caches. -/
structure SourceFreshness (secret : BitVec 256) : Prop where
  counter : ∀ lay tree leaf message cache,EncodingFreshBelow (lay.val+1) cache →
    ∀ result ∈ support (roRun secret (counterSearch lay tree leaf message 0 counterLimit) cache),
      EncodingFreshBelow lay.val result.2
  tree : ∀ lay tree leaf digits cache,EncodingFreshBelow lay.val cache →
    ∀ result ∈ support (roRun secret (buildTree lay tree leaf digits) cache),
      EncodingFreshBelow lay.val result.2
  mac : ∀ region cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (privateMac region) cache),AllSearchesFresh result.2
  nonce : ∀ message cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (privateNonce message) cache),AllSearchesFresh result.2
  digest : ∀ rho message cache,AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret (digestSearch rho message 0 attemptLimit) cache),
      EncodingFreshBelow 4 result.2
  forest : ∀ index chosen cache,EncodingFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (signForest index chosen) cache),EncodingFreshBelow 4 result.2
  forestPk : ∀ index roots cache,EncodingFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (forestPk index roots) cache),EncodingFreshBelow 4 result.2

@[simp] theorem allSearchesFresh_empty : AllSearchesFresh ∅ := by
  constructor
  · intro rho message c hc;rfl
  · intro lay hl tree leaf message c hc;rfl

theorem post_of_roRun {α : Type} {P : Cost.Query → Prop} {Post : α → Prop} {k : Nat}
    {program : M α} (h : Cost.Bound P Post k program) (secret : BitVec 256) (cache : RCache)
    (result : α × RCache) (hr : result ∈ support (roRun secret program cache)) : Post result.1 := by
  have hs : result.1 ∈ support (realize secret program) := by
    apply support_simulateQ_run'_subset SphincsSecurity.romImpl _ cache
    rw [StateT.run'_eq,support_map]
    exact ⟨result,hr,rfl⟩
  have hs' := realize_support_subset secret program hs
  rw [← fst_countWith weight program,support_map] at hs'
  obtain ⟨counted,hc,he⟩ := hs'
  rw [← he]
  exact (h.count_support counted hc).1

theorem V_bind_bounded {α β : Type} (secret : BitVec 256) (z : ENNReal)
    (first : M α) (next : α → M β) (cache : RCache) (a b : ENNReal)
    (ha : V secret z first cache ≤ a)
    (hb : ∀ result ∈ support (roRun secret first cache),V secret z (next result.1) result.2 ≤ b) :
    V secret z (first >>= next) cache ≤ a*b :=
  (V_bind_le secret z first next cache b hb).trans (mul_le_mul' ha le_rfl)

noncomputable def layerMomentBound : Nat → ENNReal
  | 0 => 1
  | n+1 => encodingEnvelope (Fin.ofNat 4 n)*
      (if n=0 then signingZ^165 else signingZ^(treeCost (Fin.ofNat 4 n))*layerMomentBound n)

theorem layerMomentBound_ge_one : ∀ n,1 ≤ layerMomentBound n := by
  intro n;induction n with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [layerMomentBound]
      apply one_le_mul (encodingEnvelope_ge_one _)
      split
      · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
      · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) ih

theorem V_signLayers_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (index : Nat) : ∀ n,n≤4 → ∀ message rcache,EncodingFreshBelow n rcache →
    V secret signingZ (signLayers cache index n message) rcache ≤ layerMomentBound n := by
  intro n
  induction n with
  | zero => intro _ message rcache _;simp only [signLayers,V_pure,layerMomentBound,le_refl]
  | succ n ih =>
      intro hn message rcache hc
      have hnv : (Fin.ofNat 4 n).val=n := Nat.mod_eq_of_lt (by omega)
      have heFresh : EncodingFreshBelow ((Fin.ofNat 4 n).val+1) rcache := by rwa [hnv]
      have hs := V_counterSearch_fresh secret (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 message
        counterLimit 0 (by decide) rcache
        (fun c _ hlim => hc _ (by rw [hnv];omega) _ _ _ _ hlim)
      simp only [signLayers,layerMomentBound]
      refine V_bind_bounded secret signingZ _ _ rcache _ _ hs ?_
      intro result hr
      have hpost := post_of_roRun (bound_counterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 message counterLimit 0)
        secret rcache result hr
      have hnext := hf.counter (Fin.ofNat 4 n) _ _ message rcache heFresh result hr
      cases hx : result.1 with
      | none =>
          simp only [hx,V_pure]
          split
          · exact one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)
          · exact one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerMomentBound_ge_one n)
      | some pair =>
          obtain ⟨counter,digits⟩ := pair
          have hd := hpost counter digits hx
          simp only [hx]
          by_cases hn0 : n=0
          · subst n
            simp only [ite_true]
            refine V_bind_bounded secret signingZ _ _ result.2 _ 1
              (V_of_bound (bound_signTop cache _ digits hd.1 hd.2.1) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_ |>.trans_eq (mul_one _)
            intro out _;rw [V_pure]
          · simp only [hn0,ite_false]
            refine V_bind_bounded secret signingZ _ _ result.2 _ _
              (V_of_bound (bound_buildTree (Fin.ofNat 4 n) _ _ digits hd.2.2) secret signingZ
                (SigGolfCandidate.Budget.one_le_zOf _) result.2) ?_
            intro treeResult htree
            have ht := hf.tree (Fin.ofNat 4 n) _ _ digits result.2 hnext treeResult htree
            rw [hnv] at ht
            refine V_bind_bounded secret signingZ _ _ treeResult.2 _ 1
              (ih (by omega) _ _ ht) ?_ |>.trans_eq (mul_one _)
            intro previous _
            cases previous.1 <;> rw [V_pure]

end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Correctness
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- One digest family for each actual source nonce, plus every encoding family. -/
def SearchesSucceedSelected (answers : Answers) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn answers (digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed answers

theorem signPayload_succeedsSelected (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedSelected answers) :
    ∃ sig,evalWithAnswerFn answers (signPayload cache message)=some sig := by
  obtain ⟨⟨counter,output⟩,hd⟩ := hgood.1 message
  rw [signPayload_eq]
  simp only [evalWithAnswerFn_bind,hd,eval_signForest]
  obtain ⟨pieces,hp⟩ := signLayers_succeeds answers cache (output.toNat%2^31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
      (forestRoots answers (output.toNat%2^31) 7)),0,0)
  simp only [hp,evalWithAnswerFn_pure]
  exact ⟨_,rfl⟩

theorem signing_complete_of_selected_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceedSelected answers) :
    SigningComplete answers keys := by
  intro message
  obtain ⟨sig,hs⟩ := signPayload_succeedsSelected answers keys.2 message hgood
  have hs' : evalWithAnswerFn answers (sign keys.2 message)=some sig := by
    rw [sign_valid_cache answers keys message hkeys.2.2]
    exact hs
  obtain ⟨w,he⟩ := signPayload_expands answers keys.2 message sig hkeys.2.1 hs
  rw [← hkeys.1] at he
  exact ⟨sig,w,hs',he,expand_implies_verify answers message keys.1 sig w he⟩
end SigGolfCandidate.T3.Correctness

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) := Presampling.tableSampler

/-- For a fixed table of actual private nonce answers, only one digest search
per message is needed. The search table is independently uniform. -/
def tableGoodForNonces (nonces : Message → HashOutput) (outputs : QuerySpace.SearchKey → HashOutput) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn (Presampling.tableAnswers outputs zeroAnswers)
      (digestSearch ((nonces message).extractLsb' 0 128) message 0 attemptLimit)=some found) ∧
  EncodingSearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)

def NonceAgreement (nonces : Message → HashOutput) (answers : Answers) : Prop :=
  ∀ message,evalWithAnswerFn answers (privateNonce message)=(nonces message).extractLsb' 0 128

theorem tableGoodForNonces_searchesSucceedSelected (nonces : Message → HashOutput)
    (outputs : QuerySpace.SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SearchesSucceedSelected answers := by
  constructor
  · intro message
    rw [hnonce]
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.digestSearch_none_table outputs zeroAnswers
      ((nonces message).extractLsb' 0 128,message)).mpr
      ((digestSearch_none_agreement outputs answers hagree
        ((nonces message).extractLsb' 0 128,message)).mp hnone)
    obtain ⟨found,hfound⟩ := hgood.1 message
    rw [hfound] at hnone'
    cases hnone'
  · intro family
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.counterSearch_none_table outputs zeroAnswers family).mpr
      ((counterSearch_none_agreement outputs answers hagree family).mp hnone)
    obtain ⟨found,hfound⟩ := hgood.2 family
    rw [hfound] at hnone'
    cases hnone'

theorem tableGoodForNonces_signingComplete (nonces : Message → HashOutput)
    (outputs : QuerySpace.SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_selected_searches answers _ (keygen_correct answers)
    (tableGoodForNonces_searchesSucceedSelected nonces outputs answers hgood hagree hnonce)

theorem not_tableGoodForNonces_iff (nonces : Message → HashOutput)
    (outputs : QuerySpace.SearchKey → HashOutput) :
    ¬tableGoodForNonces nonces outputs ↔
    (∃ message : Message,DigestFailed ((nonces message).extractLsb' 0 128,message)
      (Presampling.tableAnswers outputs zeroAnswers)) ∨
    (∃ family,EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [tableGoodForNonces,EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists',not_and_or,not_forall,not_not,DigestFailed,EncodingFailed]

theorem tableGoodForNonces_failure_le (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal)^256*(1/2^450)+(2 : ENNReal)^397*(1/2^1024) := by
  let law := ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (message : Message) outputs => DigestFailed ((nonces message).extractLsb' 0 128,message)
      (Presampling.tableAnswers outputs zeroAnswers)) (1/(2 : ENNReal)^450)
    (fun message => (Presampling.digestSearch_table_failure zeroAnswers
      ((nonces message).extractLsb' 0 128,message)).le.trans digest_failure_power)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers))
      (1/(2 : ENNReal)^1024)
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (encoding_failure_power family.1))
  rw [Fintype.card_bitVec,Nat.cast_pow,Nat.cast_ofNat] at hd'
  rw [encodingFamily_card,Nat.cast_pow,Nat.cast_ofNat] at he'
  simp only [not_tableGoodForNonces_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')

theorem tableGoodForNonces_failure_small (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] ≤ 1/(2 : ENNReal)^193 := by
  refine (tableGoodForNonces_failure_le nonces).trans ?_
  have hreal : (2 : ℝ)^256*(1/2^450)+2^397*(1/2^1024) ≤ 1/2^193 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ)^256*(1/2^450) by positivity)
    (show 0 ≤ (2 : ℝ)^397*(1/2^1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^256 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat,ofReal_inv_two_pow] using hcast

end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec ENNReal Sampling Cost Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem bound_signForest (index : Nat) (chosen : List Selection) :
    CBound (fun state : List Digest × List Digest × List Digest => state.2.2.length=7)
      35833 (signForest index chosen) := by
  unfold signForest
  refine (Bound.foldlM_range 7 _
    (fun coord (state : List Digest × List Digest × List Digest) => state.2.2.length=coord)
    (fun _ => 5119) ([],[],[]) rfl (fun coord _ state hstate => ?_)).mono_k (by decide)
  refine (bound_buildFts index coord).bind' (l := 0) (fun result _ => ?_) (by decide)
  exact .pure _ 0 (by simp [hstate])

noncomputable def postDigestMoment : ENNReal := signingZ^35833*(signingZ^2*layerMomentBound 4)
noncomputable def payloadMoment : ENNReal := signingZ^2*(digestEnvelope*postDigestMoment)
noncomputable def signingMoment : ENNReal := signingZ^2*payloadMoment

theorem postDigestMoment_ge_one : 1 ≤ postDigestMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerMomentBound_ge_one 4))

theorem payloadMoment_ge_one : 1 ≤ payloadMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestEnvelope_ge_one postDigestMoment_ge_one)

theorem V_signPayload_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (signPayload cache message) rcache ≤ payloadMoment := by
  rw [signPayload_eq]
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateNonce message) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro nonce hn
  have hnFresh := hf.nonce message rcache hc nonce hn
  refine V_bind_bounded secret signingZ _ _ nonce.2 _ _
    (V_digestSearch_fresh secret nonce.1 message attemptLimit 0 (by decide) nonce.2
      (fun c _ hlim => hnFresh.1 _ _ _ hlim)) ?_
  intro found hd
  have hdFresh := hf.digest nonce.1 message nonce.2 hnFresh found hd
  cases hx : found.1 with
  | none => simp only [V_pure];exact postDigestMoment_ge_one
  | some pair =>
      obtain ⟨counter,output⟩ := pair
      refine V_bind_bounded secret signingZ _ _ found.2 _ _
        (V_of_bound (bound_signForest (output.toNat%2^31) (selections output)) secret signingZ
          (SigGolfCandidate.Budget.one_le_zOf _) found.2) ?_
      intro forest hforest
      have hlen := post_of_roRun (bound_signForest (output.toNat%2^31) (selections output))
        secret found.2 forest hforest
      have hforestFresh := hf.forest _ _ found.2 hdFresh forest hforest
      refine V_bind_bounded secret signingZ _ _ forest.2 _ _
        (V_of_bound (bound_forestPk (output.toNat%2^31) forest.1.2.2 hlen) secret signingZ
          (SigGolfCandidate.Budget.one_le_zOf _) forest.2) ?_
      intro root hroot
      have hrootFresh := hf.forestPk _ _ forest.2 hforestFresh root hroot
      refine V_bind_bounded secret signingZ _ _ root.2 _ 1
        (V_signLayers_of_freshness secret hf cache (output.toNat%2^31) 4 (by decide) (root.1,0,0) root.2 hrootFresh)
        ?_ |>.trans_eq (mul_one _)
      intro pieces _
      cases pieces.1 <;> rw [V_pure]

theorem V_sign_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ signingMoment := by
  unfold sign
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateMac cache.region) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro result hr
  have hmac := hf.mac cache.region rcache hc result hr
  split
  · rw [V_pure];exact payloadMoment_ge_one
  · exact V_signPayload_of_freshness secret hf cache message result.2 hmac

theorem layerMomentBound_four :
    layerMomentBound 4 = signingZ^85922 * encodingEnvelope 0 * encodingEnvelope 1 *
      encodingEnvelope 2 * encodingEnvelope 3 := by
  change encodingEnvelope 3*(signingZ^21439*(encodingEnvelope 2*
    (signingZ^21439*(encodingEnvelope 1*(signingZ^42879*(encodingEnvelope 0*signingZ^165)))))) = _
  ring

theorem signingMoment_eq : signingMoment=signingZ^121761 *
    (digestEnvelope*encodingEnvelope 0*encodingEnvelope 1*encodingEnvelope 2*encodingEnvelope 3) := by
  rw [signingMoment,payloadMoment,postDigestMoment,layerMomentBound_four]
  ring

theorem signingMoment_le_two : signingMoment ≤ 2 := by
  rw [signingMoment_eq,SigGolfCandidate.Budget.zOf_pow]
  have hreal := BaseAudit.source_signing_envelope
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ)^((121761 : ℝ)/131072) by positivity)] at hcast
  norm_num only [ENNReal.ofReal_ofNat] at hcast
  have he : digestEnvelope*encodingEnvelope 0*encodingEnvelope 1*encodingEnvelope 2*encodingEnvelope 3 =
      ENNReal.ofReal ((507635451307 / 500000000000) * (1009892452433 / 1000000000000) *
        (1008345227909 / 1000000000000) * (1008345227909 / 1000000000000) * (503409673483 / 500000000000) : ℝ) := by
    change ENNReal.ofReal (BaseAudit.b0 : ℝ)*ENNReal.ofReal (BaseAudit.b1 : ℝ)*
      ENNReal.ofReal (BaseAudit.b2 : ℝ)*ENNReal.ofReal (BaseAudit.b3 : ℝ)*ENNReal.ofReal (BaseAudit.b4 : ℝ) = _
    rw [← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ) by norm_num [BaseAudit.b0]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ)*(BaseAudit.b1 : ℝ) by norm_num [BaseAudit.b0,BaseAudit.b1]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ)*(BaseAudit.b1 : ℝ)*(BaseAudit.b2 : ℝ) by norm_num [BaseAudit.b0,BaseAudit.b1,BaseAudit.b2]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ)*(BaseAudit.b1 : ℝ)*(BaseAudit.b2 : ℝ)*(BaseAudit.b3 : ℝ) by norm_num [BaseAudit.b0,BaseAudit.b1,BaseAudit.b2,BaseAudit.b3])]
    norm_num [BaseAudit.b0,BaseAudit.b1,BaseAudit.b2,BaseAudit.b3,BaseAudit.b4]
  rw [he]
  convert hcast using 1 <;> norm_num

theorem V_sign_le_two_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness secret hf cache message rcache hc).trans signingMoment_le_two
end SigGolfCandidate.T3.Budgets

namespace SigGolfCandidate.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem signingZ_pow (cost : Nat) :
    signingZ^cost=(2 : ENNReal)^((cost : ℝ)/131072) := by
  rw [SigGolfCandidate.Budget.zOf_pow,← ENNReal.ofReal_rpow_of_pos (by norm_num),ENNReal.ofReal_ofNat]
  norm_num

theorem realized_sign_exponential_budget_of_freshness (secret : BitVec 256)
    (hf : SourceFreshness secret) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFresh rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal)^((result.2 : ℝ)/131072)) ≤ 2 := by
  have h := V_sign_le_two_of_freshness secret hf cache message rcache hc
  rw [V_realized] at h
  simp only [signingZ_pow] at h
  rw [StateT.run'_eq,expectedValue_map]
  exact h
end SigGolfCandidate.T3.Budgets

end

/-! Authored module: Freshness. -/
section
namespace SigGolfCandidate.T3.Freshness
open OracleComp OracleSpec Sampling QuerySpace Correctness
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Seeded (cacheAfter romImpl_support_cacheAfter)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def avoidsQuery (secret : BitVec 256) (target : HashInput) : Spec.Domain → Prop
 | .inl (.inl _) => True
 | .inl (.inr input) => input ≠ target
 | .inr coordinate => privateInput secret coordinate ≠ target

abbrev Avoids {α : Type} (secret : BitVec 256) (target : HashInput) (program : M α) : Prop :=
 AllQueriesSatisfy program (avoidsQuery secret target)

theorem avoids_pure {α : Type} (secret : BitVec 256) (target : HashInput) (value : α) :
 Avoids secret target (pure value) := allQueriesSatisfy_pure _ _
theorem avoids_bind {α β : Type} {secret : BitVec 256} {target : HashInput}
 {program : M α} {next : α → M β} (hp : Avoids secret target program)
 (hn : ∀ a, Avoids secret target (next a)) : Avoids secret target (program >>= next) :=
 allQueriesSatisfy_bind hp hn

theorem avoids_map {α β : Type} (f : α → β) {secret : BitVec 256} {target : HashInput}
 {program : M α} (hp : Avoids secret target program) : Avoids secret target (f <$> program) := by
 rw [map_eq_bind_pure_comp]
 exact avoids_bind hp fun _ => avoids_pure _ _ _

theorem avoids_mapM {α β : Type} (secret : BitVec 256) (target : HashInput)
 (items : List α) (f : α → M β) (h : ∀ a, Avoids secret target (f a)) :
 Avoids secret target (items.mapM f) := by
 induction items with
 | nil => exact avoids_pure _ _ _
 | cons a items ih =>
   rw [List.mapM_cons]
   exact avoids_bind (h a) fun _ => avoids_bind ih fun _ => avoids_pure _ _ _

theorem avoids_foldlM {α β : Type} (secret : BitVec 256) (target : HashInput)
 (items : List β) (f : α → β → M α) (h : ∀ a b, Avoids secret target (f a b)) (initial : α) :
 Avoids secret target (items.foldlM f initial) := by
 induction items generalizing initial with
 | nil => exact avoids_pure _ _ _
 | cons a items ih =>
   rw [List.foldlM_cons]
   exact avoids_bind (h initial a) ih

theorem cache_step_ne (input target : HashInput) (hne : input ≠ target) (cache : RCache)
 (result : HashOutput × RCache) (hr : result ∈ support ((SphincsSecurity.romImpl (.inr input)).run cache)) :
 result.2 target = cache target := by
 rw [romImpl_support_cacheAfter (.inr input) cache result hr]
 dsimp only [cacheAfter]
 cases hc : cache input <;> simp only [hc]
 exact QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)

theorem query_preserves (secret : BitVec 256) (target : HashInput) (q : Spec.Domain)
 (hq : avoidsQuery secret target q) (cache : RCache) (result : Spec.Range q × RCache)
 (hr : result ∈ support (roRun secret (liftM (Spec.query q)) cache)) : result.2 target=cache target := by
 rcases q with (n|input)|coordinate
 · change result ∈ support ((SphincsSecurity.romImpl (.inl n)).run cache) at hr
   rw [romImpl_support_cacheAfter (.inl n) cache result hr]
   rfl
 · have hr : result ∈ support ((SphincsSecurity.romImpl (.inr input)).run cache) := by
     simpa only [roRun,realize,simulateQ_spec_query,realHandler] using hr
   exact cache_step_ne input target hq cache result hr
 · have hr : result ∈ support ((SphincsSecurity.romImpl (.inr (privateInput secret coordinate))).run cache) := by
     simpa only [roRun,realize,simulateQ_spec_query,realHandler] using hr
   exact cache_step_ne _ target hq cache result hr

/-- Every possible source oracle execution preserves a cache entry it never queries. -/
theorem preserves {α : Type} (secret : BitVec 256) (target : HashInput) (program : M α)
 (hp : Avoids secret target program) (cache : RCache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : result.2 target=cache target := by
 induction program using OracleComp.inductionOn generalizing cache with
 | pure value =>
   rw [roRun_pure,support_pure,Set.mem_singleton_iff] at hr
   subst result; rfl
 | query_bind q next ih =>
   change AllQueriesSatisfy _ (avoidsQuery secret target) at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rw [roRun_bind,mem_support_bind_iff] at hr
   obtain ⟨step,hs,hr⟩ := hr
   exact (ih step.1 (hp.2 step.1) step.2 hr).trans (query_preserves secret target q hp.1 cache step hs)

/-- A tagged query is separated from all search inputs with a different tag. -/
def HasTag (tag : Nat) (input : HashInput) : Prop :=
 ∃ lay tree position index, queryHeader input = bytesLE 16 (header tag lay tree position index)

theorem tagged_ne {tag tag' : Nat} {input input' : HashInput}
 (h : HasTag tag input) (h' : HasTag tag' input') (hne : tag%256 ≠ tag'%256) : input ≠ input' := by
 rcases h with ⟨l,t,p,i,h⟩
 rcases h' with ⟨l',t',p',i',h'⟩
 intro he
 exact header_ne_of_tag hne (bytesLE_injective (h.symm.trans ((congrArg queryHeader he).trans h')))

theorem hasTag_padded (front back : HashInput) (hfront : front.length=16)
 (tag lay tree position index : Nat) :
 HasTag tag (pad64 (front ++ bytesLE 16 (header tag lay tree position index) ++ back)) :=
 ⟨lay,tree,position,index,queryHeader_padded _ _ hfront _⟩

@[simp] theorem hasTag_encoding (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter : Nat) :
 HasTag 4 (encodingTrial lay tree leaf message counter) := ⟨lay.val,tree,0,leaf,queryHeader_encoding ..⟩
@[simp] theorem hasTag_digest (rho : Digest) (message : Message) (counter : Nat) :
 HasTag 12 (digestTrial rho message counter) :=
 ⟨0,0,0,(BitVec.ofNat 32 counter).toNat,queryHeader_digest ..⟩



theorem tagged_ne_search {tag : Nat} {input target : HashInput}
 (hi : HasTag tag input) (ht : HasTag 4 target ∨ HasTag 12 target)
 (h4 : tag%256 ≠ 4) (h12 : tag%256 ≠ 12) : input ≠ target := by
 rcases ht with ht | ht
 · exact tagged_ne hi ht h4
 · exact tagged_ne hi ht h12

theorem avoids_shortHash_of_ne (secret : BitVec 256) (target input : HashInput)
 (hne : pad64 input ≠ target) : Avoids secret target (shortHash input) := by
 unfold shortHash
 apply avoids_bind
 · exact (allQueriesSatisfy_query_iff _ _).mpr hne
 · intro _; exact avoids_pure _ _ _

theorem avoids_privateHash_of_ne (secret : BitVec 256) (target : HashInput) (coordinate : Coordinate)
 (hne : privateInput secret coordinate ≠ target) : Avoids secret target (privateHash coordinate) :=
 (allQueriesSatisfy_query_iff _ _).mpr hne

theorem hasTag_privatePair (secret : BitVec 256) (tag lay tree position index : Nat) :
 HasTag tag (privateInput secret (.inl (header tag lay tree position index))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) tag lay tree position index

theorem hasTag_privateMac (secret : BitVec 256) (region : Region) :
 HasTag 14 (privateInput secret (.inr (.inr region))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) 14 0 0 0 0

theorem hasTag_privateNonce (secret : BitVec 256) (message : Message) :
 HasTag 7 (privateInput secret (.inr (.inl message))) := by
 exact hasTag_padded _ _ (bytesLE_length ..) 7 0 0 0 0

attribute [aesop safe apply] avoids_pure avoids_bind avoids_map avoids_mapM avoids_foldlM
macro "avoids_search" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

section NonSearch
variable (secret : BitVec 256) (target : HashInput) (ht : HasTag 4 target ∨ HasTag 12 target)
include ht

@[aesop safe apply] theorem avoids_privatePair (tag lay tree position index : Nat)
 (h4 : tag%256 ≠ 4) (h12 : tag%256 ≠ 12) :
 Avoids secret target (privatePair tag lay tree position index) := by
 unfold privatePair
 apply avoids_bind
 · exact avoids_privateHash_of_ne secret target _
     (tagged_ne_search (hasTag_privatePair ..) ht h4 h12)
 · intro _; exact avoids_pure _ _ _

@[aesop safe apply] theorem avoids_privateMac (region : Region) :
 Avoids secret target (privateMac region) := by
 have hk (i : Nat) : Avoids secret target (privateHash (.inl (header 14 0 0 0 i))) :=
   avoids_privateHash_of_ne secret target _
     (tagged_ne_search (hasTag_privatePair secret 14 0 0 0 i) ht (by decide) (by decide))
 unfold privateMac privateMacKey
 simp only [bind_assoc,pure_bind]
 exact avoids_bind (hk 0) fun _ => avoids_bind (hk 1) fun _ => avoids_pure _ _ _

@[aesop safe apply] theorem avoids_privateNonce (message : Message) :
 Avoids secret target (privateNonce message) := by
 unfold privateNonce
 apply avoids_bind
 · exact avoids_privateHash_of_ne secret target _
     (tagged_ne_search (hasTag_privateNonce ..) ht (by decide) (by decide))
 · intro _; exact avoids_pure _ _ _

@[aesop safe apply] theorem avoids_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 Avoids secret target (chain lay tree leaf i start count value) := by
 unfold chain
 apply avoids_foldlM
 intro value step
 apply avoids_shortHash_of_ne
 apply tagged_ne_search (tag := 1) _ ht (by decide) (by decide)
 unfold chainInput
 simpa only [List.append_assoc] using
   (hasTag_padded zero16 (zero16 ++ bytesLE 16 value) (by simp [zero16]) 1 lay.val tree (step+256*i) leaf)

@[aesop safe apply] theorem avoids_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
 Avoids secret target (leafHash lay tree leaf ends) := by
 unfold leafHash
 apply avoids_shortHash_of_ne
 exact tagged_ne_search (hasTag_padded _ _ (bytesLE_length ..) 2 lay.val tree 0 leaf) ht (by decide) (by decide)

@[aesop safe apply] theorem avoids_nodeHash (tag lay tree heap : Nat) (left right : Digest)
 (h4 : tag%256 ≠ 4) (h12 : tag%256 ≠ 12) :
 Avoids secret target (nodeHash tag lay tree heap left right) := by
 unfold nodeHash
 apply avoids_shortHash_of_ne
 apply tagged_ne_search (tag := tag) _ ht h4 h12
 simpa only [List.append_assoc] using
   (hasTag_padded (bytesLE 16 left) (zero16 ++ bytesLE 16 right) (bytesLE_length ..) tag lay tree 0 heap)

@[aesop safe apply] theorem avoids_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
 (signatureOnly : Bool) : Avoids secret target (buildLeaf lay tree leaf digits signatureOnly) := by
 unfold buildLeaf; avoids_search

@[aesop safe apply] theorem avoids_buildLevel (tag lay tree h level : Nat) (nodes : List Digest)
 (h4 : tag%256 ≠ 4) (h12 : tag%256 ≠ 12) :
 Avoids secret target (buildLevel tag lay tree h level nodes) := by unfold buildLevel; avoids_search

@[aesop safe apply] theorem avoids_buildLevels (tag lay tree h : Nat) (leaves : List Digest)
 (h4 : tag%256 ≠ 4) (h12 : tag%256 ≠ 12) :
 Avoids secret target (buildLevels tag lay tree h leaves) := by unfold buildLevels; avoids_search

@[aesop safe apply] theorem avoids_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
 Avoids secret target (buildTree lay tree selected digits) := by unfold buildTree; avoids_search

@[aesop safe apply] theorem avoids_ftsLeaf (index coord leaf : Nat) (value : Digest) :
 Avoids secret target (ftsLeaf index coord leaf value) := by
 unfold ftsLeaf
 apply avoids_shortHash_of_ne
 apply tagged_ne_search (tag := 9) _ ht (by decide) (by decide)
 simpa only [List.append_assoc] using
   (hasTag_padded zero16 (bytesLE 16 value ++ zero16) (by simp [zero16]) 9 coord index 0 leaf)

@[aesop safe apply] theorem avoids_buildFts (index coord : Nat) :
 Avoids secret target (buildFts index coord) := by unfold buildFts; avoids_search

@[aesop safe apply] theorem avoids_signForest (index : Nat) (chosen : List Selection) :
 Avoids secret target (signForest index chosen) := by unfold signForest; avoids_search

@[aesop safe apply] theorem avoids_forestPk (index : Nat) (roots : List Digest) :
 Avoids secret target (forestPk index roots) := by
 unfold forestPk
 apply avoids_shortHash_of_ne
 exact tagged_ne_search (hasTag_padded _ _ (bytesLE_length ..) 11 0 index 0 0) ht (by decide) (by decide)


@[aesop safe apply] theorem avoids_mask (level index : Nat) :
 Avoids secret target (mask level index) := by unfold mask pairedMask; avoids_search
@[aesop safe apply] theorem avoids_keygenPayload : Avoids secret target keygenPayload := by
 unfold keygenPayload maskedLevel pairedMask; avoids_search
@[aesop safe apply] theorem avoids_keygen : Avoids secret target keygen := by
 unfold keygen; avoids_search

end NonSearch


theorem encodingTrial_ne_of_layer (lay other : Layer) (hne : lay ≠ other)
 (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter : Nat)
 (tree' leaf' : Nat) (message' : Digest × BitVec 96 × Digest) (counter' : Nat) :
 encodingTrial lay tree leaf message counter ≠ encodingTrial other tree' leaf' message' counter' := by
 intro he
 have hh := congrArg queryHeader he
 simp only [queryHeader_encoding] at hh
 apply header_ne_of_layer _ (bytesLE_injective hh)
 have h1 : lay.val < 256 := by have := lay.isLt; omega
 have h2 : other.val < 256 := by have := other.isLt; omega
 rw [Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2]
 exact fun h => hne (Fin.ext h)

/-- Counter search at one layer never fills a different layer's search family. -/
theorem avoids_counterSearch (secret : BitVec 256) (lay other : Layer) (hne : lay ≠ other)
 (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter fuel : Nat)
 (tree' leaf' : Nat) (message' : Digest × BitVec 96 × Digest) (counter' : Nat) :
 Avoids secret (encodingTrial other tree' leaf' message' counter')
   (counterSearch lay tree leaf message counter fuel) := by
 induction fuel generalizing counter with
 | zero => exact avoids_pure _ _ _
 | succ fuel ih =>
   unfold counterSearch
   apply avoids_bind
   · apply avoids_shortHash_of_ne
     exact encodingTrial_ne_of_layer lay other hne tree leaf message counter tree' leaf' message' counter'
   · intro answer
     split
     · exact ih _
     · exact avoids_pure _ _ _

@[aesop safe apply] theorem avoids_digest_encoding (secret : BitVec 256) (target : HashInput)
 (ht : HasTag 4 target) (rho : Digest) (message : Message) (counter : BitVec 32) :
 Avoids secret target (digest rho message counter) := by
 unfold digest publicHash
 apply (allQueriesSatisfy_query_iff _ _).mpr
 change pad64 (digestInput rho message counter) ≠ target
 exact tagged_ne (hasTag_padded _ _ (bytesLE_length ..) 12 0 0 0 counter.toNat) ht (by decide)

theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : HasTag 4 target)
 (rho : Digest) (message : Message) (counter fuel : Nat) :
 Avoids secret target (digestSearch rho message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold digestSearch; avoids_search
 | succ fuel ih => unfold digestSearch; avoids_search

/-- All search freshness follows from the exact cache-entry preservation theorem;
this quantifies over every possible oracle answer and every starting cache. -/
theorem preserves_allSearches {α : Type} (secret : BitVec 256) (program : M α)
 (h : ∀ target,HasTag 4 target ∨ HasTag 12 target → Avoids secret target program)
 (cache : RCache) (hc : Budgets.AllSearchesFresh cache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : Budgets.AllSearchesFresh result.2 := by
 constructor
 · intro rho message c hlt
   rw [preserves secret _ program (h _ (Or.inr (hasTag_digest ..))) cache result hr]
   exact hc.1 rho message c hlt
 · intro lay hl tree leaf message c hlt
   rw [preserves secret _ program (h _ (Or.inl (hasTag_encoding ..))) cache result hr]
   exact hc.2 lay hl tree leaf message c hlt

theorem preserves_encodingBelow {α : Type} (secret : BitVec 256) (program : M α)
 (h : ∀ target,HasTag 4 target → Avoids secret target program)
 (n : Nat) (cache : RCache) (hc : Budgets.EncodingFreshBelow n cache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) : Budgets.EncodingFreshBelow n result.2 := by
 intro lay hl tree leaf message c hlt
 rw [preserves secret _ program (h _ (hasTag_encoding ..)) cache result hr]
 exact hc lay hl tree leaf message c hlt

/-- The seven source-stage freshness obligations used by the exponential-moment
composition are discharged by query separation, rather than assumed for caches. -/
theorem sourceFreshness (secret : BitVec 256) : Budgets.SourceFreshness secret where
 counter := by
   intro lay tree leaf message cache hc result hr other ho tree' leaf' message' c hlt
   have hne : lay ≠ other := by intro he; subst other; omega
   rw [preserves secret _ _ (avoids_counterSearch secret lay other hne tree leaf message 0 counterLimit
     tree' leaf' message' c) cache result hr]
   exact hc other (by omega) tree' leaf' message' c hlt
 tree := by
   intro lay tree leaf digits cache hc result hr
   exact preserves_encodingBelow secret _
     (fun target ht => avoids_buildTree secret target (Or.inl ht) lay tree leaf digits)
     lay.val cache hc result hr
 mac := by
   intro region cache hc result hr
   exact preserves_allSearches secret _
     (fun target ht => avoids_privateMac secret target ht region) cache hc result hr
 nonce := by
   intro message cache hc result hr
   exact preserves_allSearches secret _
     (fun target ht => avoids_privateNonce secret target ht message) cache hc result hr
 digest := by
   intro rho message cache hc result hr
   exact preserves_encodingBelow secret _
     (fun target ht => avoids_digestSearch_encoding secret target ht rho message 0 attemptLimit)
     4 cache hc.2 result hr
 forest := by
   intro index chosen cache hc result hr
   exact preserves_encodingBelow secret _
     (fun target ht => avoids_signForest secret target (Or.inl ht) index chosen)
     4 cache hc result hr
 forestPk := by
   intro index roots cache hc result hr
   exact preserves_encodingBelow secret _
     (fun target ht => avoids_forestPk secret target (Or.inl ht) index roots)
     4 cache hc result hr

theorem keygen_preserves_fresh (secret : BitVec 256) (cache : RCache)
 (hc : Budgets.AllSearchesFresh cache) (result : (Digest × Cache) × RCache)
 (hr : result ∈ support (roRun secret keygen cache)) : Budgets.AllSearchesFresh result.2 :=
 preserves_allSearches secret keygen (fun target ht => avoids_keygen secret target ht) cache hc result hr

theorem keygen_fresh_from_empty (secret : BitVec 256) (result : (Digest × Cache) × RCache)
 (hr : result ∈ support (roRun secret keygen ∅)) : Budgets.AllSearchesFresh result.2 :=
 keygen_preserves_fresh secret ∅ Budgets.allSearchesFresh_empty result hr

end SigGolfCandidate.T3.Freshness

end

/-! Authored module: BudgetClosure. -/
section
/-! Actual source compression budgets. The signing moment is proved after the
same source key generation in the same lazy random oracle, and then averaged
over a uniformly sampled message. Machine refinement is a separate obligation. -/
namespace SigGolfCandidate.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Budgets Cost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  V_sign_le_two_of_freshness secret (Freshness.sourceFreshness secret) cache message rcache hc

theorem realized_sign_exponential_budget (secret : BitVec 256) (cache : Cache)
    (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal)^((result.2 : ℝ)/131072)) ≤ 2 :=
  realized_sign_exponential_budget_of_freshness secret (Freshness.sourceFreshness secret)
    cache message rcache hc

/-- Count only the signing phase, while retaining the key generation's random
oracle state. The cache here is the one actually returned by source keygen. -/
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)

theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message)=(do
      let keys ← realize secret keygen
      World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount,realize_bind]
  congr 1
  funext keys
  exact realize_count secret _

/-- Source signing meets its exponential compression budget after honest key
generation, for every fixed secret and every fixed message. -/
theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2 : ENNReal)^((result.1.2 : ℝ)/131072)) ≤ 2 := by
  rw [honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two secret keys.1.2 message keys.2
    (Freshness.keygen_fresh_from_empty secret keys hkeys)
  simpa only [V,signingZ_pow] using h

theorem realized_honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue ((simulateQ SphincsSecurity.romImpl (do
      let keys ← realize secret keygen
      World.countBlocks (realize secret (sign keys.2 message)))).run' ∅)
      (fun result => (2 : ENNReal)^((result.2 : ℝ)/131072)) ≤ 2 := by
  rw [← honestSignCount_realize secret message,StateT.run'_eq,expectedValue_map]
  exact honest_sign_exponential_budget secret message

/-- The public budget statement averages the message; the pointwise bound is
stronger and gives this average directly. -/
theorem uniform_message_sign_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestSignCount message))).run' ∅)
      (fun result => (2 : ENNReal)^((result.2 : ℝ)/131072)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq,expectedValue_map]
  exact honest_sign_exponential_budget secret message

end SigGolfCandidate.T3.BudgetClosure

end

/-! Authored module: SourceReplay. -/
section
namespace SigGolfCandidate.T3.SourceReplay
open OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The source interface includes a uniform-query branch, but the four source programs
never use it. Only public hashes and keyed derivation coordinates occur. -/
def isHash : Spec.Domain → Prop
 | .inl (.inl _) => False
 | _ => True

abbrev HashOnly {α : Type} (program : M α) : Prop := AllQueriesSatisfy program isHash

theorem hashOnly_pure {α : Type} (value : α) : HashOnly (pure value) :=
 allQueriesSatisfy_pure _ _

theorem hashOnly_bind {α β : Type} {program : M α} {next : α → M β}
 (hp : HashOnly program) (hn : ∀ a, HashOnly (next a)) : HashOnly (program >>= next) :=
 allQueriesSatisfy_bind hp hn

theorem hashOnly_map {α β : Type} (f : α → β) {program : M α}
 (hp : HashOnly program) : HashOnly (f <$> program) := by
 rw [map_eq_bind_pure_comp]
 exact hashOnly_bind hp fun _ => hashOnly_pure _

theorem hashOnly_mapM {α β : Type} (items : List α) (f : α → M β)
 (h : ∀ a, HashOnly (f a)) : HashOnly (items.mapM f) := by
 induction items with
 | nil => exact hashOnly_pure []
 | cons a items ih =>
   rw [List.mapM_cons]
   exact hashOnly_bind (h a) fun _ => hashOnly_bind ih fun _ => hashOnly_pure _

theorem hashOnly_foldlM {α β : Type} (items : List β) (f : α → β → M α)
 (h : ∀ a b, HashOnly (f a b)) (initial : α) : HashOnly (items.foldlM f initial) := by
 induction items generalizing initial with
 | nil => exact hashOnly_pure _
 | cons a items ih =>
   rw [List.foldlM_cons]
   exact hashOnly_bind (h initial a) ih

@[simp] theorem hashOnly_publicHash (input : HashInput) : HashOnly (publicHash input) := by
 exact (allQueriesSatisfy_query_iff _ _).mpr trivial
@[simp] theorem hashOnly_privateHash (coordinate : Coordinate) : HashOnly (privateHash coordinate) := by
 exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Deterministic source answers from one fixed public random-oracle table. Uniform
answers are arbitrary zero values and cannot affect a HashOnly computation. -/
def fixedAnswers (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id) :
 Correctness.Answers
 | .inl (.inl n) => (⟨0,Nat.zero_lt_succ n⟩ : Fin (n+1))
 | .inl (.inr input) => hash input
 | .inr coordinate => hash (privateInput secret coordinate)

theorem fixed_replay {α : Type} (secret : BitVec 256)
 (hash : QueryImpl SphincsSecurity.HashSpec Id) (program : M α) (hp : HashOnly program) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret program) =
   pure (evalWithAnswerFn (fixedAnswers secret hash) program) := by
 induction program using OracleComp.inductionOn with
 | pure a => simp [realize]
 | query_bind q next ih =>
   change AllQueriesSatisfy _ isHash at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rcases q with (n|input)|coordinate
   · exact False.elim hp.1
   · simp only [realize,simulateQ_bind,simulateQ_spec_query,realHandler]
     simp only [simulateQ_bind,simulateQ_spec_query,unifFwdAnswerImpl,QueryImpl.add_apply_inr,
       QueryImpl.liftTarget_apply,evalWithAnswerFn_bind,evalWithAnswerFn,fixedAnswers,
       pure_bind]
     exact ih _ (hp.2 _)
   · simp only [realize,simulateQ_bind,simulateQ_spec_query,realHandler]
     simp only [simulateQ_bind,simulateQ_spec_query,unifFwdAnswerImpl,QueryImpl.add_apply_inr,
       QueryImpl.liftTarget_apply,evalWithAnswerFn_bind,evalWithAnswerFn,fixedAnswers,
       pure_bind]
     exact ih _ (hp.2 _)


attribute [aesop safe apply] hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM hashOnly_foldlM
  hashOnly_publicHash hashOnly_privateHash

macro "hashes" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

@[aesop safe apply] theorem hashOnly_shortHash (input : HashInput) : HashOnly (shortHash input) := by
 unfold shortHash; hashes
@[aesop safe apply] theorem hashOnly_privatePair (tag lay tree position index : Nat) :
 HashOnly (privatePair tag lay tree position index) := by
 unfold privatePair; hashes
@[aesop safe apply] theorem hashOnly_privateMac (region : Region) : HashOnly (privateMac region) := by
 exact Security.SourceQueries.privateMac_allowed isHash (fun _ => trivial) region
@[aesop safe apply] theorem hashOnly_privateNonce (message : Message) : HashOnly (privateNonce message) := by
 unfold privateNonce; hashes
@[aesop safe apply] theorem hashOnly_mask (level index : Nat) : HashOnly (mask level index) := by
 unfold mask pairedMask; hashes
@[aesop safe apply] theorem hashOnly_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
 HashOnly (chain lay tree leaf i start count value) := by
 unfold chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
 HashOnly (leafHash lay tree leaf ends) := by unfold leafHash; hashes
@[aesop safe apply] theorem hashOnly_nodeHash (tag lay tree heap : Nat) (left right : Digest) :
 HashOnly (nodeHash tag lay tree heap left right) := by unfold nodeHash; hashes
@[aesop safe apply] theorem hashOnly_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat)
 (signatureOnly : Bool) : HashOnly (buildLeaf lay tree leaf digits signatureOnly) := by
 unfold buildLeaf; hashes
@[aesop safe apply] theorem hashOnly_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) :
 HashOnly (buildLevel tag lay tree h level nodes) := by unfold buildLevel; hashes
@[aesop safe apply] theorem hashOnly_buildLevels (tag lay tree h : Nat) (leaves : List Digest) :
 HashOnly (buildLevels tag lay tree h leaves) := by unfold buildLevels; hashes
@[aesop safe apply] theorem hashOnly_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
 HashOnly (buildTree lay tree selected digits) := by unfold buildTree; hashes
@[aesop safe apply] theorem hashOnly_keygenPayload : HashOnly keygenPayload := by
 unfold keygenPayload maskedLevel pairedMask; hashes
@[aesop safe apply] theorem hashOnly_keygen : HashOnly keygen := by
 unfold keygen; hashes
@[aesop safe apply] theorem hashOnly_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest)
 (counter fuel : Nat) : HashOnly (counterSearch lay tree leaf message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold counterSearch; hashes
 | succ fuel ih => unfold counterSearch; hashes
@[aesop safe apply] theorem hashOnly_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
 HashOnly (digest rho message counter) := by unfold digest; hashes
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
 HashOnly (digestSearch rho message counter fuel) := by
 induction fuel generalizing counter with
 | zero => unfold digestSearch; hashes
 | succ fuel ih => unfold digestSearch; hashes
@[aesop safe apply] theorem hashOnly_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
 HashOnly (ftsLeaf index coord leaf secret) := by unfold ftsLeaf; hashes
@[aesop safe apply] theorem hashOnly_buildFts (index coord : Nat) : HashOnly (buildFts index coord) := by
 unfold buildFts; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (roots : List Digest) :
 HashOnly (forestPk index roots) := by unfold forestPk; hashes
@[aesop safe apply] theorem hashOnly_topPath (cache : Cache) (leaf : Nat) : HashOnly (topPath cache leaf) := by
 unfold topPath; hashes
@[aesop safe apply] theorem hashOnly_signTop (cache : Cache) (leaf : Nat) (digits : List Nat) :
 HashOnly (signTop cache leaf digits) := by unfold signTop; hashes
@[aesop safe apply] theorem hashOnly_signLayers (cache : Cache) (index n : Nat) (message : Digest × BitVec 96 × Digest) :
 HashOnly (signLayers cache index n message) := by
 induction n generalizing message with
 | zero => unfold signLayers; hashes
 | succ n ih => unfold signLayers; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
 HashOnly (signPayload cache message) := by unfold signPayload; hashes
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
 HashOnly (sign cache message) := by unfold sign; hashes
@[aesop safe apply] theorem hashOnly_recoverChild (index coord : Nat) (leaves : List Nat)
 (values : List Digest) (proof : Fin 115 → Digest) (level node used : Nat) :
 HashOnly (recoverChild index coord leaves values proof level node used) := by
 induction level generalizing node used with
 | zero => unfold recoverChild; hashes
 | succ level ih => unfold recoverChild; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (chosen : List Selection) :
 HashOnly (recoverFts sig index chosen) := by unfold recoverFts; hashes
@[aesop safe apply] theorem hashOnly_recoverLayer (sig : Signature) (index : Nat) (lay : Layer)
 (digits : List Nat) : HashOnly (recoverLayer sig index lay digits) := by unfold recoverLayer; hashes
@[aesop safe apply] theorem hashOnly_recoverPair (sig : Signature) (index : Nat) (lay : Layer)
 (digits : List Nat) : HashOnly (recoverPair sig index lay digits) := by unfold recoverPair; hashes
@[aesop safe apply] theorem hashOnly_rootHash (index : Nat) (lay : Layer) (pair : Digest × BitVec 96 × Digest) :
 HashOnly (rootHash index lay pair) := by unfold rootHash; hashes
@[aesop safe apply] theorem hashOnly_recoverNext (sig : Signature) (index n : Nat) (lay : Layer)
 (digits : List Nat) : HashOnly (recoverNext sig index n lay digits) := by unfold recoverNext; split <;> hashes
@[aesop safe apply] theorem hashOnly_expandNext (sig : Signature) (index n : Nat) (lay : Layer)
 (digits : List Nat) : HashOnly (expandNext sig index n lay digits) := by unfold expandNext; hashes
@[aesop safe apply] theorem hashOnly_expandLayers (sig : Signature) (index n : Nat) (value : Digest × BitVec 96 × Digest) :
 HashOnly (expandLayers sig index n value) := by
 induction n generalizing value with
 | zero => unfold expandLayers; hashes
 | succ n ih => unfold expandLayers; hashes
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
 HashOnly (expand message pk sig) := by unfold expand; hashes
@[aesop safe apply] theorem hashOnly_verifyLayers (w : Witness) (index n : Nat) (root : Digest × BitVec 96 × Digest) :
 HashOnly (verifyLayers w index n root) := by
 induction n generalizing root with
 | zero => unfold verifyLayers; hashes
 | succ n ih => unfold verifyLayers; hashes
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
 HashOnly (verify message pk w) := by unfold verify; hashes

theorem keygen_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret keygen) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) keygen) :=
 fixed_replay secret hash keygen hashOnly_keygen

theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (cache : Cache) (message : Message) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (sign cache message)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (sign cache message)) :=
 fixed_replay secret hash (sign cache message) (hashOnly_sign cache message)

theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (message : Message) (pk : Digest) (sig : Signature) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (expand message pk sig)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (expand message pk sig)) :=
 fixed_replay secret hash (expand message pk sig) (hashOnly_expand message pk sig)

theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
 (message : Message) (pk : Digest) (w : Witness) :
 simulateQ (unifFwdAnswerImpl hash) (realize secret (verify message pk w)) =
 pure (evalWithAnswerFn (fixedAnswers secret hash) (verify message pk w)) :=
 fixed_replay secret hash (verify message pk w) (hashOnly_verify message pk w)

end SigGolfCandidate.T3.SourceReplay

end

/-! Authored module: NonceSampling. -/
section
/-! Joint finite presampling of all private nonces and all public searches.
This is an exact ROM identity, without a security or computational assumption. -/
namespace SigGolfCandidate.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey

@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler

def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))

theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))

theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]

theorem searchQuery_length (key : SearchKey) : (searchQuery key).length = 64 := by
  cases key with
  | inl key => exact Sampling.encodingTrial_length _ _ _ _ _
  | inr key => exact Sampling.digestTrial_length _ _ _

theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega

def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery

theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)

noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)

theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)

theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)

/-- The combined uniform function is exactly a pair of independent uniform functions. -/
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm


/-- Joint finite precomputation preserves the law of every source program. -/
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1

/-- All private nonce answers and all public search answers can be sampled
independently before running the actual source against their shared cache. -/
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl

#print axioms presample_source
end SigGolfCandidate.T3.NonceSampling

end

/-! Authored module: Completeness. -/
section
namespace SigGolfCandidate.T3.Completeness
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Honest source execution, including both witness expansion and verification. -/
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness

/-- Every message is run against the same oracle, matching the quantifier in
the contract. This finite mathematical program is not meant to be executed. -/
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true

theorem honestProgram_true (answers : Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceed answers) :
    evalWithAnswerFn answers (honestProgram message)=true := by
  obtain ⟨sig,witness,hs,he,hv⟩ := Correctness.honest_signing_complete_of_searches answers hgood message
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]

theorem honestProgram_true_for (answers : Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceedFor answers message) :
    evalWithAnswerFn answers (honestProgram message)=true := by
  obtain ⟨sig,witness,hs,he,hv⟩ := Correctness.signing_complete_for_of_searches answers
    (evalWithAnswerFn answers keygen) (Correctness.keygen_correct answers) message hgood
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]

theorem hashOnly_honestProgram (message : Message) : SourceReplay.HashOnly (honestProgram message) := by
  unfold honestProgram
  apply SourceReplay.hashOnly_bind SourceReplay.hashOnly_keygen
  intro keys
  apply SourceReplay.hashOnly_bind (SourceReplay.hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact SourceReplay.hashOnly_pure false
  | some sig =>
    apply SourceReplay.hashOnly_bind (SourceReplay.hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact SourceReplay.hashOnly_pure false
    | some witness => exact SourceReplay.hashOnly_verify message keys.1 witness

theorem hashOnly_everyMessageProgram : SourceReplay.HashOnly everyMessageProgram := by
  apply SourceReplay.hashOnly_foldlM
  intro accepted message
  exact SourceReplay.hashOnly_bind (hashOnly_honestProgram message) fun _ =>
    SourceReplay.hashOnly_pure _

theorem everyMessageProgram_true (answers : Correctness.Answers)
    (hall : ∀ message,evalWithAnswerFn answers (honestProgram message)=true) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  have hf : ∀ messages : List Message,∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted)=accepted := by
    intro messages
    induction messages with
    | nil => intro accepted;rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons,evalWithAnswerFn_bind,evalWithAnswerFn_pure,hall,Bool.and_true]
      exact ih accepted
  exact hf _ true

theorem everyMessageProgram_true_of_complete (answers : Correctness.Answers)
    (hcomplete : Correctness.SigningComplete answers (evalWithAnswerFn answers keygen)) :
    evalWithAnswerFn answers everyMessageProgram=true := by
  apply everyMessageProgram_true
  intro message
  obtain ⟨sig,witness,hs,he,hv⟩ := hcomplete message
  simp only [honestProgram,evalWithAnswerFn_bind,hs,he,hv]

noncomputable local instance : SampleableType (QuerySpace.SearchKey → HashOutput) :=
  Presampling.tableSampler

/-- Exact finite presampling transfers any proof that good tables rule out
failure back to the original source ROM execution. -/
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (QuerySpace.SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs,good outputs →
      Pr[fun value => value=false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)]=0) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (QuerySpace.SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)

/-- A reached source value has a consistent total hash table extending every
presampled search answer. Uniform queries, if present, remain probabilistic. -/
theorem failure_zero_of_fixed_replay (secret : BitVec 256) (program : M Bool)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      cache.AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program)=(pure true : ProbComp Bool)) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        cache]=0 := by
  rw [probEvent_eq_zero_iff]
  intro value hv
  rw [StateT.run'_eq,support_map] at hv
  obtain ⟨result,hr,he⟩ := hv
  have hx := (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
    (realize secret program) cache result.1).mpr ⟨result.2,hr⟩
  obtain ⟨f,hf,hvalue⟩ := hx
  rw [hgood f hf,mem_support_pure_iff] at hvalue
  simp only [← he,hvalue,Bool.true_eq_false,not_false_eq_true]

theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : QuerySpace.SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program)=(pure true : ProbComp Bool)) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)]=0 :=
  failure_zero_of_fixed_replay secret program _ hgood

theorem honest_prepared_failure_zero (secret : BitVec 256) (message : Message)
    (outputs : QuerySpace.SearchKey → HashOutput) (hgood : Budgets.tableGoodFor message outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run'
        (Presampling.preparedCache outputs)]=0 := by
  refine prepared_failure_zero secret (honestProgram message) outputs ?_
  intro hash hagree
  have hsrc : Correctness.SearchesSucceedFor (SourceReplay.fixedAnswers secret hash) message := by
    apply Budgets.tableGoodFor_searchesSucceedFor message outputs _ hgood
    intro key
    change hash (QuerySpace.searchQuery key)=outputs key
    exact hagree (Presampling.preparedCache_apply outputs key)
  exact (SourceReplay.fixed_replay secret hash _ (hashOnly_honestProgram message)).trans
    (congrArg (pure : Bool → ProbComp Bool) (honestProgram_true_for _ message hsrc))

/-- Source completeness for every fixed secret and fixed message. Its only
numerical input here is the fresh digest acceptance rate. No adaptive
independence assumption is required for the source's chosen nonce or roots. -/
theorem honest_failure_small_of_acceptance (secret : BitVec 256) (message : Message)
    (p : ℝ) (hp : 1/3300 ≤ p) (hp1 : p≤1)
    (haccept : Pr[fun answer => (Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)]=ENNReal.ofReal p) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1/(2 : ENNReal)^321 := by
  exact (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans
    (Budgets.tableGoodFor_failure_small_of_acceptance message p hp hp1 haccept)

/-- Unconditional honest source completeness at the candidate's actual digest
and encoding parameters, for every fixed secret and fixed message. -/
theorem honest_failure_small (secret : BitVec 256) (message : Message) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1/(2 : ENNReal)^321 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_small message)

/-- A weaker numerical corollary for a fixed message. This alone does not
establish the contract's common-oracle, all-message completeness statement. -/
theorem honest_failure_128 (secret : BitVec 256) (message : Message) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1/(2 : ENNReal)^128 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_128 message)

noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler

theorem everyMessage_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : Budgets.tableGoodForNonces nonces outputs) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run'
        (NonceSampling.preparedCache secret nonces outputs)]=0 := by
  refine failure_zero_of_fixed_replay secret everyMessageProgram _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (SourceReplay.fixedAnswers secret hash) := by
    intro key
    change hash (QuerySpace.searchQuery key)=outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : Budgets.NonceAgreement nonces (SourceReplay.fixedAnswers secret hash) := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := Budgets.tableGoodForNonces_signingComplete nonces outputs
    (SourceReplay.fixedAnswers secret hash) hgood hsearch hnonce
  exact (SourceReplay.fixed_replay secret hash _ hashOnly_everyMessageProgram).trans
    (congrArg (pure : Bool → ProbComp Bool) (everyMessageProgram_true_of_complete _ hcomplete))

/-- One shared random oracle supports all 2^256 messages except with probability
at most 2^-193. Private nonces are sampled independently of public search rows;
the failure event is uniform over every possible resulting nonce table. -/
theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value=false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1/(2 : ENNReal)^193 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value=false))
    (NonceSampling.presample_source secret everyMessageProgram)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent (p := fun outputs => ¬Budgets.tableGoodForNonces nonces outputs)
    (fun outputs _ hgood => everyMessage_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans
    (Budgets.tableGoodForNonces_failure_small nonces)

/-- Source-level form of the common-oracle completeness requirement. Machine
refinement is still required to transfer this to `SigGolf.Submission.Completeness`. -/
theorem source_completeness (secret : BitVec 256) :
    1-1/(2 : ENNReal)^128 ≤
      Pr[= true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  have hsmall : 1/(2 : ENNReal)^193 ≤ 1/(2 : ENNReal)^128 := by norm_num
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero,tsub_zero]
  exact tsub_le_tsub_left (hf.trans hsmall) 1

end SigGolfCandidate.T3.Completeness

end

/-! Authored module: CountedReplay. -/
section
/-! Count instrumentation adds no oracle queries. Every supported hash-only source
run, including its counted values, can be replayed against one total hash table
agreeing with the initial random-oracle cache. -/
namespace SigGolfCandidate.T3.CountedReplay
open OracleComp OracleSpec SourceReplay Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A counter is pure instrumentation; the source computation issues exactly the
same kinds of oracle queries after instrumentation. -/
theorem hashOnly_countWith {α : Type} (weight : Cost.Query → Nat) (program : M α)
 (hp : HashOnly program) : HashOnly (Cost.countWith weight program) := by
 induction program using OracleComp.inductionOn with
 | pure value =>
   rw [Cost.countWith_pure]
   exact hashOnly_pure _
 | query_bind q next ih =>
   change AllQueriesSatisfy _ isHash at hp
   rw [allQueriesSatisfy_query_bind_iff] at hp
   rw [Cost.countWith_bind,Cost.countWith_query]
   apply hashOnly_bind
   · apply hashOnly_map
     exact (allQueriesSatisfy_query_iff _ _).mpr hp.1
   · intro pair
     exact hashOnly_map _ (ih pair.1 (hp.2 pair.1))

theorem hashOnly_countBlocks {α : Type} (program : M α) (hp : HashOnly program) :
 HashOnly (Cost.countBlocks program) := hashOnly_countWith Cost.weight program hp

/-- This is one table for the entire program, so sequential phases and their
counters replay consistently in the same oracle. It is not a fresh-table claim. -/
theorem support_replay {α : Type} (secret : BitVec 256) (program : M α) (hp : HashOnly program)
 (cache : RCache) (result : α × RCache)
 (hr : result ∈ support (roRun secret program cache)) :
 ∃ hash : QueryImpl SphincsSecurity.HashSpec Id,
   cache.AgreesWithFn hash ∧ result.1 = evalWithAnswerFn (fixedAnswers secret hash) program := by
 have hsupport : ∃ cache' : RCache,
     (result.1,cache') ∈ support ((simulateQ
       (unifFwdImpl SphincsSecurity.HashSpec + SphincsSecurity.HashSpec.randomOracle)
       (realize secret program)).run cache) := by
   exact ⟨result.2,hr⟩
 obtain ⟨hash,hagree,hreplay⟩ :=
   (exists_agreesWithFn_mem_support_simulateQ_unifFwdAnswerImpl_iff
     (realize secret program) cache result.1).mpr hsupport
 rw [fixed_replay secret hash program hp,support_pure,Set.mem_singleton_iff] at hreplay
 exact ⟨hash,hagree,hreplay⟩

theorem counted_support_replay {α : Type} (program : M α) (hp : HashOnly program)
 (secret : BitVec 256) (cache : RCache) (result : (α × Nat) × RCache)
 (hr : result ∈ support (roRun secret (Cost.countBlocks program) cache)) :
 ∃ hash : QueryImpl SphincsSecurity.HashSpec Id,
   cache.AgreesWithFn hash ∧
   result.1 = evalWithAnswerFn (fixedAnswers secret hash) (Cost.countBlocks program) :=
 support_replay secret (Cost.countBlocks program) (hashOnly_countBlocks program hp) cache result hr

end SigGolfCandidate.T3.CountedReplay

end

/-! Authored module: SearchCost. -/
section
/-! Deterministic source compression accounting under a single fixed oracle. -/


end

/-! Authored module: ExpansionBudget. -/
section
/-! Compression cost coupling between a successful source signer and its
counter-recovering expander, under the same fixed answer function. -/
namespace SigGolfCandidate.T3.ExpansionBudget
open OracleComp OracleSpec Cost Correctness SearchCost
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Expansion and signing repeat the identical layer search. -/
theorem expandLayers_cost_step (answers : Answers) (sig : Signature) (index n : Nat)
    (value : Digest × BitVec 96 × Digest) (counter : BitVec 32) (digits : List Nat)
    (hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
      (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit)=some (counter,digits)) :
    cost answers (expandLayers sig index (n+1) value) =
      cost answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) +
      cost answers (expandNext sig index n (Fin.ofNat 4 n) digits) +
      cost answers (expandLayers sig index n
        (evalWithAnswerFn answers (expandNext sig index n (Fin.ofNat 4 n) digits))) := by
  simp only [expandLayers, cost_bind, hs]
  cases hx : evalWithAnswerFn answers (expandLayers sig index n
      (evalWithAnswerFn answers (expandNext sig index n (Fin.ofNat 4 n) digits))) <;>
    simp only [cost_pure, Nat.add_zero, Nat.add_assoc]

theorem signLayers_cost_step (answers : Answers) (cache : Cache) (index n : Nat)
    (value : Digest × BitVec 96 × Digest) (counter : BitVec 32) (digits : List Nat)
    (hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
      (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit)=some (counter,digits)) :
    cost answers (signLayers cache index (n+1) value) =
      cost answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) +
      if n=0 then cost answers (signTop cache (route index (Fin.ofNat 4 n)).1 digits)
      else cost answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 digits) +
        cost answers (signLayers cache index n
          ((((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
            (route index (Fin.ofNat 4 n)).1 digits)).1.getD (height (Fin.ofNat 4 n) - 1) []).getD 0 0, 0, ((evalWithAnswerFn answers (buildTree (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
            (route index (Fin.ofNat 4 n)).1 digits)).1.getD (height (Fin.ofNat 4 n) - 1) []).getD 1 0))) := by
  simp only [signLayers, cost_bind, hs]
  split
  · simp only [cost_bind, cost_pure, Nat.add_zero]
  · simp only [cost_bind]
    split <;> simp only [cost_pure, Nat.add_zero]

/-- The source's reconstruction work is the only extra charge in each layer;
all search calls cancel against the calls already made by the signer. -/
theorem expandLayers_cost_le (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region=cacheRegion (maskedTop answers)) (hindex : index < 2^31) :
    ∀ n,n ≤ 4 → ∀ value pieces,
      evalWithAnswerFn answers (signLayers cache index n value)=some pieces →
      ∀ sig : Signature,PiecesAgree sig pieces n →
        cost answers (expandLayers sig index n value) ≤
          cost answers (signLayers cache index n value) + recoveryLayersCost n := by
  intro n
  induction n with
  | zero => intro hn value pieces he sig hagree; simp only [signLayers,expandLayers,cost_pure,recoveryLayersCost,Nat.add_zero,Nat.le_refl]
  | succ n ih =>
      intro hn value pieces he sig hagree
      have hsource := he
      simp only [signLayers,evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some found =>
          obtain ⟨counter,digits⟩ := found
          have hd := (counterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 value
            counterLimit 0 counter digits (by decide) hs).2.2
          have hvalid := validDigits_decode hd
          have hrec := cost_bound answers
            (bound_expandNext sig index n (Fin.ofNat 4 n) digits hvalid
              (decode_length_sum hd).1 (decode_length_sum hd).2)
          rw [expandLayers_cost_step answers sig index n value counter digits hs,
            signLayers_cost_step answers cache index n value counter digits hs]
          simp only [hs] at he
          by_cases hn0 : n=0
          · subst n
            simp only [ite_true,expandLayers,cost_pure,recoveryLayersCost,Nat.add_zero]
            omega
          · simp only [hn0,ite_false,evalWithAnswerFn_bind,
              eval_buildTree_result answers (Fin.ofNat 4 n) _ _ digits hvalid (route_leaf_bound index _)] at he
            cases hp : evalWithAnswerFn answers (signLayers cache index n
              ((((builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                (height (Fin.ofNat 4 n) - 1) []).getD 0 0, 0, ((builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                (height (Fin.ofNat 4 n) - 1) []).getD 1 0))) with
            | none => simp only [hp,evalWithAnswerFn_pure,reduceCtorEq] at he
            | some previous =>
                simp only [hp,evalWithAnswerFn_pure,Option.some.injEq] at he
                subst pieces
                obtain ⟨hlen,_⟩ := signLayers_expandLayers answers cache index hcache hindex
                  n (by omega) _ previous hp
                change PiecesAgree sig (previous++[honestPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n+1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover := recoverPair_honestPieces answers sig index (Fin.ofNat 4 n) digits hvalid hlayer
                have hprevious := ih (by omega) _ previous hp sig (PiecesAgree.prefix hlen hagree)
                simp only [treeValue] at hrecover
                have hnext : evalWithAnswerFn answers (expandNext sig index n (Fin.ofNat 4 n) digits) =
                    (((builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                      (height (Fin.ofNat 4 n)-1) []).getD 0 0,0,
                     ((builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                      (height (Fin.ofNat 4 n)-1) []).getD 1 0) := by
                  rw [eval_expandNext, eval_recoverNext, if_neg hn0, hrecover]
                rw [hnext]
                simp only [hn0,ite_false,recoveryLayersCost,
                  eval_buildTree_result answers (Fin.ofNat 4 n) _ _ digits hvalid (route_leaf_bound index _)]
                omega


theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput) (root : Digest)
    (hd : evalWithAnswerFn answers (digestSearch sig.rho message 0 attemptLimit)=some (counter,output))
    (hf : evalWithAnswerFn answers (recoverFts sig (output.toNat%2^31) (selections output))=some root) :
    cost answers (expand message pk sig) =
      cost answers (digestSearch sig.rho message 0 attemptLimit) +
      cost answers (recoverFts sig (output.toNat%2^31) (selections output)) +
      cost answers (expandLayers sig (output.toNat%2^31) 4 (root, 0, 0)) := by
  simp only [expand,cost_bind,hd,hf]
  split
  · split <;> simp only [cost_pure,Nat.add_zero,Nat.add_assoc]
  · simp only [cost_pure,Nat.add_zero,Nat.add_assoc]

theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit)=some (counter,output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) +
      cost answers (signForest (output.toNat%2^31) (selections output)) +
      cost answers (forestPk (output.toNat%2^31)
        (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2) +
      cost answers (signLayers cache (output.toNat%2^31) 4
        (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
          (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2),0,0)) := by
  rw [signPayload_eq]
  simp only [cost_bind,hd]
  split <;> simp only [cost_pure,Nat.add_zero,Nat.add_assoc]

/-- Honest expansion repeats the signer's searches and adds at most 643
compressions for forest and hypertree recovery. Other signing work only helps. -/
theorem expand_cost_le_payload_add (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region=cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message)=some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message)+643 := by
  rw [signPayload_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers
    (digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at he
  | some found =>
      obtain ⟨counter,output⟩ := found
      simp only [hd,evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers
        (signLayers cache (output.toNat%2^31) 4
          (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
            (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2),0,0)) with
      | none => simp only [hl,evalWithAnswerFn_pure,reduceCtorEq] at he
      | some pieces =>
          simp only [hl,evalWithAnswerFn_pure,Option.some.injEq] at he
          subst sig
          have hadm := (digestSearch_some answers (evalWithAnswerFn answers (privateNonce message))
            message attemptLimit 0 counter output (by decide) hd).2.2.2
          have hforest := assembled_forest_recovery answers
            (evalWithAnswerFn answers (privateNonce message)) output pieces hadm
          have hroots := congrArg (fun state : List Digest × List Digest × List Digest => state.2.2)
            (eval_signForest answers (output.toNat%2^31) (selections output))
          dsimp only at hroots
          rw [← hroots] at hforest
          have hindex : output.toNat%2^31 < 2^31 := Nat.mod_lt _ (by decide)
          have hlayer := expandLayers_cost_le answers cache (output.toNat%2^31)
            hcache hindex 4 (by decide) _ pieces hl
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))) pieces)
            (fun _ _ => rfl)
          rw [recoveryLayersCost_four] at hlayer
          have hrec := cost_bound answers ((bound_recoverFts
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))) pieces)
            (output.toNat%2^31) (selections output)).mono_k (forestRecoveryCost_le output hadm))
          have hexpand := expand_cost_step answers message pk
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))) pieces)
            counter output
            (evalWithAnswerFn answers (forestPk (output.toNat%2^31)
              (evalWithAnswerFn answers (signForest (output.toNat%2^31) (selections output))).2.2))
            (by simpa only [assembledSignature_rho] using hd) hforest
          rw [hexpand,signPayload_cost_step answers cache message counter output hd]
          simp only [assembledSignature_rho]
          omega

/-- Every source signer first checks the two-key cache MAC. -/
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region)=2 := by
    simp only [cost,privateMac_count,evalWithAnswerFn_map]
  simp only [sign,cost_bind,hmac]
  omega

theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2+cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region)=2 := by
    simp only [cost,privateMac_count,evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [sign,cost_bind,hmac,← hvalid,ne_eq,not_true_eq_false,ite_false]

/-- Pointwise compression coupling under one fixed answer function. Dividing
by the expander budget 2^20 is no larger than dividing signing by 2^17. -/
theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message)=some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8*cost answers (sign (evalWithAnswerFn answers keygen).2 message) := by
  have hk := keygen_correct answers
  rw [sign_honest_cache answers message] at hs
  have h := expand_cost_le_payload_add answers (evalWithAnswerFn answers keygen).2 message sig
    hk.2.1 hs (evalWithAnswerFn answers keygen).1
  have hmin := FullCacheExpansionCost.signPayload_cost_ge answers
    (evalWithAnswerFn answers keygen).2 message sig hs
  rw [sign_cost_honest]
  omega


#print axioms expand_cost_le_eight_sign
end SigGolfCandidate.T3.ExpansionBudget

end

/-! Authored module: ExpansionClosure. -/
section
namespace SigGolfCandidate.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Sampling Cost SearchCost
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def jointCounts {κ σ ω : Type} (initial : M κ) (signer : κ → M (Option σ))
    (expander : κ → σ → M ω) : M (Nat × Nat) := do
  let keys ← initial
  let signed ← countBlocks (signer keys)
  match signed.1 with
  | none => pure (signed.2,0)
  | some sig =>
      let expanded ← countBlocks (expander keys sig)
      pure (signed.2,expanded.2)

/-- Pure accounting for an arbitrary initial phase, signer and expander. -/
theorem eval_joint_cost_le {κ σ ω : Type} (answers : Correctness.Answers)
    (initial : M κ) (signer : κ → M (Option σ)) (expander : κ → σ → M ω)
    (hbound : ∀ sig,
      evalWithAnswerFn answers (signer (evalWithAnswerFn answers initial))=some sig →
      cost answers (expander (evalWithAnswerFn answers initial) sig) ≤
        8*cost answers (signer (evalWithAnswerFn answers initial))) :
    (evalWithAnswerFn answers (jointCounts initial signer expander)).2 ≤
      8*(evalWithAnswerFn answers (jointCounts initial signer expander)).1 := by
  unfold jointCounts
  have hfst := counted_fst answers (signer (evalWithAnswerFn answers initial))
  generalize hk : evalWithAnswerFn answers initial = keys at hfst hbound ⊢
  simp only [evalWithAnswerFn_bind,hk]
  generalize hc : evalWithAnswerFn answers (countBlocks (signer keys)) = signed at hfst ⊢
  rcases signed with ⟨sig,n⟩
  cases sig with
  | none => simp only [evalWithAnswerFn_pure];omega
  | some sig =>
      simp only [evalWithAnswerFn_bind,evalWithAnswerFn_pure]
      have hh := hbound sig hfst.symm
      simpa only [SearchCost.cost,hc] using hh


/-- Retain both phase charges in the shared oracle, with expansion charged only when reached. -/
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)

/-- Continuing with witness expansion does not increase the expectation of
the already recorded signing charge. -/
theorem joint_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal)^((result.1.1 : ℝ)/131072)) ≤ 2 := by
  refine le_trans ?_ (BudgetClosure.honest_sign_exponential_budget secret message)
  simp only [honestJointCounts,jointCounts,BudgetClosure.honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig,signCost⟩,rcache⟩
  cases sig with
  | none => simp only [roRun_pure,expectedValue_pure,le_refl]
  | some sig =>
    simp only [roRun_bind,expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [roRun_pure,expectedValue_pure,le_refl]

theorem hashOnly_honestJointCounts (message : Message) : SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply SourceReplay.hashOnly_bind SourceReplay.hashOnly_keygen
  intro keys
  apply SourceReplay.hashOnly_bind (CountedReplay.hashOnly_countBlocks _ (SourceReplay.hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact SourceReplay.hashOnly_pure _
  | some sig =>
    apply SourceReplay.hashOnly_bind (CountedReplay.hashOnly_countBlocks _ (SourceReplay.hashOnly_expand message keys.1 sig))
    intro expanded
    exact SourceReplay.hashOnly_pure _

theorem joint_cost_le (answers : Correctness.Answers) (message : Message) :
    (evalWithAnswerFn answers (honestJointCounts message)).2 ≤
      8 * (evalWithAnswerFn answers (honestJointCounts message)).1 := by
  exact eval_joint_cost_le (κ := Digest × Cache) (σ := Signature) (ω := Option Witness) answers keygen
    (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
    (ExpansionBudget.expand_cost_le_eight_sign answers message)

/-- Expansion is charged only if signing succeeded; its charge is bounded on
every supported execution using the same fixed table for all three phases. -/
theorem support_joint_cost_le (secret : BitVec 256) (message : Message)
    (result : (Nat × Nat) × RCache)
    (hr : result ∈ support (roRun secret (honestJointCounts message) ∅)) :
    result.1.2 ≤ 8 * result.1.1 := by
  obtain ⟨hash,_,heval⟩ := CountedReplay.support_replay secret _
    (hashOnly_honestJointCounts message) ∅ result hr
  rw [heval]
  exact joint_cost_le _ message

/-- The expander meets its exponential compression budget after the actual
key generator and signer in their shared random oracle. -/
theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal)^((result.1.2 : ℝ)/1048576)) ≤ 2 := by
  refine le_trans ?_ (joint_sign_exponential_budget secret message)
  apply expectedValue_mono_of_support
  intro result hr
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (result.1.2 : ℝ) ≤ 8 * (result.1.1 : ℝ) := by
    exact_mod_cast support_joint_cost_le secret message result hr
  linarith

theorem uniform_message_expand_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal)^((result.2 : ℝ)/1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq,expectedValue_map]
  exact honest_expand_exponential_budget secret message

end SigGolfCandidate.T3.ExpansionClosure

end


