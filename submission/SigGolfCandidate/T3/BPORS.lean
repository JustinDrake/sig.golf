import SigGolfCandidate.T3.PackedChain
import SigGolfCandidate.T3.FullCache.NativeGame
import SigGolfCandidate.T3.FullCache.NativeMac
import SigGolfCandidate.T3.FullCache.RequestRun
import SigGolfCandidate.T3.SearchCost
import SigGolfCandidate.T3.FullCache.ExpansionCost
import SigGolfCandidate.T3.FullCache.SourcePrelude
import SigGolfCandidate.T3.Gate6.VerifierGate
import SigGolfCandidate.T3.Gate6.SourceBudget
import SigGolfCandidate.T3.Gate6.NearCoverage
import SigGolfCandidate.T3.Gate6.Sampling
import SigGolfCandidate.T3.Gate6.DigestCounting
import SigGolfCandidate.T3M.Extract.Main
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
import SigGolfCandidate.T3M.Final.SecurityP
import SigGolfCandidate.T3M.Witness.Queries
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.QueryCap (counted counted_pure counted_bind counted_map counted_forget counted_query_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev State := Nat × LazyPrivate.State
noncomputable def run {α : Type} (program : M α) (state : State) : ProbComp (α × State) :=
  (fun result => (result.1.1,(state.1+result.1.2,result.2))) <$>
    LazyPrivate.run (counted Derivation.charged program) state.2
theorem run_pure {α : Type} (value : α) (state : State) :
    run (pure value : M α) state=pure (value,state) := by
  simp only [run,counted_pure,LazyPrivate.run_pure,map_pure,Nat.add_zero]
theorem run_bind {α β : Type} (program : M α) (next : α → M β) (state : State) :
    run (program >>= next) state=(do
      let result ← run program state
      run (next result.1) result.2) := by
  simp only [run,counted_bind,LazyPrivate.run_bind,LazyPrivate.run_map,LazyPrivate.run_pure,
    map_bind,map_pure,bind_pure_comp,bind_map_left,Functor.map_map,Prod.map,id_eq,Nat.add_assoc]
theorem run_map {α β : Type} (f : α → β) (program : M α) (state : State) :
    run (f <$> program) state=Prod.map f id <$> run program state := by
  simp only [run,counted_map,LazyPrivate.run_map,Functor.map_map,Function.comp_def,Prod.map,id_eq]
theorem run_erasure {α : Type} (program : M α) (state : State) :
    Prod.map id Prod.snd <$> run program state=LazyPrivate.run program state.2 := by
  unfold run
  rw [Functor.map_map]
  change Prod.map Prod.fst id <$> LazyPrivate.run (counted Derivation.charged program) state.2=_
  rw [← LazyPrivate.run_map,counted_forget]
theorem run_query (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (fun result => (result.1,(state.1+FullGame.queryCharge input,result.2))) <$>
        LazyPrivate.run (liftM (T3.Spec.query input)) state.2 := by
  have hq : counted Derivation.charged (liftM (T3.Spec.query input))=
      (fun answer => (answer,FullGame.queryCharge input)) <$> (liftM (T3.Spec.query input) : M _) := by
    simpa only [counted_pure,Nat.add_zero,pure_bind,bind_pure,bind_pure_comp,map_pure,FullGame.queryCharge] using
      (counted_query_bind Derivation.charged input (fun answer => pure answer))
  simp only [run,hq,LazyPrivate.run_map,Functor.map_map,Function.comp_def,Prod.map,id_eq]
noncomputable def handler : QueryImpl T3.Spec (StateT State ProbComp) :=
  fun input => StateT.mk fun state => run (liftM (T3.Spec.query input)) state
theorem run_simulate {α : Type} (program : M α) (state : State) :
    (simulateQ handler program).run state=run program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
        handler,StateT.run_mk,run_bind,ih]
theorem count_monotone {α : Type} (program : M α) (state : State) (result : α × State)
    (hr : result ∈ support (run program state)) : state.1 ≤ result.2.1 := by
  rw [run,support_map] at hr
  obtain ⟨middle,_,rfl⟩ := hr
  exact Nat.le_add_right _ _
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × State) :=
  run (FullGame.idealGame adversary) (0,∅,∅)
theorem experiment_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | experiment adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | FullGame.idealLazyExperiment adversary] := by
  simp only [experiment,run,FullGame.idealLazyExperiment,probEvent_map,Function.comp_def,Nat.zero_add]
theorem real_to_counted_ideal (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact FullGame.real_to_ideal_lazy adversary q hq
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem authenticated_completed_target_bound (published : T3.Cache) (request : Request)
    (state : LazyPrivate.State) (hfresh : state.1 (.inr (.inl request.message))=none)
    (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published request) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [FullGame.authenticatedRecord,LazyPrivate.run_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro result hresult
  have hp := LazyPrivate.privateMac_preserves_nonce request.cache.region request.message state result hresult
  split_ifs
  · have h := LazyPrivate.payload_completed_target_bound request.cache request.message result.2
      (hp.1.trans hfresh) targets
    rw [hp.2] at h
    exact h
  · simp only [LazyPrivate.run_pure,expectedValue_pure,Option.elim_none,Sampling.targetWeight_average]
    exact le_add_right le_rfl
theorem counted_completed_target_bound (published : T3.Cache) (request : Request)
    (state : State) (hfresh : state.2.1 (.inr (.inl request.message))=none)
    (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (FullGame.authenticatedRecord published request) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2.2/(2 : ENNReal)^128 := by
  have h := congrArg (fun program => expectedValue program
    (fun result : (Option Signature × Option HashOutput) × LazyPrivate.State =>
      result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)))
    (run_erasure (FullGame.authenticatedRecord published request) state)
  rw [expectedValue_map] at h
  exact h.trans_le (authenticated_completed_target_bound published request state.2 hfresh targets)
noncomputable def recordLaw (published : T3.Cache) (request : Request) (state : State) :
    PMF (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets) :=
  liftM (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state))
theorem recordLaw_target_bound (published : T3.Cache) (request : Request) (state : State)
    (hfresh : state.2.1 (.inr (.inl request.message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | recordLaw published request state] ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2.2/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state))
      (fun result => Sampling.targetWeight targets result.2) ≤ _
  rw [Sampling.completeRecord_expected]
  exact counted_completed_target_bound published request state hfresh targets
theorem recordLaw_scaled_cap (published : T3.Cache) (request : Request) (state : State)
    (hfresh : state.2.1 (.inr (.inl request.message))=none)
    (hfinite : SphincsSecurity.Finite state.2.2) (budget : Nat)
    (hsize : QueryCache.enncard state.2.2 ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬Sampling.TargetCacheExceptional state.2.2) (point : DigestSampling.IndexBuckets) :
    (1024/1025 : ENNReal)*((recordLaw published request state).map Prod.snd) point ≤
      (PMF.uniformOfFintype DigestSampling.IndexBuckets) point := by
  have hc : Fintype.card DigestSampling.IndexBuckets=2^59 := by
    norm_num [DigestSampling.IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  have h := recordLaw_target_bound published request state hfresh {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  have hpoint := h.trans (Sampling.clean_point_bound_arithmetic state.2.2 hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point)
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem recordLaw_erasure (published : T3.Cache) (request : Request) (state : State) :
    (recordLaw published request state).map (fun result => (result.1.1.1,result.1.2))=
      (liftM (run (FullGame.authenticatedSign published request) state) : PMF (Option Signature × State)) := by
  have hsign : Prod.map Prod.fst id <$> run (FullGame.authenticatedRecord published request) state=
      run (FullGame.authenticatedSign published request) state := by
    rw [← run_map,FullGame.authenticatedRecord_erasure]
  have hg :
      𝒮[(fun result => (result.1.1.1,result.1.2)) <$>
        Sampling.completeRecord (fun result => result.1.2)
          (run (FullGame.authenticatedRecord published request) state)]=
      𝒮[run (FullGame.authenticatedSign published request) state] := by
    trans 𝒮[Prod.map Prod.fst id <$>
      (Prod.fst <$> Sampling.completeRecord (fun result => result.1.2)
        (run (FullGame.authenticatedRecord published request) state))]
    · rw [Functor.map_map]
      rfl
    · rw [evalSPMF_map,Sampling.completeRecord_erasure,← evalSPMF_map,hsign]
  apply PMF.ext
  intro response
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    ← PMF.probOutput_eq_apply]
  have h := evalSPMF_ext_iff.mp hg response
  rw [probOutput_map] at h
  exact h
abbrev Interaction := LazyPrivate.Interaction
noncomputable def interactionSource (published : T3.Cache) : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => FullGame.authenticatedSign published request
def Outcome : Interaction.Domain → Type
  | .inl input => SphincsSecurity.OracleWorld.Range input × State
  | .inr _ => (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)
noncomputable def interactionRecord (published : T3.Cache) : (input : Interaction.Domain) → State → PMF (Outcome input)
  | .inl input,state => liftM (run (forwardWorld input) state)
  | .inr request,state => recordLaw published request state
def response : (input : Interaction.Domain) → Outcome input → Interaction.Range input
  | .inl _,result => result.1
  | .inr _,result => result.1.1.1
def advance : (input : Interaction.Domain) → State → Outcome input → State
  | .inl _,_,result => result.2
  | .inr _,_,result => result.1.2
def label : (input : Interaction.Domain) → Outcome input → DigestSampling.IndexBuckets
  | .inl _,_ => default
  | .inr _,result => result.2
noncomputable def active (budget : Nat) : Interaction.Domain → State → Bool
  | .inl _,_ => false
  | .inr request,state => decide (
      state.2.1 (.inr (.inl request.message))=none ∧ SphincsSecurity.Finite state.2.2 ∧
      QueryCache.enncard state.2.2 ≤ budget ∧ ¬Sampling.TargetCacheExceptional state.2.2)
noncomputable def proposalModel (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction State DigestSampling.IndexBuckets where
  Outcome := Outcome
  record := interactionRecord published
  response := response
  advance := advance
  label := label
  active := active budget
  base := PMF.uniformOfFintype DigestSampling.IndexBuckets
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state hactive point
    cases input with
    | inl input => simp [active] at hactive
    | inr request =>
        change decide (_ ∧ _ ∧ _ ∧ _)=true at hactive
        obtain ⟨hfresh,hfinite,hsize,hclean⟩ := of_decide_eq_true hactive
        exact recordLaw_scaled_cap published request state hfresh hfinite budget hsize hbudget hclean point
theorem proposal_query_erasure (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : Interaction.Domain) (state : State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (run (interactionSource published input) state) : PMF (Interaction.Range input × State)) := by
  cases input with
  | inl input =>
      change (fun result : SphincsSecurity.OracleWorld.Range input × State => (result.1,result.2)) <$>
        (liftM (run (forwardWorld input) state) : PMF _)=_
      change id <$> (liftM (run (forwardWorld input) state) : PMF _)=_
      rw [id_map]
      rfl
  | inr request => exact recordLaw_erasure published request state
theorem proposal_execution_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α) (state : State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (run (simulateQ (interactionSource published) program) state) : PMF (α × State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (run (simulateQ (interactionSource published) program) state) : PMF (α × State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
theorem logged_source {α : Type} (published : T3.Cache) (program : OracleComp Interaction α) :
    simulateQ (interactionSource published) (ProposalOverflow.logged program)=
      FullGame.loggedWith (FullGame.authenticatedSign published) program := by
  rw [ProposalOverflow.logged,QueryImpl.simulateQ_writerTMapBase_run]
  unfold FullGame.loggedWith
  congr 2
  funext input
  cases input <;>
    simp [QueryImpl.writerTMapBase,ProposalOverflow.logging,QueryImpl.withTraceAppend_apply,
      ProposalOverflow.logFragment,interactionSource]
  · rfl
  · apply WriterT.ext
    simp
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ProposalOverflow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem signing_trace_overflow {Result : Type} (published : T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (proposalModel published budget hbudget)).traced program).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  full_trace_overflow_bound (proposalModel published budget hbudget) rfl program state
theorem signing_count_le_fragment (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : List DigestSampling.IndexBuckets × (Nat × State))
    (result : LazyPrivate.Interaction.Range input × (List DigestSampling.IndexBuckets × (Nat × State)))
    (hr : result ∈ (((counted (proposalModel published budget hbudget)).traced input).run state).support) :
    result.2.2.1 ≤ state.2.1 + (logFragment input result.1).length := by
  rw [counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [proposalModel, active, logFragment]
  | inr request => simp only [logFragment, List.length_singleton]; split <;> omega
theorem signing_count_le_log {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × State))
    (result : (Result × QueryLog Requests) × (List DigestSampling.IndexBuckets × (Nat × State)))
    (hr : result ∈ ((simulateQ (counted (proposalModel published budget hbudget)).traced
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
      have hstep := signing_count_le_fragment published budget hbudget input state middle hm
      rw [simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨last, hl, hr⟩ := hr
      have hrest := ih middle.1 middle.2 last hl
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp only [List.length_append]
      omega
theorem signing_log_overflow {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (proposalModel published budget hbudget)).traced
        (logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow published budget hbudget (logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (counted (proposalModel published budget hbudget)).traced
      (logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log published budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (counted (proposalModel published budget hbudget)).traced
        (logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]
theorem source_proposal_overflow {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (proposalModel published budget hbudget).traced (logged program)).run ([],state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← counted_trace_erasure (proposalModel published budget hbudget) (logged program) ([],0,state),
    probEvent_map]
  exact signing_log_overflow published budget hbudget program state
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev History := List DigestSampling.IndexBuckets
noncomputable def tracedExperiment (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (History × State)) := do
  let generated ← (liftM (run keygen (0,∅,∅)) : PMF _)
  let interaction ← (simulateQ (proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (FullGame.verdict generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem tracedExperiment_erasure (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment adversary budget hbudget=
      (liftM (experiment adversary) : PMF (Bool × State)) := by
  unfold tracedExperiment experiment FullGame.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem tracedExperiment_event (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.1≤q | tracedExperiment adversary q hq]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment adversary] := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.1=true ∧ result.2.1≤q | law]) (tracedExperiment_erasure adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq] at h
  calc
    _ = Pr[fun result => result.1=true ∧ result.2.1≤q | (liftM (experiment adversary) : PMF _)] := h
    _ = _ := by
      simp only [probEvent_eq_tsum_ite]
      rfl
theorem real_to_traced (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.1≤q | tracedExperiment adversary q hq]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [tracedExperiment_event]
  exact real_to_counted_ideal adversary q (hq.trans_lt (by norm_num))
theorem verdict_success_log (publicKey : Digest) (interaction : Option Forgery × QueryLog Requests)
    (state : State) (result : Bool × State)
    (hr : result ∈ support (run (FullGame.verdict publicKey interaction) state))
    (hwin : result.1=true) : interaction.2.length≤2^32 := by
  unfold FullGame.verdict at hr
  cases ho : interaction.1 with
  | none =>
      simp only [ho,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [ho,run_bind,mem_support_bind_iff,run_pure,support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,_,rfl⟩ := hr
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hwin
      exact hwin.1
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem winning_trace_overflow (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      tracedExperiment adversary budget hbudget] ≤ (2 : ENNReal)⁻¹^700 := by
  rw [← expectedValue_ite_one]
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  change expectedValue (run keygen (0,∅,∅)) _ ≤ _
  apply expectedValue_le_of_support
  intro generated _
  apply le_trans ?_ (source_proposal_overflow generated.1.2 budget hbudget
    (adversary generated.1.1 generated.1.2) generated.2)
  rw [← expectedValue_ite_one]
  apply expectedValue_mono
  intro interaction
  change expectedValue (run (FullGame.verdict generated.1.1 interaction.1) interaction.2.2)
    (fun checked => if checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length then 1 else 0) ≤ _
  apply expectedValue_le_of_support
  intro checked hchecked
  by_cases h : checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length
  · have hl := verdict_success_log generated.1.1 interaction.1 interaction.2.2 checked hchecked h.1
    simp only [h,if_true,show interaction.1.2.length≤2^32 ∧
      BPORS.Numeric.proposalLength < interaction.2.1.length from ⟨hl,h.2⟩,le_refl]
  · simp only [h,if_false,zero_le]
theorem split_winning_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.1≤q | tracedExperiment adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment adversary q hq]+
      Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
        tracedExperiment adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.1≤q
  · by_cases hn : result.2.1.length≤BPORS.Numeric.proposalLength
    · simp [hw,hw.1,hw.2,hn,Nat.not_lt.mpr hn]
    · simp [hw,hw.1,hw.2,hn,Nat.lt_of_not_ge hn]
  · simp only [hw,if_false,zero_le]
theorem real_to_bounded_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment adversary q hq]+
        (2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_traced adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  exact (split_winning_trace adversary q hq).trans
    (add_le_add le_rfl (winning_trace_overflow adversary q hq))
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Sampling.allTargetMoment DigestSampling.acceptanceProbability
theorem lazy_query_public_finite (input : T3.Spec.Domain) (state : LazyPrivate.State)
    (hfinite : SphincsSecurity.Finite state.2) (result : T3.Spec.Range input × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state)) :
    SphincsSecurity.Finite result.2.2 := by
  rw [LazyPrivate.run_query] at hr
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,hm,rfl⟩ := hr
      exact SphincsSecurity.finite_of_mem_support_romImpl hfinite hm
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨_,_,rfl⟩ := hr
      exact hfinite
theorem lazy_query_public_size (input : T3.Spec.Domain) (state : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state)) :
    QueryCache.enncard result.2.2 ≤ QueryCache.enncard state.2+FullGame.queryCharge input := by
  rw [LazyPrivate.run_query] at hr
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,hm,rfl⟩ := hr
      cases input with
      | inl input =>
          have he := SphincsSecurity.romImpl_uniform_query_enncard_eq input state.2 middle hm
          simpa only [FullGame.queryCharge,Derivation.charged,if_false,Nat.cast_zero,add_zero] using he.le
      | inr input =>
          simpa only [FullGame.queryCharge,Derivation.charged,if_true,Nat.cast_one] using
            SphincsSecurity.romImpl_hash_query_enncard_le input state.2 middle hm
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨_,_,rfl⟩ := hr
      exact le_add_right le_rfl
theorem lazy_query_moment (input : T3.Spec.Domain) (state : LazyPrivate.State)
    (hfinite : SphincsSecurity.Finite state.2) :
    expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
      (fun result => Sampling.allTargetMoment result.2.2) ≤
      Sampling.allTargetMoment state.2+DigestSampling.acceptanceProbability*FullGame.queryCharge input := by
  rw [LazyPrivate.run_query]
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,expectedValue_bind,expectedValue_pure]
      cases input with
      | inl input =>
          simpa only [expectedValue,FullGame.queryCharge,Derivation.charged,Bool.false_eq_true,if_false,Nat.cast_zero,mul_zero,add_zero]
            using Sampling.expected_allTargetMoment_step (.inl input) state.2 hfinite
      | inr input =>
          simpa only [expectedValue,FullGame.queryCharge,Derivation.charged,if_true,Nat.cast_one,mul_one]
            using Sampling.expected_allTargetMoment_step (.inr input) state.2 hfinite
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,expectedValue_bind,expectedValue_pure]
      rw [expectedValue_const (by simp)]
      exact le_add_right le_rfl
def WellFormed (state : State) : Prop :=
  SphincsSecurity.Finite state.2.2 ∧ QueryCache.enncard state.2.2 ≤ state.1
theorem initial_wellFormed : WellFormed (0,∅,∅) := by
  exact ⟨SphincsSecurity.finite_empty,by simp [QueryCache.enncard]⟩
theorem query_wellFormed (input : T3.Spec.Domain) (state : State) (hw : WellFormed state)
    (result : T3.Spec.Range input × State)
    (hr : result ∈ support (run (liftM (T3.Spec.query input)) state)) : WellFormed result.2 := by
  rw [run_query,support_map] at hr
  obtain ⟨middle,hm,rfl⟩ := hr
  refine ⟨lazy_query_public_finite input state.2 hw.1 middle hm,?_⟩
  change QueryCache.enncard middle.2.2≤((state.1+FullGame.queryCharge input : Nat) : ENNReal)
  rw [Nat.cast_add]
  exact (lazy_query_public_size input state.2 middle hm).trans (add_le_add hw.2 le_rfl)
theorem run_wellFormed {α : Type} (program : M α) (state : State) (hw : WellFormed state)
    (result : α × State) (hr : result ∈ support (run program state)) : WellFormed result.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact hw
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      exact ih middle.1 middle.2 (query_wellFormed input state hw middle hm) result hr
theorem active_iff_fresh_clean (request : Request) (state : State) (hw : WellFormed state)
    (budget : Nat) (hcount : state.1≤budget) :
    active budget (.inr request) state=true ↔
      state.2.1 (.inr (.inl request.message))=none ∧ ¬Sampling.TargetCacheExceptional state.2.2 := by
  simp only [active,decide_eq_true_eq]
  constructor
  · exact fun h => ⟨h.1,h.2.2.2⟩
  · intro h
    exact ⟨h.1,hw.1,hw.2.trans (by exact_mod_cast hcount),h.2⟩
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem run_project_support {α : Type} (program : M α) (state : State) (result : α × State)
    (hr : result ∈ support (run program state)) :
    (result.1,result.2.2) ∈ support (LazyPrivate.run program state.2) := by
  rw [← run_erasure program state,support_map]
  exact ⟨result,hr,rfl⟩
theorem run_nonce_preserves {α : Type} (protectedMessage : Message) (program : M α)
    (hprogram : NonceFreshness.Avoids protectedMessage program)
    (state : State) (result : α × State) (hr : result ∈ support (run program state)) :
    result.2.2.1 (.inr (.inl protectedMessage))=state.2.1 (.inr (.inl protectedMessage)) :=
  NonceFreshness.run_preserves protectedMessage program hprogram state.2
    (result.1,result.2.2) (run_project_support program state result hr)
theorem forwardWorld_avoids (protectedMessage : Message) (input : SphincsSecurity.OracleWorld.Domain) :
    NonceFreshness.Avoids protectedMessage (forwardWorld input) := by
  unfold forwardWorld
  apply (allQueriesSatisfy_query_iff _ _).mpr
  simp [NonceFreshness.nonceQuery]
theorem authenticatedSign_avoids (protectedMessage : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache≠published ∨ request.message≠protectedMessage) :
    NonceFreshness.Avoids protectedMessage (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply NonceFreshness.avoids_bind protectedMessage
    (NonceFreshness.avoids_privateMac protectedMessage request.cache.region)
  intro tag
  split_ifs with hc
  · exact NonceFreshness.avoids_signPayload protectedMessage request.cache request.message
      (hrequest.resolve_left (not_not.mpr hc))
  · exact NonceFreshness.avoids_pure protectedMessage none
def NoPublishedRequest (published : T3.Cache) (message : Message) (log : QueryLog Requests) : Prop :=
  ∀ entry ∈ log, entry.1.cache≠published ∨ entry.1.message≠message
theorem logged_nonce_fresh {α : Type} (protectedMessage : Message) (published : T3.Cache)
    (program : OracleComp Interaction α) (state : State)
    (hfresh : state.2.1 (.inr (.inl protectedMessage))=none)
    (result : (α × QueryLog Requests) × State)
    (hr : result ∈ support (run (FullGame.loggedWith (FullGame.authenticatedSign published) program) state))
    (hlog : NoPublishedRequest published protectedMessage result.1.2) :
    result.2.2.1 (.inr (.inl protectedMessage))=none := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [FullGame.loggedWith_pure,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact hfresh
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [FullGame.loggedWith_world,run_bind,mem_support_bind_iff] at hr
          obtain ⟨middle,hm,hr⟩ := hr
          have hf := (run_nonce_preserves protectedMessage (forwardWorld input)
            (forwardWorld_avoids protectedMessage input) state middle hm).trans hfresh
          exact ih middle.1 middle.2 hf result hr hlog
      | inr request =>
          rw [FullGame.loggedWith_request,run_bind,mem_support_bind_iff] at hr
          obtain ⟨middle,hm,hr⟩ := hr
          rw [run_map,support_map] at hr
          obtain ⟨last,hl,rfl⟩ := hr
          have hrequest := hlog ⟨request,middle.1⟩ (List.mem_cons_self ..)
          have hf := (run_nonce_preserves protectedMessage (FullGame.authenticatedSign published request)
            (authenticatedSign_avoids protectedMessage published request hrequest) state middle hm).trans hfresh
          apply ih middle.1 middle.2 hf last hl
          intro entry he
          exact hlog entry (List.mem_cons_of_mem _ he)
theorem counted_keygen_nonce_fresh (message : Message) (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen (0,∅,∅))) :
    generated.2.2.1 (.inr (.inl message))=none :=
  NonceFreshness.keygen_nonce_fresh message (generated.1,generated.2.2)
    (run_project_support keygen (0,∅,∅) generated hg)
theorem first_published_request_active {α : Type} (message : Message) (cache : T3.Cache)
    (generated : (Digest × T3.Cache) × State) (hg : generated ∈ support (run keygen (0,∅,∅)))
    (program : OracleComp Interaction α) (result : (α × QueryLog Requests) × State)
    (hr : result ∈ support (run
      (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2) program) generated.2))
    (hlog : NoPublishedRequest generated.1.2 message result.1.2)
    (budget : Nat) (hcount : result.2.1≤budget)
    (hclean : ¬Sampling.TargetCacheExceptional result.2.2.2) :
    active budget (.inr ⟨message,cache⟩) result.2=true := by
  have hgen := run_wellFormed keygen (0,∅,∅) initial_wellFormed generated hg
  have hw := run_wellFormed _ generated.2 hgen result hr
  apply (active_iff_fresh_clean ⟨message,cache⟩ result.2 hw budget hcount).mpr
  exact ⟨logged_nonce_fresh message generated.1.2 program generated.2
    (counted_keygen_nonce_fresh message generated hg) result hr hlog,hclean⟩
theorem authenticatedSign_hashOnly (published : T3.Cache) (request : Request) :
    SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) request.cache.region)
  intro tag
  split_ifs
  · exact SourceQueries.signPayload_allowed SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
      (fun _ => trivial) request.cache request.message
  · exact SourceQueries.pure_allowed _ _
theorem authenticatedRecord_hashOnly (published : T3.Cache) (request : Request) :
    SourceReplay.HashOnly (FullGame.authenticatedRecord published request) := by
  apply (SourceQueries.map_allowed_iff SourceReplay.IsHash Prod.fst _).mp
  rw [FullGame.authenticatedRecord_erasure]
  exact authenticatedSign_hashOnly published request
theorem authenticatedRecord_replay (published : T3.Cache) (request : Request)
    (before : LazyPrivate.State) (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) before))
    (after : LazyPrivate.State) (hle : SourceReplay.Extends result.2 after) :
    LazyPrivate.run (FullGame.authenticatedRecord published request) after=pure (result.1,after) :=
  SourceReplay.replay_run _ (authenticatedRecord_hashOnly published request) before result hr after hle
end SigGolfCandidate.T3.Security.CountedPrivate
end
namespace SigGolfResearch.Gate6.NativeCache
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Security
open SphincsSecurity (Finite)
open SphincsSecurity.QueryCap (counted counted_pure counted_query_bind)
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] totalWeight
theorem expected_totalWeight_step (q : Nat) (query : SphincsSecurity.OracleWorld.Domain)
    (cache : RCache) (hfinite : Finite cache) :
    expectedValue ((SphincsSecurity.romImpl query).run cache) (fun result => totalWeight q result.2) ≤
      totalWeight q cache := by
  have h := SphincsSecurity.expected_potential_romImpl_le_charge (totalWeight q)
    (fun _ _ => 0) (fun current hc input hf =>
      (expected_totalWeight_fresh q current hc input hf).trans_eq (add_zero _).symm) query cache hfinite
  have hz : SphincsSecurity.hashQueryCharge (fun _ _ => (0 : ENNReal)) cache query=0 := by
    cases query <;> rfl
  rw [hz,add_zero] at h
  exact h
theorem lazy_query_weight (q : Nat) (input : Spec.Domain) (state : LazyPrivate.State)
    (hfinite : Finite state.2) :
    expectedValue (LazyPrivate.run (liftM (Spec.query input)) state)
      (fun result => totalWeight q result.2.2) ≤ totalWeight q state.2 := by
  rw [LazyPrivate.run_query]
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,expectedValue_bind,expectedValue_pure]
      exact expected_totalWeight_step q input state.2 hfinite
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,expectedValue_bind,expectedValue_pure]
      rw [expectedValue_const (by simp)]
end SigGolfResearch.Gate6.NativeCache
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Sampling.allTargetMoment DigestSampling.acceptanceProbability
structure Observation (α : Type) where
  value : α
  calls : Nat
  exceptional : Bool
  state : LazyPrivate.State
noncomputable def observe {α : Type} (program : M α) : LazyPrivate.State → ProbComp (Observation α) :=
  OracleComp.construct
    (fun value state => pure ⟨value,0,decide (Sampling.TargetCacheExceptional state.2),state⟩)
    (fun input _ next state => do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,FullGame.queryCharge input+last.calls,
        decide (Sampling.TargetCacheExceptional state.2) || last.exceptional,last.state⟩) <$>
          next middle.1 middle.2) program
theorem observe_pure {α : Type} (value : α) (state : LazyPrivate.State) :
    observe (pure value : M α) state=
      pure ⟨value,0,decide (Sampling.TargetCacheExceptional state.2),state⟩ := rfl
theorem observe_query_bind {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    observe (liftM (T3.Spec.query input) >>= next) state=(do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,FullGame.queryCharge input+last.calls,
        decide (Sampling.TargetCacheExceptional state.2) || last.exceptional,last.state⟩) <$>
          observe (next middle.1) middle.2) := rfl
theorem exception_potential_ge_one (state : LazyPrivate.State)
    (hbad : Sampling.TargetCacheExceptional state.2) (budget : Nat) :
    1 ≤ (Sampling.allTargetMoment state.2+DigestSampling.acceptanceProbability*budget)/(2 : ENNReal)^94 := by
  calc
    1 = (2 : ENNReal)^94/(2 : ENNReal)^94 :=
      (ENNReal.div_self (by norm_num) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right
      ((Sampling.targetCacheExceptional_moment state.2 hbad).trans le_self_add) _
theorem query_remaining_potential (input : T3.Spec.Domain) (state : LazyPrivate.State)
    (hfinite : SphincsSecurity.Finite state.2) (remaining : Nat) :
    expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
      (fun result => (Sampling.allTargetMoment result.2.2+
        DigestSampling.acceptanceProbability*remaining)/(2 : ENNReal)^94) ≤
      (Sampling.allTargetMoment state.2+
        DigestSampling.acceptanceProbability*((FullGame.queryCharge input+remaining : Nat) : ENNReal))/(2 : ENNReal)^94 := by
  have hmass : Pr[⊥ | LazyPrivate.run (liftM (T3.Spec.query input)) state]=0 := by simp
  have he : expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
      (fun result => (Sampling.allTargetMoment result.2.2+
        DigestSampling.acceptanceProbability*remaining)/(2 : ENNReal)^94)=
      (expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
        (fun result => Sampling.allTargetMoment result.2.2)+
          DigestSampling.acceptanceProbability*remaining)/(2 : ENNReal)^94 := by
    simp only [div_eq_mul_inv,expectedValue_mul_const,expectedValue_add]
    rw [expectedValue_const hmass]
  rw [he]
  apply ENNReal.div_le_div_right
  calc
    _ ≤ (Sampling.allTargetMoment state.2+
          DigestSampling.acceptanceProbability*FullGame.queryCharge input)+
          DigestSampling.acceptanceProbability*remaining :=
      add_le_add (lazy_query_moment input state hfinite) le_rfl
    _ = _ := by push_cast;ring
theorem observe_exception_bound {α : Type} (program : M α) (state : LazyPrivate.State)
    (hfinite : SphincsSecurity.Finite state.2) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.exceptional=true | observe program state] ≤
      (Sampling.allTargetMoment state.2+DigestSampling.acceptanceProbability*budget)/(2 : ENNReal)^94 := by
  induction program using OracleComp.inductionOn generalizing state budget with
  | pure value =>
      by_cases hb : Sampling.TargetCacheExceptional state.2
      · exact probEvent_le_one.trans (exception_potential_ge_one state hb budget)
      · simp only [observe_pure,probEvent_pure,Nat.zero_le,decide_eq_false hb,Bool.false_eq_true,
          and_false,ite_false,zero_le]
  | query_bind input next ih =>
      by_cases hb : Sampling.TargetCacheExceptional state.2
      · exact probEvent_le_one.trans (exception_potential_ge_one state hb budget)
      · rw [observe_query_bind,probEvent_bind_eq_expectedValue]
        simp only [probEvent_map,Function.comp_def,decide_eq_false hb,Bool.false_or]
        by_cases hc : Derivation.charged input
        · cases budget with
          | zero =>
              simp [FullGame.queryCharge,hc,expectedValue]
          | succ remaining =>
              have he : ∀ n : Nat, FullGame.queryCharge input+n≤remaining+1 ↔ n≤remaining := by
                simp only [FullGame.queryCharge,if_pos hc];omega
              simp_rw [he]
              calc
                _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
                    (fun middle => (Sampling.allTargetMoment middle.2.2+
                      DigestSampling.acceptanceProbability*remaining)/(2 : ENNReal)^94) := by
                  apply expectedValue_mono_of_support
                  intro middle hm
                  exact ih middle.1 middle.2 (lazy_query_public_finite input state hfinite middle hm) remaining
                _ ≤ _ := by
                  simpa only [FullGame.queryCharge,if_pos hc,Nat.add_comm 1] using
                    query_remaining_potential input state hfinite remaining
        · simp only [FullGame.queryCharge,if_neg hc,Nat.zero_add]
          calc
            _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
                (fun middle => (Sampling.allTargetMoment middle.2.2+
                  DigestSampling.acceptanceProbability*budget)/(2 : ENNReal)^94) := by
              apply expectedValue_mono_of_support
              intro middle hm
              exact ih middle.1 middle.2 (lazy_query_public_finite input state hfinite middle hm) budget
            _ ≤ _ := by
              simpa only [FullGame.queryCharge,if_neg hc,Nat.zero_add] using
                query_remaining_potential input state hfinite budget
theorem observe_empty_exception_bound {α : Type} (program : M α) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.exceptional=true | observe program (∅,∅)] ≤
      DigestSampling.acceptanceProbability*budget/(2 : ENNReal)^94 := by
  simpa only [Sampling.allTargetMoment_empty,zero_add] using
    observe_exception_bound program (∅,∅) SphincsSecurity.finite_empty budget
theorem observe_empty_exception_small {α : Type} (program : M α) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.exceptional=true | observe program (∅,∅)] ≤
      budget/(2 : ENNReal)^98 := by
  calc
    _ ≤ DigestSampling.acceptanceProbability*budget/(2 : ENNReal)^94 :=
      observe_empty_exception_bound program budget
    _ ≤ (1/16 : ENNReal)*budget/(2 : ENNReal)^94 :=
      ENNReal.div_le_div_right (mul_le_mul' Acceptance.acceptanceProbability_le_one_sixteenth le_rfl) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow]
      ring
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.QueryCap (counted counted_pure counted_query_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem observe_counter_erasure {α : Type} (program : M α) (state : LazyPrivate.State) :
    (fun result : Observation α => ((result.value,result.calls),result.state)) <$> observe program state=
      LazyPrivate.run (counted Derivation.charged program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [observe_pure,map_pure,counted_pure,LazyPrivate.run_pure]
  | query_bind input next ih =>
      rw [observe_query_bind,map_bind,counted_query_bind,LazyPrivate.run_bind]
      apply bind_congr
      intro middle
      simp only [Functor.map_map,LazyPrivate.run_bind,LazyPrivate.run_pure,bind_pure_comp]
      have h := congrArg (Functor.map (fun result : (α × Nat) × LazyPrivate.State =>
        ((result.1.1,FullGame.queryCharge input+result.1.2),result.2))) (ih middle.1 middle.2)
      rw [LazyPrivate.run_map]
      have he : Prod.map (fun result : α × Nat => (result.1,(if Derivation.charged input then 1 else 0)+result.2)) id=
          (fun result : (α × Nat) × LazyPrivate.State =>
            ((result.1.1,FullGame.queryCharge input+result.1.2),result.2)) := by
        funext result
        rcases result with ⟨⟨value,calls⟩,state⟩
        rfl
      rw [he]
      simpa only [Functor.map_map] using h
noncomputable def observedExperiment (adversary : Adversary) : ProbComp (Observation Bool) :=
  observe (FullGame.idealGame adversary) (∅,∅)
theorem observedExperiment_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.value=true ∧ result.calls≤q | observedExperiment adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | FullGame.idealLazyExperiment adversary] := by
  have h := congrArg (fun program : ProbComp ((Bool × Nat) × LazyPrivate.State) =>
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | program])
    (observe_counter_erasure (FullGame.idealGame adversary) (∅,∅))
  simpa only [observedExperiment,FullGame.idealLazyExperiment,probEvent_map,Function.comp_def] using h
theorem split_observed_win (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.value=true ∧ result.calls≤q | observedExperiment adversary] ≤
      Pr[fun result => result.value=true ∧ result.calls≤q ∧ result.exceptional=false |
        observedExperiment adversary]+
      Pr[fun result => result.calls≤q ∧ result.exceptional=true | observedExperiment adversary] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.value=true ∧ result.calls≤q
  · cases hb : result.exceptional <;> simp [hw,hw.2,hb]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_observed (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.value=true ∧ result.calls≤q ∧ result.exceptional=false |
        observedExperiment adversary]+
        q/(2 : ENNReal)^98+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := FullGame.real_to_ideal_lazy adversary q hq
  rw [← observedExperiment_event] at h
  apply h.trans
  apply add_le_add_left
  apply add_le_add_left
  exact (split_observed_win adversary q).trans
    (add_le_add le_rfl (observe_empty_exception_small (FullGame.idealGame adversary) q))
end SigGolfCandidate.T3.Security.CountedPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Sampling.allTargetMoment DigestSampling.acceptanceProbability
structure State where
  source : CountedPrivate.State
  exceptional : Bool
noncomputable def flag (state : State) (next : CountedPrivate.State) : Bool :=
  state.exceptional || decide (Sampling.TargetCacheExceptional state.source.2.2) ||
    decide (Sampling.TargetCacheExceptional next.2.2)
noncomputable def handler : QueryImpl T3.Spec (StateT State ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1,⟨result.2,flag state result.2⟩)) <$>
      CountedPrivate.run (liftM (T3.Spec.query input)) state.source
noncomputable def run {α : Type} (program : M α) (state : State) : ProbComp (α × State) :=
  (simulateQ handler program).run state
theorem run_pure {α : Type} (value : α) (state : State) :
    run (pure value : M α) state=pure (value,state) := rfl
theorem run_bind {α β : Type} (program : M α) (next : α → M β) (state : State) :
    run (program >>= next) state=(do
      let result ← run program state
      run (next result.1) result.2) := by
  simp only [run,simulateQ_bind,StateT.run_bind]
theorem run_map {α β : Type} (f : α → β) (program : M α) (state : State) :
    run (f <$> program) state=Prod.map f id <$> run program state := by
  simp only [run,simulateQ_map,StateT.run_map]
  rfl
theorem run_query (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (fun result => (result.1,⟨result.2,flag state result.2⟩)) <$>
        CountedPrivate.run (liftM (T3.Spec.query input)) state.source := by
  simp only [run,simulateQ_spec_query,handler,StateT.run_mk]
theorem run_erasure {α : Type} (program : M α) (state : State) :
    Prod.map id State.source <$> run program state=CountedPrivate.run program state.source := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run_pure,CountedPrivate.run_pure,map_pure,Prod.map,id_eq]
  | query_bind input next ih =>
      rw [run_bind,CountedPrivate.run_bind,map_bind,run_query,bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 ⟨result.2,flag state result.2⟩
theorem run_project_support {α : Type} (program : M α) (state : State) (result : α × State)
    (hr : result ∈ support (run program state)) :
    (result.1,result.2.source) ∈ support (CountedPrivate.run program state.source) := by
  rw [← run_erasure program state,support_map]
  exact ⟨result,hr,rfl⟩
theorem flag_monotone (state : State) (next : CountedPrivate.State)
    (h : state.exceptional=true) : flag state next=true := by simp [flag,h]
theorem run_flag_monotone {α : Type} (program : M α) (state : State)
    (h : state.exceptional=true) (result : α × State) (hr : result ∈ support (run program state)) :
    result.2.exceptional=true := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact h
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [run_query,support_map] at hm
      obtain ⟨step,_,rfl⟩ := hm
      exact ih step.1 _ (flag_monotone state step.2 h) result hr
def Coherent (state : State) : Prop :=
  Sampling.TargetCacheExceptional state.source.2.2 → state.exceptional=true
theorem flag_coherent (state : State) (next : CountedPrivate.State) :
    Coherent ⟨next,flag state next⟩ := by
  intro h
  simp [flag,h]
theorem run_coherent {α : Type} (program : M α) (state : State) (h : Coherent state)
    (result : α × State) (hr : result ∈ support (run program state)) : Coherent result.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact h
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [run_query,support_map] at hm
      obtain ⟨step,_,rfl⟩ := hm
      exact ih step.1 _ (flag_coherent state step.2) result hr
theorem flag_of_clean (state : State) (hflag : state.exceptional=false)
    (hclean : ¬Sampling.TargetCacheExceptional state.source.2.2) (next : CountedPrivate.State) :
    flag state next=decide (Sampling.TargetCacheExceptional next.2.2) := by
  simp [flag,hflag,hclean]
theorem run_exception_bound {α : Type} (program : M α) (state : State)
    (hflag : state.exceptional=false) (hfinite : SphincsSecurity.Finite state.source.2.2)
    (budget : Nat) :
    Pr[fun result => result.2.source.1 ≤ state.source.1+budget ∧ result.2.exceptional=true |
      run program state] ≤
      (Sampling.allTargetMoment state.source.2.2+
        DigestSampling.acceptanceProbability*budget)/(2 : ENNReal)^94 := by
  induction program using OracleComp.inductionOn generalizing state budget with
  | pure value => simp [run_pure,hflag]
  | query_bind input next ih =>
      by_cases hb : Sampling.TargetCacheExceptional state.source.2.2
      · exact probEvent_le_one.trans (CountedPrivate.exception_potential_ge_one state.source.2 hb budget)
      · rw [run_bind,probEvent_bind_eq_expectedValue,run_query]
        rw [CountedPrivate.run_query]
        simp only [Functor.map_map,expectedValue_map,Function.comp_def,flag_of_clean state hflag hb]
        by_cases hc : Derivation.charged input
        · cases budget with
          | zero =>
              apply le_trans (b := 0) ?_ bot_le
              apply expectedValue_le_of_support
              intro middle hm
              apply le_of_eq
              apply probEvent_eq_zero
              intro result hr hwin
              have hsource := run_project_support (next middle.1)
                ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                  decide (Sampling.TargetCacheExceptional middle.2.2)⟩ result hr
              have hmon := CountedPrivate.count_monotone _ _ _ hsource
              simp only [FullGame.queryCharge,if_pos hc] at hmon
              omega
          | succ remaining =>
              calc
                _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state.source.2)
                    (fun middle => (Sampling.allTargetMoment middle.2.2+
                      DigestSampling.acceptanceProbability*remaining)/(2 : ENNReal)^94) := by
                  apply expectedValue_mono_of_support
                  intro middle hm
                  by_cases hmBad : Sampling.TargetCacheExceptional middle.2.2
                  · exact probEvent_le_one.trans (CountedPrivate.exception_potential_ge_one middle.2 hmBad remaining)
                  · have hi := ih middle.1
                      ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                        decide (Sampling.TargetCacheExceptional middle.2.2)⟩
                      (by simp [hmBad]) (CountedPrivate.lazy_query_public_finite input state.source.2 hfinite middle hm) remaining
                    simpa only [FullGame.queryCharge,if_pos hc,Nat.add_assoc,Nat.add_comm 1] using hi
                _ ≤ _ := by
                  simpa only [FullGame.queryCharge,if_pos hc,Nat.add_comm 1] using
                    CountedPrivate.query_remaining_potential input state.source.2 hfinite remaining
        · calc
            _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state.source.2)
                (fun middle => (Sampling.allTargetMoment middle.2.2+
                  DigestSampling.acceptanceProbability*budget)/(2 : ENNReal)^94) := by
              apply expectedValue_mono_of_support
              intro middle hm
              by_cases hmBad : Sampling.TargetCacheExceptional middle.2.2
              · exact probEvent_le_one.trans (CountedPrivate.exception_potential_ge_one middle.2 hmBad budget)
              · have hi := ih middle.1
                  ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                    decide (Sampling.TargetCacheExceptional middle.2.2)⟩
                  (by simp [hmBad]) (CountedPrivate.lazy_query_public_finite input state.source.2 hfinite middle hm) budget
                simpa only [FullGame.queryCharge,if_neg hc,Nat.add_zero] using hi
            _ ≤ _ := by
              simpa only [FullGame.queryCharge,if_neg hc,Nat.zero_add] using
                CountedPrivate.query_remaining_potential input state.source.2 hfinite budget
theorem gate6_bad_potential (q : Nat) (cache : Sampling.RCache)
    (hq : QueryCache.enncard cache ≤ q) (hbad : Sampling.TargetCacheExceptional cache) :
    1 ≤ SigGolfResearch.Gate6.NativeCache.totalWeight q cache :=
  SigGolfResearch.Gate6.NativeCache.totalWeight_bad q cache hq
    ((Sampling.targetCacheExceptional_iff_native cache).mp hbad)
theorem gate6_run_exception_bound {α : Type} (program : M α) (state : State)
    (hflag : state.exceptional=false) (hfinite : SphincsSecurity.Finite state.source.2.2)
    (budget q : Nat) (hcap : QueryCache.enncard state.source.2.2+(budget : ENNReal) ≤ q) :
    Pr[fun result => result.2.source.1 ≤ state.source.1+budget ∧ result.2.exceptional=true |
      run program state] ≤ SigGolfResearch.Gate6.NativeCache.totalWeight q state.source.2.2 := by
  induction program using OracleComp.inductionOn generalizing state budget with
  | pure value => simp [run_pure,hflag]
  | query_bind input next ih =>
      by_cases hb : Sampling.TargetCacheExceptional state.source.2.2
      · exact probEvent_le_one.trans (gate6_bad_potential q state.source.2.2 (le_self_add.trans hcap) hb)
      · rw [run_bind,probEvent_bind_eq_expectedValue,run_query]
        rw [CountedPrivate.run_query]
        simp only [Functor.map_map,expectedValue_map,Function.comp_def,flag_of_clean state hflag hb]
        by_cases hc : Derivation.charged input
        · cases budget with
          | zero =>
              apply le_trans (b := 0) ?_ bot_le
              apply expectedValue_le_of_support
              intro middle hm
              apply le_of_eq
              apply probEvent_eq_zero
              intro result hr hwin
              have hsource := run_project_support (next middle.1)
                ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                  decide (Sampling.TargetCacheExceptional middle.2.2)⟩ result hr
              have hmon := CountedPrivate.count_monotone _ _ _ hsource
              simp only [FullGame.queryCharge,if_pos hc] at hmon
              omega
          | succ remaining =>
              calc
                _  ≤  expectedValue (LazyPrivate.run (liftM (Spec.query input)) state.source.2)
                    (fun middle => SigGolfResearch.Gate6.NativeCache.totalWeight q middle.2.2) := by
                  apply expectedValue_mono_of_support
                  intro middle hm
                  have hs := CountedPrivate.lazy_query_public_size input state.source.2 middle hm
                  simp only [FullGame.queryCharge,if_pos hc,Nat.cast_one] at hs
                  have hn : QueryCache.enncard middle.2.2+(remaining : ENNReal) ≤ q := by
                    calc
                      _  ≤  (QueryCache.enncard state.source.2.2+1)+remaining := add_le_add hs le_rfl
                      _ = QueryCache.enncard state.source.2.2+((remaining+1 : Nat) : ENNReal) := by push_cast;ring
                      _  ≤  _ := hcap
                  by_cases hmBad : Sampling.TargetCacheExceptional middle.2.2
                  · exact probEvent_le_one.trans (gate6_bad_potential q middle.2.2 (le_self_add.trans hn) hmBad)
                  · have hi := ih middle.1
                      ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                        decide (Sampling.TargetCacheExceptional middle.2.2)⟩
                      (by simp [hmBad]) (CountedPrivate.lazy_query_public_finite input state.source.2 hfinite middle hm) remaining hn
                    simpa only [FullGame.queryCharge,if_pos hc,Nat.add_assoc,Nat.add_comm 1] using hi
                _  ≤  _ := SigGolfResearch.Gate6.NativeCache.lazy_query_weight q input state.source.2 hfinite
        · calc
            _  ≤  expectedValue (LazyPrivate.run (liftM (Spec.query input)) state.source.2)
                (fun middle => SigGolfResearch.Gate6.NativeCache.totalWeight q middle.2.2) := by
              apply expectedValue_mono_of_support
              intro middle hm
              have hs := CountedPrivate.lazy_query_public_size input state.source.2 middle hm
              simp only [FullGame.queryCharge,if_neg hc,Nat.cast_zero,add_zero] at hs
              have hn : QueryCache.enncard middle.2.2+(budget : ENNReal) ≤ q :=
                (add_le_add hs le_rfl).trans hcap
              by_cases hmBad : Sampling.TargetCacheExceptional middle.2.2
              · exact probEvent_le_one.trans (gate6_bad_potential q middle.2.2 (le_self_add.trans hn) hmBad)
              · have hi := ih middle.1
                  ⟨(state.source.1+FullGame.queryCharge input,middle.2),
                    decide (Sampling.TargetCacheExceptional middle.2.2)⟩
                  (by simp [hmBad]) (CountedPrivate.lazy_query_public_finite input state.source.2 hfinite middle hm) budget hn
                simpa only [FullGame.queryCharge,if_neg hc,Nat.add_zero] using hi
            _  ≤  _ := SigGolfResearch.Gate6.NativeCache.lazy_query_weight q input state.source.2 hfinite
theorem gate6_run_empty_tail {α : Type} (program : M α) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.source.1 ≤ q ∧ result.2.exceptional=true |
      run program ⟨(0,∅,∅),false⟩] ≤ (2^700 : ENNReal)⁻¹ := by
  have h := gate6_run_exception_bound program ⟨(0,∅,∅),false⟩ rfl SphincsSecurity.finite_empty q q (by simp)
  simpa only [Nat.zero_add] using h.trans (SigGolfResearch.Gate6.NativeCache.initial_totalWeight_le q hq)
theorem gate6_not_bad_of_zero (cache : SigGolfResearch.Gate6.NativeCache.RCache) (hfinite : SphincsSecurity.Finite cache)
    (hzero : QueryCache.enncard cache=0) : ¬Sampling.TargetCacheExceptional cache := by
  intro hbad
  obtain ⟨mark,hmark⟩ := (Sampling.targetCacheExceptional_iff_native cache).mp hbad
  have hc : SigGolfResearch.Gate6.NativeCache.count mark cache=0 :=
    le_antisymm ((SigGolfResearch.Gate6.NativeCache.count_le_enncard mark cache hfinite).trans_eq hzero) bot_le
  norm_num [hzero,hc] at hmark
theorem gate6_run_zero_exception {α : Type} (program : M α) (state : State)
    (hflag : state.exceptional=false) (hfinite : SphincsSecurity.Finite state.source.2.2)
    (hzero : QueryCache.enncard state.source.2.2=0) :
    Pr[fun result => result.2.source.1 ≤ state.source.1 ∧ result.2.exceptional=true |
      run program state]=0 := by
  apply le_antisymm _ bot_le
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure,hflag]
  | query_bind input next ih =>
      have hb := gate6_not_bad_of_zero state.source.2.2 hfinite hzero
      rw [run_bind,probEvent_bind_eq_expectedValue,run_query,CountedPrivate.run_query]
      simp only [Functor.map_map,expectedValue_map,Function.comp_def,flag_of_clean state hflag hb]
      apply expectedValue_le_of_support
      intro middle hm
      apply le_of_eq
      by_cases hc : Derivation.charged input
      · apply probEvent_eq_zero
        intro result hr hwin
        have hsource := run_project_support (next middle.1)
          ⟨(state.source.1+FullGame.queryCharge input,middle.2),
            decide (Sampling.TargetCacheExceptional middle.2.2)⟩ result hr
        have hmon := CountedPrivate.count_monotone _ _ _ hsource
        simp only [FullGame.queryCharge,if_pos hc] at hmon
        omega
      · have hf := CountedPrivate.lazy_query_public_finite input state.source.2 hfinite middle hm
        have hs := CountedPrivate.lazy_query_public_size input state.source.2 middle hm
        simp only [FullGame.queryCharge,if_neg hc,Nat.cast_zero,add_zero,hzero] at hs
        have hz : QueryCache.enncard middle.2.2=0 := le_antisymm hs bot_le
        have hn := gate6_not_bad_of_zero middle.2.2 hf hz
        have hi := ih middle.1
          ⟨(state.source.1+FullGame.queryCharge input,middle.2),decide (Sampling.TargetCacheExceptional middle.2.2)⟩
          (by simp [hn]) hf hz
        simpa only [FullGame.queryCharge,if_neg hc,Nat.add_zero] using le_antisymm hi bot_le
theorem gate6_run_empty_linear_charge {α : Type} (program : M α) (q bits : Nat)
    (hq : q ≤ 2^127) (hbits : bits ≤ 700) :
    Pr[fun result => result.2.source.1 ≤ q ∧ result.2.exceptional=true |
      run program ⟨(0,∅,∅),false⟩] ≤ (q : ENNReal)/2^bits := by
  by_cases hz : q=0
  · subst q
    rw [gate6_run_zero_exception program ⟨(0,∅,∅),false⟩ rfl SphincsSecurity.finite_empty (by simp)]
    exact bot_le
  · calc
      _ ≤ (2^700 : ENNReal)⁻¹ := gate6_run_empty_tail program q hq
      _ ≤ (2^bits : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) hbits)
      _ = (1 : ENNReal)/2^bits := by simp
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 1 ≤ q by omega)) _
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem monitored_completed_target_bound (published : T3.Cache) (request : Request)
    (state : State) (hfresh : state.source.2.1 (.inr (.inl request.message))=none)
    (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (FullGame.authenticatedRecord published request) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.source.2.2/(2 : ENNReal)^128 := by
  have h := congrArg (fun program => expectedValue program
    (fun result : (Option Signature × Option HashOutput) × CountedPrivate.State =>
      result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)))
    (run_erasure (FullGame.authenticatedRecord published request) state)
  rw [expectedValue_map] at h
  exact h.trans_le (CountedPrivate.counted_completed_target_bound published request state.source hfresh targets)
noncomputable def recordLaw (published : T3.Cache) (request : Request) (state : State) :
    PMF (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets) :=
  liftM (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state))
theorem recordLaw_target_bound (published : T3.Cache) (request : Request) (state : State)
    (hfresh : state.source.2.1 (.inr (.inl request.message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | recordLaw published request state] ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.source.2.2/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state))
      (fun result => Sampling.targetWeight targets result.2) ≤ _
  rw [Sampling.completeRecord_expected]
  exact monitored_completed_target_bound published request state hfresh targets
theorem recordLaw_scaled_cap (published : T3.Cache) (request : Request) (state : State)
    (hfresh : state.source.2.1 (.inr (.inl request.message))=none)
    (hfinite : SphincsSecurity.Finite state.source.2.2) (budget : Nat)
    (hsize : QueryCache.enncard state.source.2.2 ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬Sampling.TargetCacheExceptional state.source.2.2) (point : DigestSampling.IndexBuckets) :
    (1024/1025 : ENNReal)*((recordLaw published request state).map Prod.snd) point ≤
      (PMF.uniformOfFintype DigestSampling.IndexBuckets) point := by
  have hc : Fintype.card DigestSampling.IndexBuckets=2^59 := by
    norm_num [DigestSampling.IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  have h := recordLaw_target_bound published request state hfresh {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  have hpoint := h.trans (Sampling.clean_point_bound_arithmetic state.source.2.2 hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point)
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem recordLaw_erasure (published : T3.Cache) (request : Request) (state : State) :
    (recordLaw published request state).map (fun result => (result.1.1.1,result.1.2))=
      (liftM (run (FullGame.authenticatedSign published request) state) : PMF (Option Signature × State)) := by
  have hsign : Prod.map Prod.fst id <$> run (FullGame.authenticatedRecord published request) state=
      run (FullGame.authenticatedSign published request) state := by
    rw [← run_map,FullGame.authenticatedRecord_erasure]
  have hg :
      𝒮[(fun result => (result.1.1.1,result.1.2)) <$>
        Sampling.completeRecord (fun result => result.1.2)
          (run (FullGame.authenticatedRecord published request) state)]=
      𝒮[run (FullGame.authenticatedSign published request) state] := by
    trans 𝒮[Prod.map Prod.fst id <$>
      (Prod.fst <$> Sampling.completeRecord (fun result => result.1.2)
        (run (FullGame.authenticatedRecord published request) state))]
    · rw [Functor.map_map]
      rfl
    · rw [evalSPMF_map,Sampling.completeRecord_erasure,← evalSPMF_map,hsign]
  apply PMF.ext
  intro response
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    ← PMF.probOutput_eq_apply]
  have h := evalSPMF_ext_iff.mp hg response
  rw [probOutput_map] at h
  exact h
abbrev Interaction := LazyPrivate.Interaction
noncomputable def interactionSource (published : T3.Cache) : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => FullGame.authenticatedSign published request
def Outcome : Interaction.Domain → Type
  | .inl input => SphincsSecurity.OracleWorld.Range input × State
  | .inr _ => (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)
noncomputable def interactionRecord (published : T3.Cache) : (input : Interaction.Domain) → State → PMF (Outcome input)
  | .inl input,state => liftM (run (forwardWorld input) state)
  | .inr request,state => recordLaw published request state
def response : (input : Interaction.Domain) → Outcome input → Interaction.Range input
  | .inl _,result => result.1
  | .inr _,result => result.1.1.1
def advance : (input : Interaction.Domain) → State → Outcome input → State
  | .inl _,_,result => result.2
  | .inr _,_,result => result.1.2
def label : (input : Interaction.Domain) → Outcome input → DigestSampling.IndexBuckets
  | .inl _,_ => default
  | .inr _,result => result.2
noncomputable def active (budget : Nat) : Interaction.Domain → State → Bool
  | .inl _,_ => false
  | .inr request,state => decide (
      state.source.2.1 (.inr (.inl request.message))=none ∧ SphincsSecurity.Finite state.source.2.2 ∧
      QueryCache.enncard state.source.2.2 ≤ budget ∧ ¬Sampling.TargetCacheExceptional state.source.2.2)
noncomputable def proposalModel (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction State DigestSampling.IndexBuckets where
  Outcome := Outcome
  record := interactionRecord published
  response := response
  advance := advance
  label := label
  active := active budget
  base := PMF.uniformOfFintype DigestSampling.IndexBuckets
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state hactive point
    cases input with
    | inl input => simp [active] at hactive
    | inr request =>
        change decide (_ ∧ _ ∧ _ ∧ _)=true at hactive
        obtain ⟨hfresh,hfinite,hsize,hclean⟩ := of_decide_eq_true hactive
        exact recordLaw_scaled_cap published request state hfresh hfinite budget hsize hbudget hclean point
theorem proposal_query_erasure (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : Interaction.Domain) (state : State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (run (interactionSource published input) state) : PMF (Interaction.Range input × State)) := by
  cases input with
  | inl input =>
      change (fun result : SphincsSecurity.OracleWorld.Range input × State => (result.1,result.2)) <$>
        (liftM (run (forwardWorld input) state) : PMF _)=_
      change id <$> (liftM (run (forwardWorld input) state) : PMF _)=_
      rw [id_map]
      rfl
  | inr request => exact recordLaw_erasure published request state
theorem proposal_execution_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α) (state : State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (run (simulateQ (interactionSource published) program) state) : PMF (α × State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (run (simulateQ (interactionSource published) program) state) : PMF (α × State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
theorem logged_source {α : Type} (published : T3.Cache) (program : OracleComp Interaction α) :
    simulateQ (interactionSource published) (ProposalOverflow.logged program)=
      FullGame.loggedWith (FullGame.authenticatedSign published) program := by
  rw [ProposalOverflow.logged,QueryImpl.simulateQ_writerTMapBase_run]
  unfold FullGame.loggedWith
  congr 2
  funext input
  cases input <;>
    simp [QueryImpl.writerTMapBase,ProposalOverflow.logging,QueryImpl.withTraceAppend_apply,
      ProposalOverflow.logFragment,interactionSource]
  · rfl
  · apply WriterT.ext
    simp
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ProposalOverflow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem signing_trace_overflow {Result : Type} (published : T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction Result) (state : State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (proposalModel published budget hbudget)).traced program).run ([],0,state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 :=
  full_trace_overflow_bound (proposalModel published budget hbudget) rfl program state
theorem signing_count_le_fragment (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : List DigestSampling.IndexBuckets × (Nat × State))
    (result : LazyPrivate.Interaction.Range input × (List DigestSampling.IndexBuckets × (Nat × State)))
    (hr : result ∈ (((counted (proposalModel published budget hbudget)).traced input).run state).support) :
    result.2.2.1 ≤ state.2.1 + (logFragment input result.1).length := by
  rw [counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [proposalModel, active, logFragment]
  | inr request => simp only [logFragment, List.length_singleton]; split <;> omega
theorem signing_count_le_log {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × State))
    (result : (Result × QueryLog Requests) × (List DigestSampling.IndexBuckets × (Nat × State)))
    (hr : result ∈ ((simulateQ (counted (proposalModel published budget hbudget)).traced
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
      have hstep := signing_count_le_fragment published budget hbudget input state middle hm
      rw [simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨last, hl, hr⟩ := hr
      have hrest := ih middle.1 middle.2 last hl
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      simp only [List.length_append]
      omega
theorem signing_log_overflow {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (counted (proposalModel published budget hbudget)).traced
        (logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow published budget hbudget (logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (counted (proposalModel published budget hbudget)).traced
      (logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log published budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (counted (proposalModel published budget hbudget)).traced
        (logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]
theorem source_proposal_overflow {Result : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp LazyPrivate.Interaction Result) (state : State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (proposalModel published budget hbudget).traced (logged program)).run ([],state)] ≤
      (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← counted_trace_erasure (proposalModel published budget hbudget) (logged program) ([],0,state),
    probEvent_map]
  exact signing_log_overflow published budget hbudget program state
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × State) :=
  run (FullGame.idealGame adversary) ⟨(0,∅,∅),false⟩
theorem experiment_erasure (adversary : Adversary) :
    Prod.map id State.source <$> experiment adversary=CountedPrivate.experiment adversary :=
  run_erasure (FullGame.idealGame adversary) ⟨(0,∅,∅),false⟩
theorem experiment_event (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | CountedPrivate.experiment adversary] := by
  rw [← experiment_erasure adversary,probEvent_map]
  rfl
theorem real_to_monitored_ideal (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact CountedPrivate.real_to_counted_ideal adversary q hq
abbrev History := List DigestSampling.IndexBuckets
noncomputable def tracedExperiment (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (History × State)) := do
  let generated ← (liftM (run keygen ⟨(0,∅,∅),false⟩) : PMF _)
  let interaction ← (simulateQ (proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (FullGame.verdict generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem tracedExperiment_erasure (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment adversary budget hbudget=
      (liftM (experiment adversary) : PMF (Bool × State)) := by
  unfold tracedExperiment experiment FullGame.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem tracedExperiment_event (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment adversary q hq]=
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment adversary] := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | law]) (tracedExperiment_erasure adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq] at h
  calc
    _ = Pr[fun result => result.1=true ∧ result.2.source.1≤q | (liftM (experiment adversary) : PMF _)] := h
    _ = _ := by
      simp only [probEvent_eq_tsum_ite]
      rfl
theorem real_to_traced (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment adversary q hq]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [tracedExperiment_event]
  exact real_to_monitored_ideal adversary q (hq.trans_lt (by norm_num))
theorem verdict_success_log (publicKey : Digest) (interaction : Option Forgery × QueryLog Requests)
    (state : State) (result : Bool × State)
    (hr : result ∈ support (run (FullGame.verdict publicKey interaction) state))
    (hwin : result.1=true) : interaction.2.length≤2^32 := by
  unfold FullGame.verdict at hr
  cases ho : interaction.1 with
  | none =>
      simp only [ho,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [ho,run_bind,mem_support_bind_iff,run_pure,support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,_,rfl⟩ := hr
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hwin
      exact hwin.1
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem winning_trace_overflow (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      tracedExperiment adversary budget hbudget] ≤ (2 : ENNReal)⁻¹^700 := by
  rw [← expectedValue_ite_one]
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  change expectedValue (run keygen ⟨(0,∅,∅),false⟩) _ ≤ _
  apply expectedValue_le_of_support
  intro generated _
  apply le_trans ?_ (source_proposal_overflow generated.1.2 budget hbudget
    (adversary generated.1.1 generated.1.2) generated.2)
  rw [← expectedValue_ite_one]
  apply expectedValue_mono
  intro interaction
  change expectedValue (run (FullGame.verdict generated.1.1 interaction.1) interaction.2.2)
    (fun checked => if checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length then 1 else 0) ≤ _
  apply expectedValue_le_of_support
  intro checked hchecked
  by_cases h : checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length
  · have hl := verdict_success_log generated.1.1 interaction.1 interaction.2.2 checked hchecked h.1
    simp only [h,if_true,show interaction.1.2.length≤2^32 ∧
      BPORS.Numeric.proposalLength < interaction.2.1.length from ⟨hl,h.2⟩,le_refl]
  · simp only [h,if_false,zero_le]
theorem split_winning_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment adversary q hq]+
      Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
        tracedExperiment adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q
  · by_cases hn : result.2.1.length≤BPORS.Numeric.proposalLength
    · simp [hw,hw.1,hw.2,hn,Nat.not_lt.mpr hn]
    · simp [hw,hw.1,hw.2,hn,Nat.lt_of_not_ge hn]
  · simp only [hw,if_false,zero_le]
theorem real_to_bounded_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment adversary q hq]+
        (2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_traced adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  exact (split_winning_trace adversary q hq).trans
    (add_le_add le_rfl (winning_trace_overflow adversary q hq))
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem event_lift {α : Type} (program : ProbComp α) (predicate : α → Prop) :
    Pr[predicate | (liftM program : PMF α)]=Pr[predicate | program] := by
  simp only [probEvent_eq_tsum_ite]
  rfl
theorem experiment_exception_bound (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | experiment adversary] ≤
      q/(2 : ENNReal)^146 := by
  exact gate6_run_empty_linear_charge (FullGame.idealGame adversary) q 146 hq (by decide)
theorem traced_exception_bound (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
      tracedExperiment adversary q hq] ≤ q/(2 : ENNReal)^146 := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | law])
    (tracedExperiment_erasure adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq,event_lift] at h
  rw [h]
  exact experiment_exception_bound adversary q hq
theorem split_bounded_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
      result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment adversary q hq]+
      Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
        tracedExperiment adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q ∧ result.2.1.length≤BPORS.Numeric.proposalLength
  · cases hb : result.2.2.exceptional <;> simp [hw,hw.2.1,hb]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_bounded_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_bounded_trace adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  apply add_le_add_left
  exact (split_bounded_trace adversary q hq).trans
    (add_le_add le_rfl (traced_exception_bound adversary q hq))
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] BPORS.History.fullPrice BPORS.History.fullNearPrice
theorem full_game_excess_price (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice result.2.1-1 else 0) ≤ 11324/100000000 := by
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  apply expectedValue_le_of_le
  intro generated
  apply le_trans ?_ (BPORS.History.adaptive_selected_full_excess
    (proposalModel generated.1.2 budget hbudget) rfl
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) generated.2
    (fun result => result.2.1) (fun _ => List.Sublist.refl _))
  apply expectedValue_mono
  intro interaction
  exact expectedValue_le_of_le _ (fun _ => le_rfl)
theorem full_game_near_price (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice result.2.1 else 0) ≤ 404 := by
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  apply expectedValue_le_of_le
  intro generated
  apply le_trans ?_ (BPORS.History.adaptive_selected_near_price
    (proposalModel generated.1.2 budget hbudget) rfl
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) generated.2
    (fun result => result.2.1) (fun _ => List.Sublist.refl _))
  apply expectedValue_mono
  intro interaction
  exact expectedValue_le_of_le _ (fun _ => le_rfl)
theorem full_game_selected_excess (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) (selected : Bool × (History × State) → History)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice (selected result)-1 else 0) ≤ 11324/100000000 := by
  apply le_trans ?_ (full_game_excess_price adversary budget hbudget)
  apply expectedValue_mono
  intro result
  split_ifs
  · exact tsub_le_tsub_right (BPORS.History.fullPrice_sublist (hselected result)) 1
  · exact le_rfl
theorem full_game_selected_near (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) (selected : Bool × (History × State) → History)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice (selected result) else 0) ≤ 404 := by
  apply le_trans ?_ (full_game_near_price adversary budget hbudget)
  apply expectedValue_mono
  intro result
  split_ifs
  · exact BPORS.History.fullNearPrice_sublist (hselected result)
  · exact le_rfl
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem traced_query_record {ι State Label : Type} {spec : OracleSpec ι}
    (model : ProposalModel spec State Label) (input : spec.Domain)
    (before : List Label × State) (result : spec.Range input × (List Label × State))
    (hr : result ∈ ((model.traced input).run before).support) :
    ∃ record,record ∈ (model.record input before.2).support ∧
      result.1=model.response input record ∧ result.2.2=model.advance input before.2 record ∧
      before.1.Sublist result.2.1 ∧
      (model.active input before.2=true → model.label input record ∈ result.2.1) := by
  simp only [traced,proposalRecordImpl,StateT.run_mk] at hr
  by_cases ha : model.active input before.2=true
  · rw [if_pos ha,PMF.mem_support_map_iff] at hr
    obtain ⟨source,hs,rfl⟩ := hr
    have ho := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source,hs,rfl⟩
    rw [recordProposalBridge_record] at ho
    refine ⟨source.2,ho,rfl,rfl,?_,?_⟩
    · exact (List.sublist_append_left before.1 source.1).trans
        (List.sublist_append_left (before.1++source.1) [model.label input source.2])
    · intro _
      simp
  · rw [if_neg ha,PMF.mem_support_map_iff] at hr
    obtain ⟨record,ho,rfl⟩ := hr
    exact ⟨record,ho,rfl,rfl,List.Sublist.refl _,fun h => False.elim (ha h)⟩
theorem traced_history_extends {ι State Label α : Type} {spec : OracleSpec ι}
    (model : ProposalModel spec State Label) (program : OracleComp spec α)
    (before : List Label × State) (result : α × (List Label × State))
    (hr : result ∈ ((simulateQ model.traced program).run before).support) :
    before.1.Sublist result.2.1 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [simulateQ_pure,StateT.run_pure,PMF.monad_pure_eq_pure,PMF.mem_support_pure_iff] at hr
      subst result
      exact List.Sublist.refl _
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      obtain ⟨_,_,_,_,hprefix,_⟩ := traced_query_record model input before middle hm
      exact hprefix.trans (ih middle.1 middle.2 result hr)
end SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem pmf_support {α : Type} (program : ProbComp α) :
    (liftM program : PMF α).support=support program := by
  ext value
  rw [PMF.mem_support_iff,← PMF.probOutput_eq_apply,mem_support_iff]
  rfl
theorem recordLaw_support (published : T3.Cache) (request : Request) (state : State)
    (record : ((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)
    (hr : record ∈ (recordLaw published request state).support) :
    record.1 ∈ support (run (FullGame.authenticatedRecord published request) state) ∧
      ∀ output,record.1.1.2=some output → record.2=(DigestSampling.samplingData output).1 := by
  change record ∈ (liftM (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state)) : PMF _).support at hr
  rw [pmf_support,Sampling.completeRecord,mem_support_bind_iff] at hr
  obtain ⟨source,hs,hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨point,hp,hr⟩ := hr
  rw [support_pure,Set.mem_singleton_iff] at hr
  subst record
  refine ⟨hs,?_⟩
  intro output houtput
  rw [Sampling.completeLabel,houtput,Option.elim_some,support_pure,Set.mem_singleton_iff] at hp
  exact hp
theorem active_request_record (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (request : Request) (before : History × State)
    (ha : active budget (.inr request) before.2=true)
    (result : Option Signature × (History × State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced (.inr request)).run before).support) :
    ∃ observed : (Option Signature × Option HashOutput) × State,
      observed ∈ support (run (FullGame.authenticatedRecord published request) before.2) ∧
      observed.1.1=result.1 ∧ observed.2=result.2.2 ∧
      ∀ output,observed.1.2=some output → (DigestSampling.samplingData output).1 ∈ result.2.1 := by
  obtain ⟨record,ho,hresponse,hstate,_,hlabel⟩ :=
    BPORS.Adaptive.ProposalModel.traced_query_record (proposalModel published budget hbudget)
      (.inr request) before result hr
  have hsource := recordLaw_support published request before.2 record ho
  refine ⟨record.1,hsource.1,hresponse.symm,hstate.symm,?_⟩
  intro output houtput
  have hp := hlabel ha
  change record.2 ∈ result.2.1 at hp
  rw [hsource.2 output houtput] at hp
  exact hp
theorem empty_cache_clean : ¬Sampling.TargetCacheExceptional ∅ := by
  intro h
  have hp := Sampling.targetCacheExceptional_moment ∅ h
  rw [Sampling.allTargetMoment_empty] at hp
  norm_num at hp
theorem initial_coherent : Coherent ⟨(0,∅,∅),false⟩ := by
  intro h
  exact False.elim (empty_cache_clean h)
theorem clean_before_of_clean_after {α : Type} (program : M α) (before : State)
    (hc : Coherent before) (result : α × State) (hr : result ∈ support (run program before))
    (hflag : result.2.exceptional=false) : ¬Sampling.TargetCacheExceptional before.source.2.2 := by
  intro hbad
  have hh := run_flag_monotone program before (hc hbad) result hr
  rw [hflag] at hh
  contradiction
theorem first_request_active {α : Type} (message : Message) (cache : T3.Cache)
    (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩))
    (program : OracleComp Interaction α) (result : (α × QueryLog Requests) × State)
    (hr : result ∈ support (run
      (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2) program) generated.2))
    (hlog : CountedPrivate.NoPublishedRequest generated.1.2 message result.1.2)
    (budget : Nat) (hcount : result.2.source.1≤budget) (hflag : result.2.exceptional=false) :
    active budget (.inr ⟨message,cache⟩) result.2=true := by
  have hgen := run_coherent keygen ⟨(0,∅,∅),false⟩ initial_coherent generated hg
  have hc := run_coherent _ generated.2 hgen result hr
  have hclean : ¬Sampling.TargetCacheExceptional result.2.source.2.2 := by
    intro hbad
    have hh := hc hbad
    rw [hflag] at hh
    contradiction
  exact CountedPrivate.first_published_request_active message cache
    (generated.1,generated.2.source) (run_project_support keygen ⟨(0,∅,∅),false⟩ generated hg)
    program (result.1,result.2.source) (run_project_support _ generated.2 result hr)
    hlog budget hcount hclean
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
abbrev WellFormed (state : State) := CountedPrivate.WellFormed state.source
theorem run_lazy_support {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) :
    (result.1,result.2.source.2) ∈ support (LazyPrivate.run program before.source.2) :=
  CountedPrivate.run_project_support program before.source (result.1,result.2.source)
    (run_project_support program before result hr)
theorem run_extends {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) :
    SourceReplay.Extends before.source.2 result.2.source.2 :=
  SourceReplay.run_extends program before.source.2 (result.1,result.2.source.2)
    (run_lazy_support program before result hr)
theorem run_wellFormed {α : Type} (program : M α) (before : State) (hw : WellFormed before)
    (result : α × State) (hr : result ∈ support (run program before)) : WellFormed result.2 :=
  CountedPrivate.run_wellFormed program before.source hw (result.1,result.2.source)
    (run_project_support program before result hr)
theorem run_count_monotone {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) : before.source.1 ≤ result.2.source.1 :=
  CountedPrivate.count_monotone program before.source (result.1,result.2.source)
    (run_project_support program before result hr)
theorem run_nonce_preserves {α : Type} (message : Message) (program : M α)
    (havoid : NonceFreshness.Avoids message program) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) :
    result.2.source.2.1 (.inr (.inl message))=before.source.2.1 (.inr (.inl message)) :=
  CountedPrivate.run_nonce_preserves message program havoid before.source
    (result.1,result.2.source) (run_project_support program before result hr)
theorem authenticatedRecord_avoids (message : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache≠published ∨ request.message≠message) :
    NonceFreshness.Avoids message (FullGame.authenticatedRecord published request) := by
  apply (SourceQueries.map_allowed_iff (fun input => input≠NonceFreshness.nonceQuery message)
    Prod.fst _).mp
  rw [FullGame.authenticatedRecord_erasure]
  exact CountedPrivate.authenticatedSign_avoids message published request hrequest
def Covered (published : T3.Cache) (history : History) (state : State) (message : Message) : Prop :=
  state.source.2.1 (.inr (.inl message))=none ∨
    ∃ record : Option Signature × Option HashOutput,
      SourceReplay.Resolves state.source.2 (FullGame.authenticatedRecord published ⟨message,published⟩) record ∧
      ∀ output,record.2=some output → (DigestSampling.samplingData output).1 ∈ history
def Covers (published : T3.Cache) (history : History) (state : State) : Prop :=
  ∀ message,Covered published history state message
theorem covered_preserves (published : T3.Cache) (beforeHistory afterHistory : History)
    (before after : State) (message : Message)
    (hc : Covered published beforeHistory before message)
    (hext : SourceReplay.Extends before.source.2 after.source.2)
    (hh : beforeHistory.Sublist afterHistory)
    (hfresh : before.source.2.1 (.inr (.inl message))=none →
      after.source.2.1 (.inr (.inl message))=none) :
    Covered published afterHistory after message := by
  rcases hc with hf | ⟨record,hr,hlabel⟩
  · exact Or.inl (hfresh hf)
  · exact Or.inr ⟨record,hr.mono hext,fun output ho => hh.subset (hlabel output ho)⟩
theorem covers_keygen (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) :
    Covers generated.1.2 [] generated.2 := by
  intro message
  exact Or.inl (CountedPrivate.counted_keygen_nonce_fresh message
    (generated.1,generated.2.source) (run_project_support keygen ⟨(0,∅,∅),false⟩ generated hg))
theorem fresh_active (published : T3.Cache) (budget : Nat) (request : Request) (state : State)
    (hw : WellFormed state) (hc : Coherent state) (hflag : state.exceptional=false)
    (hcount : state.source.1≤budget) (hfresh : state.source.2.1 (.inr (.inl request.message))=none) :
    active budget (.inr request) state=true := by
  change CountedPrivate.active budget (.inr request) state.source=true
  apply (CountedPrivate.active_iff_fresh_clean request state.source hw budget hcount).mpr
  refine ⟨hfresh,?_⟩
  intro hb
  have hh := hc hb
  rw [hflag] at hh
  contradiction
theorem traced_query_covers (published : T3.Cache) (budget : Nat) (hbudget : budget≤2^127)
    (input : Interaction.Domain) (before : History × State)
    (hcover : Covers published before.1 before.2) (hw : WellFormed before.2)
    (hc : Coherent before.2) (hflag : before.2.exceptional=false) (hcount : before.2.source.1≤budget)
    (result : Interaction.Range input × (History × State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced input).run before).support) :
    Covers published result.2.1 result.2.2 := by
  obtain ⟨record,ho,hresponse,hstate,hh,hlabel⟩ :=
    BPORS.Adaptive.ProposalModel.traced_query_record (proposalModel published budget hbudget)
      input before result hr
  cases input with
  | inl input =>
      change record ∈ (liftM (run (forwardWorld input) before.2) : PMF _).support at ho
      rw [pmf_support] at ho
      change result.2.2=record.2 at hstate
      intro message
      have hext := run_extends _ before.2 record ho
      have hnonce := run_nonce_preserves message _
        (CountedPrivate.forwardWorld_avoids message input) before.2 record ho
      rw [hstate]
      exact covered_preserves published before.1 result.2.1 before.2 record.2 message
        (hcover message) hext hh (fun hf => hnonce.trans hf)
  | inr request =>
      have hsource := recordLaw_support published request before.2 record ho
      have hext := run_extends _ before.2 record.1 hsource.1
      change result.2.2=record.1.2 at hstate
      intro message
      by_cases hsame : request.cache=published ∧ request.message=message
      · rcases hcover message with hf | ⟨old,hresolve,oldLabels⟩
        · have hactive := fresh_active published budget request before.2 hw hc hflag hcount
            (by rw [hsame.2]; exact hf)
          have hresolved := SourceReplay.resolves_of_run (FullGame.authenticatedRecord published request)
            (CountedPrivate.authenticatedRecord_hashOnly published request) before.2.source.2
            (record.1.1,record.1.2.source.2)
            (run_lazy_support _ before.2 record.1 hsource.1)
          have hreq : request=⟨message,published⟩ := by
            cases request
            simp_all
          rw [hstate]
          apply Or.inr
          refine ⟨record.1.1,?_,?_⟩
          · simpa only [hreq] using hresolved
          · intro output houtput
            have hp := hlabel hactive
            change record.2 ∈ result.2.1 at hp
            rw [hsource.2 output houtput] at hp
            exact hp
        · rw [hstate]
          exact Or.inr ⟨old,hresolve.mono hext,fun output ho => hh.subset (oldLabels output ho)⟩
      · have hdiff : request.cache≠published ∨ request.message≠message := by tauto
        have hn := run_nonce_preserves message _ (authenticatedRecord_avoids message published request hdiff)
          before.2 record.1 hsource.1
        rw [hstate]
        exact covered_preserves published before.1 result.2.1 before.2 record.1.2 message
          (hcover message) hext hh (fun hf => hn.trans hf)
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem traced_source_support {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (program : OracleComp Interaction α)
    (before : History × State) (result : α × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel published budget hbudget).traced program).run before).support) :
    (result.1,result.2.2) ∈ support (run (simulateQ (interactionSource published) program) before.2) := by
  rw [← pmf_support,← proposal_trace_erasure published budget hbudget program before.1 before.2]
  rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff]
  exact ⟨result,hr,rfl⟩
theorem traced_query_source_support (published : T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (input : Interaction.Domain)
    (before : History × State) (result : Interaction.Range input × (History × State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced input).run before).support) :
    (result.1,result.2.2) ∈ support (run (interactionSource published input) before.2) := by
  simpa only [simulateQ_spec_query] using
    traced_source_support published budget hbudget (liftM (Interaction.query input)) before result
      (by simpa only [simulateQ_spec_query] using hr)
theorem run_false_before {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) (hflag : result.2.exceptional=false) :
    before.exceptional=false := by
  cases hb : before.exceptional with
  | false => rfl
  | true =>
      have h := run_flag_monotone program before hb result hr
      rw [hflag] at h
      contradiction
theorem traced_covers {α : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (before : History × State)
    (hcover : Covers published before.1 before.2) (hw : WellFormed before.2) (hc : Coherent before.2)
    (result : α × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel published budget hbudget).traced program).run before).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    Covers published result.2.1 result.2.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [simulateQ_pure,StateT.run_pure,PMF.monad_pure_eq_pure,PMF.mem_support_pure_iff] at hr
      subst result
      exact hcover
  | query_bind input next ih =>
      have hsource := traced_source_support published budget hbudget _ before result hr
      have hbefore := run_false_before _ before.2 (result.1,result.2.2) hsource hflag
      have hbound := (run_count_monotone _ before.2 (result.1,result.2.2) hsource).trans hcount
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      have hstep := traced_query_source_support published budget hbudget input before middle hm
      have hmCover := traced_query_covers published budget hbudget input before hcover hw hc hbefore hbound middle hm
      exact ih middle.1 middle.2 hmCover (run_wellFormed _ before.2 hw (middle.1,middle.2.2) hstep)
        (run_coherent _ before.2 hc (middle.1,middle.2.2) hstep) result hr hcount hflag
theorem actual_interaction_covers {α : Type} (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (result : α × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel generated.1.2 budget hbudget).traced program).run
      ([],generated.2)).support) (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    Covers generated.1.2 result.2.1 result.2.2 :=
  traced_covers generated.1.2 budget hbudget program ([],generated.2) (covers_keygen generated hg)
    (run_wellFormed keygen ⟨(0,∅,∅),false⟩ CountedPrivate.initial_wellFormed generated hg)
    (run_coherent keygen ⟨(0,∅,∅),false⟩ initial_coherent generated hg) result hr hcount hflag
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.SourceReplay
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def answers (state : LazyPrivate.State) : Correctness.Answers
  | .inl (.inl n) => (⟨0,Nat.zero_lt_succ n⟩ : Fin (n+1))
  | .inl (.inr input) => (state.2 input).getD 0
  | .inr coordinate => (state.1 coordinate).getD 0
theorem answers_known (state : LazyPrivate.State) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) (h : known state input=some answer) : answers state input=answer := by
  cases input with
  | inl input =>
      cases input with
      | inl input => cases h
      | inr input =>
          change state.2 input=some answer at h
          change (state.2 input).getD (0 : HashOutput)=answer
          rw [h,Option.getD_some]
  | inr coordinate =>
      change state.1 coordinate=some answer at h
      change (state.1 coordinate).getD (0 : HashOutput)=answer
      rw [h,Option.getD_some]
theorem Resolves.eval {α : Type} {state : LazyPrivate.State} {program : M α} {value : α}
    (h : Resolves state program value) (oracleAnswers : Correctness.Answers)
    (hagrees : ∀ input answer,known state input=some answer → oracleAnswers input=answer) :
    evalWithAnswerFn oracleAnswers program=value := by
  induction h with
  | pure value => rfl
  | query input answer hanswer next value _ ih =>
      rw [evalWithAnswerFn_bind]
      change evalWithAnswerFn oracleAnswers (next (simulateQ oracleAnswers (liftM (T3.Spec.query input))))=value
      rw [simulateQ_spec_query,hagrees input answer hanswer]
      exact ih
theorem Resolves.value_unique {α : Type} {state : LazyPrivate.State} {program : M α}
    {value other : α} (h : Resolves state program value) (ho : Resolves state program other) : value=other :=
  (h.eval (answers state) (answers_known state)).symm.trans
    (ho.eval (answers state) (answers_known state))
theorem supported_eval {α : Type} (program : M α) (hhash : HashOnly program)
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run program before)) :
    evalWithAnswerFn (answers result.2) program=result.1 :=
  (resolves_of_run program hhash before result hr).eval _ (answers_known result.2)
end SigGolfCandidate.T3.Security.SourceReplay
namespace SigGolfCandidate.T3.Security.SigningRecords
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem payloadRecord_has_digest (answers : Correctness.Answers) (cache : T3.Cache) (message : Message)
    (hs : (evalWithAnswerFn answers (payloadRecord cache message)).1≠none) :
    (evalWithAnswerFn answers (payloadRecord cache message)).2≠none := by
  unfold payloadRecord at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs ⊢
  exact payloadRecord_success_has_digest answers cache _ message hs
theorem authenticatedRecord_success (answers : Correctness.Answers) (published : T3.Cache)
    (request : Request) (hs : (evalWithAnswerFn answers (FullGame.authenticatedRecord published request)).1≠none) :
    request.cache=published ∧ (evalWithAnswerFn answers (FullGame.authenticatedRecord published request)).2≠none := by
  unfold FullGame.authenticatedRecord at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs ⊢
  by_cases hcache : request.cache=published
  · simp only [if_pos hcache] at hs ⊢
    exact ⟨hcache,payloadRecord_has_digest answers request.cache request.message hs⟩
  · simp only [if_neg hcache,evalWithAnswerFn_pure,ne_eq,not_true_eq_false] at hs
theorem authenticatedRecord_selected_valid (answers : Correctness.Answers) (published : T3.Cache)
    (request : Request) (output : HashOutput)
    (ho : (evalWithAnswerFn answers (FullGame.authenticatedRecord published request)).2=some output) :
    request.cache=published ∧ admissible (selections output)=true := by
  unfold FullGame.authenticatedRecord at ho
  simp only [evalWithAnswerFn_bind] at ho
  by_cases hcache : request.cache=published
  · simp only [if_pos hcache,payloadRecord,evalWithAnswerFn_bind] at ho
    exact ⟨hcache,(payloadRecord_selected_valid answers request.cache _ request.message output ho).choose_spec.2⟩
  · simp only [if_neg hcache,evalWithAnswerFn_pure,reduceCtorEq] at ho
end SigGolfCandidate.T3.Security.SigningRecords
end
section
namespace SigGolfCandidate.T3.Security.SourceReplay
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem privateNonce_caches (message : Message) (before : LazyPrivate.State)
    (result : Digest × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (privateNonce message) before)) :
    ∃ output,result.2.1 (.inr (.inl message))=some output := by
  rw [privateNonce,LazyPrivate.run_bind,mem_support_bind_iff] at hr
  obtain ⟨answer,ha,hr⟩ := hr
  rw [LazyPrivate.run_pure,support_pure,Set.mem_singleton_iff] at hr
  subst result
  exact ⟨answer.1,hash_query_caches (NonceFreshness.nonceQuery message) trivial before answer ha⟩
theorem authenticatedRecord_nonce_used (published : T3.Cache) (request : Request)
    (hcache : request.cache=published) (before : LazyPrivate.State)
    (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) before)) :
    ∃ output,result.2.1 (.inr (.inl request.message))=some output := by
  unfold FullGame.authenticatedRecord at hr
  rw [LazyPrivate.run_bind,mem_support_bind_iff] at hr
  obtain ⟨mac,_,hr⟩ := hr
  rw [if_pos hcache,payloadRecord,LazyPrivate.run_bind,mem_support_bind_iff] at hr
  obtain ⟨nonce,hn,hr⟩ := hr
  obtain ⟨output,ho⟩ := privateNonce_caches request.message mac.2 nonce hn
  exact ⟨output,(run_extends _ nonce.2 result hr).1 ho⟩
theorem Resolves.success_record {state : LazyPrivate.State} (published : T3.Cache) (request : Request)
    (record : Option Signature × Option HashOutput)
    (hr : Resolves state (FullGame.authenticatedRecord published request) record) (hs : record.1≠none) :
    request.cache=published ∧ record.2≠none ∧
      ∃ output,state.1 (.inr (.inl request.message))=some output := by
  have he := hr.eval (answers state) (answers_known state)
  have hsuccess := SigningRecords.authenticatedRecord_success (answers state) published request
    (by simpa only [he] using hs)
  have hcache := hsuccess.1
  rw [he] at hsuccess
  refine ⟨hcache,hsuccess.2,?_⟩
  exact authenticatedRecord_nonce_used published request hcache state (record,state)
    (by rw [hr.run_eq_pure,support_pure]; exact Set.mem_singleton _)
end SigGolfCandidate.T3.Security.SourceReplay
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem covered_record_label (published : T3.Cache) (history : History) (state : State)
    (hc : Covers published history state) (request : Request) (record : Option Signature × Option HashOutput)
    (hr : SourceReplay.Resolves state.source.2 (FullGame.authenticatedRecord published request) record)
    (hs : record.1≠none) :
    request.cache=published ∧ ∃ output,record.2=some output ∧
      admissible (selections output)=true ∧ (DigestSampling.samplingData output).1 ∈ history := by
  obtain ⟨hcache,hdigest,nonce,hnonce⟩ := hr.success_record published request record hs
  obtain ⟨output,houtput⟩ := Option.ne_none_iff_exists'.mp hdigest
  have he := hr.eval (SourceReplay.answers state.source.2) (SourceReplay.answers_known state.source.2)
  have hadmissible := SigningRecords.authenticatedRecord_selected_valid
    (SourceReplay.answers state.source.2) published request output (by rw [he]; exact houtput)
  refine ⟨hcache,output,houtput,hadmissible.2,?_⟩
  rcases hc request.message with hf | ⟨old,ho,hlabels⟩
  · rw [hf] at hnonce
    contradiction
  · have hreq : request=⟨request.message,published⟩ := by
      cases request
      simp_all
    rw [hreq] at hr
    have heq : old=record := ho.value_unique hr
    exact hlabels output (by rw [heq]; exact houtput)
theorem sign_response_record (published : T3.Cache) (request : Request) (before : State)
    (result : Option Signature × State)
    (hr : result ∈ support (run (FullGame.authenticatedSign published request) before)) :
    ∃ selected,SourceReplay.Resolves result.2.source.2
      (FullGame.authenticatedRecord published request) (result.1,selected) := by
  have he : Prod.map Prod.fst id <$> run (FullGame.authenticatedRecord published request) before=
      run (FullGame.authenticatedSign published request) before := by
    rw [← run_map,FullGame.authenticatedRecord_erasure]
  rw [← he,support_map] at hr
  obtain ⟨observed,ho,rfl⟩ := hr
  exact ⟨observed.1.2,SourceReplay.resolves_of_run _
    (CountedPrivate.authenticatedRecord_hashOnly published request) before.source.2
    (observed.1,observed.2.source.2) (run_lazy_support _ before observed ho)⟩
theorem logged_records_resolve {α : Type} (published : T3.Cache) (program : OracleComp Interaction α)
    (before : State) (result : (α × QueryLog Requests) × State)
    (hr : result ∈ support (run (FullGame.loggedWith (FullGame.authenticatedSign published) program) before)) :
    ∀ entry ∈ result.1.2,∃ selected,SourceReplay.Resolves result.2.source.2
      (FullGame.authenticatedRecord published entry.1) (entry.2,selected) := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FullGame.loggedWith_pure,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [FullGame.loggedWith_world,run_bind,mem_support_bind_iff] at hr
          obtain ⟨middle,_,hr⟩ := hr
          exact ih middle.1 middle.2 result hr
      | inr request =>
          rw [FullGame.loggedWith_request,run_bind,mem_support_bind_iff] at hr
          obtain ⟨middle,hm,hr⟩ := hr
          rw [run_map,support_map] at hr
          obtain ⟨last,hl,rfl⟩ := hr
          intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            obtain ⟨selected,hs⟩ := sign_response_record published request before middle hm
            exact ⟨selected,hs.mono (run_extends _ middle.2 last hl)⟩
          · exact ih middle.1 middle.2 last hl entry he
theorem traced_log_disclosures {α : Type} (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (result : (α × QueryLog Requests) × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel generated.1.2 budget hbudget).traced
      (ProposalOverflow.logged program)).run ([],generated.2)).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∀ entry ∈ result.1.2,entry.2≠none → entry.1.cache=generated.1.2 ∧
      ∃ output,SourceReplay.Resolves result.2.2.source.2
        (FullGame.authenticatedRecord generated.1.2 entry.1) (entry.2,some output) ∧
        admissible (selections output)=true ∧ (DigestSampling.samplingData output).1 ∈ result.2.1 := by
  have hc := actual_interaction_covers generated hg budget hbudget
    (ProposalOverflow.logged program) result hr hcount hflag
  have hsource := traced_source_support generated.1.2 budget hbudget
    (ProposalOverflow.logged program) ([],generated.2) result hr
  rw [logged_source] at hsource
  intro entry he hs
  obtain ⟨selected,hresolve⟩ := logged_records_resolve generated.1.2 program generated.2
    (result.1,result.2.2) hsource entry he
  obtain ⟨hcache,output,houtput,hadmissible,hlabel⟩ :=
    covered_record_label generated.1.2 result.2.1 result.2.2 hc entry.1 (entry.2,selected) hresolve hs
  change selected=some output at houtput
  rw [houtput] at hresolve
  exact ⟨hcache,output,hresolve,hadmissible,hlabel⟩
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem traced_query_record_suffix {ι State Label : Type} {spec : OracleSpec ι}
    (model : ProposalModel spec State Label) (input : spec.Domain)
    (before : List Label × State) (result : spec.Range input × (List Label × State))
    (hr : result ∈ ((model.traced input).run before).support) :
    ∃ record,record ∈ (model.record input before.2).support ∧
      result.1=model.response input record ∧ result.2.2=model.advance input before.2 record ∧
      ∃ added,result.2.1=before.1++added ∧
        (model.active input before.2=true → ∃ extras,added=extras++[model.label input record]) := by
  simp only [traced,proposalRecordImpl,StateT.run_mk] at hr
  by_cases ha : model.active input before.2=true
  · rw [if_pos ha,PMF.mem_support_map_iff] at hr
    obtain ⟨source,hs,rfl⟩ := hr
    have ho := (PMF.mem_support_map_iff Prod.snd _ _).mpr ⟨source,hs,rfl⟩
    rw [recordProposalBridge_record] at ho
    exact ⟨source.2,ho,rfl,rfl,source.1++[model.label input source.2],List.append_assoc ..,
      fun _ => ⟨source.1,rfl⟩⟩
  · rw [if_neg ha,PMF.mem_support_map_iff] at hr
    obtain ⟨record,ho,rfl⟩ := hr
    exact ⟨record,ho,rfl,rfl,[],(List.append_nil _).symm,fun h => False.elim (ha h)⟩
end SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
abbrev JournalEntry := Message × (Option Signature × Option HashOutput)
abbrev Journal := List JournalEntry
def journalLabels (journal : Journal) : History :=
  journal.filterMap fun entry => entry.2.2.map (fun output => (DigestSampling.samplingData output).1)
def JournalOK (published : T3.Cache) (history : History) (state : State) (journal : Journal) : Prop :=
  (journal.map Prod.fst).Nodup ∧
  (∀ entry ∈ journal,SourceReplay.Resolves state.source.2
    (FullGame.authenticatedRecord published ⟨entry.1,published⟩) entry.2) ∧
  (∀ message,state.source.2.1 (.inr (.inl message))=none ∨ message ∈ journal.map Prod.fst) ∧
  (journalLabels journal).Sublist history
theorem journal_keygen (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) :
    JournalOK generated.1.2 [] generated.2 [] := by
  refine ⟨by simp,by simp,?_,List.Sublist.refl _⟩
  intro message
  exact Or.inl (CountedPrivate.counted_keygen_nonce_fresh message
    (generated.1,generated.2.source) (run_project_support keygen ⟨(0,∅,∅),false⟩ generated hg))
theorem journal_used_nonce (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) (message : Message)
    (hm : message ∈ journal.map Prod.fst) :
    ∃ output,state.source.2.1 (.inr (.inl message))=some output := by
  rw [List.mem_map] at hm
  obtain ⟨entry,he,hkey⟩ := hm
  have hr := hj.2.1 entry he
  have hn := SourceReplay.authenticatedRecord_nonce_used published ⟨entry.1,published⟩ rfl state.source.2
    (entry.2,state.source.2) (by rw [hr.run_eq_pure,support_pure]; exact Set.mem_singleton _)
  change entry.1=message at hkey
  rw [hkey] at hn
  exact hn
theorem journal_keeps (published : T3.Cache) (beforeHistory afterHistory : History)
    (before after : State) (journal : Journal) (hj : JournalOK published beforeHistory before journal)
    (hext : SourceReplay.Extends before.source.2 after.source.2)
    (hh : beforeHistory.Sublist afterHistory)
    (hfresh : ∀ message,before.source.2.1 (.inr (.inl message))=none →
      after.source.2.1 (.inr (.inl message))=none ∨ message ∈ journal.map Prod.fst) :
    JournalOK published afterHistory after journal := by
  refine ⟨hj.1,fun entry he => (hj.2.1 entry he).mono hext,?_,hj.2.2.2.trans hh⟩
  intro message
  exact (hj.2.2.1 message).elim (hfresh message) Or.inr
theorem journal_append (published : T3.Cache) (beforeHistory afterHistory : History)
    (before after : State) (journal : Journal) (hj : JournalOK published beforeHistory before journal)
    (hext : SourceReplay.Extends before.source.2 after.source.2)
    (message : Message) (record : Option Signature × Option HashOutput)
    (hfresh : before.source.2.1 (.inr (.inl message))=none)
    (hresolve : SourceReplay.Resolves after.source.2 (FullGame.authenticatedRecord published ⟨message,published⟩) record)
    (hother : ∀ other,other≠message → after.source.2.1 (.inr (.inl other))=before.source.2.1 (.inr (.inl other)))
    (hh : (journalLabels journal++(record.2.toList.map fun output => (DigestSampling.samplingData output).1)).Sublist
      afterHistory) :
    JournalOK published afterHistory after (journal++[(message,record)]) := by
  have hnot : message ∉ journal.map Prod.fst := by
    intro hm
    obtain ⟨output,ho⟩ := journal_used_nonce published beforeHistory before journal hj message hm
    rw [hfresh] at ho
    contradiction
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.map_append,List.map_singleton,List.nodup_append,List.nodup_singleton,true_and,and_true]
    refine ⟨hj.1,?_⟩
    intro a ha b hb hab
    have hbm := List.mem_singleton.mp hb
    apply hnot
    simpa only [hab,hbm] using ha
  · intro entry he
    rcases List.mem_append.mp he with he | he
    · exact (hj.2.1 entry he).mono hext
    · rw [List.mem_singleton] at he
      subst entry
      exact hresolve
  · intro other
    by_cases he : other=message
    · exact Or.inr (by simp [he])
    · rcases hj.2.2.1 other with hf | hm
      · exact Or.inl ((hother other he).trans hf)
      · exact Or.inr (by simp only [List.map_append,List.mem_append]; exact Or.inl hm)
  · cases hd : record.2 <;> simpa [journalLabels,hd] using hh
theorem traced_query_journal (published : T3.Cache) (budget : Nat) (hbudget : budget≤2^127)
    (input : Interaction.Domain) (before : History × State) (journal : Journal)
    (hj : JournalOK published before.1 before.2 journal) (hw : WellFormed before.2)
    (hc : Coherent before.2) (hflag : before.2.exceptional=false) (hcount : before.2.source.1≤budget)
    (result : Interaction.Range input × (History × State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced input).run before).support) :
    ∃ afterJournal,JournalOK published result.2.1 result.2.2 afterJournal := by
  obtain ⟨record,ho,hresponse,hstate,added,hh,hlabel⟩ :=
    BPORS.Adaptive.ProposalModel.traced_query_record_suffix (proposalModel published budget hbudget)
      input before result hr
  have hhistory : before.1.Sublist result.2.1 := by
    rw [hh]
    exact List.sublist_append_left before.1 added
  cases input with
  | inl input =>
      change record ∈ (liftM (run (forwardWorld input) before.2) : PMF _).support at ho
      rw [pmf_support] at ho
      change result.2.2=record.2 at hstate
      rw [hstate]
      refine ⟨journal,journal_keeps published before.1 result.2.1 before.2 record.2 journal hj
        (run_extends _ before.2 record ho) hhistory ?_⟩
      intro message hf
      exact Or.inl ((run_nonce_preserves message _ (CountedPrivate.forwardWorld_avoids message input)
        before.2 record ho).trans hf)
  | inr request =>
      have hsource := recordLaw_support published request before.2 record ho
      have hext := run_extends _ before.2 record.1 hsource.1
      change result.2.2=record.1.2 at hstate
      by_cases hcache : request.cache=published
      · by_cases hfresh : before.2.source.2.1 (.inr (.inl request.message))=none
        · have ha := fresh_active published budget request before.2 hw hc hflag hcount hfresh
          obtain ⟨extras,hprefix⟩ := hlabel ha
          have hres := SourceReplay.resolves_of_run (FullGame.authenticatedRecord published request)
            (CountedPrivate.authenticatedRecord_hashOnly published request) before.2.source.2
            (record.1.1,record.1.2.source.2) (run_lazy_support _ before.2 record.1 hsource.1)
          have hreq : request=⟨request.message,published⟩ := by cases request; simp_all
          have hn : ∀ other,other≠request.message →
              record.1.2.source.2.1 (.inr (.inl other))=before.2.source.2.1 (.inr (.inl other)) := by
            intro other hother
            exact run_nonce_preserves other _
              (authenticatedRecord_avoids other published request (Or.inr hother.symm)) before.2 record.1 hsource.1
          have hsub : (journalLabels journal++(record.1.1.2.toList.map
              fun output => (DigestSampling.samplingData output).1)).Sublist result.2.1 := by
            rw [hh,hprefix]
            cases hd : record.1.1.2 with
            | none => simpa only [Option.toList_none,List.map_nil,List.append_nil] using
                hj.2.2.2.trans (List.sublist_append_left before.1 (extras++[(proposalModel published budget hbudget).label (.inr request) record]))
            | some output =>
                have he := hsource.2 output hd
                change record.2=(DigestSampling.samplingData output).1 at he
                change (journalLabels journal++[ (DigestSampling.samplingData output).1 ]).Sublist
                  (before.1++(extras++[record.2]))
                rw [← he,← List.append_assoc]
                exact (hj.2.2.2.trans (List.sublist_append_left before.1 extras)).append (List.Sublist.refl _)
          rw [hreq] at hres
          rw [hstate]
          exact ⟨journal++[(request.message,record.1.1)],journal_append published before.1 result.2.1 before.2
            record.1.2 journal hj hext request.message record.1.1 hfresh hres hn hsub⟩
        · rw [hstate]
          refine ⟨journal,journal_keeps published before.1 result.2.1 before.2 record.1.2 journal hj hext hhistory ?_⟩
          intro message hf
          by_cases he : message=request.message
          · exact Or.inr (by rw [he]; exact (hj.2.2.1 request.message).resolve_left hfresh)
          · exact Or.inl ((run_nonce_preserves message _
              (authenticatedRecord_avoids message published request (Or.inr (fun h => he h.symm)))
                before.2 record.1 hsource.1).trans hf)
      · rw [hstate]
        refine ⟨journal,journal_keeps published before.1 result.2.1 before.2 record.1.2 journal hj hext hhistory ?_⟩
        intro message hf
        exact Or.inl ((run_nonce_preserves message _
          (authenticatedRecord_avoids message published request (Or.inl hcache))
            before.2 record.1 hsource.1).trans hf)
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem traced_journal {α : Type} (published : T3.Cache) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (before : History × State) (journal : Journal)
    (hj : JournalOK published before.1 before.2 journal) (hw : WellFormed before.2) (hc : Coherent before.2)
    (result : α × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel published budget hbudget).traced program).run before).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∃ afterJournal,JournalOK published result.2.1 result.2.2 afterJournal := by
  induction program using OracleComp.inductionOn generalizing before result journal with
  | pure value =>
      rw [simulateQ_pure,StateT.run_pure,PMF.monad_pure_eq_pure,PMF.mem_support_pure_iff] at hr
      subst result
      exact ⟨journal,hj⟩
  | query_bind input next ih =>
      have hsource := traced_source_support published budget hbudget _ before result hr
      have hbefore := run_false_before _ before.2 (result.1,result.2.2) hsource hflag
      have hbound := (run_count_monotone _ before.2 (result.1,result.2.2) hsource).trans hcount
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,PMF.monad_bind_eq_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      have hstep := traced_query_source_support published budget hbudget input before middle hm
      obtain ⟨middleJournal,hmJournal⟩ :=
        traced_query_journal published budget hbudget input before journal hj hw hc hbefore hbound middle hm
      exact ih middle.1 middle.2 middleJournal hmJournal
        (run_wellFormed _ before.2 hw (middle.1,middle.2.2) hstep)
        (run_coherent _ before.2 hc (middle.1,middle.2.2) hstep) result hr hcount hflag
theorem actual_interaction_journal {α : Type} (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (result : α × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel generated.1.2 budget hbudget).traced program).run
      ([],generated.2)).support) (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∃ journal,JournalOK generated.1.2 result.2.1 result.2.2 journal :=
  traced_journal generated.1.2 budget hbudget program ([],generated.2) [] (journal_keygen generated hg)
    (run_wellFormed keygen ⟨(0,∅,∅),false⟩ CountedPrivate.initial_wellFormed generated hg)
    (run_coherent keygen ⟨(0,∅,∅),false⟩ initial_coherent generated hg) result hr hcount hflag
theorem journal_contains_success (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) (request : Request)
    (record : Option Signature × Option HashOutput)
    (hr : SourceReplay.Resolves state.source.2 (FullGame.authenticatedRecord published request) record)
    (hs : record.1≠none) : request.cache=published ∧ (request.message,record) ∈ journal := by
  obtain ⟨hcache,_,nonce,hnonce⟩ := hr.success_record published request record hs
  refine ⟨hcache,?_⟩
  have hused : request.message ∈ journal.map Prod.fst := by
    rcases hj.2.2.1 request.message with hf | hm
    · rw [hf] at hnonce
      contradiction
    · exact hm
  rw [List.mem_map] at hused
  obtain ⟨entry,he,hkey⟩ := hused
  change entry.1=request.message at hkey
  have hres := hj.2.1 entry he
  rw [hkey] at hres
  have hreq : request=⟨request.message,published⟩ := by cases request; simp_all
  rw [hreq] at hr
  have heq := hres.value_unique hr
  have he' : entry=(request.message,record) := Prod.ext hkey heq
  rw [← he']
  exact he
theorem actual_log_journal {α : Type} (generated : (Digest × T3.Cache) × State)
    (hg : generated ∈ support (run keygen ⟨(0,∅,∅),false⟩)) (budget : Nat) (hbudget : budget≤2^127)
    (program : OracleComp Interaction α) (result : (α × QueryLog Requests) × (History × State))
    (hr : result ∈ ((simulateQ (proposalModel generated.1.2 budget hbudget).traced
      (ProposalOverflow.logged program)).run ([],generated.2)).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∃ journal,JournalOK generated.1.2 result.2.1 result.2.2 journal ∧
      ∀ entry ∈ result.1.2,entry.2≠none → entry.1.cache=generated.1.2 ∧
        ∃ output,(entry.1.message,(entry.2,some output)) ∈ journal ∧ admissible (selections output)=true := by
  obtain ⟨journal,hj⟩ := actual_interaction_journal generated hg budget hbudget
    (ProposalOverflow.logged program) result hr hcount hflag
  have hsource := traced_source_support generated.1.2 budget hbudget
    (ProposalOverflow.logged program) ([],generated.2) result hr
  rw [logged_source] at hsource
  refine ⟨journal,hj,?_⟩
  intro entry he hs
  obtain ⟨selected,hresolve⟩ := logged_records_resolve generated.1.2 program generated.2
    (result.1,result.2.2) hsource entry he
  obtain ⟨hcache,hmem⟩ := journal_contains_success generated.1.2 result.2.1 result.2.2 journal hj
    entry.1 (entry.2,selected) hresolve hs
  have hd := (hresolve.success_record generated.1.2 entry.1 (entry.2,selected) hs).2.1
  obtain ⟨output,houtput⟩ := Option.ne_none_iff_exists'.mp hd
  change selected=some output at houtput
  rw [houtput] at hmem hresolve
  have heval := hresolve.eval (SourceReplay.answers result.2.2.source.2)
    (SourceReplay.answers_known result.2.2.source.2)
  exact ⟨hcache,output,hmem,(SigningRecords.authenticatedRecord_selected_valid
    (SourceReplay.answers result.2.2.source.2) generated.1.2 entry.1 output (by rw [heval])).2⟩
theorem journal_prices (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) :
    BPORS.History.fullPrice (journalLabels journal)≤BPORS.History.fullPrice history ∧
      BPORS.History.fullNearPrice (journalLabels journal)≤BPORS.History.fullNearPrice history :=
  ⟨BPORS.History.fullPrice_sublist hj.2.2.2,BPORS.History.fullNearPrice_sublist hj.2.2.2⟩
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.PublicVerdict
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def IsPublicHash : T3.Spec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False
abbrev Only {α : Type} (program : M α) := AllQueriesSatisfy program IsPublicHash
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed
  SourceQueries.map_allowed SourceQueries.foldlM_allowed SourceQueries.mapM_allowed
  SourceQueries.publicHash_allowed SourceQueries.shortHash_allowed SourceQueries.digest_allowed
macro "public_verdict_queries" : tactic => `(tactic|
  aesop (config := { maxRuleApplications := 1000 }) (add simp IsPublicHash))
@[local aesop safe apply] theorem chain_public (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Only (chain lay tree leaf i start count value) := by
  unfold chain; public_verdict_queries
@[local aesop safe apply] theorem leafHash_public (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Only (leafHash lay tree leaf ends) := by unfold leafHash; public_verdict_queries
@[local aesop safe apply] theorem nodeHash_public (tag lay tree heap : Nat) (left right : Digest) :
    Only (nodeHash tag lay tree heap left right) := by unfold nodeHash; public_verdict_queries
@[local aesop safe apply] theorem ftsLeaf_public (index coord leaf : Nat) (secret : Digest) :
    Only (ftsLeaf index coord leaf secret) := by unfold ftsLeaf; public_verdict_queries
@[local aesop safe apply] theorem forestPk_public (index : Nat) (roots : List Digest) :
    Only (forestPk index roots) := by unfold forestPk; public_verdict_queries
@[local aesop safe apply] theorem counterSearch_public (lay : Layer) (tree leaf : Nat)
    (message : Digest × BitVec 96 × Digest) (counter fuel : Nat) : Only (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; public_verdict_queries
  | succ fuel ih => unfold counterSearch; public_verdict_queries
@[local aesop safe apply] theorem digestSearch_public (rho : Digest) (message : Message)
    (counter fuel : Nat) : Only (digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; public_verdict_queries
  | succ fuel ih => unfold digestSearch; public_verdict_queries
theorem recoverChild_public (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (level node used : Nat) :
    Only (recoverChild index coord leaves values proof level node used) := by
  induction level generalizing node used with
  | zero => unfold recoverChild;public_verdict_queries
  | succ level ih => unfold recoverChild;public_verdict_queries
attribute [local aesop safe apply] recoverChild_public
theorem recoverFts_public (sig : Signature) (index : Nat) (chosen : List Selection) :
    Only (recoverFts sig index chosen) := by
  unfold recoverFts;public_verdict_queries
attribute [local aesop safe apply] recoverFts_public
theorem recoverLayer_public (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    Only (recoverLayer sig index lay digits) := by
  unfold recoverLayer;public_verdict_queries
attribute [local aesop safe apply] recoverLayer_public
theorem recoverPair_public (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) :
    Only (recoverPair sig index lay digits) := by
  unfold recoverPair;public_verdict_queries
attribute [local aesop safe apply] recoverPair_public
theorem rootHash_public (index : Nat) (lay : Layer) (pair : (Digest × BitVec 96 × Digest)) :
    Only (rootHash index lay pair) := by
  unfold rootHash;public_verdict_queries
attribute [local aesop safe apply] rootHash_public
theorem recoverNext_public (sig : Signature) (index n : Nat) (lay : Layer) (digits : List Nat) :
    Only (recoverNext sig index n lay digits) := by
  unfold recoverNext;split <;> public_verdict_queries
attribute [local aesop safe apply] recoverNext_public
theorem expandNext_public (sig : Signature) (index n : Nat) (lay : Layer) (digits : List Nat) :
    Only (expandNext sig index n lay digits) := by
  unfold expandNext;public_verdict_queries
attribute [local aesop safe apply] expandNext_public
theorem expandLayers_public (sig : Signature) (index n : Nat) (value : Digest × BitVec 96 × Digest) :
    Only (expandLayers sig index n value) := by
  induction n generalizing value with
  | zero => unfold expandLayers;public_verdict_queries
  | succ n ih => unfold expandLayers;public_verdict_queries
attribute [local aesop safe apply] expandLayers_public
theorem expand_public (message : Message) (pk : Digest) (sig : Signature) :
    Only (expand message pk sig) := by
  unfold expand;public_verdict_queries
attribute [local aesop safe apply] expand_public
theorem verifyLayers_public (witness : Witness) (index n : Nat) (root : Digest × BitVec 96 × Digest) :
    Only (verifyLayers witness index n root) := by
  induction n generalizing root with
  | zero => unfold verifyLayers;public_verdict_queries
  | succ n ih => unfold verifyLayers;public_verdict_queries
attribute [local aesop safe apply] verifyLayers_public
theorem verify_public (message : Message) (pk : Digest) (witness : Witness) :
    Only (verify message pk witness) := by
  unfold verify;public_verdict_queries
attribute [local aesop safe apply] verify_public
theorem checkForgery_public (publicKey : Digest) (log : QueryLog Requests) (forgery : Forgery) :
    Only (checkForgery publicKey log forgery) := by
  cases forgery <;> unfold checkForgery <;> public_verdict_queries
theorem verdict_public (publicKey : Digest) (result : Option Forgery × QueryLog Requests) :
    Only (FullGame.verdict publicKey result) := by
  unfold FullGame.verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checkForgery_public publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
theorem only_avoids {α : Type} (program : M α) (hp : Only program) (message : Message) :
    NonceFreshness.Avoids message program := by
  induction program using OracleComp.inductionOn with
  | pure value => exact NonceFreshness.avoids_pure message value
  | query_bind input next ih =>
      obtain ⟨hi,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      apply (allQueriesSatisfy_query_bind_iff _ _ _).mpr
      refine ⟨?_,fun answer => ih answer (hn answer)⟩
      cases input with
      | inl input => simp [NonceFreshness.nonceQuery]
      | inr coordinate => exact False.elim hi
end SigGolfCandidate.T3.Security.PublicVerdict
end
section
namespace SigGolfCandidate.T3.Security.SigningRecords
open OracleComp OracleSpec Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
theorem payloadAfterDigest_forestRows (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    payloadAfterDigest cache rho output=(do
      let index := output.toNat%2^31
      let state ← forestRows index (selections output)
      let root ← forestPk index state.2.2
      let some layers ← signLayers cache index 4 (root, 0, 0) | pure none
      pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
        fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)) := rfl
theorem payloadAfterDigest_fields (answers : Answers) (cache : T3.Cache) (rho : Digest)
    (output : HashOutput) (sig : Signature)
    (hs : evalWithAnswerFn answers (payloadAfterDigest cache rho output)=some sig) :
    sig.rho=rho ∧
      (∀ i,sig.secrets i=(forestOpenPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0) ∧
      (∀ i,sig.proof i=(forestProofPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0) := by
  rw [payloadAfterDigest_forestRows] at hs
  simp only [evalWithAnswerFn_bind,eval_forestRows] at hs
  cases hp : evalWithAnswerFn answers (signLayers cache (output.toNat%2^31) 4
    (evalWithAnswerFn answers (forestPk (output.toNat%2^31) (forestRoots answers (output.toNat%2^31) 7)),0,0)) with
  | none => simp only [hp,evalWithAnswerFn_pure,reduceCtorEq] at hs
  | some parts =>
      simp only [hp,evalWithAnswerFn_pure,Option.some.injEq] at hs
      subst sig
      exact ⟨rfl,fun _ => rfl,fun _ => rfl⟩
theorem recordForNonce_selected_payload (answers : Answers) (cache : T3.Cache) (rho : Digest)
    (message : Message) (sig : Signature) (output : HashOutput)
    (hs : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).1=some sig)
    (ho : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).2=some output) :
    evalWithAnswerFn answers (payloadAfterDigest cache rho output)=some sig := by
  unfold payloadRecordForNonce at hs ho
  simp only [evalWithAnswerFn_bind] at hs ho
  cases hd : evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at hs
  | some found =>
      rcases found with ⟨counter,value⟩
      simp only [hd,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Option.some.injEq] at hs ho
      subst output
      exact hs
theorem authenticatedRecord_fields (answers : Answers) (published : T3.Cache) (request : Request)
    (sig : Signature) (output : HashOutput)
    (hr : evalWithAnswerFn answers (FullGame.authenticatedRecord published request)=(some sig,some output)) :
    request.cache=published ∧ admissible (selections output)=true ∧
      sig.rho=evalWithAnswerFn answers (privateNonce request.message) ∧
      (∀ i,sig.secrets i=(forestOpenPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0) ∧
      (∀ i,sig.proof i=(forestProofPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0) := by
  have ho : (evalWithAnswerFn answers (FullGame.authenticatedRecord published request)).2=some output := by rw [hr]
  obtain ⟨hcache,hadmissible⟩ := authenticatedRecord_selected_valid answers published request output ho
  refine ⟨hcache,hadmissible,?_⟩
  unfold FullGame.authenticatedRecord at hr
  simp only [evalWithAnswerFn_bind,if_pos hcache,payloadRecord] at hr
  apply payloadAfterDigest_fields answers request.cache _ output sig
  exact recordForNonce_selected_payload answers request.cache _ request.message sig output
    (by rw [hr]) (by rw [hr])
attribute [local irreducible] evalWithAnswerFn
theorem secret_at_coordinate (answers : Answers) (sig : Signature) (output : HashOutput)
    (hs : ∀ i,sig.secrets i=(forestOpenPrefix answers (output.toNat%2^31) (selections output) 7).getD i.val 0)
    (coord : Fin 7) (slot : Fin 3) :
    sig.secrets ⟨3*coord.val+slot.val,by omega⟩=
      (evalWithAnswerFn answers (buildFts (output.toNat%2^31) coord.val)).2.getD
        (((selections output).getD coord.val ⟨0,[]⟩).bucket*128+
          ((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0) 0 := by
  rw [hs]
  have hlen : ((selections output).getD coord.val ⟨0,[]⟩).leaves.length=3 :=
    selection_leaves_length output _ (selection_getD_mem output coord.val coord.isLt)
  have hblock : (forestOpened answers (output.toNat%2^31) coord.val
      ((selections output).getD coord.val ⟨0,[]⟩)).length=3 := by
    simp only [forestOpened,List.length_map,hlen]
  have hp := forestOpenPrefix_length answers (output.toNat%2^31) output coord.val (by omega)
  change ((List.range 7).flatMap (fun c => forestOpened answers (output.toNat%2^31) c
      ((selections output).getD c ⟨0,[]⟩))).getD (3*coord.val+slot.val) 0=_
  have hget := flatMap_range_getD (fun c => forestOpened answers (output.toNat%2^31) c
      ((selections output).getD c ⟨0,[]⟩)) 7 coord.val slot.val coord.isLt (by rw [hblock]; exact slot.isLt)
  rw [show ((List.range coord.val).flatMap (fun c => forestOpened answers (output.toNat%2^31) c
      ((selections output).getD c ⟨0,[]⟩))).length=3*coord.val from hp] at hget
  rw [hget]
  have hj : slot.val<((selections output).getD coord.val ⟨0,[]⟩).leaves.length := by rw [hlen];exact slot.isLt
  rw [List.getD_eq_getElem (forestOpened answers (output.toNat%2^31) coord.val
    ((selections output).getD coord.val ⟨0,[]⟩)) 0 (by rw [hblock];exact slot.isLt)]
  simp only [forestOpened,List.getElem_map,
    List.getD_eq_getElem ((selections output).getD coord.val ⟨0,[]⟩).leaves 0 hj]
end SigGolfCandidate.T3.Security.SigningRecords
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem journal_public_preserves {α : Type} (published : T3.Cache) (history : History)
    (before : State) (journal : Journal) (hj : JournalOK published history before journal)
    (program : M α) (hp : PublicVerdict.Only program) (result : α × State)
    (hr : result ∈ support (run program before)) : JournalOK published history result.2 journal := by
  apply journal_keeps published history history before result.2 journal hj
    (run_extends program before result hr) (List.Sublist.refl _)
  intro message hf
  exact Or.inl ((run_nonce_preserves message program (PublicVerdict.only_avoids program hp message)
    before result hr).trans hf)
theorem traced_game_journal (adversary : Adversary) (budget : Nat) (hbudget : budget≤2^127)
    (result : Bool × (History × State)) (hr : result ∈ (tracedExperiment adversary budget hbudget).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.source.2 keygen generated ∧
        JournalOK generated.2 result.2.1 result.2.2 journal := by
  unfold tracedExperiment at hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨generated,hg,hr⟩ := hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨interaction,hi,hr⟩ := hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨checked,hv,hr⟩ := hr
  rw [PMF.monad_pure_eq_pure,PMF.mem_support_pure_iff] at hr
  subst result
  rw [pmf_support] at hg hv
  have hbudgetBefore := (run_count_monotone _ interaction.2.2 checked hv).trans hcount
  have hcleanBefore := run_false_before _ interaction.2.2 checked hv hflag
  obtain ⟨journal,hj⟩ := actual_interaction_journal generated hg budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) interaction hi hbudgetBefore hcleanBefore
  have hsource := traced_source_support generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) ([],generated.2) interaction hi
  have hgen := SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
    (generated.1,generated.2.source.2) (run_lazy_support keygen ⟨(0,∅,∅),false⟩ generated hg)
  refine ⟨generated.1,journal,hgen.mono ?_,?_⟩
  · exact (run_extends _ generated.2 (interaction.1,interaction.2.2) hsource).trans
      (run_extends _ interaction.2.2 checked hv)
  · exact journal_public_preserves generated.1.2 interaction.2.1 interaction.2.2 journal hj
      (FullGame.verdict generated.1.1 interaction.1) (PublicVerdict.verdict_public _ _) checked hv
theorem journal_entry_openings (published : T3.Cache) (history : History) (state : State)
    (journal : Journal) (hj : JournalOK published history state journal)
    (message : Message) (sig : Signature) (output : HashOutput)
    (he : (message,(some sig,some output)) ∈ journal) :
    admissible (selections output)=true ∧
      (∀ i,sig.secrets i=(Correctness.forestOpenPrefix (SourceReplay.answers state.source.2)
        (output.toNat%2^31) (selections output) 7).getD i.val 0) ∧
      (∀ coord : Fin 7,∀ slot : Fin 3,sig.secrets ⟨3*coord.val+slot.val,by omega⟩=
        (evalWithAnswerFn (SourceReplay.answers state.source.2) (buildFts (output.toNat%2^31) coord.val)).2.getD
          (((selections output).getD coord.val ⟨0,[]⟩).bucket*128+
            ((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0) 0) := by
  have hresolve := hj.2.1 (message,(some sig,some output)) he
  have hfields := SigningRecords.authenticatedRecord_fields (SourceReplay.answers state.source.2)
    published ⟨message,published⟩ sig output
    (hresolve.eval (SourceReplay.answers state.source.2) (SourceReplay.answers_known state.source.2))
  exact ⟨hfields.2.1,hfields.2.2.2.1,SigningRecords.secret_at_coordinate
    (SourceReplay.answers state.source.2) sig output hfields.2.2.2.1⟩
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.BPORS.History
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def journalOutputs (journal : Journal) : List HashOutput := journal.filterMap fun entry => entry.2.2
theorem journalLabels_outputs (journal : Journal) :
    journalLabels journal=(journalOutputs journal).map (fun output => (DigestSampling.samplingData output).1) := by
  induction journal with
  | nil => rfl
  | cons entry tail ih =>
      unfold journalLabels journalOutputs at *
      cases hd : entry.2.2 <;> simp [hd,ih]
def chosenLeaves (output : HashOutput) (coord : Fin 7) : Finset (Fin 128) :=
  ((((selections output).getD coord.val ⟨0,[]⟩).leaves).map fun leaf => Fin.ofNat 128 leaf).toFinset
theorem chosenLeaves_card (output : HashOutput) (coord : Fin 7) : (chosenLeaves output coord).card≤3 := by
  unfold chosenLeaves
  apply le_trans (List.toFinset_card_le _)
  rw [List.length_map,selection_leaves_length output _ (Correctness.selection_getD_mem output coord.val coord.isLt)]
theorem chosenLeaves_mem (output : HashOutput) (coord : Fin 7) (slot : Fin 3) :
    Fin.ofNat 128 (((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0) ∈ chosenLeaves output coord := by
  rw [chosenLeaves,List.mem_toFinset,List.mem_map]
  refine ⟨_,?_,rfl⟩
  have hl := selection_leaves_length output _ (Correctness.selection_getD_mem output coord.val coord.isLt)
  rw [List.getD_eq_getElem ((selections output).getD coord.val ⟨0,[]⟩).leaves 0
    (by rw [hl]; exact slot.isLt)]
  exact List.getElem_mem _
theorem chosen_leaf_bound (output : HashOutput) (coord : Fin 7) (slot : Fin 3) :
    ((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0<128 := by
  have hm := Correctness.selection_getD_mem output coord.val coord.isLt
  have hl := selection_leaves_length output _ hm
  apply selection_leaf_bound output _ _ hm
  rw [List.getD_eq_getElem ((selections output).getD coord.val ⟨0,[]⟩).leaves 0
    (by rw [hl]; exact slot.isLt)]
  exact List.getElem_mem _
theorem sampling_index_value (output : HashOutput) :
    (DigestSampling.samplingData output).1.1.val=output.toNat%2^31 := DigestSampling.rawView_index output
theorem sampling_bucket_value (output : HashOutput) (coord : Fin 7) :
    ((DigestSampling.samplingData output).1.2 coord).val=((selections output).getD coord.val ⟨0,[]⟩).bucket := by
  change ((DigestSampling.rawView output).2 coord).1.val=_
  rw [← DigestSampling.rawSelections_eq_selections]
  rw [List.getD_eq_getElem _ _ (by simpa [DigestSampling.rawSelections] using coord.isLt)]
  simp only [DigestSampling.rawSelections,List.getElem_ofFn]
def exposedLeaves : List HashOutput → Fin (2^31) → Fin 7 → Fin 16 → Finset (Fin 128)
  | [],_,_,_ => ∅
  | output::tail,index,coord,bucket =>
      if (DigestSampling.samplingData output).1.1=index ∧ (DigestSampling.samplingData output).1.2 coord=bucket
      then chosenLeaves output coord ∪ exposedLeaves tail index coord bucket
      else exposedLeaves tail index coord bucket
theorem exposedLeaves_card (outputs : List HashOutput) (index : Fin (2^31)) (coord : Fin 7) (bucket : Fin 16) :
    (exposedLeaves outputs index coord bucket).card ≤
      3*((atIndex index (outputs.map (fun output => (DigestSampling.samplingData output).1))).map
        (fun row => row coord)).count bucket := by
  induction outputs with
  | nil => simp [exposedLeaves,atIndex]
  | cons output tail ih =>
      by_cases hi : (DigestSampling.samplingData output).1.1=index
      · by_cases hb : (DigestSampling.samplingData output).1.2 coord=bucket
        · simp only [exposedLeaves,hi,hb,and_self,ite_true,List.map_cons,atIndex_cons,List.count_cons_self]
          have h := (Finset.card_union_le (chosenLeaves output coord) (exposedLeaves tail index coord bucket)).trans
            (Nat.add_le_add (chosenLeaves_card output coord) ih)
          omega
        · simpa only [exposedLeaves,hi,hb,true_and,and_false,ite_false,atIndex_cons,List.map_cons,ite_true,
            List.count_cons_of_ne hb] using ih
      · simpa only [exposedLeaves,hi,false_and,ite_false,List.map_cons,atIndex_cons] using ih
theorem exposedLeaves_of_member (outputs : List HashOutput) (output : HashOutput) (ho : output ∈ outputs)
    (coord : Fin 7) (leaf : Fin 128) (hl : leaf ∈ chosenLeaves output coord) :
    leaf ∈ exposedLeaves outputs (DigestSampling.samplingData output).1.1 coord
      ((DigestSampling.samplingData output).1.2 coord) := by
  induction outputs with
  | nil => simp at ho
  | cons first tail ih =>
      rcases List.mem_cons.mp ho with ho | ho
      · subst first
        simp only [exposedLeaves,eq_self_iff_true,and_self,ite_true,Finset.mem_union]
        exact Or.inl hl
      · have htail := ih ho
        unfold exposedLeaves
        split_ifs
        · exact Finset.mem_union_right _ htail
        · exact htail
theorem journal_exposure_card (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) (index : Fin (2^31)) (coord : Fin 7) (bucket : Fin 16) :
    (exposedLeaves (journalOutputs journal) index coord bucket).card ≤
      3*((atIndex index history).map (fun row => row coord)).count bucket := by
  have h := exposedLeaves_card (journalOutputs journal) index coord bucket
  rw [← journalLabels_outputs] at h
  exact h.trans (Nat.mul_le_mul_left 3 (((atIndex_sublist index hj.2.2.2).map (fun row => row coord)).count_le bucket))
theorem journal_output_mem (journal : Journal) (message : Message) (signature : Option Signature)
    (output : HashOutput) (he : (message,(signature,some output)) ∈ journal) : output ∈ journalOutputs journal := by
  rw [journalOutputs,List.mem_filterMap]
  exact ⟨(message,(signature,some output)),he,rfl⟩
theorem journal_opened_exposure (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) (message : Message) (sig : Signature) (output : HashOutput)
    (he : (message,(some sig,some output)) ∈ journal) (coord : Fin 7) (slot : Fin 3) :
    ∃ leaf : Fin 128,
      leaf ∈ exposedLeaves (journalOutputs journal) (DigestSampling.samplingData output).1.1 coord
        ((DigestSampling.samplingData output).1.2 coord) ∧
      sig.secrets ⟨3*coord.val+slot.val,by omega⟩=
        (evalWithAnswerFn (SourceReplay.answers state.source.2)
          (buildFts (DigestSampling.samplingData output).1.1.val coord.val)).2.getD
            (((DigestSampling.samplingData output).1.2 coord).val*128+leaf.val) 0 := by
  let leaf := Fin.ofNat 128 (((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0)
  refine ⟨leaf,?_,?_⟩
  · exact exposedLeaves_of_member (journalOutputs journal) output
      (journal_output_mem journal message (some sig) output he) coord leaf (chosenLeaves_mem output coord slot)
  · rw [sampling_index_value,sampling_bucket_value]
    have hleaf : leaf.val=((selections output).getD coord.val ⟨0,[]⟩).leaves.getD slot.val 0 := by
      exact Nat.mod_eq_of_lt (chosen_leaf_bound output coord slot)
    rw [hleaf]
    exact (journal_entry_openings published history state journal hj message sig output he).2.2 coord slot
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.BPORS.History
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem journal_coverage_bound (published : T3.Cache) (history : History) (state : State) (journal : Journal)
    (hj : JournalOK published history state journal) (index : Fin (2^31)) :
    Pr[fun output : HashOutput => digestAdmissible output=true ∧
      SigGolfResearch.Gate6.CoordinateCovered (exposedLeaves (journalOutputs journal) index)
        (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ wordEnvelope (atIndex index history) := by
  simp_rw [SigGolfResearch.Gate6.Source.actual_predicate_iff]
  let word := atIndex index history
  let table : Fin 7 → Fin word.length → Fin 16 := fun coord i => (word.get i) coord
  have htable (coord : Fin 7) : List.ofFn (table coord)=word.map (fun row => row coord) := by
    change List.ofFn (fun i : Fin word.length => (word.get i) coord)=_
    simpa only [List.ofFn_get] using (List.ofFn_comp' word.get (fun row => row coord))
  have h := SigGolfResearch.Gate6.accepted_covered_le_forestEnvelope table
    (exposedLeaves (journalOutputs journal) index) (by
      intro coord bucket
      rw [htable]
      exact journal_exposure_card published history state journal hj index coord bucket)
  change _ ≤ wordEnvelope word
  apply h.trans_eq
  simp only [BPORS.Numeric.forestEnvelope,wordEnvelope,htable]
theorem journal_average_coverage_bound (published : T3.Cache) (history : History) (state : State)
    (journal : Journal) (hj : JournalOK published history state journal) :
    expectedValue ($ᵗ (Fin (2^31)) : ProbComp _)
      (fun index => Pr[fun output : HashOutput => digestAdmissible output=true ∧
        SigGolfResearch.Gate6.CoordinateCovered (exposedLeaves (journalOutputs journal) index)
          (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
          ($ᵗ HashOutput : ProbComp HashOutput)]) ≤
      fullPrice history/(2 : ENNReal)^128 := by
  apply le_trans (expectedValue_mono _ (fun index => journal_coverage_bound published history state journal hj index))
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage fullPrice
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  have hscale : (2 : ENNReal)^97*((2 : ENNReal)^128)⁻¹=((2 : ENNReal)^31)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
  simp only [div_eq_mul_inv]
  rw [mul_comm ((2 : ENNReal)^97),mul_assoc,hscale]
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.SourceReplay
open OracleComp OracleSpec
open SphincsSecurity.QueryCap (counted counted_pure counted_query_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def queried {α : Type} (oracleAnswers : Correctness.Answers) (program : M α) : List T3.Spec.Domain :=
  ((simulateQ oracleAnswers.withLogging program).run).2.map Sigma.fst
@[simp] theorem queried_pure {α : Type} (oracleAnswers : Correctness.Answers) (value : α) :
    queried oracleAnswers (pure value)=[] := rfl
@[simp] theorem queried_query_bind {α : Type} (oracleAnswers : Correctness.Answers)
    (input : T3.Spec.Domain) (next : T3.Spec.Range input → M α) :
    queried oracleAnswers (liftM (T3.Spec.query input) >>= next)=
      input::queried oracleAnswers (next (oracleAnswers input)) := rfl
theorem queried_bind {α β : Type} (oracleAnswers : Correctness.Answers) (program : M α) (next : α → M β) :
    queried oracleAnswers (program >>= next)=queried oracleAnswers program++
      queried oracleAnswers (next (evalWithAnswerFn oracleAnswers program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input rest ih =>
      rw [bind_assoc,queried_query_bind,queried_query_bind,ih,evalWithAnswerFn_bind,
        show evalWithAnswerFn oracleAnswers (liftM (T3.Spec.query input))=oracleAnswers input from
          simulateQ_spec_query oracleAnswers input,List.cons_append]
theorem Resolves.queried_known {α : Type} {state : LazyPrivate.State} {program : M α} {value : α}
    (hr : Resolves state program value) (oracleAnswers : Correctness.Answers)
    (hagrees : ∀ input answer,known state input=some answer → oracleAnswers input=answer) :
    ∀ input ∈ queried oracleAnswers program,known state input=some (oracleAnswers input) := by
  induction hr with
  | pure value => simp
  | query input answer ha next value _ ih =>
      rw [queried_query_bind,hagrees input answer ha]
      intro query hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst query
        rw [hagrees input answer ha]
        exact ha
      · exact ih query hq
theorem hash_charged (input : T3.Spec.Domain) (hi : IsHash input) : Derivation.charged input := by
  cases input with
  | inl input => cases input <;> exact hi
  | inr coordinate => trivial
theorem counted_hashOnly {α : Type} (program : M α) (hp : HashOnly program) :
    HashOnly (counted Derivation.charged program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact SourceQueries.pure_allowed _ _
  | query_bind input next ih =>
      obtain ⟨hi,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [counted_query_bind]
      apply (allQueriesSatisfy_query_bind_iff _ _ _).mpr
      refine ⟨hi,?_⟩
      intro answer
      exact SourceQueries.bind_allowed _ (ih answer (hn answer)) (fun _ => SourceQueries.pure_allowed _ _)
theorem counted_query_length {α : Type} (oracleAnswers : Correctness.Answers) (program : M α)
    (hp : HashOnly program) :
    evalWithAnswerFn oracleAnswers (counted Derivation.charged program)=
      (evalWithAnswerFn oracleAnswers program,(queried oracleAnswers program).length) := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [counted_query_bind,evalWithAnswerFn_bind,evalWithAnswerFn_bind,evalWithAnswerFn_bind,
        show evalWithAnswerFn oracleAnswers (liftM (T3.Spec.query input))=oracleAnswers input from
          simulateQ_spec_query oracleAnswers input,ih _ (hn _)]
      simp only [evalWithAnswerFn_pure,queried_query_bind,List.length_cons,
        if_pos (hash_charged input hi),Nat.add_comm 1]
end SigGolfCandidate.T3.Security.SourceReplay
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem supported_public_query_known {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : State) (result : α × State) (hr : result ∈ support (run program before))
    (input : HashInput)
    (hq : .inl (.inr input) ∈ SourceReplay.queried (SourceReplay.answers result.2.source.2) program) :
    result.2.source.2.2 input=some ((SourceReplay.answers result.2.source.2) (.inl (.inr input))) :=
  (SourceReplay.resolves_of_run program hp before.source.2 (result.1,result.2.source.2)
    (run_lazy_support program before result hr)).queried_known
      (SourceReplay.answers result.2.source.2) (SourceReplay.answers_known result.2.source.2) _ hq
theorem supported_query_length {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : State) (result : α × State) (hr : result ∈ support (run program before)) :
    result.2.source.1=before.source.1+
      (SourceReplay.queried (SourceReplay.answers result.2.source.2) program).length := by
  have hsource := run_project_support program before result hr
  rw [CountedPrivate.run,support_map] at hsource
  obtain ⟨observed,ho,he⟩ := hsource
  have hresolve := SourceReplay.resolves_of_run (SphincsSecurity.QueryCap.counted Derivation.charged program)
    (SourceReplay.counted_hashOnly program hp) before.source.2 observed ho
  have heval := hresolve.eval (SourceReplay.answers observed.2) (SourceReplay.answers_known observed.2)
  rw [SourceReplay.counted_query_length _ program hp] at heval
  have hcounter := congrArg (fun x => x.2.1) he
  have hcache := congrArg (fun x => x.2.2) he
  have hlen := congrArg Prod.snd heval
  change before.source.1+observed.1.2=result.2.source.1 at hcounter
  change observed.2=result.2.source.2 at hcache
  change (SourceReplay.queried (SourceReplay.answers observed.2) program).length=observed.1.2 at hlen
  rw [← hcounter,← hcache,hlen]
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.QueryCap (counted counted_pure counted_query_bind)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Test := LazyPrivate.State → (input : T3.Spec.Domain) → T3.Spec.Range input → Bool
structure Observation (α : Type) where
  value : α
  calls : Nat
  hit : Bool
  state : LazyPrivate.State
noncomputable def observe {α : Type} (test : Test) (program : M α) : LazyPrivate.State → ProbComp (Observation α) :=
  OracleComp.construct
    (fun value state => pure ⟨value,0,false,state⟩)
    (fun input _ next state => do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,FullGame.queryCharge input+last.calls,
        test state input middle.1 || last.hit,last.state⟩) <$> next middle.1 middle.2) program
theorem observe_pure {α : Type} (test : Test) (value : α) (state : LazyPrivate.State) :
    observe test (pure value : M α) state=pure ⟨value,0,false,state⟩ := rfl
theorem observe_query_bind {α : Type} (test : Test) (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    observe test (liftM (T3.Spec.query input) >>= next) state=(do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,FullGame.queryCharge input+last.calls,
        test state input middle.1 || last.hit,last.state⟩) <$> observe test (next middle.1) middle.2) := rfl
theorem observe_erasure {α : Type} (test : Test) (program : M α) (state : LazyPrivate.State) :
    (fun result : Observation α => ((result.value,result.calls),result.state)) <$> observe test program state=
      LazyPrivate.run (counted Derivation.charged program) state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [observe_pure,map_pure,counted_pure,LazyPrivate.run_pure]
  | query_bind input next ih =>
      rw [observe_query_bind,map_bind,counted_query_bind,LazyPrivate.run_bind]
      apply bind_congr
      intro middle
      simp only [Functor.map_map,bind_pure_comp]
      have h := congrArg (Functor.map (fun result : (α × Nat) × LazyPrivate.State =>
        ((result.1.1,FullGame.queryCharge input+result.1.2),result.2))) (ih middle.1 middle.2)
      rw [LazyPrivate.run_map]
      have he : Prod.map (fun result : α × Nat => (result.1,(if Derivation.charged input then 1 else 0)+result.2)) id=
          (fun result : (α × Nat) × LazyPrivate.State =>
            ((result.1.1,FullGame.queryCharge input+result.1.2),result.2)) := by
        funext result
        rcases result with ⟨⟨value,calls⟩,state⟩
        rfl
      rw [he]
      simpa only [Functor.map_map] using h
theorem split_first_hit {α : Type} (program : ProbComp (Observation α)) (flag : Bool) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ (flag || result.hit)=true | program] ≤
      (if flag=true then 1 else 0)+Pr[fun result => result.calls≤budget ∧ result.hit=true | program] := by
  cases flag with
  | false => simp
  | true => exact probEvent_le_one.trans le_self_add
theorem observe_hit_bound {α : Type} (test : Test) (rate : ENNReal)
    (hstep : ∀ state input,
      Pr[fun result => test state input result.1=true |
        LazyPrivate.run (liftM (T3.Spec.query input)) state] ≤ FullGame.queryCharge input*rate)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true | observe test program state] ≤ budget*rate := by
  induction program using OracleComp.inductionOn generalizing state budget with
  | pure value => simp [observe_pure]
  | query_bind input next ih =>
      rw [observe_query_bind,probEvent_bind_eq_expectedValue]
      simp only [probEvent_map,Function.comp_def]
      by_cases hc : Derivation.charged input
      · cases budget with
        | zero => simp [FullGame.queryCharge,hc,expectedValue]
        | succ remaining =>
            have he : ∀ n : Nat,FullGame.queryCharge input+n≤remaining+1 ↔ n≤remaining := by
              simp only [FullGame.queryCharge,if_pos hc];omega
            simp_rw [he]
            calc
              _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
                  (fun middle => (if test state input middle.1=true then 1 else 0)+(remaining : ENNReal)*rate) := by
                apply expectedValue_mono
                intro middle
                exact (split_first_hit (observe test (next middle.1) middle.2)
                  (test state input middle.1) remaining).trans
                    (add_le_add le_rfl (ih middle.1 middle.2 remaining))
              _ = Pr[fun middle => test state input middle.1=true |
                  LazyPrivate.run (liftM (T3.Spec.query input)) state]+(remaining : ENNReal)*rate := by
                rw [expectedValue_add,expectedValue_ite_one,
                  expectedValue_const (by simp)]
              _ ≤ rate+(remaining : ENNReal)*rate := by
                apply add_le_add _ le_rfl
                simpa only [FullGame.queryCharge,if_pos hc,Nat.cast_one,one_mul] using hstep state input
              _ = _ := by push_cast;ring
      · have he : ∀ n : Nat,FullGame.queryCharge input+n≤budget ↔ n≤budget := by
          simp [FullGame.queryCharge,hc]
        simp_rw [he]
        calc
          _ ≤ expectedValue (LazyPrivate.run (liftM (T3.Spec.query input)) state)
              (fun middle => (if test state input middle.1=true then 1 else 0)+(budget : ENNReal)*rate) := by
            apply expectedValue_mono
            intro middle
            exact (split_first_hit (observe test (next middle.1) middle.2) (test state input middle.1) budget).trans
              (add_le_add le_rfl (ih middle.1 middle.2 budget))
          _ = Pr[fun middle => test state input middle.1=true |
              LazyPrivate.run (liftM (T3.Spec.query input)) state]+(budget : ENNReal)*rate := by
            rw [expectedValue_add,expectedValue_ite_one,expectedValue_const (by simp)]
          _ ≤ 0+(budget : ENNReal)*rate := by
            apply add_le_add _ le_rfl
            simpa only [FullGame.queryCharge,if_neg hc,Nat.cast_zero,zero_mul] using hstep state input
          _ = _ := zero_add _
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev PublicTargets := LazyPrivate.State → HashInput → Finset Digest
noncomputable def publicTargetTest (targets : PublicTargets) : Test
  | state,.inl (.inr input),output =>
      decide (state.2 input=none ∧ output.extractLsb' 0 128 ∈ targets state input)
  | _,.inl (.inl _),_ => false
  | _,.inr _,_ => false
theorem uniform_low_mem (targets : Finset Digest) :
    Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)]=
      targets.card/(2 : ENNReal)^128 := by
  have h := LazyPrivate.uniform_hash_low_expectation
    (fun digest => if digest ∈ targets then (1 : ENNReal) else 0)
  rw [expectedValue_ite_one,expectedValue_ite_one] at h
  rw [h,probEvent_uniformSample]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Fintype.card_bitVec,
    Nat.cast_pow,Nat.cast_ofNat]
theorem public_target_step (targets : PublicTargets) (state : LazyPrivate.State) (input : HashInput) :
    Pr[fun result => publicTargetTest targets state (.inl (.inr input)) result.1=true |
      LazyPrivate.run (liftM (T3.Spec.query (.inl (.inr input)))) state]=
      if state.2 input=none then (targets state input).card/(2 : ENNReal)^128 else 0 := by
  change Pr[fun result => publicTargetTest targets state (.inl (.inr input)) result.1=true |
    LazyPrivate.run (Sampling.publicHandler input) state]=_
  rw [LazyPrivate.run_publicQuery]
  by_cases hfresh : state.2 input=none
  · rw [if_pos hfresh,randomOracle,QueryImpl.withCaching_run_none _ hfresh]
    simp only [map_eq_bind_pure_comp,bind_assoc,probEvent_bind_eq_expectedValue,
      probEvent_pure,publicTargetTest,hfresh,true_and,decide_eq_true_eq,
      Function.comp_apply,expectedValue_pure]
    rw [expectedValue_ite_one]
    exact uniform_low_mem _
  · rw [if_neg hfresh]
    apply probEvent_eq_zero
    intro result _
    simp only [publicTargetTest,decide_eq_true_eq,not_and]
    exact fun h => False.elim (hfresh h)
theorem public_target_hazard (targets : PublicTargets) (maxTargets : Nat)
    (hcard : ∀ state input,(targets state input).card ≤ maxTargets)
    (state : LazyPrivate.State) (input : T3.Spec.Domain) :
    Pr[fun result => publicTargetTest targets state input result.1=true |
      LazyPrivate.run (liftM (T3.Spec.query input)) state] ≤
      FullGame.queryCharge input*((maxTargets : ENNReal)/(2 : ENNReal)^128) := by
  cases input with
  | inl input =>
      cases input with
      | inl n => simp [publicTargetTest]
      | inr input =>
          rw [public_target_step]
          simp only [FullGame.queryCharge,Derivation.charged,if_true,Nat.cast_one,one_mul]
          split
          · exact ENNReal.div_le_div_right (by exact_mod_cast hcard state input) _
          · exact bot_le
  | inr coordinate => simp [publicTargetTest]
theorem public_targets_bound {α : Type} (targets : PublicTargets) (maxTargets : Nat)
    (hcard : ∀ state input,(targets state input).card ≤ maxTargets)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true |
      observe (publicTargetTest targets) program state] ≤
      budget*((maxTargets : ENNReal)/(2 : ENNReal)^128) :=
  observe_hit_bound _ _ (public_target_hazard targets maxTargets hcard) program state budget
noncomputable def onePublicTarget
    (target : LazyPrivate.State → HashInput → Option Digest) : PublicTargets :=
  fun state input => (target state input).toFinset
theorem one_public_target_bound {α : Type} (target : LazyPrivate.State → HashInput → Option Digest)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true |
      observe (publicTargetTest (onePublicTarget target)) program state] ≤
      budget/(2 : ENNReal)^128 := by
  have hcard : ∀ state input,(onePublicTarget target state input).card≤1 := by
    intro state input
    simp only [onePublicTarget]
    cases target state input <;> simp
  simpa only [Nat.cast_one,mul_one_div] using
    public_targets_bound (onePublicTarget target) 1 hcard program state budget
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Reference := LazyPrivate.State → HashInput → Option HashInput
noncomputable def knownTarget (reference : Reference) (state : LazyPrivate.State)
    (input : HashInput) : Option Digest := do
  let honest ← reference state input
  let output ← state.2 honest
  pure (output.extractLsb' 0 128)
theorem knownTarget_eq_some (reference : Reference) (state : LazyPrivate.State)
    (input : HashInput) (target : Digest) :
    knownTarget reference state input=some target ↔
      ∃ honest output,reference state input=some honest ∧ state.2 honest=some output ∧
        output.extractLsb' 0 128=target := by
  unfold knownTarget
  cases h : reference state input <;> simp
  rename_i honest
  cases ho : state.2 honest <;> simp
theorem known_target_test_iff (reference : Reference) (state : LazyPrivate.State)
    (input : HashInput) (answer : HashOutput) :
    publicTargetTest (onePublicTarget (knownTarget reference)) state (.inl (.inr input)) answer=true ↔
      state.2 input=none ∧ ∃ honest output,
        reference state input=some honest ∧ state.2 honest=some output ∧
        answer.extractLsb' 0 128=output.extractLsb' 0 128 := by
  simp only [publicTargetTest,decide_eq_true_eq,onePublicTarget,Option.mem_toFinset,
    Option.mem_def,knownTarget_eq_some]
  constructor
  · rintro ⟨hfresh,honest,output,hr,ho,he⟩
    exact ⟨hfresh,honest,output,hr,ho,he.symm⟩
  · rintro ⟨hfresh,honest,output,hr,ho,he⟩
    exact ⟨hfresh,honest,output,hr,ho,he.symm⟩
theorem known_target_distinct (reference : Reference) (state : LazyPrivate.State)
    (input honest : HashInput) (answer output : HashOutput)
    (hfresh : state.2 input=none) (hknown : state.2 honest=some output)
    (href : reference state input=some honest)
    (heq : answer.extractLsb' 0 128=output.extractLsb' 0 128) :
    input≠honest ∧
      publicTargetTest (onePublicTarget (knownTarget reference)) state (.inl (.inr input)) answer=true := by
  refine ⟨?_,(known_target_test_iff reference state input answer).mpr
    ⟨hfresh,honest,output,href,hknown,heq⟩⟩
  intro he
  rw [he,hknown] at hfresh
  contradiction
noncomputable def experiment (test : Test) (adversary : Adversary) : ProbComp (Observation Bool) :=
  observe test (FullGame.idealGame adversary) (∅,∅)
theorem experiment_erasure (test : Test) (adversary : Adversary) :
    (fun result : Observation Bool => ((result.value,result.calls),result.state)) <$>
      experiment test adversary=FullGame.idealLazyExperiment adversary :=
  observe_erasure test (FullGame.idealGame adversary) (∅,∅)
theorem experiment_event (test : Test) (adversary : Adversary) (budget : Nat) :
    Pr[fun result => result.value=true ∧ result.calls≤budget | experiment test adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤budget | FullGame.idealLazyExperiment adversary] := by
  have h := congrArg (fun law => Pr[fun result => result.1.1=true ∧ result.1.2≤budget | law])
    (experiment_erasure test adversary)
  simpa only [probEvent_map,Function.comp_def] using h
theorem experiment_split (test : Test) (adversary : Adversary) (budget : Nat) :
    Pr[fun result => result.value=true ∧ result.calls≤budget | experiment test adversary] ≤
      Pr[fun result => result.value=true ∧ result.calls≤budget ∧ result.hit=false |
        experiment test adversary]+
      Pr[fun result => result.calls≤budget ∧ result.hit=true | experiment test adversary] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.value=true ∧ result.calls≤budget
  · cases hh : result.hit <;> simp [hw]
  · simp only [hw,if_false,zero_le]
theorem real_to_no_public_target (targets : PublicTargets) (maxTargets : Nat)
    (hcard : ∀ state input,(targets state input).card ≤ maxTargets)
    (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.value=true ∧ result.calls≤q ∧ result.hit=false |
        experiment (publicTargetTest targets) adversary]+
      q*((maxTargets : ENNReal)/(2 : ENNReal)^128)+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := FullGame.real_to_ideal_lazy adversary q hq
  rw [← experiment_event (publicTargetTest targets) adversary q] at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact (experiment_split _ adversary q).trans
    (add_le_add le_rfl (public_targets_bound targets maxTargets hcard _ _ q))
theorem real_to_no_known_target (reference : Reference) (adversary : Adversary)
    (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.value=true ∧ result.calls≤q ∧ result.hit=false |
        experiment (publicTargetTest (onePublicTarget (knownTarget reference))) adversary]+
      q/(2 : ENNReal)^128+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have hcard : ∀ state input,(onePublicTarget (knownTarget reference) state input).card≤1 := by
    intro state input
    simp only [onePublicTarget]
    cases knownTarget reference state input <;> simp
  simpa only [Nat.cast_one,mul_one_div] using
    real_to_no_public_target (onePublicTarget (knownTarget reference)) 1 hcard adversary q hq
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.EncodingTargets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open FirstHit
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def wordList {lay : Layer} (word : Encoding lay) : List Nat :=
  List.ofFn fun i => (word i).val
theorem wordList_injective (lay : Layer) : Function.Injective (@wordList lay) := by
  intro left right he
  funext i
  apply Fin.ext
  exact congrFun (List.ofFn_injective he) i
noncomputable def preimages (lay : Layer) (word : Encoding lay) : Finset Digest :=
  Finset.univ.filter (fun digest => decode lay digest=some (wordList word))
@[simp] theorem mem_preimages (lay : Layer) (word : Encoding lay) (digest : Digest) :
    digest ∈ preimages lay word ↔ decode lay digest=some (wordList word) := by
  simp only [preimages,Finset.mem_filter,Finset.mem_univ,true_and]
theorem preimages_card (lay : Layer) (word : Encoding lay) : (preimages lay word).card≤1 := by
  apply Finset.card_le_one.mpr
  intro left hl right hr
  exact decode_some_injective ((mem_preimages _ _ _).mp hl) ((mem_preimages _ _ _).mp hr)
noncomputable def targets (lay : Layer) (words : Finset (Encoding lay)) : Finset Digest :=
  words.biUnion (preimages lay)
@[simp] theorem mem_targets (lay : Layer) (words : Finset (Encoding lay)) (digest : Digest) :
    digest ∈ targets lay words ↔ ∃ word ∈ words,decode lay digest=some (wordList word) := by
  simp only [targets,Finset.mem_biUnion,mem_preimages]
theorem targets_card (lay : Layer) (words : Finset (Encoding lay)) :
    (targets lay words).card≤words.card := by
  calc
    _ ≤ ∑ word ∈ words,(preimages lay word).card := Finset.card_biUnion_le
    _ ≤ ∑ _word ∈ words,1 := Finset.sum_le_sum fun word _ => preimages_card lay word
    _ = _ := by simp
theorem source_decoded_target {lay : Layer} {digest : Digest} {digits : List Nat}
    (hd : decode lay digest=some digits) (words : Finset (Encoding lay)) :
    digest ∈ targets lay words ↔ decodedWord hd ∈ words := by
  rw [mem_targets]
  constructor
  · rintro ⟨word,hw,he⟩
    have hl : wordList (decodedWord hd)=wordList word := by
      rw [wordList,decodedWord_list hd]
      exact Option.some.inj (hd.symm.trans he)
    exact wordList_injective lay hl ▸ hw
  · intro hw
    refine ⟨decodedWord hd,hw,?_⟩
    simpa only [wordList,decodedWord_list hd] using hd
theorem uniform_target_words (lay : Layer) (words : Finset (Encoding lay)) :
    Pr[fun output => ∃ word ∈ words,
      decode lay (output.extractLsb' 0 128)=some (wordList word) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ words.card/(2 : ENNReal)^128 := by
  have he : Pr[fun output => ∃ word ∈ words,
      decode lay (output.extractLsb' 0 128)=some (wordList word) |
        ($ᵗ HashOutput : ProbComp HashOutput)]=
      Pr[fun output => output.extractLsb' 0 128 ∈ targets lay words |
        ($ᵗ HashOutput : ProbComp HashOutput)] :=
    probEvent_congr' (fun output _ => (mem_targets _ _ _).symm) rfl
  rw [he,uniform_low_mem]
  exact ENNReal.div_le_div_right (by exact_mod_cast targets_card lay words) _
abbrev Family := (lay : Layer) × Finset (Encoding lay)
noncomputable def selectedTargets (select : LazyPrivate.State → HashInput → Option Family) : PublicTargets :=
  fun state input => match select state input with
    | none => ∅
    | some family => targets family.1 family.2
theorem selected_targets_card (select : LazyPrivate.State → HashInput → Option Family)
    (bound : Nat) (hb : ∀ state input family,select state input=some family → family.2.card ≤ bound)
    (state : LazyPrivate.State) (input : HashInput) :
    (selectedTargets select state input).card ≤ bound := by
  unfold selectedTargets
  cases he : select state input with
  | none => simp
  | some family => exact (targets_card family.1 family.2).trans (hb _ _ _ he)
theorem selected_encoding_bound {α : Type}
    (select : LazyPrivate.State → HashInput → Option Family) (bound : Nat)
    (hb : ∀ state input family,select state input=some family → family.2.card ≤ bound)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true |
      observe (publicTargetTest (selectedTargets select)) program state] ≤
      budget*((bound : ENNReal)/(2 : ENNReal)^128) :=
  public_targets_bound _ bound (selected_targets_card select bound hb) program state budget
abbrev PointedWord := (lay : Layer) × (Encoding lay × ChainIndex lay)
noncomputable def unitFamily (word : PointedWord) : Family :=
  ⟨word.1,MixedCode.unitNeighbors word.2.1 word.2.2⟩
theorem selected_unit_neighbor_bound {α : Type}
    (select : LazyPrivate.State → HashInput → Option PointedWord)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true |
      observe (publicTargetTest (selectedTargets (fun state input =>
        (select state input).map unitFamily))) program state] ≤
      budget*((57 : ENNReal)/(2 : ENNReal)^128) := by
  apply selected_encoding_bound _ 57 _ program state budget
  intro before input family he
  cases hs : select before input with
  | none => simp [hs] at he
  | some word =>
      simp only [hs,Option.map_some,Option.some.injEq] at he
      rw [← he]
      exact unit_neighbors_bound word.1 word.2.1 word.2.2
abbrev UnpointedWord := (lay : Layer) × Encoding lay
noncomputable def allNeighborFamily (word : UnpointedWord) : Family :=
  ⟨word.1,MixedCode.allUnitNeighbors word.2⟩
theorem selected_all_neighbor_bound {α : Type}
    (select : LazyPrivate.State → HashInput → Option UnpointedWord)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => result.calls≤budget ∧ result.hit=true |
      observe (publicTargetTest (selectedTargets (fun state input =>
        (select state input).map allNeighborFamily))) program state] ≤
      budget*((3306 : ENNReal)/(2 : ENNReal)^128) := by
  apply selected_encoding_bound _ 3306 _ program state budget
  intro before input family he
  cases hs : select before input with
  | none => simp [hs] at he
  | some word =>
      simp only [hs,Option.map_some,Option.some.injEq] at he
      rw [← he]
      exact all_neighbors_bound word.1 word.2
end SigGolfCandidate.T3.Security.EncodingTargets
end
section
namespace SigGolfCandidate.T3.MixedCode
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {code : Code}
def backwardWork (reference candidate : Encoding code) : Nat :=
  ∑ i,((reference i).val-(candidate i).val)
theorem backwardWork_zero_iff (reference candidate : Encoding code) :
    backwardWork reference candidate=0 ↔ ∀ i,(reference i).val ≤ (candidate i).val := by
  simp only [backwardWork,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies,
    Nat.sub_eq_zero_iff_le]
theorem backwardWork_zero_valid_iff {reference candidate : Encoding code}
    (hr : Valid reference) (hc : Valid candidate) :
    backwardWork reference candidate=0 ↔ candidate=reference := by
  constructor
  · intro h
    exact (eq_of_le_of_valid hr hc ((backwardWork_zero_iff _ _).mp h)).symm
  · intro h
    subst candidate
    simp [backwardWork]
theorem UnitNeighborAt.backwardWork_eq_one {reference candidate : Encoding code}
    {lowered : Fin code.n} (h : UnitNeighborAt reference candidate lowered) :
    backwardWork reference candidate=1 := by
  unfold backwardWork
  rw [Finset.sum_eq_single lowered]
  · have := h.2.2.1
    omega
  · intro other _ ho
    exact Nat.sub_eq_zero_of_le (h.2.2.2 other ho)
  · simp
theorem backwardWork_one_iff {reference candidate : Encoding code}
    (hr : Valid reference) (hc : Valid candidate) :
    backwardWork reference candidate=1 ↔ ∃ lowered,UnitNeighborAt reference candidate lowered := by
  constructor
  · intro h
    have hex : ∃ i,(reference i).val-(candidate i).val≠0 := by
      by_contra hn
      push Not at hn
      have hz : backwardWork reference candidate=0 := Finset.sum_eq_zero fun i _ => hn i
      omega
    obtain ⟨lowered,hl⟩ := hex
    have hle : (reference lowered).val-(candidate lowered).val≤1 := by
      rw [← h]
      unfold backwardWork
      exact Finset.single_le_sum
        (f := fun i : Fin code.n => (reference i).val-(candidate i).val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ lowered)
    have hone : (reference lowered).val-(candidate lowered).val=1 := by omega
    refine ⟨lowered,hr,hc,by omega,?_⟩
    intro other ho
    have hp : ((reference other).val-(candidate other).val)+
        ((reference lowered).val-(candidate lowered).val)≤backwardWork reference candidate := by
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun i => (reference i).val-(candidate i).val)
        (Finset.subset_univ ({other,lowered} : Finset (Fin code.n))) (fun _ _ _ => Nat.zero_le _)
      simpa only [backwardWork,Finset.sum_pair ho] using hsum
    omega
  · rintro ⟨lowered,hl⟩
    exact hl.backwardWork_eq_one
theorem backwardWork_trichotomy {reference candidate : Encoding code}
    (hr : Valid reference) (hc : Valid candidate) :
    candidate=reference ∨ (∃ lowered,UnitNeighborAt reference candidate lowered) ∨
      2≤backwardWork reference candidate := by
  by_cases hz : backwardWork reference candidate=0
  · exact Or.inl ((backwardWork_zero_valid_iff hr hc).mp hz)
  · by_cases ho : backwardWork reference candidate=1
    · exact Or.inr (Or.inl ((backwardWork_one_iff hr hc).mp ho))
    · exact Or.inr (Or.inr (by omega))
theorem distinct_backward_cases {reference candidate : Encoding code}
    (hr : Valid reference) (hc : Valid candidate) (hne : candidate≠reference) :
    candidate ∈ allUnitNeighbors reference ∨ 2≤backwardWork reference candidate := by
  rcases backwardWork_trichotomy hr hc with he | hu | ht
  · exact False.elim (hne he)
  · exact Or.inl (mem_allUnitNeighbors.mpr hu)
  · exact Or.inr ht
theorem two_backward_steps {reference candidate : Encoding code}
    (h : 2≤backwardWork reference candidate) :
    (∃ i,(candidate i).val+2≤(reference i).val) ∨
      ∃ i j,i≠j ∧ (candidate i).val<(reference i).val ∧
        (candidate j).val<(reference j).val := by
  by_cases htwo : ∃ i,(candidate i).val+2≤(reference i).val
  · exact Or.inl htwo
  · push Not at htwo
    have hex : ∃ i,(candidate i).val<(reference i).val := by
      by_contra hn
      push Not at hn
      have hz := (backwardWork_zero_iff reference candidate).mpr hn
      omega
    obtain ⟨i,hi⟩ := hex
    have hexj : ∃ j,j≠i ∧ (candidate j).val<(reference j).val := by
      by_contra hn
      push Not at hn
      have he : backwardWork reference candidate=(reference i).val-(candidate i).val := by
        unfold backwardWork
        apply Finset.sum_eq_single i
        · intro j _ hj
          exact Nat.sub_eq_zero_of_le (hn j hj)
        · simp
      have := htwo i
      omega
    obtain ⟨j,hji,hj⟩ := hexj
    exact Or.inr ⟨i,j,Ne.symm hji,hi,hj⟩
end SigGolfCandidate.T3.MixedCode
namespace SigGolfCandidate.T3.Security.EncodingTargets
open MixedCode
theorem decoded_backward_cases {lay : Layer} {referenceDigest candidateDigest : Digest}
    {referenceDigits candidateDigits : List Nat}
    (hr : decode lay referenceDigest=some referenceDigits)
    (hc : decode lay candidateDigest=some candidateDigits)
    (hne : candidateDigest≠referenceDigest) :
    decodedWord hc ∈ allUnitNeighbors (decodedWord hr) ∨
      2≤backwardWork (decodedWord hr) (decodedWord hc) := by
  apply distinct_backward_cases (decodedWord_valid hr) (decodedWord_valid hc)
  intro he
  have hl : candidateDigits=referenceDigits := by
    rw [← decodedWord_list hc,← decodedWord_list hr,he]
  rw [hl] at hc
  exact hne (decode_some_injective hc hr)
end SigGolfCandidate.T3.Security.EncodingTargets
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure QueryEvent where
  before : LazyPrivate.State
  input : T3.Spec.Domain
  answer : T3.Spec.Range input
structure Recorded (α : Type) where
  value : α
  events : List QueryEvent
  state : LazyPrivate.State
noncomputable def record {α : Type} (program : M α) : LazyPrivate.State → ProbComp (Recorded α) :=
  OracleComp.construct
    (fun value state => pure ⟨value,[],state⟩)
    (fun input _ next state => do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,⟨state,input,middle.1⟩::last.events,last.state⟩) <$>
        next middle.1 middle.2) program
theorem record_pure {α : Type} (value : α) (state : LazyPrivate.State) :
    record (pure value : M α) state=pure ⟨value,[],state⟩ := rfl
theorem record_query_bind {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    record (liftM (T3.Spec.query input) >>= next) state=(do
      let middle ← LazyPrivate.run (liftM (T3.Spec.query input)) state
      (fun last => ⟨last.value,⟨state,input,middle.1⟩::last.events,last.state⟩) <$>
        record (next middle.1) middle.2) := rfl
def summarize {α : Type} (test : Test) (result : Recorded α) : Observation α :=
  ⟨result.value,(result.events.map (fun event => FullGame.queryCharge event.input)).sum,
    result.events.any (fun event => test event.before event.input event.answer),result.state⟩
theorem record_observe {α : Type} (test : Test) (program : M α) (state : LazyPrivate.State) :
    summarize test <$> record program state=observe test program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [record_pure,map_pure,observe_pure];rfl
  | query_bind input next ih =>
      rw [record_query_bind,map_bind,observe_query_bind]
      apply bind_congr
      intro middle
      have h := congrArg (Functor.map (fun last : Observation α =>
        (⟨last.value,FullGame.queryCharge input+last.calls,
          test state input middle.1 || last.hit,last.state⟩ : Observation α)))
        (ih middle.1 middle.2)
      simpa only [Functor.map_map,summarize,List.map_cons,List.sum_cons,List.any_cons,
        Function.comp_def] using h
theorem record_erasure {α : Type} (program : M α) (state : LazyPrivate.State) :
    (fun result : Recorded α => (result.value,result.state)) <$> record program state=
      LazyPrivate.run program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [record_pure,map_pure,LazyPrivate.run_pure]
  | query_bind input next ih =>
      rw [record_query_bind,map_bind,LazyPrivate.run_bind]
      apply bind_congr
      intro middle
      simpa only [Functor.map_map,Function.comp_def] using ih middle.1 middle.2
theorem recorded_support {α : Type} (program : M α) (state : LazyPrivate.State)
    (result : Recorded α) (hr : result ∈ support (record program state)) :
    (result.value,result.state) ∈ support (LazyPrivate.run program state) := by
  rw [← record_erasure,support_map]
  exact ⟨result,hr,rfl⟩
theorem recorded_query_known {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : Recorded α) (hr : result ∈ support (record program before)) :
    ∀ event ∈ result.events,SourceReplay.known result.state event.input=some event.answer ∧
      SourceReplay.Extends event.before result.state := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [record_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      obtain ⟨hi,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [record_query_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last,hl,rfl⟩ := hr
      have htail := recorded_support (next middle.1) middle.2 last hl
      have hext := SourceReplay.run_extends (next middle.1) middle.2 (last.value,last.state) htail
      intro event he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨SourceReplay.known_mono middle.2 last.state hext
          (SourceReplay.hash_query_caches input hi before middle hm),
          (SourceReplay.query_extends input before middle hm).trans hext⟩
      · exact ih middle.1 (hn middle.1) middle.2 last hl event he
theorem recorded_inputs {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : Recorded α) (hr : result ∈ support (record program before))
    (answers : Correctness.Answers)
    (hagrees : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer) :
    result.events.map QueryEvent.input=SourceReplay.queried answers program := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [record_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      rfl
  | query_bind input next ih =>
      obtain ⟨hi,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [record_query_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last,hl,rfl⟩ := hr
      have htail := recorded_support (next middle.1) middle.2 last hl
      have hext := SourceReplay.run_extends (next middle.1) middle.2 (last.value,last.state) htail
      have hknown := SourceReplay.known_mono middle.2 last.state hext
        (SourceReplay.hash_query_caches input hi before middle hm)
      rw [List.map_cons,SourceReplay.queried_query_bind,hagrees input middle.1 hknown]
      exact congrArg (List.cons input) (ih middle.1 (hn middle.1) middle.2 last hl hagrees)
theorem recorded_hit_bound {α : Type} (test : Test) (rate : ENNReal)
    (hstep : ∀ state input,
      Pr[fun result => test state input result.1=true |
        LazyPrivate.run (liftM (T3.Spec.query input)) state] ≤ FullGame.queryCharge input*rate)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤budget ∧
      ∃ event ∈ result.events,test event.before event.input event.answer=true | record program state] ≤
        budget*rate := by
  have h := observe_hit_bound test rate hstep program state budget
  rw [← record_observe,probEvent_map] at h
  simpa only [Function.comp_def,summarize,List.any_eq_true] using h
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem extracted_public_occurrence {α : Type} (program : M α)
    (hp : SourceReplay.HashOnly program) (before : LazyPrivate.State)
    (result : Recorded α) (hr : result ∈ support (record program before))
    (input : HashInput)
    (hq : .inl (.inr input) ∈ SourceReplay.queried (SourceReplay.answers result.state) program) :
    ∃ prior,⟨prior,.inl (.inr input),SourceReplay.answers result.state (.inl (.inr input))⟩ ∈ result.events ∧
      SourceReplay.Extends prior result.state := by
  rw [← recorded_inputs program hp before result hr (SourceReplay.answers result.state)
    (SourceReplay.answers_known result.state)] at hq
  obtain ⟨event,he,hi⟩ := List.mem_map.mp hq
  obtain ⟨prior,query,answer⟩ := event
  change query=.inl (.inr input) at hi
  subst query
  obtain ⟨hknown,hext⟩ := recorded_query_known program hp before result hr _ he
  have ha := SourceReplay.answers_known result.state _ _ hknown
  exact ⟨prior,by simpa only [ha] using he,hext⟩
theorem recorded_cost_eq_length {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : Recorded α) (hr : result ∈ support (record program before)) :
    (result.events.map (fun event => FullGame.queryCharge event.input)).sum=
      (SourceReplay.queried (SourceReplay.answers result.state) program).length := by
  have he := recorded_inputs program hp before result hr (SourceReplay.answers result.state)
    (SourceReplay.answers_known result.state)
  rw [← he,List.length_map]
  have hcharges : ∀ event ∈ result.events,FullGame.queryCharge event.input=1 := by
    intro event hevent
    have hknown := (recorded_query_known program hp before result hr event hevent).1
    rcases event with ⟨prior,query,answer⟩
    change SourceReplay.known result.state query=some answer at hknown
    have hi : SourceReplay.IsHash query := by
      cases query with
      | inl input =>
          cases input with
          | inl n => simp [SourceReplay.known] at hknown
          | inr input => trivial
      | inr coordinate => trivial
    simp only [FullGame.queryCharge,if_pos (SourceReplay.hash_charged query hi)]
  rw [List.map_congr_left hcharges]
  simp
def KnownPublicHit (reference : Reference) {α : Type} (result : Recorded α) : Prop :=
  ∃ prior input answer honest output,
    (⟨prior,.inl (.inr input),answer⟩ : QueryEvent) ∈ result.events ∧
    prior.2 input=none ∧ reference prior input=some honest ∧ prior.2 honest=some output ∧
    answer.extractLsb' 0 128=output.extractLsb' 0 128
theorem knownPublicHit_iff (reference : Reference) {α : Type} (result : Recorded α) :
    KnownPublicHit reference result ↔
      ∃ event ∈ result.events,
        publicTargetTest (onePublicTarget (knownTarget reference)) event.before event.input event.answer=true := by
  constructor
  · rintro ⟨prior,input,answer,honest,output,he,hfresh,href,hknown,heq⟩
    exact ⟨⟨prior,.inl (.inr input),answer⟩,he,
      (known_target_test_iff reference prior input answer).mpr
        ⟨hfresh,honest,output,href,hknown,heq⟩⟩
  · rintro ⟨⟨prior,query,answer⟩,he,ht⟩
    cases query with
    | inl query =>
        cases query with
        | inl n => simp [publicTargetTest] at ht
        | inr input =>
            obtain ⟨hfresh,honest,output,href,hknown,heq⟩ :=
              (known_target_test_iff reference prior input answer).mp ht
            exact ⟨prior,input,answer,honest,output,he,hfresh,href,hknown,heq⟩
    | inr coordinate => simp [publicTargetTest] at ht
theorem recorded_known_public_hit_bound {α : Type} (reference : Reference)
    (program : M α) (state : LazyPrivate.State) (budget : Nat) :
    Pr[fun result => (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤budget ∧
      KnownPublicHit reference result | record program state] ≤ budget/(2 : ENNReal)^128 := by
  have hcard : ∀ state input,(onePublicTarget (knownTarget reference) state input).card≤1 := by
    intro state input
    simp only [onePublicTarget]
    cases knownTarget reference state input <;> simp
  have h := recorded_hit_bound _ _
    (public_target_hazard (onePublicTarget (knownTarget reference)) 1 hcard) program state budget
  simpa only [Nat.cast_one,mul_one_div,← knownPublicHit_iff] using h
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure State where
  base : MonitoredPrivate.State
  events : List FirstHit.QueryEvent
noncomputable def handler : QueryImpl T3.Spec (StateT State ProbComp) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1,⟨result.2,state.events++[⟨state.base.source.2,input,result.1⟩]⟩)) <$>
      MonitoredPrivate.run (liftM (T3.Spec.query input)) state.base
noncomputable def run {α : Type} (program : M α) (state : State) : ProbComp (α × State) :=
  (simulateQ handler program).run state
theorem run_pure {α : Type} (value : α) (state : State) :
    run (pure value : M α) state=pure (value,state) := rfl
theorem run_bind {α β : Type} (program : M α) (next : α → M β) (state : State) :
    run (program >>= next) state=(do let middle ← run program state;run (next middle.1) middle.2) := by
  simp only [run,simulateQ_bind,StateT.run_bind]
theorem run_map {α β : Type} (f : α → β) (program : M α) (state : State) :
    run (f <$> program) state=Prod.map f id <$> run program state := by
  simp only [run,simulateQ_map,StateT.run_map]
  rfl
theorem run_query (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (fun result => (result.1,⟨result.2,state.events++[⟨state.base.source.2,input,result.1⟩]⟩)) <$>
        MonitoredPrivate.run (liftM (T3.Spec.query input)) state.base := by
  simp only [run,simulateQ_spec_query,handler,StateT.run_mk]
theorem run_erasure {α : Type} (program : M α) (state : State) :
    Prod.map id State.base <$> run program state=MonitoredPrivate.run program state.base := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run_pure,map_pure,MonitoredPrivate.run_pure,Prod.map,id_eq]
  | query_bind input next ih =>
      rw [run_bind,map_bind,MonitoredPrivate.run_bind,run_query,bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 ⟨middle.2,state.events++[⟨state.base.source.2,input,middle.1⟩]⟩
theorem run_support {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) :
    (result.1,result.2.base) ∈ support (MonitoredPrivate.run program before.base) := by
  rw [← run_erasure,support_map]
  exact ⟨result,hr,rfl⟩
theorem run_query_explicit (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (fun result =>
        let counted := (state.base.source.1+FullGame.queryCharge input,result.2)
        (result.1,⟨⟨counted,MonitoredPrivate.flag state.base counted⟩,
          state.events++[⟨state.base.source.2,input,result.1⟩]⟩)) <$>
        LazyPrivate.run (liftM (T3.Spec.query input)) state.base.source.2 := by
  rw [run_query,MonitoredPrivate.run_query,CountedPrivate.run_query]
  simp only [Functor.map_map]
def recorded {α : Type} (result : α × State) : FirstHit.Recorded α :=
  ⟨result.1,result.2.events,result.2.base.source.2⟩
def prepend {α : Type} (events : List FirstHit.QueryEvent) (result : FirstHit.Recorded α) :
    FirstHit.Recorded α := ⟨result.value,events++result.events,result.state⟩
theorem run_recorded {α : Type} (program : M α) (state : State) :
    recorded <$> run program state=
      prepend state.events <$> FirstHit.record program state.base.source.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run_pure,map_pure,FirstHit.record_pure,recorded,prepend,List.append_nil]
  | query_bind input next ih =>
      rw [run_bind,map_bind,run_query_explicit,bind_map_left]
      rw [FirstHit.record_query_bind,map_bind]
      apply bind_congr
      intro middle
      rw [ih]
      simp only [Functor.map_map]
      congr 1
      funext last
      simp [prepend,List.append_assoc]
def CostCoherent (state : State) : Prop :=
  state.base.source.1=(state.events.map (fun event => FullGame.queryCharge event.input)).sum
theorem run_cost_coherent {α : Type} (program : M α) (before : State) (hc : CostCoherent before)
    (result : α × State) (hr : result ∈ support (run program before)) : CostCoherent result.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact hc
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [run_query_explicit,support_map] at hm
      obtain ⟨step,hs,rfl⟩ := hm
      apply ih step.1 _ _ result hr
      change before.base.source.1+FullGame.queryCharge input=
        ((before.events++[(⟨before.base.source.2,input,step.1⟩ : FirstHit.QueryEvent)]).map
          (fun event => FullGame.queryCharge event.input)).sum
      simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
      exact congrArg (fun n => n+FullGame.queryCharge input) hc
theorem run_events_extend {α : Type} (program : M α) (before : State) (result : α × State)
    (hr : result ∈ support (run program before)) : before.events.IsPrefix result.2.events := by
  have hm : recorded result ∈ support (recorded <$> run program before) := by
    rw [support_map]
    exact ⟨result,hr,rfl⟩
  rw [run_recorded,support_map] at hm
  obtain ⟨last,hl,he⟩ := hm
  have hevents := congrArg FirstHit.Recorded.events he
  exact ⟨last.events,hevents⟩
end SigGolfCandidate.T3.Security.QueryRecorded
end
section
namespace SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {ι State Label Extra : Type} {spec : OracleSpec ι}
structure Refinement (model : ProposalModel spec State Label) (Extra : Type) where
  project : Extra → State
  Outcome : spec.Domain → Type
  outcome : (input : spec.Domain) → Outcome input → model.Outcome input
  record : (input : spec.Domain) → Extra → PMF (Outcome input)
  advance : (input : spec.Domain) → Extra → Outcome input → Extra
  record_project : ∀ input state,(record input state).map (outcome input)=model.record input (project state)
  advance_project : ∀ input state result,
    project (advance input state result)=model.advance input (project state) (outcome input result)
namespace Refinement
variable {model : ProposalModel spec State Label} (refinement : Refinement model Extra)
theorem label_project (input : spec.Domain) (state : Extra) :
    (refinement.record input state).map (fun result => model.label input (refinement.outcome input result))=
      (model.record input (refinement.project state)).map (model.label input) := by
  rw [← refinement.record_project input state,PMF.map_comp]
  rfl
noncomputable def model' : ProposalModel spec Extra Label where
  Outcome := refinement.Outcome
  record := refinement.record
  response input result := model.response input (refinement.outcome input result)
  advance := refinement.advance
  label input result := model.label input (refinement.outcome input result)
  active input state := model.active input (refinement.project state)
  base := model.base
  accept := model.accept
  positive := model.positive
  lt_one := model.lt_one
  cap := by
    intro input state ha point
    rw [refinement.label_project]
    exact model.cap input (refinement.project state) ha point
theorem rejected_project (input : spec.Domain) (state : Extra) :
    refinement.model'.rejected input state=model.rejected input (refinement.project state) := by
  unfold rejected
  change (if h : model.active input (refinement.project state)=true then
    proposalResidualLaw model.base
      ((refinement.record input state).map (fun result => model.label input (refinement.outcome input result)))
      model.accept model.lt_one _ else model.base)=_
  simp only [refinement.label_project]
theorem bridge_project (input : spec.Domain) (state : Extra) :
    (recordProposalBridge (refinement.record input state) (refinement.model'.rejected input state)
      model.accept model.positive model.lt_one.le).map (Prod.map id (refinement.outcome input))=
      recordProposalBridge (model.record input (refinement.project state))
        (model.rejected input (refinement.project state)) model.accept model.positive model.lt_one.le := by
  rw [refinement.rejected_project,← refinement.record_project input state]
  simp only [recordProposalBridge,PMF.map_bind,PMF.bind_map,PMF.map_comp,Function.comp_def,Prod.map,id_eq]
theorem traced_query_project (input : spec.Domain) (state : List Label × Extra) :
    Prod.map id (Prod.map id refinement.project) <$> (refinement.model'.traced input).run state=
      (model.traced input).run (state.1,refinement.project state.2) := by
  change PMF.map _ _=_
  simp only [traced,proposalRecordImpl,StateT.run_mk]
  change PMF.map _ (if model.active input (refinement.project state.2) then _ else _)=_
  by_cases ha : model.active input (refinement.project state.2)=true
  · simp only [ha,if_true,PMF.map_comp,Function.comp_def,Prod.map,id_eq]
    change (recordProposalBridge (refinement.record input state.2) (refinement.model'.rejected input state.2)
      model.accept model.positive model.lt_one.le).map (fun result =>
        (model.response input (refinement.outcome input result.2),
          (state.1++result.1++[model.label input (refinement.outcome input result.2)],
            refinement.project (refinement.advance input state.2 result.2))))=_
    simp_rw [refinement.advance_project]
    rw [← refinement.bridge_project input state.2,PMF.map_comp]
    rfl
  · simp only [ha,Bool.false_eq_true,if_false,PMF.map_comp,Function.comp_def,Prod.map,id_eq]
    change (refinement.record input state.2).map (fun result =>
      (model.response input (refinement.outcome input result),
        (state.1,refinement.project (refinement.advance input state.2 result))))=_
    simp_rw [refinement.advance_project]
    rw [← refinement.record_project input state.2,PMF.map_comp]
    rfl
theorem traced_project {α : Type} (program : OracleComp spec α) (state : List Label × Extra) :
    Prod.map id (Prod.map id refinement.project) <$>
      (simulateQ refinement.model'.traced program).run state=
        (simulateQ model.traced program).run (state.1,refinement.project state.2) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map id refinement.project)
    refinement.traced_query_project program state
end Refinement
end SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
end
section
namespace SigGolfCandidate.T3.Sampling
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
theorem completeRecord_map {A B : Type} (f : A → B) (observed : B → Option HashOutput)
    (program : ProbComp A) :
    Prod.map f id <$> completeRecord (fun record => observed (f record)) program=
      completeRecord observed (f <$> program) := by
  simp only [completeRecord,map_bind,map_pure,bind_map_left,Prod.map,id_eq]
end SigGolfCandidate.T3.Sampling
namespace SigGolfCandidate.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def recordLaw (published : T3.Cache) (request : Request) (state : State) :
    PMF (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets) :=
  liftM (Sampling.completeRecord (fun result => result.1.2)
    (run (FullGame.authenticatedRecord published request) state))
def Outcome : LazyPrivate.Interaction.Domain → Type
  | .inl input => SphincsSecurity.OracleWorld.Range input × State
  | .inr _ => (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)
def outcome : (input : LazyPrivate.Interaction.Domain) → Outcome input → MonitoredPrivate.Outcome input
  | .inl _,result => (result.1,result.2.base)
  | .inr _,result => ((result.1.1,result.1.2.base),result.2)
noncomputable def interactionRecord (published : T3.Cache) :
    (input : LazyPrivate.Interaction.Domain) → State → PMF (Outcome input)
  | .inl input,state => liftM (run (forwardWorld input) state)
  | .inr request,state => recordLaw published request state
def advance : (input : LazyPrivate.Interaction.Domain) → State → Outcome input → State
  | .inl _,_,result => result.2
  | .inr _,_,result => result.1.2
theorem recordLaw_project (published : T3.Cache) (request : Request) (state : State) :
    (recordLaw published request state).map (outcome (.inr request))=
      MonitoredPrivate.recordLaw published request state.base := by
  have hm := Sampling.completeRecord_map (Prod.map id State.base)
    (fun result : (Option Signature × Option HashOutput) × MonitoredPrivate.State => result.1.2)
    (run (FullGame.authenticatedRecord published request) state)
  rw [run_erasure] at hm
  have h := congrArg (fun program : ProbComp (((Option Signature × Option HashOutput) ×
      MonitoredPrivate.State) × DigestSampling.IndexBuckets) => (liftM program : PMF _)) hm
  rw [liftM_map,PMF.monad_map_eq_map] at h
  exact h
theorem interactionRecord_project (published : T3.Cache) (input : LazyPrivate.Interaction.Domain)
    (state : State) :
    (interactionRecord published input state).map (outcome input)=
      MonitoredPrivate.interactionRecord published input state.base := by
  cases input with
  | inl input =>
      rw [← PMF.monad_map_eq_map,interactionRecord,← liftM_map]
      change (liftM (Prod.map id State.base <$> run (forwardWorld input) state) : PMF _)=_
      rw [run_erasure]
      rfl
  | inr request => exact recordLaw_project published request state
noncomputable def refinement (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel.Refinement (MonitoredPrivate.proposalModel published budget hbudget) State where
  project := State.base
  Outcome := Outcome
  outcome := outcome
  record := interactionRecord published
  advance := advance
  record_project := interactionRecord_project published
  advance_project := by intro input state result;cases input <;> rfl
noncomputable def proposalModel (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :=
  (refinement published budget hbudget).model'
theorem proposal_trace_project {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id (Prod.map id State.base) <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
        (simulateQ (MonitoredPrivate.proposalModel published budget hbudget).traced program).run
          (history,state.base) :=
  (refinement published budget hbudget).traced_project program (history,state)
theorem recordLaw_erasure (published : T3.Cache) (request : Request) (state : State) :
    (recordLaw published request state).map (fun result => (result.1.1.1,result.1.2))=
      (liftM (run (FullGame.authenticatedSign published request) state) : PMF (Option Signature × State)) := by
  have hsign : Prod.map Prod.fst id <$> run (FullGame.authenticatedRecord published request) state=
      run (FullGame.authenticatedSign published request) state := by
    rw [← run_map,FullGame.authenticatedRecord_erasure]
  have hg :
      𝒮[(fun result => (result.1.1.1,result.1.2)) <$>
        Sampling.completeRecord (fun result => result.1.2)
          (run (FullGame.authenticatedRecord published request) state)]=
      𝒮[run (FullGame.authenticatedSign published request) state] := by
    trans 𝒮[Prod.map Prod.fst id <$>
      (Prod.fst <$> Sampling.completeRecord (fun result => result.1.2)
        (run (FullGame.authenticatedRecord published request) state))]
    · rw [Functor.map_map]
      rfl
    · rw [evalSPMF_map,Sampling.completeRecord_erasure,← evalSPMF_map,hsign]
  apply PMF.ext
  intro response
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,← PMF.probOutput_eq_apply]
  have h := evalSPMF_ext_iff.mp hg response
  rw [probOutput_map] at h
  exact h
theorem proposal_query_erasure (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (run (MonitoredPrivate.interactionSource published input) state) :
        PMF (LazyPrivate.Interaction.Range input × State)) := by
  cases input with
  | inl input =>
      change id <$> (liftM (run (forwardWorld input) state) : PMF _)=_
      rw [id_map]
      rfl
  | inr request => exact recordLaw_erasure published request state
theorem proposal_execution_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (run (simulateQ (MonitoredPrivate.interactionSource published) program) state) : PMF (α × State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (run (simulateQ (MonitoredPrivate.interactionSource published) program) state) : PMF (α × State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
end SigGolfCandidate.T3.Security.QueryRecorded
end
section
namespace SigGolfCandidate.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen FullGame.idealGame
def initial : State := ⟨⟨(0,∅,∅),false⟩,[]⟩
theorem initial_cost : CostCoherent initial := rfl
theorem lift_run_erasure {α : Type} (program : M α) (state : State) :
    Prod.map id State.base <$> (liftM (run program state) : PMF _)=
      (liftM (MonitoredPrivate.run program state.base) : PMF _) := by
  rw [← liftM_map,run_erasure]
noncomputable def tracedExperiment (adversary : Adversary) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (MonitoredPrivate.History × State)) := do
  let generated ← (liftM (run keygen initial) : PMF _)
  let interaction ← (simulateQ (proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (FullGame.verdict generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem traced_base_erasure (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id (Prod.map id State.base) <$> tracedExperiment adversary budget hbudget=
      MonitoredPrivate.tracedExperiment adversary budget hbudget := by
  unfold tracedExperiment MonitoredPrivate.tracedExperiment
  simp only [map_bind,map_pure,Prod.map,id_eq]
  have hk := lift_run_erasure keygen initial
  change Prod.map id State.base <$> (liftM (run keygen initial) : PMF _)=
    (liftM (MonitoredPrivate.run keygen ⟨(0,∅,∅),false⟩) : PMF _) at hk
  rw [← hk,bind_map_left]
  apply bind_congr
  intro generated
  simp only [Prod.map,id_eq]
  rw [← proposal_trace_project generated.1.2 budget hbudget _ [] generated.2,bind_map_left]
  apply bind_congr
  intro interaction
  simp only [Prod.map,id_eq]
  rw [← lift_run_erasure (FullGame.verdict generated.1.1 interaction.1) interaction.2.2,bind_map_left]
  rfl
theorem traced_source_erasure (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment adversary budget hbudget=
      (liftM (run (FullGame.idealGame adversary) initial) : PMF _) := by
  unfold tracedExperiment FullGame.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [MonitoredPrivate.logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
def recordedTrace (result : Bool × (MonitoredPrivate.History × State)) : FirstHit.Recorded Bool :=
  recorded (result.1,result.2.2)
theorem traced_record_erasure (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (FullGame.idealGame adversary) (∅,∅)) : PMF _) := by
  have hr : recorded <$> run (FullGame.idealGame adversary) initial=
      FirstHit.record (FullGame.idealGame adversary) (∅,∅) := by
    rw [run_recorded]
    have hp : prepend ([] : List FirstHit.QueryEvent)=(id : FirstHit.Recorded Bool → FirstHit.Recorded Bool) := by
      funext result
      rfl
    change prepend [] <$> FirstHit.record (FullGame.idealGame adversary) (∅,∅)=_
    rw [hp,id_map]
  calc
    _ = recorded <$> (Prod.map id Prod.snd <$> tracedExperiment adversary budget hbudget) := by
      rw [Functor.map_map]
      rfl
    _ = recorded <$> (liftM (run (FullGame.idealGame adversary) initial) : PMF _) := by
      rw [traced_source_erasure]
    _ = (liftM (recorded <$> run (FullGame.idealGame adversary) initial) : PMF _) := (liftM_map _ _).symm
    _ = _ := by rw [hr]
theorem traced_cost_coherent (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment adversary budget hbudget).support) : CostCoherent result.2.2 := by
  have hp : (result.1,result.2.2) ∈
      (Prod.map id Prod.snd <$> tracedExperiment adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [traced_source_erasure] at hp
  rw [MonitoredPrivate.pmf_support] at hp
  exact run_cost_coherent (FullGame.idealGame adversary) initial initial_cost
    (result.1,result.2.2) hp
theorem known_public_hit_bound (reference : FirstHit.Reference) (adversary : Adversary)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
      tracedExperiment adversary q hq] ≤ q/(2 : ENNReal)^128 := by
  have h := FirstHit.recorded_known_public_hit_bound reference (FullGame.idealGame adversary) (∅,∅) q
  have he := congrArg (fun law => Pr[fun result : FirstHit.Recorded Bool =>
      (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤q ∧
      FirstHit.KnownPublicHit reference result | law]) (traced_record_erasure adversary q hq)
  rw [probEvent_map,MonitoredPrivate.event_lift] at he
  apply le_trans _ (he.le.trans h)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (tracedExperiment adversary q hq).support
  · have hc := traced_cost_coherent adversary q hq result hr
    simp only [Function.comp_def,recordedTrace,recorded]
    rw [show result.2.2.base.source.1=
      (result.2.2.events.map (fun event => FullGame.queryCharge event.input)).sum from hc]
  · have hz : (tracedExperiment adversary q hq) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self,le_refl]
theorem real_to_clean_trace (adversary : Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.base.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false |
          tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := MonitoredPrivate.real_to_clean_bounded_trace adversary q hq
  rw [← traced_base_erasure adversary q hq,probEvent_map] at h
  exact h
theorem full_game_excess_price (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice result.2.1-1 else 0) ≤ 11324/100000000 := by
  have h := MonitoredPrivate.full_game_excess_price adversary budget hbudget
  rw [← traced_base_erasure adversary budget hbudget,expectedValue_map] at h
  exact h
theorem full_game_near_price (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice result.2.1 else 0) ≤ 404 := by
  have h := MonitoredPrivate.full_game_near_price adversary budget hbudget
  rw [← traced_base_erasure adversary budget hbudget,expectedValue_map] at h
  exact h
end SigGolfCandidate.T3.Security.QueryRecorded
end
section
namespace SigGolfCandidate.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def CleanWin (q : Nat) (result : Bool × (MonitoredPrivate.History × State)) : Prop :=
  result.1=true ∧ result.2.2.base.source.1≤q ∧
    result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false
theorem split_known_hit (reference : FirstHit.Reference) (adversary : Adversary)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[CleanWin q | tracedExperiment adversary q hq] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment adversary q hq]+
      Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : CleanWin q result
  · have hcount := hw.2.1
    by_cases hh : FirstHit.KnownPublicHit reference (recordedTrace result)
    · simp [hw,hcount,hh]
    · simp [hw,hcount,hh]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_without_known (reference : FirstHit.Reference) (adversary : Adversary)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^128+q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_clean_trace adversary q hq).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact (split_known_hit reference adversary q hq).trans
    (add_le_add le_rfl (known_public_hit_bound reference adversary q hq))
theorem traced_base_support (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    (result.1,result.2.1,result.2.2.base) ∈
      (MonitoredPrivate.tracedExperiment adversary budget hbudget).support := by
  rw [← traced_base_erasure,PMF.monad_map_eq_map,PMF.support_map]
  exact ⟨result,hr,rfl⟩
theorem traced_game_journal (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment adversary budget hbudget).support)
    (hcount : result.2.2.base.source.1≤budget) (hflag : result.2.2.base.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.base.source.2 keygen generated ∧
        MonitoredPrivate.JournalOK generated.2 result.2.1 result.2.2.base journal :=
  MonitoredPrivate.traced_game_journal adversary budget hbudget (result.1,result.2.1,result.2.2.base)
    (traced_base_support adversary budget hbudget result hr) hcount hflag
theorem traced_journal_exposure (adversary : Adversary) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment adversary budget hbudget).support)
    (hcount : result.2.2.base.source.1≤budget) (hflag : result.2.2.base.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.base.source.2 keygen generated ∧
        MonitoredPrivate.JournalOK generated.2 result.2.1 result.2.2.base journal ∧
        BPORS.History.fullPrice (MonitoredPrivate.journalLabels journal)≤BPORS.History.fullPrice result.2.1 ∧
        BPORS.History.fullNearPrice (MonitoredPrivate.journalLabels journal)≤BPORS.History.fullNearPrice result.2.1 := by
  obtain ⟨generated,journal,hg,hj⟩ := traced_game_journal adversary budget hbudget result hr hcount hflag
  exact ⟨generated,journal,hg,hj,MonitoredPrivate.journal_prices generated.2 result.2.1 result.2.2.base journal hj⟩
end SigGolfCandidate.T3.Security.QueryRecorded
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem record_bind {α β : Type} (program : M α) (next : α → M β) (state : LazyPrivate.State) :
    record (program >>= next) state=(do
      let first ← record program state
      let last ← record (next first.value) first.state
      pure ⟨last.value,first.events++last.events,last.state⟩) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [pure_bind,record_pure,List.nil_append];simp
  | query_bind input rest ih =>
      rw [bind_assoc,record_query_bind,record_query_bind]
      simp only [bind_map_left,bind_assoc]
      apply bind_congr
      intro middle
      rw [ih]
      simp only [map_bind,map_pure]
      apply bind_congr
      intro first
      apply bind_congr
      intro last
      rfl
theorem record_map {α β : Type} (f : α → β) (program : M α) (state : LazyPrivate.State) :
    record (f <$> program) state=
      (fun result : Recorded α => (⟨f result.value,result.events,result.state⟩ : Recorded β)) <$>
        record program state := by
  rw [map_eq_bind_pure_comp,record_bind]
  simp only [Function.comp_def,record_pure,map_pure,List.append_nil,bind_pure_comp]
theorem record_bind_support {α β : Type} (program : M α) (next : α → M β)
    (before : LazyPrivate.State) (result : Recorded β)
    (hr : result ∈ support (record (program >>= next) before)) :
    ∃ first ∈ support (record program before),∃ last ∈ support (record (next first.value) first.state),
      result.value=last.value ∧ result.events=first.events++last.events ∧ result.state=last.state := by
  rw [record_bind,mem_support_bind_iff] at hr
  obtain ⟨first,hf,hr⟩ := hr
  rw [mem_support_bind_iff] at hr
  obtain ⟨last,hl,hr⟩ := hr
  rw [support_pure,Set.mem_singleton_iff] at hr
  subst result
  exact ⟨first,hf,last,hl,rfl,rfl,rfl⟩
theorem recorded_tail_public_occurrence {α β : Type} (next : α → M β) (result : Recorded β)
    (first : Recorded α) (last : Recorded β)
    (hlast : last ∈ support (record (next first.value) first.state))
    (hp : SourceReplay.HashOnly (next first.value))
    (hevents : result.events=first.events++last.events)
    (input : HashInput)
    (hq : .inl (.inr input) ∈ SourceReplay.queried (SourceReplay.answers last.state) (next first.value)) :
    ∃ prior,(⟨prior,.inl (.inr input),SourceReplay.answers last.state (.inl (.inr input))⟩ : QueryEvent)
      ∈ result.events := by
  obtain ⟨prior,he,_⟩ := extracted_public_occurrence (next first.value) hp first.state last hlast input hq
  exact ⟨prior,hevents ▸ List.mem_append_right first.events he⟩
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open FullGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq T3.Cache := Classical.decEq _
noncomputable local instance : DecidableEq SiggolfT3Mac4.Cache := Classical.decEq _
noncomputable local instance : DecidableEq Region := Classical.decEq _
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : Fintype OtherCoordinate := otherFintype
noncomputable local instance : Fintype Region := CacheAuthentication.regionFintype
noncomputable local instance : SampleableType FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType OtherTable := otherSampler
noncomputable local instance : SampleableType MacTable := CacheAuthentication.macTableSampler
structure Checker (Forgery : Type) where
  check : Digest → QueryLog Requests → Forgery → M Bool
  nonMac : ∀ pk log forgery, NonMac (check pk log forgery)
variable {Forgery : Type}
abbrev AdversaryFor (Forgery : Type) :=
  Digest → T3.Cache → OracleComp LazyPrivate.Interaction (Option Forgery)
noncomputable def verdict (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : M Bool := do
  let some forgery := result.1 | return false
  let verified ← checker.check publicKey result.2 forgery
  pure (decide (result.2.length ≤ 2^32) && verified)
theorem verdict_nonMac (checker : Checker Forgery) (publicKey : Digest)
    (result : Option Forgery × QueryLog Requests) : NonMac (verdict checker publicKey result) := by
  unfold verdict
  cases result.1 with
  | none => exact SourceQueries.pure_allowed _ _
  | some forgery =>
      exact SourceQueries.bind_allowed _ (checker.nonMac publicKey result.2 forgery)
        (fun _ => SourceQueries.pure_allowed _ _)
noncomputable def game (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← loggedWith (fun request => sign request.cache request.message)
    (adversary generated.1 generated.2)
  verdict checker generated.1 result
noncomputable def realExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp (Bool × Nat) :=
  sampleMasterSeed >>= fun secret =>
    (simulateQ romImpl (SphincsSecurity.countHashQueries
      (Derivation.realize (privateInput secret) (game checker adversary)))).run' ∅
noncomputable def tableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery)
    (q : Nat) : ProbComp (Option (Bool × Nat)) :=
  ($ᵗ FullTable : ProbComp _) >>= fun outputs =>
    (simulateQ romImpl (Derivation.tableRun outputs (Derivation.cap (game checker adversary) q))).run' ∅
theorem private_derivation_event_bound (checker : Checker Forgery)
    (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      Pr[fun outcome => ∃ result, outcome=some result ∧ result.1=true |
        tableExperiment checker adversary q] + q / ((2^256 : Nat) : ENNReal) :=
  Derivation.event_game_hop privateInput privateInput_injective
    privateInput_hit (game checker adversary) q hq (· = true)
noncomputable def countedTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (game checker adversary) (0,∅)
theorem counted_table_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true | tableExperiment checker adversary q] := by
  unfold countedTableExperiment tableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  exact table_cap_event table (game checker adversary) ∅ q (·=true)
theorem real_to_counted_table (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]+
        q/((2^256 : Nat) : ENNReal) := by
  rw [counted_table_event]
  exact private_derivation_event_bound checker adversary q hq
noncomputable def splitTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let other ← ($ᵗ OtherTable : ProbComp _)
  let mac ← ($ᵗ MacTable : ProbComp _)
  run (joinTable other mac) (game checker adversary) (0,∅)
theorem table_experiment_split (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[countedTableExperiment checker adversary]=𝒮[splitTableExperiment checker adversary] :=
  uniform_table_split_bind (fun table => run table (game checker adversary) (0,∅))
noncomputable def checkContinuation (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState) : ProbComp (Bool × CountState) :=
  (simulateQ (baseHandler other) (verdict checker publicKey result.1)).run result.2
noncomputable def realRest (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
noncomputable def idealRest (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (loggedWith (fun request => sign request.cache request.message) program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [loggedWith_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← loggedWith (fun request => sign request.cache request.message) (adversary publicKey published)
      verdict checker publicKey result)).run state=
      realRest checker other mac adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,logged_source_run]
  unfold realRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_game_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (game checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,game]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    source_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
theorem refresh_published_mac (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (generated : (Digest × Region) × CountState) :
    𝒮[do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other mac adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
        (generated.2.1+2,generated.2.2)]=
    𝒮[do
      let tag ← ($ᵗ HashOutput : ProbComp _)
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker other (MacGame.retag mac ⟨tag,generated.1.2⟩) adversary
        generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2)] := by
  exact MacGame.refresh_published generated.1.2 (fun tag mac =>
    realRest checker other mac adversary generated.1.1 ⟨tag,generated.1.2⟩
      (generated.2.1+2,generated.2.2))
noncomputable def preparedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  let mac ← ($ᵗ MacTable : ProbComp _)
  realRest checker prepared.other (MacGame.retag mac prepared.published)
    adversary prepared.publicKey prepared.published prepared.state
noncomputable def authenticatedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let prepared ← setup
  idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state
theorem split_experiment_prepared (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[splitTableExperiment checker adversary]=𝒮[preparedExperiment checker adversary] := by
  unfold splitTableExperiment preparedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_game_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact refresh_published_mac checker other adversary generated
theorem checkContinuation_long (checker : Checker Forgery) (other : OtherTable) (publicKey : Digest)
    (result : (Option Forgery × QueryLog Requests) × CountState)
    (hlong : 2^32 < result.1.2.length) (q : Nat) :
    Pr[fun outcome => outcome.1=true ∧ outcome.2.1≤q | checkContinuation checker other publicKey result]=0 := by
  have hn : ¬result.1.2.length≤2^32 := Nat.not_le.mpr hlong
  unfold checkContinuation verdict
  cases result.1.1 with
  | none => simp [StateT.run_pure]
  | some forgery =>
      simp
      intro count cache _ hshort
      exact False.elim (hn hshort)
theorem rest_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (prepared : Setup) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | do
      let mac ← ($ᵗ MacTable : ProbComp _)
      realRest checker prepared.other (MacGame.retag mac prepared.published)
        adversary prepared.publicKey prepared.published prepared.state] ≤
    Pr[fun result => result.1=true ∧ result.2.1≤q |
      idealRest checker prepared.other adversary prepared.publicKey prepared.published prepared.state]+
      ((2 : ENNReal)^152)⁻¹ := by
  have h := MacGame.authentication_hop (worldHandler prepared.other) (baseHandler prepared.other)
    prepared.published (adversary prepared.publicKey prepared.published) (2^32) prepared.state
    (checkContinuation checker prepared.other prepared.publicKey) (fun result => result.1=true ∧ result.2.1≤q)
    (fun result hlong => checkContinuation_long checker prepared.other prepared.publicKey result hlong q)
  refine h.trans (add_le_add le_rfl ?_)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
theorem prepared_authentication_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹ :=
  probEvent_bind_le_add setup _ _ _ _ (fun prepared => rest_authentication_bound checker adversary prepared q)
theorem real_to_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := real_to_counted_table checker adversary q hq
  have he := (table_experiment_split checker adversary).trans (split_experiment_prepared checker adversary)
  have hp : Pr[fun result => result.1=true ∧ result.2.1≤q | countedTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | preparedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) he
  rw [hp] at h
  exact h.trans (add_le_add (prepared_authentication_bound checker adversary q) le_rfl)
noncomputable def idealGame (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : M Bool := do
  let generated ← keygen
  let result ← loggedWith (authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict checker generated.1 result
theorem ideal_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← loggedWith (authenticatedSign published) (adversary publicKey published)
      verdict checker publicKey result)).run state=idealRest checker other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => authenticatedSign_interpretation other mac published request
  rw [hs]
  change RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= _ = _
  unfold idealRest
  apply bind_congr
  intro result
  rw [MacGame.simulate_no_mac _ _ _ (verdict_nonMac checker publicKey result.1)]
  rfl
theorem fixed_ideal_expansion (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery) :
    run (joinTable other mac) (idealGame checker adversary) (0,∅)=
      (do
        let generated ← (simulateQ (baseHandler other) keygenPayload).run (0,∅)
        idealRest checker other adversary generated.1.1 ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩
          (generated.2.1+2,generated.2.2)) := by
  rw [run,tableHandler_split,idealGame]
  simp only [keygen,bind_assoc,pure_bind,simulateQ_bind,StateT.run_bind]
  rw [MacGame.simulate_no_mac _ _ _ keygenPayload_nonMac]
  apply bind_congr
  intro generated
  rw [source_mac_run,pure_bind]
  simpa only [simulateQ_bind,StateT.run_bind] using
    ideal_rest_run checker other mac adversary generated.1.1
      ⟨MacGame.tagAt mac generated.1.2,generated.1.2⟩ (generated.2.1+2,generated.2.2)
noncomputable def idealTableExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × CountState) := do
  let table ← ($ᵗ FullTable : ProbComp _)
  run table (idealGame checker adversary) (0,∅)
theorem ideal_table_authenticated (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    𝒮[idealTableExperiment checker adversary]=𝒮[authenticatedExperiment checker adversary] := by
  unfold idealTableExperiment
  rw [uniform_table_split_bind]
  unfold authenticatedExperiment setup
  simp only [bind_assoc,pure_bind]
  apply evalSPMF_bind_congr'
  intro other
  simp_rw [fixed_ideal_expansion]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro generated
  exact sample_mac_at_bind generated.1.2 (fun tag =>
    idealRest checker other adversary generated.1.1 ⟨tag,generated.1.2⟩ (generated.2.1+2,generated.2.2))
noncomputable def idealLazyExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    ProbComp ((Bool × Nat) × LazyPrivate.State) :=
  LazyPrivate.run (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) (∅,∅)
theorem ideal_lazy_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] := by
  have h := LazyPrivate.run_eq_table
    (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)) ∅
  have hp : Pr[fun result => result.1.1=true ∧ result.1.2≤q |
      Prod.map id Prod.snd <$> idealLazyExperiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | do
        let table ← ($ᵗ FullTable : ProbComp _)
        (simulateQ romImpl (Derivation.tableRun table
          (SphincsSecurity.QueryCap.counted Derivation.charged (idealGame checker adversary)))).run ∅] :=
    probEvent_congr' (fun _ _ => Iff.rfl) h
  simp only [probEvent_map,Prod.map,id_eq,Function.comp_def] at hp
  rw [hp]
  have he : Pr[fun result => result.1=true ∧ result.2.1≤q | idealTableExperiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | authenticatedExperiment checker adversary] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (ideal_table_authenticated checker adversary)
  rw [← he]
  unfold idealTableExperiment
  simp only [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro table
  apply congrArg
  rw [run,tableHandler,countHandler_run,probEvent_map]
  simp only [plain_run,Function.comp_def,Nat.zero_add]
theorem real_to_ideal_lazy (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | idealLazyExperiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [ideal_lazy_event]
  exact real_to_authenticated checker adversary q hq
end SigGolfCandidate.T3.Security.GameWith
end
section
namespace SigGolfCandidate.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Forgery : Type}
namespace Counted
open CountedPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) (0,∅,∅)
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]=
      Pr[fun result => result.1.1=true ∧ result.1.2≤q | GameWith.idealLazyExperiment checker adversary] := by
  simp only [experiment,run,GameWith.idealLazyExperiment,probEvent_map,Function.comp_def,Nat.zero_add]
theorem real_to_counted_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact GameWith.real_to_ideal_lazy checker adversary q hq
end Counted
namespace Monitored
open MonitoredPrivate
noncomputable def experiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) : ProbComp (Bool × State) :=
  run (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) :
    Prod.map id State.source <$> experiment checker adversary=Counted.experiment checker adversary :=
  run_erasure (GameWith.idealGame checker adversary) ⟨(0,∅,∅),false⟩
theorem experiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) :
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]=
      Pr[fun result => result.1=true ∧ result.2.1≤q | Counted.experiment checker adversary] := by
  rw [← experiment_erasure checker adversary,probEvent_map]
  rfl
theorem real_to_monitored_ideal (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [experiment_event]
  exact Counted.real_to_counted_ideal checker adversary q hq
abbrev History := List DigestSampling.IndexBuckets
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (History × State)) := do
  let generated ← (liftM (run keygen ⟨(0,∅,∅),false⟩) : PMF _)
  let interaction ← (simulateQ (proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem tracedExperiment_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget=
      (liftM (experiment checker adversary) : PMF (Bool × State)) := by
  unfold tracedExperiment experiment GameWith.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem tracedExperiment_event (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq]=
      Pr[fun result => result.1=true ∧ result.2.source.1≤q | experiment checker adversary] := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.1=true ∧ result.2.source.1≤q | law]) (tracedExperiment_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq] at h
  calc
    _ = Pr[fun result => result.1=true ∧ result.2.source.1≤q | (liftM (experiment checker adversary) : PMF _)] := h
    _ = _ := by
      simp only [probEvent_eq_tsum_ite]
      rfl
theorem real_to_traced (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq]+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  rw [tracedExperiment_event]
  exact real_to_monitored_ideal checker adversary q (hq.trans_lt (by norm_num))
theorem verdict_success_log (checker : Checker Forgery) (publicKey : Digest) (interaction : Option Forgery × QueryLog Requests)
    (state : State) (result : Bool × State)
    (hr : result ∈ support (run (GameWith.verdict checker publicKey interaction) state))
    (hwin : result.1=true) : interaction.2.length≤2^32 := by
  unfold GameWith.verdict at hr
  cases ho : interaction.1 with
  | none =>
      simp only [ho,run_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [ho,run_bind,mem_support_bind_iff,run_pure,support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨middle,_,rfl⟩ := hr
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hwin
      exact hwin.1
theorem winning_trace_overflow (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      tracedExperiment checker adversary budget hbudget] ≤ (2 : ENNReal)⁻¹^700 := by
  rw [← expectedValue_ite_one]
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  change expectedValue (run keygen ⟨(0,∅,∅),false⟩) _ ≤ _
  apply expectedValue_le_of_support
  intro generated _
  apply le_trans ?_ (source_proposal_overflow generated.1.2 budget hbudget
    (adversary generated.1.1 generated.1.2) generated.2)
  rw [← expectedValue_ite_one]
  apply expectedValue_mono
  intro interaction
  change expectedValue (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2)
    (fun checked => if checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length then 1 else 0) ≤ _
  apply expectedValue_le_of_support
  intro checked hchecked
  by_cases h : checked.1=true ∧ BPORS.Numeric.proposalLength < interaction.2.1.length
  · have hl := verdict_success_log checker generated.1.1 interaction.1 interaction.2.2 checked hchecked h.1
    simp only [h,if_true,show interaction.1.2.length≤2^32 ∧
      BPORS.Numeric.proposalLength < interaction.2.1.length from ⟨hl,h.2⟩,le_refl]
  · simp only [h,if_false,zero_le]
theorem split_winning_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq]+
      Pr[fun result => result.1=true ∧ BPORS.Numeric.proposalLength < result.2.1.length |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q
  · by_cases hn : result.2.1.length≤BPORS.Numeric.proposalLength
    · simp [hw,hw.1,hw.2,hn,Nat.not_lt.mpr hn]
    · simp [hw,hw.1,hw.2,hn,Nat.lt_of_not_ge hn]
  · simp only [hw,if_false,zero_le]
theorem real_to_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq]+
        (2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_traced checker adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  exact (split_winning_trace checker adversary q hq).trans
    (add_le_add le_rfl (winning_trace_overflow checker adversary q hq))
theorem experiment_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | experiment checker adversary] ≤
      q/(2 : ENNReal)^146 := by
  exact gate6_run_empty_linear_charge (GameWith.idealGame checker adversary) q 146 hq (by decide)
theorem traced_exception_bound (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^146 := by
  have h := congrArg (fun law : PMF (Bool × State) =>
    Pr[fun result => result.2.source.1≤q ∧ result.2.exceptional=true | law])
    (tracedExperiment_erasure checker adversary q hq)
  simp only [probEvent_map,Function.comp_def,Prod.map,id_eq,event_lift] at h
  rw [h]
  exact experiment_exception_bound checker adversary q hq
theorem split_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
      result.2.1.length≤BPORS.Numeric.proposalLength | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment checker adversary q hq]+
      Pr[fun result => result.2.2.source.1≤q ∧ result.2.2.exceptional=true |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : result.1=true ∧ result.2.2.source.1≤q ∧ result.2.1.length≤BPORS.Numeric.proposalLength
  · cases hb : result.2.2.exceptional <;> simp [hw,hw.2.1,hb]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_bounded_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.exceptional=false |
          tracedExperiment checker adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
        ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_bounded_trace checker adversary q hq).trans
  apply add_le_add_left
  apply add_le_add_left
  apply add_le_add_left
  exact (split_bounded_trace checker adversary q hq).trans
    (add_le_add le_rfl (traced_exception_bound checker adversary q hq))
theorem full_game_excess_price (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice result.2.1-1 else 0) ≤ 11324/100000000 := by
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  apply expectedValue_le_of_le
  intro generated
  apply le_trans ?_ (BPORS.History.adaptive_selected_full_excess
    (proposalModel generated.1.2 budget hbudget) rfl
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) generated.2
    (fun result => result.2.1) (fun _ => List.Sublist.refl _))
  apply expectedValue_mono
  intro interaction
  exact expectedValue_le_of_le _ (fun _ => le_rfl)
theorem full_game_near_price (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice result.2.1 else 0) ≤ 404 := by
  simp only [tracedExperiment,expectedValue_bind,expectedValue_pure]
  apply expectedValue_le_of_le
  intro generated
  apply le_trans ?_ (BPORS.History.adaptive_selected_near_price
    (proposalModel generated.1.2 budget hbudget) rfl
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) generated.2
    (fun result => result.2.1) (fun _ => List.Sublist.refl _))
  apply expectedValue_mono
  intro interaction
  exact expectedValue_le_of_le _ (fun _ => le_rfl)
theorem full_game_selected_excess (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) (selected : Bool × (History × State) → History)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice (selected result)-1 else 0) ≤ 11324/100000000 := by
  apply le_trans ?_ (full_game_excess_price checker adversary budget hbudget)
  apply expectedValue_mono
  intro result
  split_ifs
  · exact tsub_le_tsub_right (BPORS.History.fullPrice_sublist (hselected result)) 1
  · exact le_rfl
theorem full_game_selected_near (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) (selected : Bool × (History × State) → History)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice (selected result) else 0) ≤ 404 := by
  apply le_trans ?_ (full_game_near_price checker adversary budget hbudget)
  apply expectedValue_mono
  intro result
  split_ifs
  · exact BPORS.History.fullNearPrice_sublist (hselected result)
  · exact le_rfl
end Monitored
end SigGolfCandidate.T3.Security.GameWith
end
section
namespace SigGolfCandidate.T3.Security.GameWith.Recorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal QueryRecorded
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen GameWith.idealGame
variable {Forgery : Type}
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (MonitoredPrivate.History × State)) := do
  let generated ← (liftM (run keygen initial) : PMF _)
  let interaction ← (simulateQ (proposalModel generated.1.2 budget hbudget).traced
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run ([],generated.2)
  let checked ← (liftM (run (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2) : PMF _)
  pure (checked.1,interaction.2.1,checked.2)
theorem traced_base_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id (Prod.map id State.base) <$> tracedExperiment checker adversary budget hbudget=
      Monitored.tracedExperiment checker adversary budget hbudget := by
  unfold tracedExperiment Monitored.tracedExperiment
  simp only [map_bind,map_pure,Prod.map,id_eq]
  have hk := lift_run_erasure keygen initial
  change Prod.map id State.base <$> (liftM (run keygen initial) : PMF _)=
    (liftM (MonitoredPrivate.run keygen ⟨(0,∅,∅),false⟩) : PMF _) at hk
  rw [← hk,bind_map_left]
  apply bind_congr
  intro generated
  simp only [Prod.map,id_eq]
  rw [← proposal_trace_project generated.1.2 budget hbudget _ [] generated.2,bind_map_left]
  apply bind_congr
  intro interaction
  simp only [Prod.map,id_eq]
  rw [← lift_run_erasure (GameWith.verdict checker generated.1.1 interaction.1) interaction.2.2,bind_map_left]
  rfl
theorem traced_source_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget=
      (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
  unfold tracedExperiment GameWith.idealGame
  simp only [run_bind,liftM_bind,map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta]
  apply bind_congr
  intro generated
  have h := proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [MonitoredPrivate.logged_source] at h
  rw [← h,bind_map_left]
  simp only [bind_pure,Prod.map,id_eq]
theorem traced_record_erasure (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    recordedTrace <$> tracedExperiment checker adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) := by
  have hr : recorded <$> run (GameWith.idealGame checker adversary) initial=
      FirstHit.record (GameWith.idealGame checker adversary) (∅,∅) := by
    rw [run_recorded]
    have hp : prepend ([] : List FirstHit.QueryEvent)=(id : FirstHit.Recorded Bool → FirstHit.Recorded Bool) := by
      funext result
      rfl
    change prepend [] <$> FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)=_
    rw [hp,id_map]
  calc
    _ = recorded <$> (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget) := by
      rw [Functor.map_map]
      rfl
    _ = recorded <$> (liftM (run (GameWith.idealGame checker adversary) initial) : PMF _) := by
      rw [traced_source_erasure]
    _ = (liftM (recorded <$> run (GameWith.idealGame checker adversary) initial) : PMF _) := (liftM_map _ _).symm
    _ = _ := by rw [hr]
theorem traced_cost_coherent (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (MonitoredPrivate.History × State))
    (hr : result ∈ (tracedExperiment checker adversary budget hbudget).support) : CostCoherent result.2.2 := by
  have hp : (result.1,result.2.2) ∈
      (Prod.map id Prod.snd <$> tracedExperiment checker adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [traced_source_erasure] at hp
  rw [MonitoredPrivate.pmf_support] at hp
  exact run_cost_coherent (GameWith.idealGame checker adversary) initial initial_cost
    (result.1,result.2.2) hp
theorem known_public_hit_bound (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
      tracedExperiment checker adversary q hq] ≤ q/(2 : ENNReal)^128 := by
  have h := FirstHit.recorded_known_public_hit_bound reference (GameWith.idealGame checker adversary) (∅,∅) q
  have he := congrArg (fun law => Pr[fun result : FirstHit.Recorded Bool =>
      (result.events.map (fun event => FullGame.queryCharge event.input)).sum≤q ∧
      FirstHit.KnownPublicHit reference result | law]) (traced_record_erasure checker adversary q hq)
  rw [probEvent_map,MonitoredPrivate.event_lift] at he
  apply le_trans _ (he.le.trans h)
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (tracedExperiment checker adversary q hq).support
  · have hc := traced_cost_coherent checker adversary q hq result hr
    simp only [Function.comp_def,recordedTrace,recorded]
    rw [show result.2.2.base.source.1=
      (result.2.2.events.map (fun event => FullGame.queryCharge event.input)).sum from hc]
  · have hz : (tracedExperiment checker adversary q hq) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self,le_refl]
theorem real_to_clean_trace (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => result.1=true ∧ result.2.2.base.source.1≤q ∧
        result.2.1.length≤BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false |
          tracedExperiment checker adversary q hq]+
      q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  have h := Monitored.real_to_clean_bounded_trace checker adversary q hq
  rw [← traced_base_erasure checker adversary q hq,probEvent_map] at h
  exact h
theorem full_game_excess_price (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice result.2.1-1 else 0) ≤ 11324/100000000 := by
  have h := Monitored.full_game_excess_price checker adversary budget hbudget
  rw [← traced_base_erasure checker adversary budget hbudget,expectedValue_map] at h
  exact h
theorem full_game_near_price (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment checker adversary budget hbudget)
      (fun result => if result.2.1.length≤BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice result.2.1 else 0) ≤ 404 := by
  have h := Monitored.full_game_near_price checker adversary budget hbudget
  rw [← traced_base_erasure checker adversary budget hbudget,expectedValue_map] at h
  exact h
theorem split_known_hit (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[CleanWin q | tracedExperiment checker adversary q hq] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq]+
      Pr[fun result => result.2.2.base.source.1≤q ∧ FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : CleanWin q result
  · have hcount := hw.2.1
    by_cases hh : FirstHit.KnownPublicHit reference (recordedTrace result)
    · simp [hw,hcount,hh]
    · simp [hw,hcount,hh]
  · simp only [hw,if_false,zero_le]
theorem real_to_clean_without_known (checker : Checker Forgery) (reference : FirstHit.Reference) (adversary : AdversaryFor Forgery)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment checker adversary] ≤
      Pr[fun result => CleanWin q result ∧ ¬FirstHit.KnownPublicHit reference (recordedTrace result) |
        tracedExperiment checker adversary q hq]+
      q/(2 : ENNReal)^128+q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  apply (real_to_clean_trace checker adversary q hq).trans
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  exact (split_known_hit checker reference adversary q hq).trans
    (add_le_add le_rfl (known_public_hit_bound checker reference adversary q hq))
end SigGolfCandidate.T3.Security.GameWith.Recorded
end
section
namespace SigGolfCandidate.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen checkForgeryP
theorem check_public (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    PublicVerdict.Only (checkForgeryP publicKey log forgery) := by
  have hv (message : Message) (witness : WBytes) : PublicVerdict.Only (verifyP message publicKey witness) :=
    publicOnly_verifyP message publicKey witness
  have he (message : Message) (signature : Signature) : PublicVerdict.Only (expandB message publicKey signature) :=
    allQ_mono (pubGood_expandB message publicKey signature) fun _ h => h.1
  cases forgery with
  | witness message witness =>
      unfold checkForgeryP
      exact allQ_bind (hv message witness) fun _ => allQ_pure _
  | signature message signature =>
      unfold checkForgeryP
      apply allQ_bind (he message signature)
      intro witness
      cases witness with
      | none => exact allQ_pure _
      | some witness => exact allQ_bind (hv message witness) fun _ => allQ_pure _
theorem check_nonMac (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    FullGame.NonMac (checkForgeryP publicKey log forgery) := by
  apply allQ_mono (check_public publicKey log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · exact h.elim
noncomputable def checker : GameWith.Checker ForgeryP := ⟨checkForgeryP,check_nonMac⟩
theorem game_eq (adversary : AdversaryP) : GameWith.game checker adversary=gameP adversary := by
  unfold GameWith.game gameP
  apply bind_congr
  rintro ⟨publicKey,cache⟩
  unfold FullGame.loggedWith signingOracle
  simp only [monadLift_self]
  apply bind_congr
  rintro ⟨forgery,log⟩
  cases forgery <;> rfl
theorem realExperiment_eq (adversary : AdversaryP) :
    GameWith.realExperiment checker adversary=realExperimentP adversary := by
  unfold GameWith.realExperiment realExperimentP
  rw [game_eq]
theorem verdict_public (publicKey : Digest) (result : Option ForgeryP × QueryLog Requests) :
    PublicVerdict.Only (GameWith.verdict checker publicKey result) := by
  unfold GameWith.verdict
  cases result.1 with
  | none => exact allQ_pure _
  | some forgery => exact allQ_bind (check_public publicKey result.2 forgery) fun _ => allQ_pure _
abbrev TraceResult := Bool × (MonitoredPrivate.History × QueryRecorded.State)
noncomputable def tracedExperiment (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF TraceResult := GameWith.Recorded.tracedExperiment checker adversary budget hbudget
theorem real_to_clean_trace (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
      q/((2^256 : Nat) : ENNReal) := by
  rw [show (QueryRecorded.CleanWin q : TraceResult → Prop)=(fun result =>
    result.1=true ∧ result.2.2.base.source.1 ≤ q ∧
      result.2.1.length ≤ BPORS.Numeric.proposalLength ∧ result.2.2.base.exceptional=false) from rfl]
  simpa only [realExperiment_eq,tracedExperiment] using
    GameWith.Recorded.real_to_clean_trace checker adversary q hq
theorem real_to_clean_without_known (reference : FirstHit.Reference) (adversary : AdversaryP)
    (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      Pr[fun result => QueryRecorded.CleanWin q result ∧
        ¬FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) |
        tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^128+q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+
      ((2 : ENNReal)^152)⁻¹+q/((2^256 : Nat) : ENNReal) := by
  simpa only [realExperiment_eq,tracedExperiment,QueryRecorded.CleanWin] using GameWith.Recorded.real_to_clean_without_known checker reference adversary q hq
theorem full_game_excess_price (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length ≤ BPORS.Numeric.proposalLength
        then BPORS.History.fullPrice result.2.1-1 else 0) ≤ 11324/100000000 :=
  GameWith.Recorded.full_game_excess_price checker adversary budget hbudget
theorem full_game_near_price (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedValue (tracedExperiment adversary budget hbudget)
      (fun result => if result.2.1.length ≤ BPORS.Numeric.proposalLength
        then BPORS.History.fullNearPrice result.2.1 else 0) ≤ 404 :=
  GameWith.Recorded.full_game_near_price checker adversary budget hbudget
theorem traced_record_erasure (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    QueryRecorded.recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) :=
  GameWith.Recorded.traced_record_erasure checker adversary budget hbudget
theorem traced_cost_coherent (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.CostCoherent result.2.2 :=
  GameWith.Recorded.traced_cost_coherent checker adversary budget hbudget result hr
end SigGolfCandidate.T3.Security.PaddedGame
end
section
namespace SigGolfCandidate.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal MonitoredPrivate
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem monitored_journal (adversary : AdversaryP) (budget : Nat) (hbudget : budget≤2^127)
    (result : Bool × (History × State)) (hr : result ∈ (GameWith.Monitored.tracedExperiment checker adversary budget hbudget).support)
    (hcount : result.2.2.source.1≤budget) (hflag : result.2.2.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.source.2 keygen generated ∧
        JournalOK generated.2 result.2.1 result.2.2 journal := by
  unfold GameWith.Monitored.tracedExperiment at hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨generated,hg,hr⟩ := hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨interaction,hi,hr⟩ := hr
  rw [PMF.monad_bind_eq_bind,PMF.mem_support_bind_iff] at hr
  obtain ⟨checked,hv,hr⟩ := hr
  rw [PMF.monad_pure_eq_pure,PMF.mem_support_pure_iff] at hr
  subst result
  rw [pmf_support] at hg hv
  have hbudgetBefore := (run_count_monotone _ interaction.2.2 checked hv).trans hcount
  have hcleanBefore := run_false_before _ interaction.2.2 checked hv hflag
  obtain ⟨journal,hj⟩ := actual_interaction_journal generated hg budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) interaction hi hbudgetBefore hcleanBefore
  have hsource := traced_source_support generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) ([],generated.2) interaction hi
  have hgen := SourceReplay.resolves_of_run keygen SourceReplay.keygen_hashOnly (∅,∅)
    (generated.1,generated.2.source.2) (run_lazy_support keygen ⟨(0,∅,∅),false⟩ generated hg)
  refine ⟨generated.1,journal,hgen.mono ?_,?_⟩
  · exact (run_extends _ generated.2 (interaction.1,interaction.2.2) hsource).trans
      (run_extends _ interaction.2.2 checked hv)
  · exact journal_public_preserves generated.1.2 interaction.2.1 interaction.2.2 journal hj
      (GameWith.verdict checker generated.1.1 interaction.1) (verdict_public _ _) checked hv
theorem traced_game_journal (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support)
    (hcount : result.2.2.base.source.1 ≤ budget) (hflag : result.2.2.base.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.base.source.2 keygen generated ∧
        JournalOK generated.2 result.2.1 result.2.2.base journal := by
  apply monitored_journal adversary budget hbudget (result.1,result.2.1,result.2.2.base) _ hcount hflag
  rw [← GameWith.Recorded.traced_base_erasure checker adversary budget hbudget,
    PMF.monad_map_eq_map,PMF.support_map]
  exact ⟨result,hr,rfl⟩
theorem traced_journal_exposure (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support)
    (hcount : result.2.2.base.source.1 ≤ budget) (hflag : result.2.2.base.exceptional=false) :
    ∃ generated : Digest × T3.Cache,∃ journal,
      SourceReplay.Resolves result.2.2.base.source.2 keygen generated ∧
        JournalOK generated.2 result.2.1 result.2.2.base journal ∧
        BPORS.History.fullPrice (journalLabels journal) ≤ BPORS.History.fullPrice result.2.1 ∧
        BPORS.History.fullNearPrice (journalLabels journal) ≤ BPORS.History.fullNearPrice result.2.1 := by
  obtain ⟨generated,journal,hg,hj⟩ := traced_game_journal adversary budget hbudget result hr hcount hflag
  exact ⟨generated,journal,hg,hj,journal_prices generated.2 result.2.1 result.2.2.base journal hj⟩
end SigGolfCandidate.T3.Security.PaddedGame
end
section
namespace SigGolfCandidate.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem large_budget (adversary : AdversaryP) (q : Nat) (hq : 2^127 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperimentP adversary] ≤
      (q : ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2 : ENNReal)^127 ≤ (q : ENNReal) := by exact_mod_cast hq
  calc
    (1 : ENNReal) = (2 : ENNReal)^127/(2 : ENNReal)^127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right hcast _
theorem securityP_of_clean_bound
    (hclean : ∀ (adversary : AdversaryP) (q : Nat), 1 ≤ q → ∀ hq : q ≤ 2^127,
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
        q/((2^256 : Nat) : ENNReal) ≤ (q : ENNReal)/2^127) : SecurityP := by
  intro adversary q hpositive
  by_cases hq : 2^127 ≤ q
  · exact large_budget adversary q hq
  · have hsmall : q ≤ 2^127 := Nat.le_of_lt (Nat.lt_of_not_ge hq)
    exact (real_to_clean_trace adversary q hsmall).trans (hclean adversary q hpositive hsmall)
end SigGolfCandidate.T3.Security.PaddedGame
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
structure Address where
  layer : Layer
  tree : Fin (2^31)
  leaf : Fin 4096
  chain : Fin 58
  deriving DecidableEq, Fintype
@[ext] theorem Address.ext {left right : Address}
    (hlayer : left.layer=right.layer) (htree : left.tree=right.tree)
    (hleaf : left.leaf=right.leaf) (hchain : left.chain=right.chain) : left=right := by
  cases left
  cases right
  simp_all
attribute [local irreducible] instFintypeAddress
abbrev Point := Address × Fin 7
abbrev Labels := Point → HashOutput
abbrev Seeds := Address → Digest
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
def row (point : Point) (value : Digest) : HashInput :=
  chainInput point.1.layer point.1.tree.val point.1.leaf.val point.1.chain.val point.2.val value
theorem row_length (point : Point) (value : Digest) : (row point value).length=64 := by
  simp [row,chainInput,zero16,bytesLE_length]
theorem row_position {left right : Point} {value value' : Digest}
    (heq : row left value=row right value') : left=right := by
  obtain ⟨hheader,_⟩ := chainInput_fields heq
  have hl := left.1.layer.isLt
  have hr := right.1.layer.isLt
  have hlt := left.1.tree.isLt
  have hrt := right.1.tree.isLt
  have hli := left.1.leaf.isLt
  have hri := right.1.leaf.isLt
  have hlc := left.1.chain.isLt
  have hrc := right.1.chain.isLt
  have hls := left.2.isLt
  have hrs := right.2.isLt
  have hh := chainHeader_injective (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hheader
  apply Prod.ext
  · apply Address.ext
    · exact hh.1
    · exact Fin.ext hh.2.1
    · exact Fin.ext hh.2.2.1
    · exact Fin.ext hh.2.2.2.1
  · exact Fin.ext hh.2.2.2.2
theorem row_separated (values : Point → Labels → Digest) :
    FiniteGraphSampling.Separated (fun point labels => row point (values point labels)) := by
  intro left right hne before after heq
  exact hne (row_position heq)
def predecessor (point : Point) : Point :=
  (point.1,⟨point.2.val-1,by have := point.2.isLt;omega⟩)
def prior (seeds : Seeds) (point : Point) (labels : Labels) : Digest :=
  if point.2.val=0 then seeds point.1 else (labels (predecessor point)).extractLsb' 0 128
def input (seeds : Seeds) (point : Point) (labels : Labels) : HashInput := row point (prior seeds point labels)
theorem input_separated (seeds : Seeds) : FiniteGraphSampling.Separated (input seeds) :=
  row_separated (prior seeds)
noncomputable def rows : Finset HashInput :=
  (Finset.univ : Finset Point).biUnion fun point => (Finset.univ : Finset Digest).image (row point)
attribute [irreducible] rows
theorem row_mem (point : Point) (value : Digest) : row point value ∈ rows := by
  classical
  rw [rows,Finset.mem_biUnion]
  simp only [Finset.mem_univ,true_and]
  exact ⟨point,Finset.mem_image.mpr ⟨value,Finset.mem_univ _,rfl⟩⟩
noncomputable def cell (seeds : Seeds) (point : Point) (labels : Labels) : rows :=
  ⟨input seeds point labels,row_mem point (prior seeds point labels)⟩
theorem cell_separated (seeds : Seeds) : FiniteGraphSampling.Separated (cell seeds) := by
  intro left right hne before after heq
  exact input_separated seeds left right hne before after (congrArg Subtype.val heq)
noncomputable local instance : SampleableType (rows → HashOutput) := SampleableType.ofFintype _
theorem read_eq_plant (seeds : Seeds) (points : List Point) (hnodup : points.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (rows → HashOutput) : ProbComp _)
      pure (FiniteGraphSampling.read (cell seeds)
        (fun point output labels => Function.update labels point output) table points before,table)]=
      𝒮[FiniteGraphSampling.plant (cell seeds)
        (fun point output labels => Function.update labels point output) points before] :=
  FiniteGraphSampling.evalDist_read_eq_plant (cell seeds) _ (cell_separated seeds) points hnodup before
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete FiniteGraphSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (rows → HashOutput) := SampleableType.ofFintype _
noncomputable def order : List Point :=
  (Finset.univ : Finset Point).toList.mergeSort (fun left right => decide (left.2.val ≤ right.2.val))
attribute [local irreducible] order
theorem order_nodup : order.Nodup := by
  unfold order
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem mem_order (point : Point) : point ∈ order := by
  rw [order,List.mem_mergeSort]
  simp
theorem order_sorted : order.Pairwise (fun left right => left.2.val ≤ right.2.val) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Point => decide (left.2.val ≤ right.2.val))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *;omega)
    (by intro a b;simp [Bool.or_eq_true];omega)
    (Finset.univ : Finset Point).toList
  simpa only [order,decide_eq_true_eq] using h
theorem cell_injective (seeds : Seeds) (labels : Labels) :
    Function.Injective (fun point => cell seeds point labels) := by
  intro left right heq
  by_contra hne
  exact cell_separated seeds left right hne labels labels heq
noncomputable def programmed (seeds : Seeds) (labels : Labels) (residual : rows → HashOutput) :
    rows → HashOutput := patch (fun point => cell seeds point labels) labels residual order
theorem programmed_at (seeds : Seeds) (labels : Labels) (residual : rows → HashOutput) (point : Point) :
    programmed seeds labels residual (cell seeds point labels)=labels point :=
  patch_at _ (cell_injective seeds labels) labels residual order point (mem_order point)
theorem programmed_other (seeds : Seeds) (labels : Labels) (residual : rows → HashOutput)
    (query : rows) (hquery : ∀ point, query.val ≠ input seeds point labels) :
    programmed seeds labels residual query=residual query := by
  apply patch_of_forall_ne
  intro point _ heq
  exact hquery point (congrArg Subtype.val heq)
theorem replay_eq_programmed (seeds : Seeds) (labels : Labels) (residual : rows → HashOutput)
    (points : List Point) (hsorted : points.Pairwise (fun left right => left.2.val ≤ right.2.val))
    (before : Labels) (hagrees : ∀ point, point ∉ points → before point=labels point) :
    replay (cell seeds) (fun point output values => Function.update values point output)
      labels residual points before=
      (labels,patch (fun point => cell seeds point labels) labels residual points) := by
  induction points generalizing before with
  | nil =>
      have hbefore : before=labels := funext fun point => hagrees point (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth,hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cell seeds first before=cell seeds first labels := by
        apply Subtype.ext
        change input seeds first before=input seeds first labels
        unfold input prior
        split_ifs with hzero
        · rfl
        · have hless : (predecessor first).2.val < first.2.val := by
            simp only [predecessor]
            omega
          have hnot : predecessor first ∉ first::rest := by
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem
            · rw [heq] at hless
              omega
            · have := hdepth _ hmem
              omega
          rw [hagrees (predecessor first) hnot]
      have hafter : ∀ point,point ∉ rest →
          Function.update before first (labels first) point=labels point := by
        intro point hpoint
        by_cases heq : point=first
        · subst point
          rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees point (fun hmem => (List.mem_cons.mp hmem).elim heq hpoint)
      rw [replay,ih hsorted _ hafter,patch,hinput]
theorem plant_eq_uniform_programmed (seeds : Seeds) :
    𝒮[plant (cell seeds) (fun point output values => Function.update values point output)
      order (fun _ => 0)]=
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        pure (labels,programmed seeds labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed seeds labels residual order order_sorted _
    (fun point hpoint => (hpoint (mem_order point)).elim)]
  rfl
theorem read_eq_uniform_programmed (seeds : Seeds) :
    𝒮[do
      let table ← ($ᵗ (rows → HashOutput) : ProbComp _)
      pure (read (cell seeds) (fun point output labels => Function.update labels point output)
        table order (fun _ => 0),table)]=
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        pure (labels,programmed seeds labels residual)] :=
  (read_eq_plant seeds order order_nodup _).trans (plant_eq_uniform_programmed seeds)
theorem read_bind_eq_uniform_programmed {Result : Type} (seeds : Seeds)
    (next : Labels → (rows → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (rows → HashOutput) : ProbComp _)
      next (read (cell seeds) (fun point output labels => Function.update labels point output)
        table order (fun _ => 0)) table]=
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next labels (programmed seeds labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (rows → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (read_eq_uniform_programmed seeds)
  simpa only [evalSPMF_bind,evalSPMF_pure,bind_assoc,pure_bind] using h
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress order
def value (seeds : Seeds) (labels : Labels) (address : Address) (step : Nat) : Digest :=
  if step=0 then seeds address
  else (labels (address,⟨(step-1)%7,Nat.mod_lt _ (by decide)⟩)).extractLsb' 0 128
theorem value_zero (seeds : Seeds) (labels : Labels) (address : Address) :
    value seeds labels address 0=seeds address := by simp [value]
theorem value_succ (seeds : Seeds) (labels : Labels) (address : Address) (step : Fin 7) :
    value seeds labels address (step.val+1)=(labels (address,step)).extractLsb' 0 128 := by
  simp [value,Nat.mod_eq_of_lt step.isLt]
theorem prior_eq_value (seeds : Seeds) (labels : Labels) (point : Point) :
    prior seeds point labels=value seeds labels point.1 point.2.val := by
  have hmod : (point.2.val-1)%7=point.2.val-1 := Nat.mod_eq_of_lt (by have := point.2.isLt;omega)
  simp only [prior,value,predecessor,hmod]
theorem row_pad64 (point : Point) (digest : Digest) : pad64 (row point digest)=row point digest := by
  simp [pad64,row_length]
def Agrees (answers : Answers) (seeds : Seeds) (labels : Labels) : Prop :=
  ∀ point, answers (.inl (.inr (input seeds point labels)))=labels point
theorem source_step (answers : Answers) (seeds : Seeds) (labels : Labels) (h : Agrees answers seeds labels)
    (address : Address) (step : Fin 7) :
    evalWithAnswerFn answers (chain address.layer address.tree.val address.leaf.val address.chain.val
      step.val 1 (value seeds labels address step.val))=value seeds labels address (step.val+1) := by
  have hin : input seeds (address,step) labels=row (address,step) (value seeds labels address step.val) := by
    rw [input,prior_eq_value]
  have hh := h (address,step)
  rw [hin] at hh
  have hc : chain address.layer address.tree.val address.leaf.val address.chain.val step.val 1
      (value seeds labels address step.val)=shortHash (row (address,step) (value seeds labels address step.val)) := by
    simp [chain,List.range'_succ,row]
  rw [hc]
  change (answers (.inl (.inr (pad64 (row (address,step) (value seeds labels address step.val)))))).extractLsb' 0 128=_
  rw [row_pad64,hh,value_succ]
theorem source_chain (answers : Answers) (seeds : Seeds) (labels : Labels) (h : Agrees answers seeds labels)
    (address : Address) (start count : Nat) (hbound : start+count ≤ 7) :
    evalWithAnswerFn answers (chain address.layer address.tree.val address.leaf.val address.chain.val
      start count (value seeds labels address start))=value seeds labels address (start+count) := by
  induction count with
  | zero => simp [chain]
  | succ count ih =>
      rw [eval_chain_add,ih (by omega)]
      simpa only [Nat.add_assoc] using source_step answers seeds labels h address ⟨start+count,by omega⟩
def sourceSeeds (answers : Answers) : Seeds := fun address =>
  leafSeed answers address.layer address.tree.val address.leaf.val address.chain.val
theorem source_prefix (answers : Answers) (labels : Labels) (h : Agrees answers (sourceSeeds answers) labels)
    (address : Address) (count : Nat) (hcount : count ≤ 7) :
    evalWithAnswerFn answers (chain address.layer address.tree.val address.leaf.val address.chain.val 0 count
      (leafSeed answers address.layer address.tree.val address.leaf.val address.chain.val))=
      value (sourceSeeds answers) labels address count := by
  simpa only [value_zero,sourceSeeds,Nat.zero_add] using
    source_chain answers (sourceSeeds answers) labels h address 0 count (by simpa using hcount)
theorem source_endpoint (answers : Answers) (labels : Labels) (h : Agrees answers (sourceSeeds answers) labels)
    (address : Address) :
    leafEnd answers address.layer address.tree.val address.leaf.val address.chain.val=
      value (sourceSeeds answers) labels address (maxDigit address.layer address.chain.val) := by
  apply source_prefix answers labels h address
  unfold maxDigit
  split_ifs <;> decide
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal Correctness
open SphincsSecurity.Concrete FiniteGraphSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress order
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (rows → HashOutput) := SampleableType.ofFintype _
def advance (point : Point) (output : HashOutput) (labels : Labels) : Labels :=
  Function.update labels point output
theorem cell_congr (seeds : Seeds) (point : Point) (left right : Labels)
    (h : point.2.val ≠ 0 → left (predecessor point)=right (predecessor point)) :
    cell seeds point left=cell seeds point right := by
  apply Subtype.ext
  change input seeds point left=input seeds point right
  unfold input prior
  split_ifs with hz
  · rfl
  · rw [h hz]
theorem read_preserves (seeds : Seeds) (table : rows → HashOutput) (points : List Point)
    (before : Labels) (point : Point) (hpoint : point ∉ points) :
    read (cell seeds) advance table points before point=before point := by
  induction points generalizing before with
  | nil => rfl
  | cons first rest ih =>
      have hne : point ≠ first := fun h => hpoint (by simp [h])
      have hrest : point ∉ rest := fun h => hpoint (List.mem_cons_of_mem _ h)
      change read (cell seeds) advance table rest
        (Function.update before first (table (cell seeds first before))) point=before point
      rw [ih _ hrest,Function.update_of_ne hne]
theorem read_consistent (seeds : Seeds) (table : rows → HashOutput) (points : List Point)
    (hnodup : points.Nodup) (hsorted : points.Pairwise (fun left right => left.2.val ≤ right.2.val))
    (before : Labels) : ∀ point ∈ points,
    read (cell seeds) advance table points before point=
      table (cell seeds point (read (cell seeds) advance table points before)) := by
  induction points generalizing before with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨hfirst,hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hdepth,hsorted⟩ := List.pairwise_cons.mp hsorted
      intro point hpoint
      rcases List.mem_cons.mp hpoint with hpoint | hpoint
      · subst point
        have hinput : cell seeds first (read (cell seeds) advance table (first::rest) before)=
            cell seeds first before := by
          apply cell_congr
          intro hz
          apply read_preserves
          intro hmem
          have hless : (predecessor first).2.val < first.2.val := by
            simp only [predecessor]
            omega
          rcases List.mem_cons.mp hmem with heq | hmem
          · rw [heq] at hless
            omega
          · have := hdepth _ hmem
            omega
        rw [hinput]
        change read (cell seeds) advance table rest
          (Function.update before first (table (cell seeds first before))) first=_
        rw [read_preserves _ _ _ _ _ hfirst,Function.update_self]
      · exact ih hrest hsorted _ point hpoint
noncomputable def graph (seeds : Seeds) (table : rows → HashOutput) : Labels :=
  read (cell seeds) advance table order (fun _ => 0)
theorem graph_consistent (seeds : Seeds) (table : rows → HashOutput) (point : Point) :
    graph seeds table point=table (cell seeds point (graph seeds table)) :=
  read_consistent seeds table order order_nodup order_sorted _ point (mem_order point)
noncomputable def tableAnswers (table : rows → HashOutput) (outside : Answers) : Answers
  | .inl (.inr query) => if h : query ∈ rows then table ⟨query,h⟩ else outside (.inl (.inr query))
  | .inl (.inl query) => outside (.inl (.inl query))
  | .inr coordinate => outside (.inr coordinate)
theorem tableAnswers_row (table : rows → HashOutput) (outside : Answers) (query : rows) :
    tableAnswers table outside (.inl (.inr query.val))=table query := by
  change (if h : query.val ∈ rows then table ⟨query.val,h⟩ else outside (.inl (.inr query.val)))=table query
  rw [dif_pos query.property]
theorem tableAnswers_seed (table : rows → HashOutput) (outside : Answers) :
    sourceSeeds (tableAnswers table outside)=sourceSeeds outside := rfl
theorem tableAnswers_leafSeed (table : rows → HashOutput) (outside : Answers)
    (lay : Layer) (tree leaf i : Nat) :
    leafSeed (tableAnswers table outside) lay tree leaf i=leafSeed outside lay tree leaf i := rfl
theorem graph_agrees (seeds : Seeds) (table : rows → HashOutput) (outside : Answers) :
    Agrees (tableAnswers table outside) seeds (graph seeds table) := by
  intro point
  rw [show input seeds point (graph seeds table)=(cell seeds point (graph seeds table)).val from rfl,
    tableAnswers_row]
  exact (graph_consistent seeds table point).symm
theorem programmed_agrees (seeds : Seeds) (labels : Labels) (residual : rows → HashOutput) (outside : Answers) :
    Agrees (tableAnswers (programmed seeds labels residual) outside) seeds labels := by
  intro point
  rw [show input seeds point labels=(cell seeds point labels).val from rfl,tableAnswers_row,programmed_at]
theorem eager_source_prefix (table : rows → HashOutput) (outside : Answers) (address : Address)
    (count : Nat) (hcount : count ≤ 7) :
    evalWithAnswerFn (tableAnswers table outside)
      (chain address.layer address.tree.val address.leaf.val address.chain.val 0 count
        (leafSeed outside address.layer address.tree.val address.leaf.val address.chain.val))=
      value (sourceSeeds outside) (graph (sourceSeeds outside) table) address count := by
  simpa only [tableAnswers_seed,tableAnswers_leafSeed] using
    source_prefix (tableAnswers table outside) (graph (sourceSeeds outside) table)
      (by rw [tableAnswers_seed];exact graph_agrees (sourceSeeds outside) table outside) address count hcount
theorem programmed_source_prefix (labels : Labels) (residual : rows → HashOutput) (outside : Answers)
    (address : Address) (count : Nat) (hcount : count ≤ 7) :
    evalWithAnswerFn (tableAnswers (programmed (sourceSeeds outside) labels residual) outside)
      (chain address.layer address.tree.val address.leaf.val address.chain.val 0 count
        (leafSeed outside address.layer address.tree.val address.leaf.val address.chain.val))=
      value (sourceSeeds outside) labels address count := by
  simpa only [tableAnswers_seed,tableAnswers_leafSeed] using
    source_prefix (tableAnswers (programmed (sourceSeeds outside) labels residual) outside) labels
      (by rw [tableAnswers_seed];exact programmed_agrees (sourceSeeds outside) labels residual outside)
      address count hcount
theorem source_prefix_bind_eq_uniform {Result : Type} (outside : Answers) (address : Address)
    (count : Nat) (hcount : count ≤ 7) (next : Digest → (rows → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (rows → HashOutput) : ProbComp _)
      next (evalWithAnswerFn (tableAnswers table outside)
        (chain address.layer address.tree.val address.leaf.val address.chain.val 0 count
          (leafSeed outside address.layer address.tree.val address.leaf.val address.chain.val))) table]=
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (value (sourceSeeds outside) labels address count)
          (programmed (sourceSeeds outside) labels residual)] := by
  simp_rw [eager_source_prefix _ outside address count hcount]
  exact read_bind_eq_uniform_programmed (sourceSeeds outside)
    (fun labels table => next (value (sourceSeeds outside) labels address count) table)
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress order
noncomputable local instance : Fintype Coordinate := coordinateFintype
abbrev HalfCoordinate := Coordinate × Fin 2
abbrev HalfTable := HalfCoordinate → Digest
noncomputable local instance : SampleableType Digest := SampleableType.ofFintype _
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType HalfTable := SampleableType.ofFintype _
noncomputable local instance : SampleableType Seeds := SampleableType.ofFintype _
noncomputable def outputEquiv : HashOutput ≃ Digest × Digest :=
  SphincsSecurity.splitHashOutputEquiv 128 (by decide)
noncomputable def joinOutput (low high : Digest) : HashOutput := outputEquiv.symm (low,high)
theorem joinOutput_low (low high : Digest) : (joinOutput low high).extractLsb' 0 128=low :=
  congrArg Prod.fst (outputEquiv.apply_symm_apply (low,high))
theorem joinOutput_high (low high : Digest) : (joinOutput low high).extractLsb' 128 128=high :=
  congrArg Prod.snd (outputEquiv.apply_symm_apply (low,high))
theorem joinOutput_parts (output : HashOutput) :
    joinOutput (output.extractLsb' 0 128) (output.extractLsb' 128 128)=output :=
  outputEquiv.symm_apply_apply output
def halves (table : FullGame.FullTable) : HalfTable := fun coordinate =>
  if coordinate.2.val=0 then (table coordinate.1).extractLsb' 0 128
  else (table coordinate.1).extractLsb' 128 128
noncomputable def halvesEquiv : FullGame.FullTable ≃ HalfTable where
  toFun := halves
  invFun table := fun coordinate => joinOutput (table (coordinate,0)) (table (coordinate,1))
  left_inv table := by
    funext coordinate
    exact joinOutput_parts (table coordinate)
  right_inv table := by
    funext coordinate
    rcases coordinate with ⟨coordinate,half⟩
    fin_cases half
    · exact joinOutput_low _ _
    · exact joinOutput_high _ _
theorem uniform_private_halves :
    𝒮[halves <$> ($ᵗ FullGame.FullTable : ProbComp _)]=𝒮[($ᵗ HalfTable : ProbComp _)] :=
  evalSPMF_map_bijective_uniform_cross (α := FullGame.FullTable) (β := HalfTable) halves halvesEquiv.bijective
def seedCoordinate (address : Address) : HalfCoordinate :=
  (.inl (header 0 address.layer.val address.tree.val (address.chain.val/2) address.leaf.val),
    ⟨address.chain.val%2,Nat.mod_lt _ (by decide)⟩)
theorem seedCoordinate_injective : Function.Injective seedCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : HalfCoordinate => coordinate.2.val) heq
  change Sum.inl (header 0 left.layer.val left.tree.val (left.chain.val/2) left.leaf.val)=
    (Sum.inl (header 0 right.layer.val right.tree.val (right.chain.val/2) right.leaf.val) : Coordinate) at hp
  have hl := left.layer.isLt
  have hr := right.layer.isLt
  have hlt := left.tree.isLt
  have hrt := right.tree.isLt
  have hli := left.leaf.isLt
  have hri := right.leaf.isLt
  have hlc := left.chain.isLt
  have hrc := right.chain.isLt
  have fields := header_injective (by decide : 0<256) (by omega) (by omega) (by omega) (by omega)
    (by decide : 0<256) (by omega) (by omega) (by omega) (by omega) (Sum.inl.inj hp)
  change left.chain.val%2=right.chain.val%2 at hh
  apply Address.ext <;> apply Fin.ext
  · exact fields.2.1
  · exact fields.2.2.1
  · exact fields.2.2.2.2
  · have := fields.2.2.2.1
    omega
def privateSeeds (table : FullGame.FullTable) : Seeds := halves table ∘ seedCoordinate
noncomputable def privateAnswers (table : FullGame.FullTable) (outside : Answers) : Answers
  | .inl query => outside (.inl query)
  | .inr coordinate => table coordinate
theorem sourceSeeds_private (table : FullGame.FullTable) (outside : Answers) :
    sourceSeeds (privateAnswers table outside)=privateSeeds table := rfl
abbrev OtherHalf := {coordinate : HalfCoordinate // coordinate ∉ Set.range seedCoordinate}
abbrev OtherHalves := OtherHalf → Digest
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType (Seeds × OtherHalves) := SampleableType.ofFintype _
noncomputable def splitHalvesEquiv : HalfTable ≃ Seeds × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range seedCoordinate)).symm.trans
    ((Equiv.ofInjective seedCoordinate seedCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
theorem splitHalves_seeds (table : HalfTable) : (splitHalvesEquiv table).1=table ∘ seedCoordinate := by
  funext address
  simp [splitHalvesEquiv,Equiv.sumArrowEquivProdArrow,Equiv.ofInjective]
noncomputable def privateTableEquiv : FullGame.FullTable ≃ Seeds × OtherHalves :=
  halvesEquiv.trans splitHalvesEquiv
theorem privateTableEquiv_seeds (table : FullGame.FullTable) :
    (privateTableEquiv table).1=privateSeeds table := splitHalves_seeds (halves table)
theorem uniform_private_seed_residual :
    𝒮[privateTableEquiv <$> ($ᵗ FullGame.FullTable : ProbComp _)]=
      𝒮[do let seeds ← ($ᵗ Seeds : ProbComp _);let other ← ($ᵗ OtherHalves : ProbComp _);pure (seeds,other)] :=
  (evalSPMF_map_bijective_uniform_cross (α := FullGame.FullTable) (β := Seeds × OtherHalves) privateTableEquiv privateTableEquiv.bijective).trans
    (FullGame.uniform_product (A := Seeds) (B := OtherHalves)).symm
theorem private_seed_bind {Result : Type} (next : FullGame.FullTable → ProbComp Result) :
    𝒮[do let table ← ($ᵗ FullGame.FullTable : ProbComp _);next table]=
      𝒮[do
        let seeds ← ($ᵗ Seeds : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        next (privateTableEquiv.symm (seeds,other))] := by
  have h := congrArg (fun law : SPMF (Seeds × OtherHalves) =>
    law >>= fun result => 𝒮[next (privateTableEquiv.symm result)]) uniform_private_seed_residual
  simpa only [evalSPMF_map,evalSPMF_bind,bind_map_left,evalSPMF_pure,bind_assoc,pure_bind,
    Equiv.symm_apply_apply] using h
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress order
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance : SampleableType Seeds := SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (rows → HashOutput) := SampleableType.ofFintype _
theorem reconstructed_seeds (seeds : Seeds) (other : OtherHalves) :
    privateSeeds (privateTableEquiv.symm (seeds,other))=seeds := by
  rw [← privateTableEquiv_seeds,Equiv.apply_symm_apply]
theorem private_chain_tables_bind {Result : Type}
    (next : FullGame.FullTable → (rows → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (rows → HashOutput) : ProbComp _)
      next privateTable publicTable]=
      𝒮[do
        let seeds ← ($ᵗ Seeds : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (privateTableEquiv.symm (seeds,other)) (programmed seeds labels residual)] := by
  rw [private_seed_bind]
  apply evalSPMF_bind_congr_left
  intro seeds
  apply evalSPMF_bind_congr_left
  intro other
  exact read_bind_eq_uniform_programmed seeds
    (fun _ table => next (privateTableEquiv.symm (seeds,other)) table)
abbrev LowLabels := Point → Digest
noncomputable local instance : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _
noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  (Equiv.arrowCongr (Equiv.refl Point) outputEquiv).trans
    (Equiv.arrowProdEquivProdArrow Point (fun _ => Digest) (fun _ => Digest))
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun point => joinOutput (low point) (high point)
theorem labelPairEquiv_symm (low high : LowLabels) :
    labelPairEquiv.symm (low,high)=joinLabels low high := rfl
theorem uniform_label_pair :
    𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)]=
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _);let high ← ($ᵗ LowLabels : ProbComp _);pure (low,high)] :=
  (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
    labelPairEquiv labelPairEquiv.bijective).trans
    (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _);next labels]=
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) uniform_label_pair
  simpa only [evalSPMF_map,evalSPMF_bind,bind_map_left,evalSPMF_pure,bind_assoc,pure_bind,
    Equiv.symm_apply_apply,labelPairEquiv_symm] using h
abbrev HiddenCoordinate := Address ⊕ Point
abbrev HiddenLabels := HiddenCoordinate → Digest
noncomputable local instance : SampleableType HiddenLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (Seeds × LowLabels) := SampleableType.ofFintype _
def seedLowEquiv : HiddenLabels ≃ Seeds × LowLabels := Equiv.sumArrowEquivProdArrow Address Point Digest
theorem seedLow_fst (hidden : HiddenLabels) : (seedLowEquiv hidden).1=hidden ∘ Sum.inl := rfl
theorem seedLow_snd (hidden : HiddenLabels) : (seedLowEquiv hidden).2=hidden ∘ Sum.inr := rfl
theorem seed_low_bind {Result : Type} (next : Seeds → LowLabels → ProbComp Result) :
    𝒮[do let seeds ← ($ᵗ Seeds : ProbComp _);let low ← ($ᵗ LowLabels : ProbComp _);next seeds low]=
      𝒮[do let hidden ← ($ᵗ HiddenLabels : ProbComp _);next (hidden ∘ Sum.inl) (hidden ∘ Sum.inr)] := by
  have hpair : 𝒮[seedLowEquiv <$> ($ᵗ HiddenLabels : ProbComp _)]=
      𝒮[do let seeds ← ($ᵗ Seeds : ProbComp _);let low ← ($ᵗ LowLabels : ProbComp _);pure (seeds,low)] :=
    (evalSPMF_map_bijective_uniform_cross (α := HiddenLabels) (β := Seeds × LowLabels)
      seedLowEquiv seedLowEquiv.bijective).trans
      (FullGame.uniform_product (A := Seeds) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (Seeds × LowLabels) =>
    law >>= fun result => 𝒮[next result.1 result.2]) hpair
  simpa only [evalSPMF_map,evalSPMF_bind,bind_map_left,evalSPMF_pure,bind_assoc,pure_bind,
    seedLow_fst,seedLow_snd] using h.symm
theorem initial_hidden_law {Result : Type}
    (next : FullGame.FullTable → (rows → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (rows → HashOutput) : ProbComp _)
      next privateTable publicTable]=
      𝒮[do
        let hidden ← ($ᵗ HiddenLabels : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (privateTableEquiv.symm (hidden ∘ Sum.inl,other))
          (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual)] := by
  rw [private_chain_tables_bind]
  calc
    _ = 𝒮[do
        let seeds ← ($ᵗ Seeds : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (privateTableEquiv.symm (seeds,other)) (programmed seeds (joinLabels low high) residual)] := by
      apply evalSPMF_bind_congr_left
      intro seeds
      apply evalSPMF_bind_congr_left
      intro other
      exact labels_bind (fun labels => do
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (privateTableEquiv.symm (seeds,other)) (programmed seeds labels residual))
    _ = 𝒮[do
        let seeds ← ($ᵗ Seeds : ProbComp _)
        let low ← ($ᵗ LowLabels : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        next (privateTableEquiv.symm (seeds,other)) (programmed seeds (joinLabels low high) residual)] := by
      apply evalSPMF_bind_congr_left
      intro seeds
      exact evalSPMF_bind_bind_swap _ _ _
    _ = _ := seed_low_bind (fun seeds low => do
      let other ← ($ᵗ OtherHalves : ProbComp _)
      let high ← ($ᵗ LowLabels : ProbComp _)
      let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
      next (privateTableEquiv.symm (seeds,other)) (programmed seeds (joinLabels low high) residual))
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete HiddenLabelObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instFintypeAddress order
def child (point : Point) : HiddenCoordinate :=
  if point.2.val=0 then .inl point.1 else .inr (predecessor point)
def parent (point : Point) : HiddenCoordinate := .inr point
theorem child_ne_parent (point : Point) : child point ≠ parent point := by
  unfold child parent
  split_ifs with hz
  · exact Sum.inl_ne_inr
  · intro heq
    have hv := congrArg (fun p : Point => p.2.val) (Sum.inr.inj heq)
    simp only [predecessor] at hv
    omega
def probe (point : Point) (candidate : Digest) : Probe HiddenCoordinate :=
  .pair (child point) (parent point) (child_ne_parent point) candidate
theorem prior_hidden (hidden : HiddenLabels) (high : LowLabels) (point : Point) :
    prior (hidden ∘ Sum.inl) point (joinLabels (hidden ∘ Sum.inr) high)=hidden (child point) := by
  unfold prior child
  split_ifs
  · rfl
  · exact joinOutput_low _ _
theorem output_hidden (hidden : HiddenLabels) (high : LowLabels) (point : Point) :
    ((joinLabels (hidden ∘ Sum.inr) high) point).extractLsb' 0 128=hidden (parent point) :=
  joinOutput_low _ _
theorem row_value_injective (point : Point) : Function.Injective (row point) := by
  intro left right heq
  unfold row chainInput at heq
  exact SphincsSecurity.bytesLE_injective (List.append_inj heq rfl).2
theorem probe_keep_iff (hidden : HiddenLabels) (high : LowLabels) (point : Point)
    (candidate : Digest) (answer : HashOutput) :
    (probe point candidate).keep hidden answer ↔
      row point candidate ≠ input (hidden ∘ Sum.inl) point (joinLabels (hidden ∘ Sum.inr) high) ∧
      answer.extractLsb' 0 128 ≠ ((joinLabels (hidden ∘ Sum.inr) high) point).extractLsb' 0 128 := by
  rw [output_hidden]
  unfold input
  rw [prior_hidden]
  simp only [probe,Probe.keep,SphincsSecurity.truncateHash]
  constructor
  · rintro ⟨hc,hp⟩
    exact ⟨fun hrow => hc ((row_value_injective point hrow).symm),Ne.symm hp⟩
  · rintro ⟨hc,hp⟩
    exact ⟨fun heq => hc (congrArg (row point) heq.symm),Ne.symm hp⟩
theorem safe_row_answer (hidden : HiddenLabels) (high : LowLabels) (residual : rows → HashOutput)
    (point : Point) (candidate : Digest) (hmiss : hidden (child point) ≠ candidate) :
    programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
      ⟨row point candidate,row_mem point candidate⟩=
      residual ⟨row point candidate,row_mem point candidate⟩ := by
  apply programmed_other
  intro other heq
  have hp : point=other := row_position heq
  subst other
  unfold input at heq
  rw [prior_hidden] at heq
  exact hmiss ((row_value_injective point heq).symm)
theorem safe_query_answer (hidden : HiddenLabels) (high : LowLabels) (residual : rows → HashOutput)
    (point : Point) (candidate : Digest)
    (hkeep : (probe point candidate).keep hidden
      (residual ⟨row point candidate,row_mem point candidate⟩)) :
    programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
      ⟨row point candidate,row_mem point candidate⟩=
      residual ⟨row point candidate,row_mem point candidate⟩ :=
  safe_row_answer hidden high residual point candidate hkeep.1
theorem probe_failure_le (allowed : HiddenCoordinate → Finset Digest)
    (ha : ∀ coordinate,(allowed coordinate).Nonempty) (point : Point) (candidate : Digest)
    (rounds : Nat) (hmin : 2^128-rounds ≤ (allowed (child point)).card) :
    (lazyResponse allowed (probe point candidate)).toPMF none ≤
      1-(1-((2^128-rounds : Nat) : ENNReal)⁻¹)^2 :=
  lazyResponse_pair_failure_le_rounds allowed ha (child point) (parent point)
    (child_ne_parent point) candidate rounds hmin
theorem probe_candidates_step (allowed : HiddenCoordinate → Finset Digest)
    (point : Point) (candidate : Digest) (answer : HashOutput) (coordinate : HiddenCoordinate) :
    (allowed coordinate).card-1 ≤ ((probe point candidate).restrict allowed answer coordinate).card :=
  Probe.card_lower (probe point candidate) allowed answer coordinate
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def advance (state : LazyPrivate.State) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) : LazyPrivate.State :=
  match input with
  | .inl (.inl _) => state
  | .inl (.inr query) => (state.1,state.2.cacheQuery query answer)
  | .inr coordinate => (state.1.cacheQuery coordinate answer,state.2)
theorem randomOracle_cache_after {D : Type} [DecidableEq D] (input : D)
    (cache : QueryCache (D →ₒ HashOutput)) (result : HashOutput × QueryCache (D →ₒ HashOutput))
    (hr : result ∈ support ((randomOracle (spec := D →ₒ HashOutput) input).run cache)) :
    result.2=cache.cacheQuery input result.1 := by
  cases hc : cache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc,support_map] at hr
      obtain ⟨answer,_,rfl⟩ := hr
      rfl
  | some answer =>
      rw [QueryImpl.withCaching_run_some _ hc,mem_support_pure_iff] at hr
      subst result
      exact (PrivateTable.cacheQuery_cached cache input answer hc).symm
theorem query_advance (state : LazyPrivate.State) (input : T3.Spec.Domain)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) state)) :
    result.2=advance state input result.1 := by
  rw [LazyPrivate.run_query] at hr
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨middle,hm,rfl⟩ := hr
      cases input with
      | inl sample =>
          change middle ∈ support ((fun answer => (answer,state.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl sample)) : ProbComp _)) at hm
          rw [support_map] at hm
          obtain ⟨answer,_,rfl⟩ := hm
          rfl
      | inr query =>
          exact congrArg (Prod.mk state.1) (randomOracle_cache_after query state.2 middle hm)
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        mem_support_pure_iff] at hr
      obtain ⟨middle,hm,rfl⟩ := hr
      exact congrArg (fun cache => (cache,state.2)) (randomOracle_cache_after coordinate state.1 middle hm)
noncomputable def sourceRecord {α : Type} (program : M α) : LazyPrivate.State → M (Recorded α) :=
  OracleComp.construct
    (fun value state => pure ⟨value,[],state⟩)
    (fun input _ next state => do
      let answer ← liftM (T3.Spec.query input)
      (fun last => ⟨last.value,⟨state,input,answer⟩::last.events,last.state⟩) <$>
        next answer (advance state input answer)) program
theorem sourceRecord_pure {α : Type} (value : α) (state : LazyPrivate.State) :
    sourceRecord (pure value : M α) state=pure ⟨value,[],state⟩ := rfl
theorem sourceRecord_query_bind {α : Type} (input : T3.Spec.Domain)
    (next : T3.Spec.Range input → M α) (state : LazyPrivate.State) :
    sourceRecord (liftM (T3.Spec.query input) >>= next) state=(do
      let answer ← liftM (T3.Spec.query input)
      (fun last => ⟨last.value,⟨state,input,answer⟩::last.events,last.state⟩) <$>
        sourceRecord (next answer) (advance state input answer)) := rfl
theorem sourceRecord_run {α : Type} (program : M α) (state : LazyPrivate.State) :
    Prod.fst <$> LazyPrivate.run (sourceRecord program state) state=record program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [sourceRecord_pure,LazyPrivate.run_pure,map_pure,record_pure]
  | query_bind input next ih =>
      rw [sourceRecord_query_bind,LazyPrivate.run_bind,map_bind,record_query_bind]
      apply bind_congr_of_forall_mem_support
      intro middle hm
      have heq := query_advance state input middle hm
      rw [← heq,LazyPrivate.run_map]
      have h := congrArg (Functor.map (fun last : Recorded α =>
        (⟨last.value,⟨state,input,middle.1⟩::last.events,last.state⟩ : Recorded α)))
        (ih middle.1 middle.2)
      simpa only [Functor.map_map,Prod.map,id_eq,Function.comp_def] using h
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
theorem recorded_private_table {α : Type} (program : M α) :
    𝒮[FirstHit.record program (∅,∅)]=
      𝒮[do
        let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
        (simulateQ SphincsSecurity.romImpl
          (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅)))).run' ∅] := by
  have h := congrArg (Functor.map Prod.fst)
    (LazyPrivate.run_eq_table (FirstHit.sourceRecord program (∅,∅)) ∅)
  simpa only [← evalSPMF_map,map_bind,Functor.map_map,Prod.map,id_eq,Function.comp_def,
    FirstHit.sourceRecord_run,← StateT.run'_eq] using h
noncomputable def finiteRecorded {α : Type} (privateTable : FullGame.FullTable)
    (inputs : Finset HashInput) (publicTable : inputs → HashOutput) (program : M α) :
    ProbComp (FirstHit.Recorded α) :=
  simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs publicTable))
    (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅)))
theorem recorded_finite_tables {α : Type} (program : M α) (inputs : Finset HashInput)
    (hinputs : ∀ privateTable : FullGame.FullTable,
      hashInputs (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅))) ⊆ inputs) :
    𝒮[FirstHit.record program (∅,∅)]=
      𝒮[do
        let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
        let publicTable ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        finiteRecorded privateTable inputs publicTable program] := by
  rw [recorded_private_table]
  apply evalSPMF_bind_congr_left
  intro privateTable
  exact evalDist_romRun_eq_finiteHash
    (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅))) inputs (hinputs privateTable) ∅
noncomputable def recordedInputs {α : Type} (program : M α) : Finset HashInput :=
  rows ∪ (Finset.univ : Finset FullGame.FullTable).biUnion fun privateTable =>
    hashInputs (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅)))
attribute [irreducible] recordedInputs
theorem rows_subset_recordedInputs {α : Type} (program : M α) : rows ⊆ recordedInputs program := by
  rw [recordedInputs]
  exact Finset.subset_union_left
theorem program_subset_recordedInputs {α : Type} (program : M α) (privateTable : FullGame.FullTable) :
    hashInputs (Derivation.tableRun privateTable (FirstHit.sourceRecord program (∅,∅))) ⊆ recordedInputs program := by
  intro input hi
  rw [recordedInputs,Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨privateTable,Finset.mem_univ _,hi⟩)
theorem recorded_finite_law {α : Type} (program : M α) :
    𝒮[FirstHit.record program (∅,∅)]=
      𝒮[do
        let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
        let publicTable ← ($ᵗ (recordedInputs program → HashOutput) : ProbComp _)
        finiteRecorded privateTable (recordedInputs program) publicTable program] :=
  recorded_finite_tables program (recordedInputs program) (program_subset_recordedInputs program)
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.FiniteRowSplit
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
variable (selected : Finset HashInput)
def includeRow (inputs : Finset HashInput) (hrows : selected ⊆ inputs) : selected → inputs :=
  fun query => ⟨query.val,hrows query.property⟩
theorem includeRow_injective (inputs : Finset HashInput) (hrows : selected ⊆ inputs) :
    Function.Injective (includeRow selected inputs hrows) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun query : inputs => query.val) heq
abbrev ExtraRow (inputs : Finset HashInput) (hrows : selected ⊆ inputs) :=
  {query : inputs // query ∉ Set.range (includeRow selected inputs hrows)}
noncomputable local instance (inputs : Finset HashInput) (hrows : selected ⊆ inputs) :
    SampleableType (ExtraRow selected inputs hrows → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (inputs : Finset HashInput) (hrows : selected ⊆ inputs) :
    SampleableType ((selected → HashOutput) × (ExtraRow selected inputs hrows → HashOutput)) := SampleableType.ofFintype _
noncomputable def publicTableEquiv (inputs : Finset HashInput) (hrows : selected ⊆ inputs) :
    (inputs → HashOutput) ≃ (selected → HashOutput) × (ExtraRow selected inputs hrows → HashOutput) :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range (includeRow selected inputs hrows))).symm.trans
    ((Equiv.ofInjective (includeRow selected inputs hrows) (includeRow_injective selected inputs hrows)).symm.sumCongr
      (Equiv.refl (ExtraRow selected inputs hrows)))) (Equiv.refl HashOutput)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
theorem publicTableEquiv_rows (inputs : Finset HashInput) (hrows : selected ⊆ inputs)
    (table : inputs → HashOutput) :
    (publicTableEquiv selected inputs hrows table).1=table ∘ includeRow selected inputs hrows := by
  funext query
  change table ((Equiv.Set.sumCompl (Set.range (includeRow selected inputs hrows)))
    (Sum.inl ((Equiv.ofInjective (includeRow selected inputs hrows) (includeRow_injective selected inputs hrows)) query)))=
      table (includeRow selected inputs hrows query)
  rfl
theorem publicTableEquiv_reconstruct (inputs : Finset HashInput) (hrows : selected ⊆ inputs)
    (chainTable : selected → HashOutput) (extra : ExtraRow selected inputs hrows → HashOutput) (query : selected) :
    (publicTableEquiv selected inputs hrows).symm (chainTable,extra) (includeRow selected inputs hrows query)=
      chainTable query := by
  calc
    _ = ((publicTableEquiv selected inputs hrows)
        ((publicTableEquiv selected inputs hrows).symm (chainTable,extra))).1 query :=
      (congrFun (publicTableEquiv_rows selected inputs hrows
        ((publicTableEquiv selected inputs hrows).symm (chainTable,extra))) query).symm
    _ = _ := congrArg
      (fun result : (selected → HashOutput) × (ExtraRow selected inputs hrows → HashOutput) => result.1 query)
      ((publicTableEquiv selected inputs hrows).apply_symm_apply (chainTable,extra))
theorem public_table_bind {Result : Type} (inputs : Finset HashInput) (hrows : selected ⊆ inputs)
    (next : (inputs → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (inputs → HashOutput) : ProbComp _);next table]=
      𝒮[do
        let chainTable ← ($ᵗ (selected → HashOutput) : ProbComp _)
        let extra ← ($ᵗ (ExtraRow selected inputs hrows → HashOutput) : ProbComp _)
        next ((publicTableEquiv selected inputs hrows).symm (chainTable,extra))] := by
  have hsplit : 𝒮[publicTableEquiv selected inputs hrows <$> ($ᵗ (inputs → HashOutput) : ProbComp _)]=
      𝒮[do
        let chainTable ← ($ᵗ (selected → HashOutput) : ProbComp _)
        let extra ← ($ᵗ (ExtraRow selected inputs hrows → HashOutput) : ProbComp _)
        pure (chainTable,extra)] :=
    (evalSPMF_map_bijective_uniform_cross (α := inputs → HashOutput)
      (β := (selected → HashOutput) × (ExtraRow selected inputs hrows → HashOutput))
      (publicTableEquiv selected inputs hrows) (publicTableEquiv selected inputs hrows).bijective).trans
      (FullGame.uniform_product (A := selected → HashOutput) (B := ExtraRow selected inputs hrows → HashOutput)).symm
  have h := congrArg (fun law : SPMF ((selected → HashOutput) × (ExtraRow selected inputs hrows → HashOutput)) =>
    law >>= fun result => 𝒮[next ((publicTableEquiv selected inputs hrows).symm result)]) hsplit
  simpa only [evalSPMF_map,evalSPMF_bind,bind_map_left,evalSPMF_pure,bind_assoc,pure_bind,
    Equiv.symm_apply_apply] using h
end SigGolfCandidate.T3.Security.FiniteRowSplit
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal FiniteRowSplit
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
noncomputable local instance : SampleableType HiddenLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance (inputs : Finset HashInput) (hrows : rows ⊆ inputs) :
    SampleableType (ExtraRow rows inputs hrows → HashOutput) := SampleableType.ofFintype _
theorem recorded_hidden_law {α : Type} (program : M α) :
    𝒮[FirstHit.record program (∅,∅)]=
      𝒮[do
        let hidden ← ($ᵗ HiddenLabels : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
        let extra ← ($ᵗ (ExtraRow rows (recordedInputs program) (rows_subset_recordedInputs program) → HashOutput) : ProbComp _)
        finiteRecorded (privateTableEquiv.symm (hidden ∘ Sum.inl,other)) (recordedInputs program)
          ((publicTableEquiv rows (recordedInputs program) (rows_subset_recordedInputs program)).symm
            (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual,extra)) program] := by
  rw [recorded_finite_law]
  trans 𝒮[do
    let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
    let chainTable ← ($ᵗ (rows → HashOutput) : ProbComp _)
    let extra ← ($ᵗ (ExtraRow rows (recordedInputs program) (rows_subset_recordedInputs program) → HashOutput) : ProbComp _)
    finiteRecorded privateTable (recordedInputs program)
      ((publicTableEquiv rows (recordedInputs program) (rows_subset_recordedInputs program)).symm
        (chainTable,extra)) program]
  · apply evalSPMF_bind_congr_left
    intro privateTable
    exact public_table_bind rows (recordedInputs program) (rows_subset_recordedInputs program)
      (fun table => finiteRecorded privateTable (recordedInputs program) table program)
  · exact initial_hidden_law (fun privateTable chainTable => do
      let extra ← ($ᵗ (ExtraRow rows (recordedInputs program) (rows_subset_recordedInputs program) → HashOutput) : ProbComp _)
      finiteRecorded privateTable (recordedInputs program)
        ((publicTableEquiv rows (recordedInputs program) (rows_subset_recordedInputs program)).symm
          (chainTable,extra)) program)
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal FiniteRowSplit
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : SampleableType HiddenLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance : SampleableType (rows → HashOutput) := SampleableType.ofFintype _
noncomputable local instance (inputs : Finset HashInput) (hrows : rows ⊆ inputs) :
    SampleableType (ExtraRow rows inputs hrows → HashOutput) := SampleableType.ofFintype _
noncomputable def hiddenRecorded {α : Type} (program : M α) : ProbComp (FirstHit.Recorded α) := do
  let hidden ← ($ᵗ HiddenLabels : ProbComp _)
  let other ← ($ᵗ OtherHalves : ProbComp _)
  let high ← ($ᵗ LowLabels : ProbComp _)
  let residual ← ($ᵗ (rows → HashOutput) : ProbComp _)
  let extra ← ($ᵗ (ExtraRow rows (recordedInputs program) (rows_subset_recordedInputs program) → HashOutput) : ProbComp _)
  finiteRecorded (privateTableEquiv.symm (hidden ∘ Sum.inl,other)) (recordedInputs program)
    ((publicTableEquiv rows (recordedInputs program) (rows_subset_recordedInputs program)).symm
      (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual,extra)) program
theorem hiddenRecorded_eq {α : Type} (program : M α) :
    𝒮[hiddenRecorded program]=𝒮[FirstHit.record program (∅,∅)] :=
  (recorded_hidden_law program).symm
end SigGolfCandidate.T3.Security.ChainGraph
namespace SigGolfCandidate.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable def hiddenExperiment (adversary : AdversaryP) : ProbComp (FirstHit.Recorded Bool) :=
  ChainGraph.hiddenRecorded (GameWith.idealGame checker adversary)
theorem traced_hidden_event (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (event : FirstHit.Recorded Bool → Prop) :
    Pr[event ∘ QueryRecorded.recordedTrace | tracedExperiment adversary budget hbudget]=
      Pr[event | hiddenExperiment adversary] := by
  have h := congrArg (fun law : PMF (FirstHit.Recorded Bool) => Pr[event | law])
    (traced_record_erasure adversary budget hbudget)
  rw [probEvent_map,MonitoredPrivate.event_lift] at h
  exact h.trans (probEvent_congr' (fun _ _ => Iff.rfl)
    (ChainGraph.hiddenRecorded_eq (GameWith.idealGame checker adversary)).symm)
theorem traced_hidden_cost_event (adversary : AdversaryP) (budget q : Nat)
    (hbudget : budget ≤ 2^127) (event : FirstHit.Recorded Bool → Prop) :
    Pr[fun result => result.2.2.base.source.1 ≤ q ∧ event (QueryRecorded.recordedTrace result) |
      tracedExperiment adversary budget hbudget]=
      Pr[fun result => (result.events.map (fun query => FullGame.queryCharge query.input)).sum ≤ q ∧
        event result | hiddenExperiment adversary] := by
  rw [← traced_hidden_event adversary budget hbudget
    (fun result => (result.events.map (fun query => FullGame.queryCharge query.input)).sum ≤ q ∧ event result)]
  rw [probEvent_eq_tsum_ite,probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases hr : result ∈ (tracedExperiment adversary budget hbudget).support
  · have hc := traced_cost_coherent adversary budget hbudget result hr
    change result.2.2.base.source.1=
      (result.2.2.events.map (fun query => FullGame.queryCharge query.input)).sum at hc
    simp only [Function.comp_def,QueryRecorded.recordedTrace,QueryRecorded.recorded,hc]
  · have hz : (tracedExperiment adversary budget hbudget) result=0 := by
      by_contra hn
      exact hr (by simpa only [PMF.mem_support_iff] using hn)
    simp only [PMF.probOutput_eq_apply,hz,ite_self]
end SigGolfCandidate.T3.Security.PaddedGame
end
section
namespace SigGolfCandidate.T3.Security.ChainGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete HiddenLabelObservation UniformTableCompletion
open ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem keep_programmed_iff (hidden : HiddenLabels) (high : LowLabels)
    (residual : rows → HashOutput) (point : Point) (candidate : Digest) :
    (probe point candidate).keep hidden
      (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
        ⟨row point candidate,row_mem point candidate⟩) ↔
      (probe point candidate).keep hidden (residual ⟨row point candidate,row_mem point candidate⟩) := by
  by_cases hmiss : hidden (child point) ≠ candidate
  · rw [safe_row_answer hidden high residual point candidate hmiss]
  · simp only [probe,Probe.keep,hmiss,false_and]
theorem guarded_row {Result : Type} (hidden : HiddenLabels) (high : LowLabels)
    (residual : rows → HashOutput) (point : Point) (candidate : Digest)
    (stopped : SPMF Result) (next : HashOutput → HiddenLabels → (rows → HashOutput) → SPMF Result) :
    (if (probe point candidate).keep hidden
      (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
        ⟨row point candidate,row_mem point candidate⟩) then
      next (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
        ⟨row point candidate,row_mem point candidate⟩) hidden residual else stopped)=
      (if (probe point candidate).keep hidden (residual ⟨row point candidate,row_mem point candidate⟩) then
        next (residual ⟨row point candidate,row_mem point candidate⟩) hidden residual else stopped) := by
  rw [keep_programmed_iff]
  split_ifs with hkeep
  · rw [safe_query_answer hidden high residual point candidate hkeep]
  · rfl
theorem fresh_row_posterior {Result : Type} (allowed : HiddenCoordinate → Finset Digest)
    (ha : ∀ coordinate,(allowed coordinate).Nonempty) (cache : ResidualTableCompletion.Cache rows)
    (high : LowLabels) (point : Point) (candidate : Digest)
    (hfresh : cache ⟨row point candidate,row_mem point candidate⟩=none)
    (stopped : SPMF Result) (next : HashOutput → HiddenLabels → (rows → HashOutput) → SPMF Result) :
    (complete allowed >>= fun hidden => completeRows cache >>= fun residual =>
      if (probe point candidate).keep hidden
        (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
          ⟨row point candidate,row_mem point candidate⟩) then
        next (programmed (hidden ∘ Sum.inl) (joinLabels (hidden ∘ Sum.inr) high) residual
          ⟨row point candidate,row_mem point candidate⟩) hidden residual else stopped)=
      observe (lazyResponse allowed (probe point candidate)) stopped (fun answer =>
        complete ((probe point candidate).restrict allowed answer) >>= fun hidden =>
          completeRows (Function.update cache ⟨row point candidate,row_mem point candidate⟩ (some answer)) >>=
            next answer hidden) := by
  simp_rw [guarded_row]
  exact ResidualProbeCompletion.bind_fresh_probe allowed ha cache
    ⟨row point candidate,row_mem point candidate⟩ hfresh (probe point candidate) stopped next
theorem output_failure (allowed : HiddenCoordinate → Finset Digest)
    (ha : ∀ coordinate,(allowed coordinate).Nonempty) (point : Point) :
    (lazyResponse allowed (.output (parent point))).toPMF none=(2 : ENNReal)⁻¹^128 := by
  rw [lazyResponse_output_failure allowed ha (parent point)]
  have hc : Fintype.card SphincsSecurity.Digest=2^128 := by
    simp [SphincsSecurity.Digest,SphincsSecurity.digestBits]
  rw [hc,Nat.cast_pow,Nat.cast_ofNat,ENNReal.inv_pow]
end SigGolfCandidate.T3.Security.ChainGraph
end
section
namespace SigGolfCandidate.T3.Security.FirstHit
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem recorded_public_known {α : Type} (program : M α) (before : LazyPrivate.State)
    (result : Recorded α) (hr : result ∈ support (record program before))
    (prior : LazyPrivate.State) (input : HashInput) (answer : HashOutput)
    (he : (⟨prior,.inl (.inr input),answer⟩ : QueryEvent) ∈ result.events) :
    result.state.2 input=some answer ∧ SourceReplay.Extends prior result.state := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [record_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      simp at he
  | query_bind query next ih =>
      rw [record_query_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last,hl,rfl⟩ := hr
      have htail := recorded_support (next middle.1) middle.2 last hl
      have hx := SourceReplay.run_extends (next middle.1) middle.2 (last.value,last.state) htail
      rcases List.mem_cons.mp he with he | he
      · cases he
        exact ⟨SourceReplay.known_mono middle.2 last.state hx
          (SourceReplay.hash_query_caches _ (by trivial) prior middle hm),
          (SourceReplay.query_extends _ prior middle hm).trans hx⟩
      · exact ih middle.1 middle.2 last hl he
theorem newly_cached_public {α : Type} (program : M α) (before : LazyPrivate.State)
    (result : Recorded α) (hr : result ∈ support (record program before))
    (input : HashInput) (answer : HashOutput) (hbefore : before.2 input=none)
    (hafter : result.state.2 input=some answer) :
    ∃ prior,(⟨prior,.inl (.inr input),answer⟩ : QueryEvent) ∈ result.events ∧ prior.2 input=none := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [record_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      exact False.elim (by simpa [hbefore] using hafter)
  | query_bind query next ih =>
      rw [record_query_bind,mem_support_bind_iff] at hr
      obtain ⟨middle,hm,hr⟩ := hr
      rw [support_map] at hr
      obtain ⟨last,hl,rfl⟩ := hr
      by_cases hmid : middle.2.2 input=none
      · obtain ⟨prior,he,hfresh⟩ := ih middle.1 middle.2 last hl hmid hafter
        exact ⟨prior,List.mem_cons_of_mem _ he,hfresh⟩
      · have hadv := query_advance before query middle hm
        cases query with
        | inl query =>
            cases query with
            | inl coin => exact False.elim (hmid (by simpa [advance] using congrArg (fun s : LazyPrivate.State => s.2 input) hadv |>.trans hbefore))
            | inr actual =>
                by_cases heq : actual=input
                · subst actual
                  have hx := SourceReplay.run_extends (next middle.1) middle.2 (last.value,last.state)
                    (recorded_support _ _ _ hl)
                  have hk := SourceReplay.known_mono middle.2 last.state hx
                    (SourceReplay.hash_query_caches (.inl (.inr input)) (by trivial) before middle hm)
                  have ha : middle.1=answer := Option.some.inj (hk.symm.trans hafter)
                  refine ⟨before,?_,hbefore⟩
                  rw [← ha]
                  exact List.mem_cons_self
                · apply False.elim
                  apply hmid
                  rw [hadv]
                  simpa [advance,QueryCache.cacheQuery,heq,Ne.symm heq] using hbefore
        | inr coordinate =>
            apply False.elim
            apply hmid
            rw [hadv]
            exact hbefore
theorem first_public_occurrence {α : Type} (program : M α) (result : Recorded α)
    (hr : result ∈ support (record program (∅,∅)))
    (prior : LazyPrivate.State) (input : HashInput) (answer : HashOutput)
    (he : (⟨prior,.inl (.inr input),answer⟩ : QueryEvent) ∈ result.events) :
    ∃ first,(⟨first,.inl (.inr input),answer⟩ : QueryEvent) ∈ result.events ∧ first.2 input=none :=
  newly_cached_public program (∅,∅) result hr input answer rfl
    (recorded_public_known program (∅,∅) result hr prior input answer he).1
end SigGolfCandidate.T3.Security.FirstHit
end
section
namespace SigGolfCandidate.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem queried_eq {α : Type} (answers : Answers) (program : M α) :
    SourceReplay.queried answers program=SecurityExtraction.queried answers program := rfl
theorem verifyP_hashOnly (message : Message) (publicKey : Digest) (witness : WBytes) :
    SourceReplay.HashOnly (verifyP message publicKey witness) := by
  apply allQ_mono (publicOnly_verifyP message publicKey witness)
  intro input h
  rcases input with (sample | query) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem public_occurrence {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (input : HashInput) (hq : .inl (.inr input) ∈ SecurityExtraction.queried answers program) :
    ∃ prior,(⟨prior,.inl (.inr input),answers (.inl (.inr input))⟩ : FirstHit.QueryEvent) ∈ result.events := by
  have hqueries : SourceReplay.queried (SourceReplay.answers result.state) program=
      SourceReplay.queried answers program := by
    rw [← FirstHit.recorded_inputs program hp before result hr (SourceReplay.answers result.state)
      (SourceReplay.answers_known result.state),← FirstHit.recorded_inputs program hp before result hr answers ha]
  obtain ⟨prior,hevent,_⟩ := FirstHit.extracted_public_occurrence program hp before result hr input
    (by rw [hqueries,queried_eq]; exact hq)
  have hknown := (FirstHit.recorded_query_known program hp before result hr _ hevent).1
  have heq := ha _ _ hknown
  exact ⟨prior,by simpa only [heq] using hevent⟩
def ActualHit (answers : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (position : Extract.Pos) (actual : HashInput) (prior : LazyPrivate.State), position.Bounded ∧ Extract.posOf actual=some position ∧
    (⟨prior,.inl (.inr actual),answers (.inl (.inr actual))⟩ : FirstHit.QueryEvent) ∈ events ∧
    SecurityExtraction.HashHit answers (Extract.honestInput answers position) actual
theorem hit_recorded {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hit : Extract.HitIn answers (SecurityExtraction.queried answers program)) :
    ActualHit answers result.events := by
  obtain ⟨position,actual,hbounded,hquery,hpos,hhit⟩ := Extract.hitIn_posOf hit
  obtain ⟨prior,hevent⟩ := public_occurrence program hp before result hr answers ha actual hquery
  exact ⟨position,actual,prior,hbounded,hpos,hevent,hhit⟩
def Conclusion (answers : Answers) (message : Message) (witness : WBytes)
    (events : List FirstHit.QueryEvent) : Prop :=
  ∃ digestAnswer : HashOutput, (wdc witness).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))=digestAnswer ∧
      (∃ prior,(⟨prior,.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))),digestAnswer⟩ :
        FirstHit.QueryEvent) ∈ events) ∧ Shaped digestAnswer witness ∧ digestGate digestAnswer=true ∧
      (ActualHit answers events ∨
        (∃ lay : Layer, Extract.Diverge answers witness (digestAnswer.toNat % 2^31) lay
          (events.map FirstHit.QueryEvent.input) ∧
          ∀ above : Layer,above.val < lay.val → Extract.Good answers witness (digestAnswer.toNat % 2^31) above) ∨
        ((∀ lay : Layer,Extract.Good answers witness (digestAnswer.toNat % 2^31) lay) ∧
          FtsExtract.FtsShaped answers digestAnswer witness))
theorem verifyP_recorded (message : Message) (publicKey : Digest) (witness : WBytes)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (verifyP message publicKey witness) before))
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hpk : publicKey=Extract.honestRoot answers 0 0) (hwin : result.value=true) :
    Conclusion answers message witness result.events := by
  have hp := verifyP_hashOnly message publicKey witness
  have hv := (SourceReplay.resolves_of_run (verifyP message publicKey witness) hp before
    (result.value,result.state) (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hv
  obtain ⟨digestAnswer,hcounter,hdigest,hquery,hshape,halternatives⟩ :=
    Extract.verifyP_extract_full answers message publicKey witness hpk hv
  obtain ⟨prior,hevent⟩ := public_occurrence _ hp before result hr answers ha _ hquery
  have hanswer : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))))=digestAnswer :=
    hdigest
  refine ⟨digestAnswer,hcounter,hdigest,⟨prior,by simpa only [hanswer] using hevent⟩,hshape,by simpa only [← hdigest] using verifyP_digestGate answers message publicKey witness hv,?_⟩
  rcases halternatives with hhit | hdiverge | hhonest
  · exact Or.inl (hit_recorded _ hp before result hr answers ha hhit)
  · obtain ⟨lay,hdiverge,hgood⟩ := hdiverge
    refine Or.inr (Or.inl ⟨lay,?_,hgood⟩)
    rw [FirstHit.recorded_inputs _ hp before result hr answers ha,queried_eq]
    exact hdiverge
  · exact Or.inr (Or.inr hhonest)
end SigGolfCandidate.T3.Security.PaddedExtraction
end
section
namespace SigGolfCandidate.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M Correctness
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def reference : FirstHit.Reference := fun state input =>
  (Extract.posOf input).map (Extract.honestInput (SourceReplay.answers state))
theorem reference_of_pos (state : LazyPrivate.State) (input : HashInput) (position : Extract.Pos)
    (hpos : Extract.posOf input=some position) :
    reference state input=some (Extract.honestInput (SourceReplay.answers state) position) := by
  simp only [reference,hpos,Option.map_some]
def UnresolvedHit (answers : Answers) (events : List FirstHit.QueryEvent) : Prop :=
  ∃ (position : Extract.Pos) (actual : HashInput) (prior : LazyPrivate.State), position.Bounded ∧ Extract.posOf actual=some position ∧
    (⟨prior,.inl (.inr actual),answers (.inl (.inr actual))⟩ : FirstHit.QueryEvent) ∈ events ∧
    prior.2 actual=none ∧
    SecurityExtraction.HashHit answers (Extract.honestInput answers position) actual ∧
    (reference prior actual≠some (Extract.honestInput answers position) ∨
      prior.2 (Extract.honestInput answers position)=none)
theorem ActualHit.mono {answers : Answers} {events events' : List FirstHit.QueryEvent}
    (hit : ActualHit answers events) (hsub : ∀ event ∈ events,event ∈ events') :
    ActualHit answers events' := by
  obtain ⟨position,actual,prior,hbounded,hpos,hevent,hhit⟩ := hit
  exact ⟨position,actual,prior,hbounded,hpos,hsub _ hevent,hhit⟩
theorem Conclusion.mono {answers : Answers} {message : Message} {witness : WBytes}
    {events events' : List FirstHit.QueryEvent} (h : Conclusion answers message witness events)
    (hsub : ∀ event ∈ events,event ∈ events') : Conclusion answers message witness events' := by
  obtain ⟨N,hcounter,hdigest,⟨prior,hevent⟩,hshape,hgate,halt⟩ := h
  refine ⟨N,hcounter,hdigest,⟨prior,hsub _ hevent⟩,hshape,hgate,?_⟩
  rcases halt with hhit | ⟨lay,hdiv,hgood⟩ | hgood
  · exact Or.inl (hhit.mono hsub)
  · refine Or.inr (Or.inl ⟨lay,hdiv.mono ?_,hgood⟩)
    intro input hin
    obtain ⟨event,hevent,rfl⟩ := List.mem_map.mp hin
    exact List.mem_map.mpr ⟨event,hsub _ hevent,rfl⟩
  · exact Or.inr (Or.inr hgood)
theorem actualHit_known_or_unresolved {α : Type} (program : M α) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program (∅,∅))) (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hit : ActualHit answers result.events) :
    FirstHit.KnownPublicHit reference result ∨ UnresolvedHit answers result.events := by
  obtain ⟨position,actual,prior,hbounded,hpos,hevent,hhit⟩ := hit
  obtain ⟨first,hfirst,hfresh⟩ := FirstHit.first_public_occurrence program result hr prior actual _ hevent
  by_cases href : reference first actual=some (Extract.honestInput answers position)
  · cases hout : first.2 (Extract.honestInput answers position) with
    | none => exact Or.inr ⟨position,actual,first,hbounded,hpos,hfirst,hfresh,hhit,Or.inr hout⟩
    | some output =>
        have hx := (FirstHit.recorded_public_known program (∅,∅) result hr first actual _ hfirst).2
        have hk := SourceReplay.known_mono first result.state hx
          (show SourceReplay.known first (.inl (.inr (Extract.honestInput answers position)))=some output from hout)
        have heq := ha _ _ hk
        exact Or.inl ⟨first,actual,answers (.inl (.inr actual)),Extract.honestInput answers position,output,
          hfirst,hfresh,href,hout,by simpa only [heq] using hhit.2⟩
  · exact Or.inr ⟨position,actual,first,hbounded,hpos,hfirst,hfresh,hhit,Or.inl href⟩
theorem padded_known_bound (adversary : Final.AdversaryP) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.2.2.base.source.1≤q ∧
      FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) |
      PaddedGame.tracedExperiment adversary q hq] ≤ q/(2 : ENNReal)^128 :=
  GameWith.Recorded.known_public_hit_bound PaddedGame.checker reference adversary q hq
end SigGolfCandidate.T3.Security.PaddedExtraction
end
section
namespace SigGolfCandidate.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M Correctness Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
def Fresh (log : QueryLog Requests) : ForgeryP → Prop
  | .witness message _ => ¬∃ entry ∈ log,entry.1.message=message ∧ entry.2.isSome=true
  | .signature message signature => ¬∃ entry ∈ log,entry.1.message=message ∧ entry.2=some signature
def WitnessOf (answers : Answers) (publicKey : Digest) : ForgeryP → Message → WBytes → Prop
  | .witness message witness, m, w => m=message ∧ w=witness
  | .signature message signature, m, w => m=message ∧ evalWithAnswerFn answers (expandB message publicKey signature)=some w
theorem check_hashOnly (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP) :
    SourceReplay.HashOnly (checkForgeryP publicKey log forgery) := by
  apply allQ_mono (PaddedGame.check_public publicKey log forgery)
  intro input h
  rcases input with (coin | input) | coordinate
  · exact h.elim
  · trivial
  · trivial
theorem check_accepting (answers : Answers) (publicKey : Digest) (log : QueryLog Requests)
    (forgery : ForgeryP) (hw : evalWithAnswerFn answers (checkForgeryP publicKey log forgery)=true) :
    Fresh log forgery ∧ ∃ message witness,WitnessOf answers publicKey forgery message witness ∧
      evalWithAnswerFn answers (verifyP message publicKey witness)=true ∧
      ∀ input ∈ SecurityExtraction.queried answers (verifyP message publicKey witness),
        input ∈ SecurityExtraction.queried answers (checkForgeryP publicKey log forgery) := by
  cases forgery with
  | witness message witness =>
      simp only [checkForgeryP,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Bool.and_eq_true,
        decide_eq_true_eq] at hw
      refine ⟨hw.1,message,witness,⟨rfl,rfl⟩,hw.2,?_⟩
      intro input hi
      simpa only [checkForgeryP,SecurityExtraction.queried_bind,SecurityExtraction.queried_pure,
        List.append_nil] using hi
  | signature message signature =>
      cases he : evalWithAnswerFn answers (expandB message publicKey signature) with
      | none => simp [checkForgeryP,evalWithAnswerFn_bind,he,evalWithAnswerFn_pure] at hw
      | some witness =>
          simp only [checkForgeryP,evalWithAnswerFn_bind,he,evalWithAnswerFn_pure,Bool.and_eq_true,
            decide_eq_true_eq] at hw
          refine ⟨hw.1,message,witness,⟨rfl,he⟩,hw.2,?_⟩
          intro input hi
          simp only [checkForgeryP,SecurityExtraction.queried_bind,he,SecurityExtraction.queried_pure,
            List.append_nil]
          exact List.mem_append_right _ hi
theorem verifyP_extracted_in {α : Type} (program : M α) (hp : SourceReplay.HashOnly program)
    (before : LazyPrivate.State) (result : FirstHit.Recorded α)
    (hr : result ∈ support (FirstHit.record program before)) (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (message : Message) (publicKey : Digest) (witness : WBytes)
    (hpk : publicKey=Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP message publicKey witness)=true)
    (hsub : ∀ input ∈ SecurityExtraction.queried answers (verifyP message publicKey witness),
      input ∈ SecurityExtraction.queried answers program) : Conclusion answers message witness result.events := by
  obtain ⟨N,hcounter,hdigest,hquery,hshape,halt⟩ := Extract.verifyP_extract_full answers message publicKey witness hpk hv
  obtain ⟨prior,hevent⟩ := public_occurrence program hp before result hr answers ha _ (hsub _ hquery)
  have hans : answers (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))))=N := hdigest
  refine ⟨N,hcounter,hdigest,⟨prior,by simpa only [hans] using hevent⟩,hshape,by simpa only [← hdigest] using verifyP_digestGate answers message publicKey witness hv,?_⟩
  rcases halt with hhit | ⟨lay,hdiv,hgood⟩ | hgood
  · exact Or.inl (hit_recorded program hp before result hr answers ha (hhit.mono hsub))
  · refine Or.inr (Or.inl ⟨lay,hdiv.mono ?_,hgood⟩)
    intro input hin
    rw [FirstHit.recorded_inputs program hp before result hr answers ha,queried_eq]
    exact hsub _ hin
  · exact Or.inr (Or.inr hgood)
theorem check_recorded (publicKey : Digest) (log : QueryLog Requests) (forgery : ForgeryP)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (checkForgeryP publicKey log forgery) before))
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hpk : publicKey=Extract.honestRoot answers 0 0) (hwin : result.value=true) :
    Fresh log forgery ∧ ∃ message witness,WitnessOf answers publicKey forgery message witness ∧
      Conclusion answers message witness result.events := by
  have hp := check_hashOnly publicKey log forgery
  have hw := (SourceReplay.resolves_of_run _ hp before (result.value,result.state)
    (FirstHit.recorded_support _ _ _ hr)).eval answers ha
  rw [hwin] at hw
  obtain ⟨hfresh,message,witness,hof,hv,hsub⟩ := check_accepting answers publicKey log forgery hw
  exact ⟨hfresh,message,witness,hof,verifyP_extracted_in _ hp before result hr answers ha message publicKey witness hpk hv hsub⟩
theorem verdict_recorded (publicKey : Digest) (interaction : Option ForgeryP × QueryLog Requests)
    (before : LazyPrivate.State) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker publicKey interaction) before))
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hpk : publicKey=Extract.honestRoot answers 0 0) (hwin : result.value=true) :
    interaction.2.length≤2^32 ∧ ∃ forgery,interaction.1=some forgery ∧ Fresh interaction.2 forgery ∧
      ∃ message witness,WitnessOf answers publicKey forgery message witness ∧
        Conclusion answers message witness result.events := by
  cases hf : interaction.1 with
  | none =>
      simp only [GameWith.verdict,hf,FirstHit.record_pure,support_pure,Set.mem_singleton_iff] at hr
      subst result
      contradiction
  | some forgery =>
      simp only [GameWith.verdict,hf,PaddedGame.checker] at hr
      obtain ⟨checked,hchecked,last,hlast,hvalue,hevents,hstate⟩ := FirstHit.record_bind_support _ _ before result hr
      rw [FirstHit.record_pure,support_pure,Set.mem_singleton_iff] at hlast
      subst last
      simp only [List.append_nil] at hevents
      have hand : (decide (interaction.2.length≤2^32) && checked.value)=true := hvalue.symm.trans hwin
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hand
      obtain ⟨hlength,hcheckedWin⟩ := hand
      have hcheck := check_recorded publicKey interaction.2 forgery before checked hchecked answers
        (by simpa only [hstate] using ha) hpk hcheckedWin
      obtain ⟨hfresh,message,witness,hof,hconclusion⟩ := hcheck
      exact ⟨hlength,forgery,rfl,hfresh,message,witness,hof,hevents ▸ hconclusion⟩
end SigGolfCandidate.T3.Security.PaddedExtraction
end
section
namespace SigGolfCandidate.T3.Security.PaddedExtraction
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M Correctness Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen verifyP expandB
def GameConclusion (adversary : AdversaryP) (answers : Answers) (result : FirstHit.Recorded Bool) : Prop :=
  ∃ generated ∈ support (FirstHit.record keygen (∅,∅)),
    ∃ interaction ∈ support (FirstHit.record
      (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
        (adversary generated.value.1 generated.value.2)) generated.state),
      generated.value.1=Extract.honestRoot answers 0 0 ∧
      interaction.value.2.length≤2^32 ∧
      ∃ forgery,interaction.value.1=some forgery ∧ Fresh interaction.value.2 forgery ∧
      ∃ message witness,WitnessOf answers generated.value.1 forgery message witness ∧
        Conclusion answers message witness result.events
theorem game_recorded (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (hr : result ∈ support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅,∅)))
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.state input=some answer → answers input=answer)
    (hwin : result.value=true) : GameConclusion adversary answers result := by
  unfold GameWith.idealGame at hr
  obtain ⟨generated,hgenerated,rest,hrest,hvalue,hevents,hstate⟩ :=
    FirstHit.record_bind_support _ _ (∅,∅) result hr
  obtain ⟨interaction,hinteraction,checked,hchecked,hrestValue,hrestEvents,hrestState⟩ :=
    FirstHit.record_bind_support _ _ generated.state rest hrest
  have hgeneratedState : SourceReplay.Extends generated.state result.state := by
    rw [hstate]
    exact SourceReplay.run_extends _ generated.state (rest.value,rest.state)
      (FirstHit.recorded_support _ _ _ hrest)
  have hgen : evalWithAnswerFn answers keygen=generated.value :=
    (SourceReplay.resolves_of_run keygen SourceReplay.hashOnly_keygen (∅,∅)
      (generated.value,generated.state) (FirstHit.recorded_support _ _ _ hgenerated)).eval answers
        (fun input answer hk => ha input answer
          (SourceReplay.known_mono generated.state result.state hgeneratedState hk))
  have hpk : generated.value.1=Extract.honestRoot answers 0 0 := by
    rw [← hgen]
    exact Extract.keygen_pk answers
  have hac : ∀ input answer,SourceReplay.known checked.state input=some answer → answers input=answer := by
    simpa only [hstate,hrestState] using ha
  have hw : checked.value=true := hrestValue.symm.trans (hvalue.symm.trans hwin)
  obtain ⟨hlength,forgery,hforgery,hfresh,message,witness,hof,hconclusion⟩ :=
    verdict_recorded generated.value.1 interaction.value interaction.state checked hchecked answers hac hpk hw
  refine ⟨generated,hgenerated,interaction,hinteraction,hpk,hlength,forgery,hforgery,hfresh,message,witness,hof,
    hconclusion.mono ?_⟩
  intro event he
  rw [hevents,hrestEvents]
  exact List.mem_append_right _ (List.mem_append_right _ he)
theorem traced_record_support (adversary : AdversaryP) (budget : Nat) (hbudget : budget≤2^127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.recordedTrace result ∈ support
      (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅,∅)) := by
  have hm : QueryRecorded.recordedTrace result ∈
      (QueryRecorded.recordedTrace <$> PaddedGame.tracedExperiment adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map,PMF.support_map]
    exact ⟨result,hr,rfl⟩
  rw [PaddedGame.traced_record_erasure,MonitoredPrivate.pmf_support] at hm
  exact hm
theorem traced_game (adversary : AdversaryP) (budget : Nat) (hbudget : budget≤2^127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.2.2.base.source.2 input=some answer → answers input=answer)
    (hwin : result.1=true) : GameConclusion adversary answers (QueryRecorded.recordedTrace result) :=
  game_recorded adversary _ (traced_record_support adversary budget hbudget result hr) answers ha hwin
theorem traced_hit_split (adversary : AdversaryP) (budget : Nat) (hbudget : budget≤2^127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support)
    (answers : Answers)
    (ha : ∀ input answer,SourceReplay.known result.2.2.base.source.2 input=some answer → answers input=answer)
    (hit : ActualHit answers (QueryRecorded.recordedTrace result).events) :
    FirstHit.KnownPublicHit reference (QueryRecorded.recordedTrace result) ∨
      UnresolvedHit answers (QueryRecorded.recordedTrace result).events :=
  actualHit_known_or_unresolved _ _ (traced_record_support adversary budget hbudget result hr) answers ha hit
end SigGolfCandidate.T3.Security.PaddedExtraction
end
section
namespace SigGolfCandidate.T3.BPORS.Adaptive
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Creation
theorem expectedValue_left_mul {α : Type} (law : PMF α)
    (factor : ENNReal) (payoff : α → ENNReal) :
    expectedValue law (fun result => factor * payoff result) =
      factor * expectedValue law payoff := by
  unfold expectedValue
  simp_rw [mul_left_comm _ factor]
  exact ENNReal.tsum_mul_left
noncomputable def expectedCharges {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (program : OracleComp spec α) : σ → ENNReal :=
  OracleComp.construct (fun _ _ => 0)
    (fun input _ next state => charge input state +
      expectedValue ((impl input).run state) (fun result => next result.1 result.2)) program
theorem expectedCharges_pure {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (value : α) (state : σ) : expectedCharges impl charge (pure value) state = 0 := rfl
theorem expectedCharges_query_bind {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α) (state : σ) :
    expectedCharges impl charge (OracleSpec.query input >>= next) state =
      charge input state + expectedValue ((impl input).run state)
        (fun result => expectedCharges impl charge (next result.1) result.2) := rfl
theorem expectedCharges_mono {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (first second : spec.Domain → σ → ENNReal)
    (invariant : σ → Prop)
    (hpreserve : ∀ input state, invariant state →
      ∀ result ∈ ((impl input).run state).support, invariant result.2)
    (hle : ∀ input state, invariant state → first input state ≤ second input state)
    (program : OracleComp spec α) (state : σ) (hinv : invariant state) :
    expectedCharges impl first program state ≤ expectedCharges impl second program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedCharges_query_bind, expectedCharges_query_bind]
      apply add_le_add (hle input state hinv)
      unfold expectedValue
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ ((impl input).run state).support
      · exact mul_le_mul' le_rfl (ih result.1 result.2 (hpreserve input state hinv result hr))
      · have hp : Pr[= result | (impl input).run state] = 0 := by
          rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
          exact hr
        rw [hp, zero_mul, zero_mul]
theorem expected_accumulator {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (counter : σ → ENNReal)
    (charge : spec.Domain → σ → ENNReal)
    (hstep : ∀ input state, expectedValue ((impl input).run state)
      (fun result => counter result.2) = counter state + charge input state)
    (program : OracleComp spec α) (state : σ) :
    expectedValue ((simulateQ impl program).run state) (fun result => counter result.2) =
      counter state + expectedCharges impl charge program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, expectedCharges_pure, add_zero]
      exact expectedValue_pure _ _
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        expectedCharges_query_bind]
      simp_rw [ih]
      rw [expectedValue_add, hstep, add_assoc]
theorem expectedCharges_add {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (first second : spec.Domain → σ → ENNReal)
    (program : OracleComp spec α) (state : σ) :
    expectedCharges impl (fun input state => first input state + second input state) program state =
      expectedCharges impl first program state + expectedCharges impl second program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [expectedCharges_pure]
  | query_bind input next ih =>
      simp_rw [expectedCharges_query_bind, ih, expectedValue_add]
      ac_rfl
theorem expectedCharges_scale {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ PMF)) (charge : spec.Domain → σ → ENNReal)
    (factor : ENNReal) (program : OracleComp spec α) (state : σ) :
    expectedCharges impl (fun input state => factor * charge input state) program state =
      factor * expectedCharges impl charge program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [expectedCharges_pure]
  | query_bind input next ih =>
      simp_rw [expectedCharges_query_bind, ih, expectedValue_left_mul]
      exact (mul_add _ _ _).symm
theorem expectedCharges_project {ι σ τ α : Type} {spec : OracleSpec ι}
    (first : QueryImpl spec (StateT σ PMF)) (second : QueryImpl spec (StateT τ PMF))
    (project : σ → τ)
    (hquery : ∀ input state, Prod.map id project <$> (first input).run state =
      (second input).run (project state))
    (charge : spec.Domain → τ → ENNReal) (program : OracleComp spec α) (state : σ) :
    expectedCharges first (fun input before => charge input (project before)) program state =
      expectedCharges second charge program (project state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind input next ih =>
      rw [expectedCharges_query_bind, expectedCharges_query_bind]
      congr 1
      simp_rw [ih]
      rw [← hquery input state, expectedValue_map]
      rfl
end Creation
namespace ProposalModel
variable {ι State Label : Type} {spec : OracleSpec ι}
noncomputable def completionPotential (model : ProposalModel spec State Label)
    (total : Nat) (payoff : List Label → ENNReal) (consumed : List Label) : ENNReal :=
  expectedValue (completeProposalWord model.base total consumed) payoff
theorem completionPotential_query (model : ProposalModel spec State Label)
    (total : Nat) (payoff : List Label → ENNReal)
    (input : spec.Domain) (state : List Label × State) :
    expectedValue ((model.traced input).run state)
      (fun result => model.completionPotential total payoff result.2.1) =
      model.completionPotential total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Label) => expectedValue law payoff)
    (model.traced_query_complete total input state)
  rw [← PMF.monad_bind_eq_bind, expectedValue_bind] at h
  exact h
theorem completionPotential_program {α : Type} (model : ProposalModel spec State Label)
    (total : Nat) (payoff : List Label → ENNReal)
    (program : OracleComp spec α) (state : List Label × State) :
    expectedValue ((simulateQ model.traced program).run state)
      (fun result => model.completionPotential total payoff result.2.1) =
      model.completionPotential total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Label) => expectedValue law payoff)
    (model.traced_complete total program state)
  rw [← PMF.monad_bind_eq_bind, expectedValue_bind] at h
  exact h
theorem completionPotential_nil (model : ProposalModel spec State Label)
    (total : Nat) (payoff : List Label → ENNReal) :
    model.completionPotential total payoff [] =
      expectedValue (independentProposalWord model.base total) payoff := by
  rw [completionPotential, completeProposalWord_nil]
def creationStep (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (input : spec.Domain) (state : Nat × (List Label × State)) : Nat :=
  min (weight input state.2) (cap - state.1)
noncomputable def creationImpl (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat) :
    QueryImpl spec (StateT (Nat × (List Label × State)) PMF) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1,
      (state.1 + creationStep weight cap input state, result.2))) <$>
        (model.traced input).run state.2
theorem creation_query_project (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (input : spec.Domain) (state : Nat × (List Label × State)) :
    Prod.map id Prod.snd <$> (model.creationImpl weight cap input).run state =
      (model.traced input).run state.2 := by
  simp only [creationImpl, StateT.run_mk, Functor.map_map]
  change id <$> (model.traced input).run state.2 = _
  exact id_map _
theorem creation_program_project {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (program : OracleComp spec α) (state : Nat × (List Label × State)) :
    Prod.map id Prod.snd <$> (simulateQ (model.creationImpl weight cap) program).run state =
      (simulateQ model.traced program).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (model.creation_query_project weight cap) program state
theorem creation_query_potential (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (input : spec.Domain)
    (state : Nat × (List Label × State)) :
    expectedValue ((model.creationImpl weight cap input).run state)
      (fun result => model.completionPotential total payoff result.2.2.1) =
      model.completionPotential total payoff state.2.1 := by
  rw [creationImpl, StateT.run_mk, expectedValue_map]
  exact model.completionPotential_query total payoff input state.2
theorem creation_query_mass_potential (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (input : spec.Domain)
    (state : Nat × (List Label × State)) :
    expectedValue ((model.creationImpl weight cap input).run state)
      (fun result => (result.2.1 : ENNReal) *
        model.completionPotential total payoff result.2.2.1) =
      (state.1 : ENNReal) * model.completionPotential total payoff state.2.1 +
        (creationStep weight cap input state : ENNReal) *
          model.completionPotential total payoff state.2.1 := by
  rw [creationImpl, StateT.run_mk, expectedValue_map]
  change expectedValue ((model.traced input).run state.2)
    (fun result => ((state.1 + creationStep weight cap input state : Nat) : ENNReal) *
      model.completionPotential total payoff result.2.1) = _
  rw [Creation.expectedValue_left_mul, model.completionPotential_query, Nat.cast_add, add_mul]
theorem creation_query_mass_le (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (input : spec.Domain) (state : Nat × (List Label × State)) (hstate : state.1 ≤ cap)
    (result : spec.Range input × (Nat × (List Label × State)))
    (hr : result ∈ ((model.creationImpl weight cap input).run state).support) :
    result.2.1 ≤ cap := by
  rw [creationImpl, StateT.run_mk, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hr
  obtain ⟨middle, _, rfl⟩ := hr
  dsimp
  unfold creationStep
  have hmin := Nat.min_le_right (weight input state.2) (cap - state.1)
  omega
theorem creation_program_mass_le {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (program : OracleComp spec α) (state : Nat × (List Label × State)) (hstate : state.1 ≤ cap)
    (result : α × (Nat × (List Label × State)))
    (hr : result ∈ ((simulateQ (model.creationImpl weight cap) program).run state).support) :
    result.2.1 ≤ cap := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hstate
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (model.creation_query_mass_le weight cap input state hstate middle hm) hr
theorem creation_program_potential {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (program : OracleComp spec α)
    (state : Nat × (List Label × State)) :
    expectedValue ((simulateQ (model.creationImpl weight cap) program).run state)
      (fun result => model.completionPotential total payoff result.2.2.1) =
      model.completionPotential total payoff state.2.1 := by
  have h := congrArg (fun law : PMF (α × (List Label × State)) =>
    expectedValue law (fun result => model.completionPotential total payoff result.2.1))
      (model.creation_program_project weight cap program state)
  rw [expectedValue_map] at h
  exact h.trans (model.completionPotential_program total payoff program state.2)
theorem creation_query_mass (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (input : spec.Domain) (state : Nat × (List Label × State)) :
    expectedValue ((model.creationImpl weight cap input).run state)
      (fun result => (result.2.1 : ENNReal)) =
      (state.1 : ENNReal) + (creationStep weight cap input state : ENNReal) := by
  rw [creationImpl, StateT.run_mk, expectedValue_map]
  change expectedValue ((model.traced input).run state.2)
    (fun _ => ((state.1 + creationStep weight cap input state : Nat) : ENNReal)) = _
  rw [expectedValue_const (by simp), Nat.cast_add]
theorem creation_program_mass {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (program : OracleComp spec α) (state : List Label × State) :
    expectedValue ((simulateQ (model.creationImpl weight cap) program).run (0, state))
      (fun result => (result.2.1 : ENNReal)) =
      Creation.expectedCharges (model.creationImpl weight cap)
        (fun input before => (creationStep weight cap input before : ENNReal))
        program (0, state) := by
  have h := Creation.expected_accumulator (model.creationImpl weight cap)
    (fun before => (before.1 : ENNReal))
    (fun input before => (creationStep weight cap input before : ENNReal))
    (model.creation_query_mass weight cap) program (0, state)
  simpa only [Nat.cast_zero, zero_add] using h
theorem creation_mass_le_source_charges {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap : Nat)
    (program : OracleComp spec α) (state : List Label × State) :
    expectedValue ((simulateQ (model.creationImpl weight cap) program).run (0, state))
      (fun result => (result.2.1 : ENNReal)) ≤
      Creation.expectedCharges model.traced (fun input before => (weight input before : ENNReal))
        program state := by
  rw [model.creation_program_mass]
  calc
    _ ≤ Creation.expectedCharges (model.creationImpl weight cap)
        (fun input before => (weight input before.2 : ENNReal)) program (0, state) := by
      apply Creation.expectedCharges_mono _ _ _ (fun _ => True)
        (fun _ _ _ _ _ => trivial) _ _ _ trivial
      intro input before _
      exact_mod_cast Nat.min_le_left (weight input before.2) (cap - before.1)
    _ = _ := Creation.expectedCharges_project _ _ Prod.snd
      (model.creation_query_project weight cap)
      (fun input before => (weight input before : ENNReal)) program (0, state)
theorem creation_charge_bound {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (program : OracleComp spec α)
    (state : Nat × (List Label × State)) (hstate : state.1 ≤ cap) :
    Creation.expectedCharges (model.creationImpl weight cap)
      (fun input before => (creationStep weight cap input before : ENNReal) *
        model.completionPotential total payoff before.2.1) program state ≤
      (cap : ENNReal) * model.completionPotential total payoff state.2.1 := by
  have hacc := Creation.expected_accumulator (model.creationImpl weight cap)
    (fun before => (before.1 : ENNReal) * model.completionPotential total payoff before.2.1)
    (fun input before => (creationStep weight cap input before : ENNReal) *
      model.completionPotential total payoff before.2.1)
    (model.creation_query_mass_potential weight cap total payoff) program state
  calc
    _ ≤ (state.1 : ENNReal) * model.completionPotential total payoff state.2.1 +
        Creation.expectedCharges (model.creationImpl weight cap)
          (fun input before => (creationStep weight cap input before : ENNReal) *
            model.completionPotential total payoff before.2.1) program state := le_add_self
    _ = expectedValue ((simulateQ (model.creationImpl weight cap) program).run state)
        (fun result => (result.2.1 : ENNReal) *
          model.completionPotential total payoff result.2.2.1) := hacc.symm
    _ ≤ expectedValue ((simulateQ (model.creationImpl weight cap) program).run state)
        (fun result => (cap : ENNReal) *
          model.completionPotential total payoff result.2.2.1) := by
      unfold expectedValue
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ ((simulateQ (model.creationImpl weight cap) program).run state).support
      · apply mul_le_mul' le_rfl
        apply mul_le_mul' _ le_rfl
        exact_mod_cast model.creation_program_mass_le weight cap program state hstate result hr
      · have hp : Pr[= result | (simulateQ (model.creationImpl weight cap) program).run state] = 0 := by
          rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
          exact hr
        rw [hp, zero_mul, zero_mul]
    _ = _ := by
      rw [Creation.expectedValue_left_mul, model.creation_program_potential]
theorem creation_charge_from_empty {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (program : OracleComp spec α) (state : State) :
    Creation.expectedCharges (model.creationImpl weight cap)
      (fun input before => (creationStep weight cap input before : ENNReal) *
        model.completionPotential total payoff before.2.1) program (0, [], state) ≤
      (cap : ENNReal) * expectedValue (independentProposalWord model.base total) payoff := by
  simpa only [completionPotential_nil] using
    model.creation_charge_bound weight cap total payoff program (0, [], state) (Nat.zero_le _)
theorem completionPotential_le_unit_excess (model : ProposalModel spec State Label)
    (total : Nat) (payoff : List Label → ENNReal) (consumed : List Label) :
    model.completionPotential total payoff consumed ≤
      1 + model.completionPotential total (fun word => payoff word - 1) consumed := by
  unfold completionPotential
  calc
    _ ≤ expectedValue (completeProposalWord model.base total consumed)
        (fun word => 1 + (payoff word - 1)) :=
      expectedValue_mono _ (fun _ => le_add_tsub)
    _ = _ := by rw [expectedValue_add, expectedValue_const (by simp)]
theorem creation_charge_split {α : Type} (model : ProposalModel spec State Label)
    (weight : spec.Domain → (List Label × State) → Nat) (cap total : Nat)
    (payoff : List Label → ENNReal) (program : OracleComp spec α) (state : State) :
    Creation.expectedCharges (model.creationImpl weight cap)
      (fun input before => (creationStep weight cap input before : ENNReal) *
        model.completionPotential total payoff before.2.1) program (0, [], state) ≤
      Creation.expectedCharges (model.creationImpl weight cap)
        (fun input before => (creationStep weight cap input before : ENNReal))
        program (0, [], state) +
      (cap : ENNReal) * expectedValue (independentProposalWord model.base total)
        (fun word => payoff word - 1) := by
  calc
    _ ≤ Creation.expectedCharges (model.creationImpl weight cap)
        (fun input before => (creationStep weight cap input before : ENNReal) +
          (creationStep weight cap input before : ENNReal) *
            model.completionPotential total (fun word => payoff word - 1) before.2.1)
        program (0, [], state) := by
      apply Creation.expectedCharges_mono _ _ _ (fun _ => True)
        (fun _ _ _ _ _ => trivial) _ _ _ trivial
      intro input before _
      simpa only [mul_add, mul_one] using mul_le_mul' (a :=
        (creationStep weight cap input before : ENNReal)) le_rfl
          (model.completionPotential_le_unit_excess total payoff before.2.1)
    _ = _ + Creation.expectedCharges (model.creationImpl weight cap)
        (fun input before => (creationStep weight cap input before : ENNReal) *
          model.completionPotential total (fun word => payoff word - 1) before.2.1)
        program (0, [], state) := Creation.expectedCharges_add _ _ _ _ _
    _ ≤ _ := add_le_add le_rfl
      (model.creation_charge_from_empty weight cap total (fun word => payoff word - 1) program state)
end ProposalModel
end SigGolfCandidate.T3.BPORS.Adaptive
namespace SigGolfCandidate.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open BPORS.Adaptive
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem adaptive_creation_full_charge {α : Type} (published : T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (weight : LazyPrivate.Interaction.Domain → (MonitoredPrivate.History × State) → Nat)
    (cap : Nat) (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    Creation.expectedCharges ((proposalModel published budget hbudget).creationImpl weight cap)
      (fun input before => (ProposalModel.creationStep weight cap input before : ENNReal) *
        (proposalModel published budget hbudget).completionPotential BPORS.Numeric.proposalLength
          BPORS.History.fullPrice before.2.1) program (0, [], state) ≤
      Creation.expectedCharges ((proposalModel published budget hbudget).creationImpl weight cap)
        (fun input before => (ProposalModel.creationStep weight cap input before : ENNReal))
        program (0, [], state) + (cap : ENNReal) * (11324/100000000) := by
  apply le_trans ((proposalModel published budget hbudget).creation_charge_split
    weight cap BPORS.Numeric.proposalLength BPORS.History.fullPrice program state)
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  change expectedValue (SphincsSecurity.Concrete.independentProposalWord
    (PMF.uniformOfFintype DigestSampling.IndexBuckets) BPORS.Numeric.proposalLength)
      (fun word => BPORS.History.fullPrice word - 1) ≤ _
  rw [ProposalModel.uniform_word_expectation]
  exact BPORS.History.fullPrice_excess_bound
theorem adaptive_creation_near_charge {α : Type} (published : T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (weight : LazyPrivate.Interaction.Domain → (MonitoredPrivate.History × State) → Nat)
    (cap : Nat) (program : OracleComp LazyPrivate.Interaction α) (state : State) :
    Creation.expectedCharges ((proposalModel published budget hbudget).creationImpl weight cap)
      (fun input before => (ProposalModel.creationStep weight cap input before : ENNReal) *
        (proposalModel published budget hbudget).completionPotential BPORS.Numeric.proposalLength
          BPORS.History.fullNearPrice before.2.1) program (0, [], state) ≤
      (cap : ENNReal) * 404 := by
  apply le_trans ((proposalModel published budget hbudget).creation_charge_from_empty
    weight cap BPORS.Numeric.proposalLength BPORS.History.fullNearPrice program state)
  apply mul_le_mul' le_rfl
  change expectedValue (SphincsSecurity.Concrete.independentProposalWord
    (PMF.uniformOfFintype DigestSampling.IndexBuckets) BPORS.Numeric.proposalLength)
      BPORS.History.fullNearPrice ≤ _
  rw [ProposalModel.uniform_word_expectation]
  exact BPORS.History.fullNearPrice_bound
end SigGolfCandidate.T3.Security.QueryRecorded
end
section
namespace SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option backward.isDefEq.respectTransparency false
theorem traced_query_inactive {ι State Label : Type} {spec : OracleSpec ι}
    (model : ProposalModel spec State Label) (input : spec.Domain)
    (state : List Label × State) (hinactive : model.active input state.2 = false) :
    (model.traced input).run state =
      (fun result => (result.1, (state.1, result.2))) <$> (model.original input).run state.2 := by
  simp only [traced, proposalRecordImpl, StateT.run_mk, hinactive, Bool.false_eq_true,
    if_false, original, PMF.monad_map_eq_map, PMF.map_comp]
  rfl
end SigGolfCandidate.T3.BPORS.Adaptive.ProposalModel
namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open BPORS.Adaptive
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
def publicHandler : QueryImpl T3.Spec (OracleComp LazyPrivate.Interaction)
  | .inl input => LazyPrivate.Interaction.query (.inl input)
  | .inr _ => pure (0 : HashOutput)
def publicProgram {α : Type} (program : M α) : OracleComp LazyPrivate.Interaction α :=
  simulateQ publicHandler program
theorem publicProgram_pure {α : Type} (value : α) :
    publicProgram (pure value : M α) = pure value := by
  simp [publicProgram]
theorem publicProgram_bind {α β : Type} (program : M α) (next : α → M β) :
    publicProgram (program >>= next) =
      (publicProgram program >>= fun value => publicProgram (next value)) := by
  simp only [publicProgram, simulateQ_bind]
theorem traced_world (published : T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : SphincsSecurity.OracleWorld.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    ((QueryRecorded.proposalModel published budget hbudget).traced (.inl input)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (liftM (QueryRecorded.run (forwardWorld input) state.2) : PMF _) := by
  rw [ProposalModel.traced_query_inactive _ _ _ (by rfl), QueryRecorded.proposal_query_erasure]
  rfl
theorem publicProgram_trace {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : M α) (hp : PublicVerdict.Only program)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
      (publicProgram program)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (liftM (QueryRecorded.run program state.2) : PMF _) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [publicProgram_pure, simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure,
        liftM_pure, PMF.monad_pure_eq_pure, PMF.monad_map_eq_map, PMF.pure_map]
  | query_bind input next ih =>
      change AllQueriesSatisfy _ PublicVerdict.IsPublicHash at hp
      rw [allQueriesSatisfy_query_bind_iff] at hp
      rcases input with (sample | input) | coordinate
      · exact False.elim hp.1
      · rw [publicProgram_bind]
        simp only [publicProgram, simulateQ_spec_query, publicHandler, simulateQ_bind,
          StateT.run_bind]
        rw [traced_world, bind_map_left, QueryRecorded.run_bind, liftM_bind, map_bind]
        apply bind_congr
        intro middle
        exact ih middle.1 (hp.2 middle.1) (state.1, middle.2)
      · exact False.elim hp.1
noncomputable def rest (adversary : AdversaryP) (publicKey : Digest) (published : T3.Cache) :
    OracleComp LazyPrivate.Interaction Bool := do
  let result ← ProposalOverflow.logged (adversary publicKey published)
  publicProgram (GameWith.verdict PaddedGame.checker publicKey result)
theorem rest_trace (adversary : AdversaryP) (published : T3.Cache) (publicKey : Digest)
    (budget : Nat) (hbudget : budget ≤ 2^127) (state : QueryRecorded.State) :
    (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
      (rest adversary publicKey published)).run ([], state) =
      (do
        let interaction ← (simulateQ (QueryRecorded.proposalModel published budget hbudget).traced
          (ProposalOverflow.logged (adversary publicKey published))).run ([], state)
        let checked ← (liftM (QueryRecorded.run
          (GameWith.verdict PaddedGame.checker publicKey interaction.1) interaction.2.2) : PMF _)
        pure (checked.1, interaction.2.1, checked.2)) := by
  rw [rest, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro interaction
  rw [publicProgram_trace published budget hbudget _ (PaddedGame.verdict_public _ _)]
  rfl
theorem padded_trace_eq (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PaddedGame.tracedExperiment adversary budget hbudget =
      (do
        let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
        (simulateQ (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
          (rest adversary generated.1.1 generated.1.2)).run ([], generated.2)) := by
  unfold PaddedGame.tracedExperiment GameWith.Recorded.tracedExperiment
  apply bind_congr
  intro generated
  exact (rest_trace adversary generated.1.2 generated.1.1 budget hbudget generated.2).symm
abbrev Weight := T3.Cache → LazyPrivate.Interaction.Domain →
  (MonitoredPrivate.History × QueryRecorded.State) → Nat
noncomputable def experiment (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF (Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State))) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ ((QueryRecorded.proposalModel generated.1.2 budget hbudget).creationImpl
    (weight generated.1.2) cap) (rest adversary generated.1.1 generated.1.2)).run
      (0, [], generated.2)
theorem experiment_project (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    Prod.map id Prod.snd <$> experiment weight cap adversary budget hbudget =
      PaddedGame.tracedExperiment adversary budget hbudget := by
  rw [experiment, map_bind, padded_trace_eq]
  apply bind_congr
  intro generated
  exact (QueryRecorded.proposalModel generated.1.2 budget hbudget).creation_program_project
    (weight generated.1.2) cap _ (0, [], generated.2)
theorem experiment_mass_le (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment weight cap adversary budget hbudget).support) :
    result.2.1 ≤ cap := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  exact (QueryRecorded.proposalModel generated.1.2 budget hbudget).creation_program_mass_le
    (weight generated.1.2) cap _ (0, [], generated.2) (Nat.zero_le _) result hr
noncomputable def expectedCharge (weight : Weight) (cap : Nat)
    (payoff : MonitoredPrivate.History → ENNReal)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
    (fun generated =>
      Creation.expectedCharges
        ((QueryRecorded.proposalModel generated.1.2 budget hbudget).creationImpl
          (weight generated.1.2) cap)
        (fun input before =>
          (ProposalModel.creationStep (weight generated.1.2) cap input before : ENNReal) *
          (QueryRecorded.proposalModel generated.1.2 budget hbudget).completionPotential
            BPORS.Numeric.proposalLength payoff before.2.1)
        (rest adversary generated.1.1 generated.1.2) (0, [], generated.2))
theorem full_charge_le_mass_excess (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedCharge weight cap BPORS.History.fullPrice adversary budget hbudget ≤
      expectedValue (experiment weight cap adversary budget hbudget)
        (fun result => (result.2.1 : ENNReal)) + (cap : ENNReal) * (11324/100000000) := by
  unfold expectedCharge
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
        (fun generated =>
          Creation.expectedCharges
            ((QueryRecorded.proposalModel generated.1.2 budget hbudget).creationImpl
              (weight generated.1.2) cap)
            (fun input before =>
              (ProposalModel.creationStep (weight generated.1.2) cap input before : ENNReal))
            (rest adversary generated.1.1 generated.1.2) (0, [], generated.2) +
          (cap : ENNReal) * (11324/100000000)) := by
      apply expectedValue_mono
      intro generated
      exact QueryRecorded.adaptive_creation_full_charge generated.1.2 budget hbudget
        (weight generated.1.2) cap _ generated.2
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), experiment, expectedValue_bind]
      congr 1
      congr 1
      funext generated
      exact ((QueryRecorded.proposalModel generated.1.2 budget hbudget).creation_program_mass
        (weight generated.1.2) cap _ ([], generated.2)).symm
theorem near_charge_le (weight : Weight) (cap : Nat)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedCharge weight cap BPORS.History.fullNearPrice adversary budget hbudget ≤
      (cap : ENNReal) * 404 := by
  unfold expectedCharge
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
        (fun _ => (cap : ENNReal) * 404) := by
      apply expectedValue_mono
      intro generated
      exact QueryRecorded.adaptive_creation_near_charge generated.1.2 budget hbudget
        (weight generated.1.2) cap _ generated.2
    _ = _ := expectedValue_const (by simp) _
end SigGolfCandidate.T3.Security.CreationGame
end
section
namespace SigGolfCandidate.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open BPORS.History
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def journalNearEvent (journal : Journal) (index : Fin (2^31))
    (missing : Fin 7) (omitted : Fin 3) (output : HashOutput) : Prop :=
  (SigGolfResearch.Gate6.digestRecord output).2.2.1=0 ∧
    BPORS.NearCovered (exposedLeaves (journalOutputs journal) index) missing omitted
      (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1
theorem journal_near_coverage_bound (published : T3.Cache) (history : History)
    (state : State) (journal : Journal) (hj : JournalOK published history state journal)
    (index : Fin (2^31)) (missing : Fin 7) (omitted : Fin 3) :
    Pr[journalNearEvent journal index missing omitted |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      nearWordEnvelope missing (atIndex index history) :=
  BPORS.nearCovered_le_wordEnvelope (atIndex index history) _
    (journal_exposure_card published history state journal hj index) missing omitted
theorem journal_any_missing_coverage_bound (published : T3.Cache) (history : History)
    (state : State) (journal : Journal) (hj : JournalOK published history state journal)
    (index : Fin (2^31)) :
    Pr[fun draw => ∃ missing : Fin 7 × Fin 3,
      journalNearEvent journal index missing.1 missing.2 draw |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      3 * ∑ missing : Fin 7, nearWordEnvelope missing (atIndex index history) := by
  have hu := probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin 7 × Fin 3))
    ($ᵗ HashOutput : ProbComp HashOutput)
    (fun missing => journalNearEvent journal index missing.1 missing.2)
  simp only [Finset.mem_univ, true_and] at hu
  apply hu.trans
  calc
    _ ≤ ∑ missing : Fin 7 × Fin 3, nearWordEnvelope missing.1 (atIndex index history) := by
      apply Finset.sum_le_sum
      intro missing _
      exact journal_near_coverage_bound published history state journal hj index missing.1 missing.2
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]
theorem journal_average_near_coverage_bound (published : T3.Cache) (history : History)
    (state : State) (journal : Journal) (hj : JournalOK published history state journal) :
    expectedValue ($ᵗ (Fin (2^31)) : ProbComp _)
      (fun index => Pr[fun draw => ∃ missing : Fin 7 × Fin 3,
        journalNearEvent journal index missing.1 missing.2 draw |
        ($ᵗ HashOutput : ProbComp HashOutput)]) ≤
      fullNearPrice history / (2 : ENNReal)^128 := by
  apply le_trans (expectedValue_mono _ (fun index =>
    journal_any_missing_coverage_bound published history state journal hj index))
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage fullNearPrice
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  have hscale : (2 : ENNReal)^97 * ((2 : ENNReal)^128)⁻¹ = ((2 : ENNReal)^31)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
  simp only [div_eq_mul_inv]
  rw [← hscale]
  exact le_of_eq (by ring)
end SigGolfCandidate.T3.Security.MonitoredPrivate
end
section
namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open BPORS.Adaptive
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def classWeight (cls : HashInput → Prop) (budget : Nat) :
    LazyPrivate.Interaction.Domain → (MonitoredPrivate.History × QueryRecorded.State) → Nat
  | .inl (.inr input), state =>
      if state.2.base.source.1 < budget ∧ cls input ∧ state.2.base.source.2.2 input = none
        then 1 else 0
  | _, _ => 0
theorem classWeight_le_one (cls : HashInput → Prop) (budget : Nat)
    (input : LazyPrivate.Interaction.Domain) (state : MonitoredPrivate.History × QueryRecorded.State) :
    classWeight cls budget input state ≤ 1 := by
  rcases input with (sample | input) | request
  · exact Nat.zero_le _
  · change (if state.2.base.source.1 < budget ∧ cls input ∧
      state.2.base.source.2.2 input = none then 1 else 0) ≤ 1
    split_ifs <;> omega
  · exact Nat.zero_le _
theorem class_creationStep_eq (cls : HashInput → Prop) (budget : Nat)
    (input : LazyPrivate.Interaction.Domain)
    (state : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : state.1 ≤ state.2.2.base.source.1) :
    ProposalModel.creationStep (classWeight cls budget) budget input state =
      classWeight cls budget input state.2 := by
  unfold ProposalModel.creationStep
  apply Nat.min_eq_left
  rcases input with (sample | input) | request
  · exact Nat.zero_le _
  · change (if state.2.2.base.source.1 < budget ∧ cls input ∧
      state.2.2.base.source.2.2 input = none then 1 else 0) ≤ budget - state.1
    split_ifs with h
    · omega
    · exact Nat.zero_le _
  · exact Nat.zero_le _
theorem traced_query_source_support (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : LazyPrivate.Interaction.Domain)
    (before : MonitoredPrivate.History × QueryRecorded.State)
    (result : LazyPrivate.Interaction.Range input × (MonitoredPrivate.History × QueryRecorded.State))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).traced input).run before).support) :
    (result.1, result.2.2) ∈ support
      (QueryRecorded.run (MonitoredPrivate.interactionSource published input) before.2) := by
  rw [← MonitoredPrivate.pmf_support,
    ← QueryRecorded.proposal_query_erasure published budget hbudget input before.2,
    ← (QueryRecorded.proposalModel published budget hbudget).traced_query_erasure input before,
    PMF.monad_map_eq_map, PMF.mem_support_map_iff]
  exact ⟨result, hr, rfl⟩
theorem recorded_count_monotone {α : Type} (program : M α)
    (before : QueryRecorded.State) (result : α × QueryRecorded.State)
    (hr : result ∈ support (QueryRecorded.run program before)) :
    before.base.source.1 ≤ result.2.base.source.1 :=
  MonitoredPrivate.run_count_monotone program before.base (result.1, result.2.base)
    (QueryRecorded.run_support program before result hr)
theorem recorded_world_hash_count (input : HashInput) (before : QueryRecorded.State)
    (result : HashOutput × QueryRecorded.State)
    (hr : result ∈ support (QueryRecorded.run (forwardWorld (.inr input)) before)) :
    result.2.base.source.1 = before.base.source.1 + 1 := by
  change result ∈ support (QueryRecorded.run (liftM (T3.Spec.query (.inl (.inr input)))) before) at hr
  rw [QueryRecorded.run_query_explicit, support_map] at hr
  obtain ⟨middle, _, rfl⟩ := hr
  rfl
theorem class_creation_query_cost (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (input : LazyPrivate.Interaction.Domain)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : before.1 ≤ before.2.2.base.source.1)
    (result : LazyPrivate.Interaction.Range input ×
      (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget input).run before).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  rw [ProposalModel.creationImpl, StateT.run_mk, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at hr
  obtain ⟨middle, hm, rfl⟩ := hr
  have hs := traced_query_source_support published budget hbudget input before.2 middle hm
  have hmon := recorded_count_monotone _ before.2.2 (middle.1, middle.2.2) hs
  change before.1 + ProposalModel.creationStep (classWeight cls budget) budget input before ≤ _
  rw [class_creationStep_eq cls budget input before hcost]
  rcases input with (sample | input) | request
  · simpa only [classWeight, Nat.add_zero] using hcost.trans hmon
  · have hc := recorded_world_hash_count input before.2.2 (middle.1, middle.2.2) hs
    rw [hc]
    exact Nat.add_le_add hcost (classWeight_le_one cls budget (.inl (.inr input)) before.2)
  · simpa only [classWeight, Nat.add_zero] using hcost.trans hmon
theorem class_creation_program_cost {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hcost : before.1 ≤ before.2.2.base.source.1)
    (result : α × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run before).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hcost
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (class_creation_query_cost published budget hbudget cls input before hcost middle hm) hr
theorem class_experiment_cost (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  exact class_creation_program_cost generated.1.2 budget hbudget cls _
    (0, [], generated.2) (Nat.zero_le _) result hr
theorem class_program_mass_eq {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : MonitoredPrivate.History × QueryRecorded.State) :
    expectedValue ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run (0, before))
      (fun result => (result.2.1 : ENNReal)) =
      Creation.expectedCharges (QueryRecorded.proposalModel published budget hbudget).traced
        (fun input state => (classWeight cls budget input state : ENNReal)) program before := by
  let model := QueryRecorded.proposalModel published budget hbudget
  apply le_antisymm
  · exact model.creation_mass_le_source_charges (classWeight cls budget) budget program before
  · have hp := Creation.expectedCharges_project (model.creationImpl (classWeight cls budget) budget)
      model.traced Prod.snd (model.creation_query_project (classWeight cls budget) budget)
      (fun input state => (classWeight cls budget input state : ENNReal)) program (0, before)
    calc
      _ = Creation.expectedCharges (model.creationImpl (classWeight cls budget) budget)
          (fun input state => (classWeight cls budget input state.2 : ENNReal))
          program (0, before) := hp.symm
      _ ≤ Creation.expectedCharges (model.creationImpl (classWeight cls budget) budget)
          (fun input state => (ProposalModel.creationStep (classWeight cls budget) budget input state : ENNReal))
          program (0, before) := by
        apply Creation.expectedCharges_mono _ _ _
          (fun state => state.1 ≤ state.2.2.base.source.1)
          (class_creation_query_cost published budget hbudget cls) _ _ _ (Nat.zero_le _)
        intro input state hcost
        exact le_of_eq (congrArg (fun value : Nat => (value : ENNReal))
          (class_creationStep_eq cls budget input state hcost)).symm
      _ = _ := (model.creation_program_mass (classWeight cls budget) budget program before).symm
noncomputable def expectedBirths (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
    (fun generated =>
      Creation.expectedCharges (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
        (fun input state => (classWeight cls budget input state : ENNReal))
        (rest adversary generated.1.1 generated.1.2) ([], generated.2))
theorem expectedBirths_eq_mass (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget =
      expectedValue (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget)
        (fun result => (result.2.1 : ENNReal)) := by
  rw [expectedBirths, experiment, expectedValue_bind]
  congr 1
  funext generated
  exact (class_program_mass_eq generated.1.2 budget hbudget cls _ ([], generated.2)).symm
theorem full_charge_le_births_excess (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedCharge (fun _ => classWeight cls budget) budget BPORS.History.fullPrice
      adversary budget hbudget ≤
      expectedBirths cls adversary budget hbudget + (budget : ENNReal) * (11324/100000000) := by
  rw [expectedBirths_eq_mass]
  exact full_charge_le_mass_excess (fun _ => classWeight cls budget) budget adversary budget hbudget
end SigGolfCandidate.T3.Security.CreationGame
end
section
namespace SigGolfCandidate.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open BPORS.Adaptive
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def publicClass (cls : HashInput → Prop) : T3.Spec.Domain → Prop
  | .inl (.inr input) => cls input
  | _ => False
noncomputable def prefixCount (cls : T3.Spec.Domain → Prop) :
    Nat → List FirstHit.QueryEvent → Nat
  | _, [] => 0
  | budget, event :: rest =>
      if FullGame.queryCharge event.input ≤ budget then
        (if cls event.input then FullGame.queryCharge event.input else 0) +
          prefixCount cls (budget - FullGame.queryCharge event.input) rest
      else 0
theorem prefixCount_le (cls : T3.Spec.Domain → Prop) (budget : Nat)
    (events : List FirstHit.QueryEvent) : prefixCount cls budget events ≤ budget := by
  induction events generalizing budget with
  | nil => exact Nat.zero_le _
  | cons event rest ih =>
      simp only [prefixCount]
      split_ifs with hfit hclass
      · have h := ih (budget - FullGame.queryCharge event.input)
        omega
      · have h := ih (budget - FullGame.queryCharge event.input)
        omega
      · exact Nat.zero_le _
theorem prefixCount_append_mono (cls : T3.Spec.Domain → Prop) (budget : Nat)
    (first last : List FirstHit.QueryEvent) :
    prefixCount cls budget first ≤ prefixCount cls budget (first ++ last) := by
  induction first generalizing budget with
  | nil => exact Nat.zero_le _
  | cons event rest ih =>
      simp only [List.cons_append, prefixCount]
      split_ifs
      · exact Nat.add_le_add_left (ih _) _
      · exact Nat.add_le_add_left (ih _) _
      · exact le_rfl
theorem prefixCount_prefix_mono (cls : T3.Spec.Domain → Prop) (budget : Nat)
    {first last : List FirstHit.QueryEvent} (hprefix : first.IsPrefix last) :
    prefixCount cls budget first ≤ prefixCount cls budget last := by
  obtain ⟨suffix, rfl⟩ := hprefix
  exact prefixCount_append_mono cls budget first suffix
theorem prefixCount_append_singleton (cls : T3.Spec.Domain → Prop)
    (budget : Nat) (events : List FirstHit.QueryEvent) (event : FirstHit.QueryEvent)
    (hfits : (events.map (fun item => FullGame.queryCharge item.input)).sum +
      FullGame.queryCharge event.input ≤ budget) :
    prefixCount cls budget (events ++ [event]) = prefixCount cls budget events +
      (if cls event.input then FullGame.queryCharge event.input else 0) := by
  induction events generalizing budget with
  | nil =>
      have hf : FullGame.queryCharge event.input ≤ budget := by simpa using hfits
      simp only [List.nil_append, prefixCount, if_pos hf, Nat.add_zero, Nat.zero_add]
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons] at hfits
      have hf : FullGame.queryCharge first.input ≤ budget := by omega
      have ht : (rest.map (fun item => FullGame.queryCharge item.input)).sum +
          FullGame.queryCharge event.input ≤ budget - FullGame.queryCharge first.input := by omega
      simp only [List.cons_append, prefixCount, if_pos hf]
      rw [ih _ ht, Nat.add_assoc]
theorem prefixCount_disjoint (first second : T3.Spec.Domain → Prop)
    (hdisjoint : ∀ input, ¬ (first input ∧ second input)) (budget : Nat)
    (events : List FirstHit.QueryEvent) :
    prefixCount (fun input => first input ∨ second input) budget events =
      prefixCount first budget events + prefixCount second budget events := by
  induction events generalizing budget with
  | nil => rfl
  | cons event rest ih =>
      simp only [prefixCount]
      by_cases hfit : FullGame.queryCharge event.input ≤ budget
      · simp only [if_pos hfit, ih]
        by_cases hf : first event.input <;> by_cases hs : second event.input
        · exact False.elim (hdisjoint event.input ⟨hf, hs⟩)
        · simp only [hf, hs, true_or, if_true, if_false, Nat.zero_add]
          omega
        · simp only [hf, hs, or_true, if_true, if_false, Nat.zero_add]
          omega
        · simp [hf, hs]
      · simp [hfit]
theorem class_source_count_step (published : T3.Cache) (budget : Nat)
    (cls : HashInput → Prop) (input : LazyPrivate.Interaction.Domain)
    (before : MonitoredPrivate.History × QueryRecorded.State)
    (hcoherent : QueryRecorded.CostCoherent before.2)
    (result : LazyPrivate.Interaction.Range input × QueryRecorded.State)
    (hr : result ∈ support
      (QueryRecorded.run (MonitoredPrivate.interactionSource published input) before.2)) :
    prefixCount (publicClass cls) budget before.2.events + classWeight cls budget input before ≤
      prefixCount (publicClass cls) budget result.2.events := by
  have hmono := prefixCount_prefix_mono (publicClass cls) budget
    (QueryRecorded.run_events_extend _ before.2 result hr)
  rcases input with (sample | input) | request
  · simpa only [classWeight, Nat.add_zero] using hmono
  · by_cases hb : before.2.base.source.1 < budget ∧ cls input ∧
        before.2.base.source.2.2 input = none
    · have hweight : classWeight cls budget (.inl (.inr input)) before = 1 := by
        change (if _ then 1 else 0) = 1
        exact if_pos hb
      rw [hweight]
      change result ∈ support
        (QueryRecorded.run (liftM (T3.Spec.query (.inl (.inr input)))) before.2) at hr
      rw [QueryRecorded.run_query_explicit, support_map] at hr
      obtain ⟨middle, _, rfl⟩ := hr
      change _ ≤ prefixCount (publicClass cls) budget
        (before.2.events ++ [⟨before.2.base.source.2, .inl (.inr input), middle.1⟩])
      rw [prefixCount_append_singleton]
      · simp only [publicClass, hb.2.1, if_true]
        rfl
      · change (before.2.events.map (fun event => FullGame.queryCharge event.input)).sum + 1 ≤ budget
        rw [← hcoherent]
        omega
    · have hweight : classWeight cls budget (.inl (.inr input)) before = 0 := by
        change (if _ then 1 else 0) = 0
        exact if_neg hb
      simpa only [hweight, Nat.add_zero] using hmono
  · simpa only [classWeight, Nat.add_zero] using hmono
def CountInvariant (cls : HashInput → Prop) (budget : Nat)
    (state : Nat × (MonitoredPrivate.History × QueryRecorded.State)) : Prop :=
  QueryRecorded.CostCoherent state.2.2 ∧
    state.1 ≤ prefixCount (publicClass cls) budget state.2.2.events
theorem class_creation_query_count (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (input : LazyPrivate.Interaction.Domain)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hinv : CountInvariant cls budget before)
    (result : LazyPrivate.Interaction.Range input ×
      (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget input).run before).support) :
    CountInvariant cls budget result.2 := by
  rw [ProposalModel.creationImpl, StateT.run_mk, PMF.monad_map_eq_map,
    PMF.mem_support_map_iff] at hr
  obtain ⟨middle, hm, rfl⟩ := hr
  have hs := traced_query_source_support published budget hbudget input before.2 middle hm
  refine ⟨QueryRecorded.run_cost_coherent _ before.2.2 hinv.1 (middle.1, middle.2.2) hs, ?_⟩
  exact (Nat.add_le_add hinv.2 (Nat.min_le_left _ _)).trans
    (class_source_count_step published budget cls input before.2 hinv.1 (middle.1, middle.2.2) hs)
theorem class_creation_program_count {α : Type} (published : T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (cls : HashInput → Prop)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : Nat × (MonitoredPrivate.History × QueryRecorded.State))
    (hinv : CountInvariant cls budget before)
    (result : α × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ ((simulateQ ((QueryRecorded.proposalModel published budget hbudget).creationImpl
      (classWeight cls budget) budget) program).run before).support) :
    CountInvariant cls budget result.2 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      exact hinv
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (class_creation_query_count published budget hbudget cls input before hinv middle hm) hr
theorem class_experiment_count (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support) :
    result.2.1 ≤ prefixCount (publicClass cls) budget result.2.2.2.events := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, hg, hr⟩ := hr
  rw [MonitoredPrivate.pmf_support] at hg
  have hc := QueryRecorded.run_cost_coherent keygen QueryRecorded.initial
    QueryRecorded.initial_cost generated hg
  exact (class_creation_program_count generated.1.2 budget hbudget cls _
    (0, [], generated.2) ⟨hc, Nat.zero_le _⟩ result hr).2
noncomputable def expectedClassCount (cls : T3.Spec.Domain → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (PaddedGame.tracedExperiment adversary budget hbudget)
    (fun result => (prefixCount cls budget result.2.2.events : ENNReal))
theorem expectedBirths_le_classCount (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget ≤
      expectedClassCount (publicClass cls) adversary budget hbudget := by
  rw [expectedBirths_eq_mass, expectedClassCount,
    ← experiment_project (fun _ => classWeight cls budget) budget adversary budget hbudget,
    expectedValue_map]
  unfold expectedValue
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support
  · apply mul_le_mul' le_rfl
    change (result.2.1 : ENNReal) ≤
      (prefixCount (publicClass cls) budget result.2.2.2.events : ENNReal)
    exact_mod_cast class_experiment_count cls adversary budget hbudget result hr
  · have hp : Pr[= result | experiment (fun _ => classWeight cls budget) budget adversary budget hbudget] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]
theorem full_charge_le_class_excess (cls : HashInput → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedCharge (fun _ => classWeight cls budget) budget BPORS.History.fullPrice
      adversary budget hbudget ≤
      expectedClassCount (publicClass cls) adversary budget hbudget +
        (budget : ENNReal) * (11324/100000000) :=
  (full_charge_le_births_excess cls adversary budget hbudget).trans
    (add_le_add (expectedBirths_le_classCount cls adversary budget hbudget) le_rfl)
theorem expectedClassCount_le (cls : T3.Spec.Domain → Prop)
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount cls adversary budget hbudget ≤ (budget : ENNReal) := by
  unfold expectedClassCount
  calc
    _ ≤ expectedValue (PaddedGame.tracedExperiment adversary budget hbudget)
        (fun _ => (budget : ENNReal)) := by
      apply expectedValue_mono
      intro result
      exact_mod_cast prefixCount_le cls budget result.2.2.events
    _ = _ := expectedValue_const (by simp) _
theorem expectedClassCount_disjoint (first second : T3.Spec.Domain → Prop)
    (hdisjoint : ∀ input, ¬ (first input ∧ second input))
    (adversary : SigGolfCandidate.T3M.Final.AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount (fun input => first input ∨ second input) adversary budget hbudget =
      expectedClassCount first adversary budget hbudget +
        expectedClassCount second adversary budget hbudget := by
  unfold expectedClassCount
  simp_rw [prefixCount_disjoint first second hdisjoint, Nat.cast_add]
  exact expectedValue_add _ _ _
end SigGolfCandidate.T3.Security.CreationGame
end
