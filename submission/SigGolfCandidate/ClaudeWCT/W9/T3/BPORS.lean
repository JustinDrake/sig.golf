import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeGame
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SecurityP
import SigGolfCandidate.T3.BPORS

set_option linter.unusedSimpArgs false
section
namespace ClaudeWCT.W9.T3.Security.CountedPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
theorem authenticatedSign_avoids (protectedMessage : Message) (published : SigGolfCandidate.T3.Cache)
    (request : Request) (hrequest : request.cache≠published ∨ request.message≠protectedMessage) :
    NonceFreshness.Avoids protectedMessage (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply NonceFreshness.avoids_bind protectedMessage
    (NonceFreshness.avoids_privateMac protectedMessage request.cache.region)
  intro tag
  split_ifs with hc
  · exact Signer.signPayload_avoids protectedMessage request.cache request.message
      (hrequest.resolve_left (not_not.mpr hc))
  · exact NonceFreshness.avoids_pure protectedMessage none
theorem authenticatedSign_hashOnly (published : SigGolfCandidate.T3.Cache) (request : Request) :
    SigGolfCandidate.T3.Security.SourceReplay.HashOnly (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  apply SourceQueries.bind_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SigGolfCandidate.T3.Security.SourceReplay.IsHash (fun _ => trivial)
      request.cache.region)
  intro tag
  split_ifs
  · exact Signer.signPayload_hashOnly request.cache request.message
  · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.W9.T3.Security.CountedPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Interaction := LazyPrivate.Interaction
noncomputable def interactionSource (published : SigGolfCandidate.T3.Cache) : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => FullGame.authenticatedSign published request
def Outcome (input : Interaction.Domain) : Type :=
  Interaction.Range input × SigGolfCandidate.T3.Security.MonitoredPrivate.State
noncomputable def interactionRecord (published : SigGolfCandidate.T3.Cache) (input : Interaction.Domain)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) : PMF (Outcome input) :=
  liftM (MonitoredPrivate.run (interactionSource published input) state)
def response (input : Interaction.Domain) (result : Outcome input) : Interaction.Range input := result.1
def advance (input : Interaction.Domain) (_ : SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : Outcome input) : SigGolfCandidate.T3.Security.MonitoredPrivate.State := result.2
def label (input : Interaction.Domain) (_ : Outcome input) : DigestSampling.IndexBuckets := default
def active : Interaction.Domain → SigGolfCandidate.T3.Security.MonitoredPrivate.State → Bool
  | .inl _, _ => false
  | .inr _, _ => true
noncomputable def proposalModel (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (_hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction SigGolfCandidate.T3.Security.MonitoredPrivate.State
      DigestSampling.IndexBuckets where
  Outcome := Outcome
  record := interactionRecord published
  response := response
  advance := advance
  label := label
  active := active
  base := PMF.pure default
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state _ point
    have hconst : (interactionRecord published input state).map (label input) = PMF.pure default :=
      PMF.map_const _ _
    rw [hconst]
    exact mul_le_of_le_one_left (by simp) ProposalOverflow.acceptance_le_one
theorem proposal_query_erasure (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : Interaction.Domain)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (MonitoredPrivate.run (interactionSource published input) state) :
        PMF (Interaction.Range input × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  change id <$> (liftM (MonitoredPrivate.run (interactionSource published input) state) : PMF _)=_
  rw [id_map]
theorem proposal_execution_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (MonitoredPrivate.run (simulateQ (interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [MonitoredPrivate.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,MonitoredPrivate.run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (MonitoredPrivate.run (simulateQ (interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.MonitoredPrivate.State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
theorem logged_source {α : Type} (published : SigGolfCandidate.T3.Cache) (program : OracleComp Interaction α) :
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
end ClaudeWCT.W9.T3.Security.MonitoredPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.MonitoredPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem signing_trace_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction Result) (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.2.2.1 ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced program).run
        ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 :=
  ProposalOverflow.full_trace_overflow_bound (proposalModel published budget hbudget) rfl program state
theorem signing_count_le_fragment (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (input : LazyPrivate.Interaction.Domain)
    (state : List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (result : LazyPrivate.Interaction.Range input ×
      (List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State)))
    (hr : result ∈ (((ProposalOverflow.counted (proposalModel published budget hbudget)).traced input).run
      state).support) :
    result.2.2.1 ≤ state.2.1 + (ProposalOverflow.logFragment input result.1).length := by
  rw [ProposalOverflow.counted_query_count _ input state result hr]
  cases input with
  | inl input => simp [proposalModel, active, ProposalOverflow.logFragment]
  | inr request => simp only [ProposalOverflow.logFragment, List.length_singleton]; split <;> omega
theorem signing_count_le_log {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (result : (Result × QueryLog Requests) ×
      (List DigestSampling.IndexBuckets × (Nat × SigGolfCandidate.T3.Security.MonitoredPrivate.State)))
    (hr : result ∈ ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
      (ProposalOverflow.logged program)).run state).support) :
    result.2.2.1 ≤ state.2.1 + result.1.2.length := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [ProposalOverflow.logged_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      rw [ProposalOverflow.logged_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
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
theorem signing_log_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
        (ProposalOverflow.logged program)).run ([],0,state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  apply le_trans ?_ (signing_trace_overflow published budget hbudget (ProposalOverflow.logged program) state)
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
      (ProposalOverflow.logged program)).run ([],0,state)).support
  · by_cases hb : result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length
    · have hcount := signing_count_le_log published budget hbudget program ([],0,state) result hr
      have hc : result.2.2.1 ≤ result.1.2.length := by simpa using hcount
      simp only [hb, if_true, show result.2.2.1 ≤ 2^32 ∧
        BPORS.Numeric.proposalLength < result.2.1.length from ⟨hc.trans hb.1,hb.2⟩, le_refl]
    · simp only [hb, if_false, zero_le]
  · have hz : ((simulateQ (ProposalOverflow.counted (proposalModel published budget hbudget)).traced
        (ProposalOverflow.logged program)).run ([],0,state)) result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, le_refl]
theorem source_proposal_overflow {Result : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction Result)
    (state : SigGolfCandidate.T3.Security.MonitoredPrivate.State) :
    Pr[fun result => result.1.2.length ≤ 2^32 ∧ BPORS.Numeric.proposalLength < result.2.1.length |
      (simulateQ (proposalModel published budget hbudget).traced (ProposalOverflow.logged program)).run
        ([],state)] ≤ (2 : ENNReal)⁻¹ ^ 700 := by
  rw [← ProposalOverflow.counted_trace_erasure (proposalModel published budget hbudget)
    (ProposalOverflow.logged program) ([],0,state), probEvent_map]
  exact signing_log_overflow published budget hbudget program state
theorem traced_source_support {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (program : OracleComp Interaction α)
    (before : SigGolfCandidate.T3.Security.MonitoredPrivate.History × SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : α × (SigGolfCandidate.T3.Security.MonitoredPrivate.History ×
      SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (hr : result ∈ ((simulateQ (proposalModel published budget hbudget).traced program).run before).support) :
    (result.1,result.2.2) ∈
      support (MonitoredPrivate.run (simulateQ (interactionSource published) program) before.2) := by
  rw [← MonitoredPrivate.pmf_support,← proposal_trace_erasure published budget hbudget program before.1 before.2]
  rw [PMF.monad_map_eq_map,PMF.mem_support_map_iff]
  exact ⟨result,hr,rfl⟩
theorem traced_query_source_support (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget≤2^127) (input : Interaction.Domain)
    (before : SigGolfCandidate.T3.Security.MonitoredPrivate.History × SigGolfCandidate.T3.Security.MonitoredPrivate.State)
    (result : Interaction.Range input × (SigGolfCandidate.T3.Security.MonitoredPrivate.History ×
      SigGolfCandidate.T3.Security.MonitoredPrivate.State))
    (hr : result ∈ (((proposalModel published budget hbudget).traced input).run before).support) :
    (result.1,result.2.2) ∈ support (MonitoredPrivate.run (interactionSource published input) before.2) := by
  simpa only [simulateQ_spec_query] using
    traced_source_support published budget hbudget (liftM (Interaction.query input)) before result
      (by simpa only [simulateQ_spec_query] using hr)
end ClaudeWCT.W9.T3.Security.MonitoredPrivate
end
section
namespace ClaudeWCT.W9.T3.Security.QueryRecorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def Outcome (input : LazyPrivate.Interaction.Domain) : Type :=
  LazyPrivate.Interaction.Range input × SigGolfCandidate.T3.Security.QueryRecorded.State
def outcome (input : LazyPrivate.Interaction.Domain) (result : Outcome input) :
    MonitoredPrivate.Outcome input := (result.1, result.2.base)
noncomputable def interactionRecord (published : SigGolfCandidate.T3.Cache)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    PMF (Outcome input) :=
  liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state)
def advance (input : LazyPrivate.Interaction.Domain) (_ : SigGolfCandidate.T3.Security.QueryRecorded.State)
    (result : Outcome input) : SigGolfCandidate.T3.Security.QueryRecorded.State := result.2
theorem interactionRecord_project (published : SigGolfCandidate.T3.Cache)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (interactionRecord published input state).map (outcome input)=
      MonitoredPrivate.interactionRecord published input state.base := by
  rw [← PMF.monad_map_eq_map,interactionRecord,← liftM_map]
  change (liftM (Prod.map id SigGolfCandidate.T3.Security.QueryRecorded.State.base <$>
    QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) : PMF _)=_
  rw [QueryRecorded.run_erasure]
  rfl
noncomputable def refinement (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel.Refinement (MonitoredPrivate.proposalModel published budget hbudget)
      SigGolfCandidate.T3.Security.QueryRecorded.State where
  project := SigGolfCandidate.T3.Security.QueryRecorded.State.base
  Outcome := Outcome
  outcome := outcome
  record := interactionRecord published
  advance := advance
  record_project := interactionRecord_project published
  advance_project := by intro input state result; rfl
noncomputable def proposalModel (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127) :=
  (refinement published budget hbudget).model'
theorem proposal_trace_project {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    Prod.map id (Prod.map id SigGolfCandidate.T3.Security.QueryRecorded.State.base) <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
        (simulateQ (MonitoredPrivate.proposalModel published budget hbudget).traced program).run
          (history,state.base) :=
  (refinement published budget hbudget).traced_project program (history,state)
theorem proposal_query_erasure (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : LazyPrivate.Interaction.Domain) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (((proposalModel published budget hbudget).original input).run state)=
      (liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) :
        PMF (LazyPrivate.Interaction.Range input × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  change id <$> (liftM (QueryRecorded.run (MonitoredPrivate.interactionSource published input) state) : PMF _)=_
  rw [id_map]
theorem proposal_execution_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    (simulateQ (proposalModel published budget hbudget).original program).run state=
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [QueryRecorded.run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,QueryRecorded.run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem proposal_trace_erasure {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (hbudget : budget ≤ 2^127) (program : OracleComp LazyPrivate.Interaction α)
    (history : List DigestSampling.IndexBuckets) (state : SigGolfCandidate.T3.Security.QueryRecorded.State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel published budget hbudget).traced program).run (history,state)=
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) state) :
        PMF (α × SigGolfCandidate.T3.Security.QueryRecorded.State)) := by
  rw [(proposalModel published budget hbudget).traced_erasure,proposal_execution_erasure]
end ClaudeWCT.W9.T3.Security.QueryRecorded
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (OracleWorld romImpl sampleMasterSeed)
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.FullGame
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
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
  Digest → SigGolfCandidate.T3.Cache → OracleComp LazyPrivate.Interaction (Option Forgery)
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
  let result ← FullGame.loggedWith (fun request => sign request.cache request.message)
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
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
noncomputable def idealRest (checker : Checker Forgery) (other : OtherTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) : ProbComp (Bool × CountState) :=
  RequestHop.run (worldHandler other) (MacGame.idealSigner (baseHandler other) published)
    (adversary publicKey published) state >>= checkContinuation checker other publicKey
theorem logged_source_run (other : OtherTable) (mac : MacTable)
    (program : OracleComp LazyPrivate.Interaction (Option Forgery)) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (FullGame.loggedWith (fun request => sign request.cache request.message) program)).run state=
      RequestHop.run (worldHandler other) (MacGame.realSigner (baseHandler other) mac) program state := by
  rw [FullGame.loggedWith_interpretation]
  change RequestHop.run (worldHandler other)
    (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (sign request.cache request.message)) program state=_
  exact congrArg (fun signer => RequestHop.run (worldHandler other) signer program state)
    (funext fun request => MacGame.source_signer_eq (baseHandler other) mac request)
theorem source_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (fun request => sign request.cache request.message) (adversary publicKey published)
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
  let result ← FullGame.loggedWith (FullGame.authenticatedSign generated.2) (adversary generated.1 generated.2)
  verdict checker generated.1 result
theorem ideal_rest_run (checker : Checker Forgery) (other : OtherTable) (mac : MacTable) (adversary : AdversaryFor Forgery)
    (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) (state : CountState) :
    (simulateQ (MacGame.sourceHandler (baseHandler other) mac) (do
      let result ← FullGame.loggedWith (FullGame.authenticatedSign published) (adversary publicKey published)
      verdict checker publicKey result)).run state=idealRest checker other adversary publicKey published state := by
  rw [simulateQ_bind,StateT.run_bind,FullGame.loggedWith_interpretation]
  have hs : (fun request => simulateQ (MacGame.sourceHandler (baseHandler other) mac)
      (FullGame.authenticatedSign published request))=MacGame.idealSigner (baseHandler other) published :=
    funext fun request => FullGame.authenticatedSign_interpretation other mac published request
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
end ClaudeWCT.W9.T3.Security.GameWith
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Forgery : Type}
namespace Counted
open SigGolfCandidate.T3.Security.CountedPrivate
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
open SigGolfCandidate.T3.Security.MonitoredPrivate
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
  let interaction ← (simulateQ (MonitoredPrivate.proposalModel generated.1.2 budget hbudget).traced
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
  have h := MonitoredPrivate.proposal_trace_erasure generated.1.2 budget hbudget
    (ProposalOverflow.logged (adversary generated.1.1 generated.1.2)) [] generated.2
  rw [MonitoredPrivate.logged_source] at h
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
  apply le_trans ?_ (MonitoredPrivate.source_proposal_overflow generated.1.2 budget hbudget
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
end Monitored
end ClaudeWCT.W9.T3.Security.GameWith
end
section
namespace ClaudeWCT.W9.T3.Security.GameWith.Recorded
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.QueryRecorded
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen GameWith.idealGame
variable {Forgery : Type}
noncomputable def tracedExperiment (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (budget : Nat)
    (hbudget : budget ≤ 2^127) : PMF (Bool × (MonitoredPrivate.History × State)) := do
  let generated ← (liftM (run keygen initial) : PMF _)
  let interaction ← (simulateQ (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
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
  rw [← QueryRecorded.proposal_trace_project generated.1.2 budget hbudget _ [] generated.2,bind_map_left]
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
  have h := QueryRecorded.proposal_trace_erasure generated.1.2 budget hbudget
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
theorem large_budget (checker : Checker Forgery) (adversary : AdversaryFor Forgery) (q : Nat) (hq : 2^127 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      (q : ENNReal)/2^127 := by
  apply probEvent_le_one.trans
  have hcast : (2 : ENNReal)^127 ≤ (q : ENNReal) := by exact_mod_cast hq
  calc
    (1 : ENNReal) = (2 : ENNReal)^127/(2 : ENNReal)^127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right hcast _
theorem security_of_clean_bound (checker : Checker Forgery)
    (hclean : ∀ (adversary : AdversaryFor Forgery) (q : Nat), 1 ≤ q → ∀ hq : q ≤ 2^127,
      Pr[CleanWin q | tracedExperiment checker adversary q hq]+
        q/(2 : ENNReal)^146+(2 : ENNReal)⁻¹^700+((2 : ENNReal)^152)⁻¹+
        q/((2^256 : Nat) : ENNReal) ≤ (q : ENNReal)/2^127)
    (adversary : AdversaryFor Forgery) (q : Nat) (hpositive : 1 ≤ q) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | realExperiment checker adversary] ≤
      (q : ENNReal)/2^127 := by
  by_cases hq : 2^127 ≤ q
  · exact large_budget checker adversary q hq
  · have hsmall : q ≤ 2^127 := Nat.le_of_lt (Nat.lt_of_not_ge hq)
    refine (real_to_clean_trace checker adversary q hsmall).trans ?_
    exact hclean adversary q hpositive hsmall
end ClaudeWCT.W9.T3.Security.GameWith.Recorded
end
section
namespace ClaudeWCT.W9.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M (allQ_bind allQ_pure)
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
    publicOnly_expandB message publicKey signature
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
  apply SigGolfCandidate.T3M.allQ_mono (check_public publicKey log forgery)
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
  simpa only [realExperiment_eq,tracedExperiment,QueryRecorded.CleanWin] using
    GameWith.Recorded.real_to_clean_without_known checker reference adversary q hq
theorem traced_record_erasure (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    QueryRecorded.recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (GameWith.idealGame checker adversary) (∅,∅)) : PMF _) :=
  GameWith.Recorded.traced_record_erasure checker adversary budget hbudget
theorem traced_cost_coherent (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.CostCoherent result.2.2 :=
  GameWith.Recorded.traced_cost_coherent checker adversary budget hbudget result hr
end ClaudeWCT.W9.T3.Security.PaddedGame
end
section
namespace ClaudeWCT.W9.T3.Security.PaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final
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
end ClaudeWCT.W9.T3.Security.PaddedGame
end
section
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
def publicHandler : QueryImpl SigGolfCandidate.T3.Spec (OracleComp LazyPrivate.Interaction)
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
theorem traced_world (published : SigGolfCandidate.T3.Cache) (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : SphincsSecurity.OracleWorld.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    ((QueryRecorded.proposalModel published budget hbudget).traced (.inl input)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (liftM (QueryRecorded.run (forwardWorld input) state.2) : PMF _) := by
  rw [ProposalModel.traced_query_inactive _ _ _ (by rfl), QueryRecorded.proposal_query_erasure]
  rfl
theorem publicProgram_trace {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
noncomputable def rest (adversary : AdversaryP) (publicKey : Digest) (published : SigGolfCandidate.T3.Cache) :
    OracleComp LazyPrivate.Interaction Bool := do
  let result ← ProposalOverflow.logged (adversary publicKey published)
  publicProgram (GameWith.verdict PaddedGame.checker publicKey result)
theorem rest_trace (adversary : AdversaryP) (published : SigGolfCandidate.T3.Cache) (publicKey : Digest)
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
abbrev Weight := SigGolfCandidate.T3.Cache → LazyPrivate.Interaction.Domain →
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
end ClaudeWCT.W9.T3.Security.CreationGame
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
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
theorem traced_query_source_support (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
theorem class_creation_query_cost (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
theorem class_creation_program_cost {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : Bool × (Nat × (MonitoredPrivate.History × QueryRecorded.State)))
    (hr : result ∈ (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget).support) :
    result.2.1 ≤ result.2.2.2.base.source.1 := by
  rw [experiment, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
  obtain ⟨generated, _, hr⟩ := hr
  exact class_creation_program_cost generated.1.2 budget hbudget cls _
    (0, [], generated.2) (Nat.zero_le _) result hr
theorem class_program_mass_eq {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
    (fun generated =>
      Creation.expectedCharges (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
        (fun input state => (classWeight cls budget input state : ENNReal))
        (rest adversary generated.1.1 generated.1.2) ([], generated.2))
theorem expectedBirths_eq_mass (cls : HashInput → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget =
      expectedValue (experiment (fun _ => classWeight cls budget) budget adversary budget hbudget)
        (fun result => (result.2.1 : ENNReal)) := by
  rw [expectedBirths, experiment, expectedValue_bind]
  congr 1
  funext generated
  exact (class_program_mass_eq generated.1.2 budget hbudget cls _ ([], generated.2)).symm
end ClaudeWCT.W9.T3.Security.CreationGame
namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.BPORS.Adaptive
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount CountInvariant recorded_count_monotone
  recorded_world_hash_count prefixCount_le prefixCount_prefix_mono prefixCount_append_singleton prefixCount_disjoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem class_source_count_step (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
        (QueryRecorded.run (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr input)))) before.2) at hr
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
theorem class_creation_query_count (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
theorem class_creation_program_count {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
    (adversary : AdversaryP)
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
noncomputable def expectedClassCount (cls : SigGolfCandidate.T3.Spec.Domain → Prop)
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) : ENNReal :=
  expectedValue (PaddedGame.tracedExperiment adversary budget hbudget)
    (fun result => (prefixCount cls budget result.2.2.events : ENNReal))
theorem expectedBirths_le_classCount (cls : HashInput → Prop)
    (adversary : AdversaryP)
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
theorem expectedClassCount_le (cls : SigGolfCandidate.T3.Spec.Domain → Prop)
    (adversary : AdversaryP)
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
theorem expectedClassCount_disjoint (first second : SigGolfCandidate.T3.Spec.Domain → Prop)
    (hdisjoint : ∀ input, ¬ (first input ∧ second input))
    (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount (fun input => first input ∨ second input) adversary budget hbudget =
      expectedClassCount first adversary budget hbudget +
        expectedClassCount second adversary budget hbudget := by
  unfold expectedClassCount
  simp_rw [prefixCount_disjoint first second hdisjoint, Nat.cast_add]
  exact expectedValue_add _ _ _
end ClaudeWCT.W9.T3.Security.CreationGame
end
