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



/-! Authored module: BPORS. -/
section
/-! Local BPORS counting and bucket-thinning laws. These are the statistical
components of the T3 reduction; domination of the adaptive signing history is
an additional obligation. -/

namespace SigGolfCandidate.T3.BPORS.Adaptive
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The state and response retain the entire execution record. Only the label
marginal of an active request is capped; its other data may depend on the label.
The adversary may choose its next request from every previous response. -/
structure ProposalModel {ι : Type} (spec : OracleSpec ι) (State Label : Type) where
  Outcome : spec.Domain → Type
  record : (input : spec.Domain) → State → PMF (Outcome input)
  response : (input : spec.Domain) → Outcome input → spec.Range input
  advance : (input : spec.Domain) → State → Outcome input → State
  label : (input : spec.Domain) → Outcome input → Label
  active : spec.Domain → State → Bool
  base : PMF Label
  accept : ENNReal
  positive : accept ≠ 0
  lt_one : accept < 1
  cap : ∀ input state,active input state=true → ∀ point,
    accept*((record input state).map (label input)) point ≤ base point

namespace ProposalModel
variable {ι State Label : Type} {spec : OracleSpec ι}

noncomputable def rejected (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : State) : PMF Label :=
  if h : model.active input state=true then
    proposalResidualLaw model.base ((model.record input state).map (model.label input))
      model.accept model.lt_one (model.cap input state h)
  else model.base

noncomputable def original (model : ProposalModel spec State Label) :
    QueryImpl spec (StateT State PMF) := fun input => StateT.mk fun state =>
  (model.record input state).map fun outcome =>
    (model.response input outcome,model.advance input state outcome)

noncomputable def traced (model : ProposalModel spec State Label) :
    QueryImpl spec (StateT (List Label × State) PMF) :=
  proposalRecordImpl model.record model.response
    (fun input state _ outcome => model.advance input state outcome)
    model.label model.rejected model.active model.accept model.positive model.lt_one.le

/-- Dropping the synthetic proposals recovers the original response/state law. -/
theorem traced_query_erasure (model : ProposalModel spec State Label)
    (input : spec.Domain) (state : List Label × State) :
    Prod.map id Prod.snd <$> (model.traced input).run state=
      (model.original input).run state.2 := by
  rw [traced,proposalRecordImpl_project]
  have h := lengthRecordImpl_project model.record model.response
    (fun input state _ outcome => model.advance input state outcome)
    model.active model.accept model.positive model.lt_one.le
    model.original id model.advance (fun _ _ _ _ => rfl) (fun _ _ => rfl) input state.2
  simpa only [Prod.map_id,id_map,id_eq] using h

/-- Erasure is valid for an arbitrary adaptive oracle program, not just a fixed
sequence of requests. -/
theorem traced_erasure {Result : Type} (model : ProposalModel spec State Label)
    (computation : OracleComp spec Result) (state : List Label × State) :
    Prod.map id Prod.snd <$> (simulateQ model.traced computation).run state=
      (simulateQ model.original computation).run state.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd model.traced_query_erasure computation state

theorem traced_query_complete (model : ProposalModel spec State Label)
    (total : Nat) (input : spec.Domain) (state : List Label × State) :
    ((model.traced input).run state).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      completeProposalWord model.base total state.1 := by
  simp only [traced,proposalRecordImpl,StateT.run_mk]
  by_cases hactive : model.active input state.2=true
  · rw [if_pos hactive,PMF.bind_map,rejected,dif_pos hactive]
    simpa only [cappedRecordProposalBridge,List.append_assoc,Function.comp_def] using
      complete_cappedRecordProposalBridge_prefix model.base
        (model.record input state.2) (model.label input) model.accept model.positive model.lt_one
        (model.cap input state.2 hactive) total state.1
  · rw [if_neg hactive,PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _

/-- Completing the adaptive trace to a fixed length has the same distribution
as completing its initial prefix, regardless of the adaptive stopping policy. -/
theorem traced_complete {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : List Label × State) :
    ((simulateQ model.traced computation).run state).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      completeProposalWord model.base total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,PMF.monad_pure_eq_pure,PMF.pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,PMF.monad_bind_eq_bind,PMF.bind_bind]
      simp_rw [ih]
      exact model.traced_query_complete total input state

theorem completed_trace_independent {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State) :
    ((simulateQ model.traced computation).run ([],state)).bind
        (fun result => completeProposalWord model.base total result.2.1)=
      independentProposalWord model.base total := by
  rw [model.traced_complete,completeProposalWord_nil]

theorem monotone_payoff_le_completion (base : PMF Label) (total : Nat)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right)
    (consumed : List Label) (hused : consumed.length ≤ total) :
    payoff consumed ≤ expectedValue (completeProposalWord base total consumed) payoff := by
  rw [completeProposalWord_eq_padding,List.take_of_length_le hused,← PMF.monad_map_eq_map,
    expectedValue_map]
  calc
    _ = expectedValue (independentProposalWord base (total-consumed.length))
        (fun _ => payoff consumed) := (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun suffix => hmono _ _ (List.sublist_append_left _ _)

/-- A monotone exposure price on the consumed trace is dominated by the full
independent proposal word. Oversized traces are kept as an explicit exception. -/
theorem capped_trace_expectation {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ total then payoff result.2.1 else 0) ≤
      expectedValue (independentProposalWord model.base total) payoff := by
  calc
    _ ≤ expectedValue ((simulateQ model.traced computation).run ([],state))
        (fun result => expectedValue (completeProposalWord model.base total result.2.1) payoff) := by
      apply expectedValue_mono
      intro result
      split
      · exact monotone_payoff_le_completion model.base total payoff hmono _ (by assumption)
      · exact bot_le
    _ = expectedValue (((simulateQ model.traced computation).run ([],state)).bind
        (fun result => completeProposalWord model.base total result.2.1)) payoff := by
      rw [← PMF.monad_bind_eq_bind,expectedValue_bind]
    _ = _ := by rw [model.completed_trace_independent]

theorem uniform_word_expectation [Fintype Label] [SampleableType Label]
    (total : Nat) (payoff : List Label → ENNReal) :
    expectedValue (independentProposalWord (PMF.uniformOfFintype Label) total) payoff=
      uniformWordAverage total payoff := by
  unfold expectedValue uniformWordAverage
  apply tsum_congr
  intro word
  simp only [probOutput_def,evalDist_sampleUniformProposalWord,PMF.evalSPMF_eq]

theorem capped_selected_expectation {Result : Type} (model : ProposalModel spec State Label)
    (total : Nat) (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Label × State) → List Label)
    (hselected : ∀ result, (selected result).Sublist result.2.1)
    (payoff : List Label → ENNReal)
    (hmono : ∀ left right,left.Sublist right → payoff left ≤ payoff right) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ total then payoff (selected result) else 0) ≤
      expectedValue (independentProposalWord model.base total) payoff := by
  apply le_trans _ (model.capped_trace_expectation total computation state payoff hmono)
  apply expectedValue_mono
  intro result
  split
  · exact hmono _ _ (hselected result)
  · exact le_rfl

end ProposalModel

end SigGolfCandidate.T3.BPORS.Adaptive

namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

theorem atIndex_sublist {α β : Type} [DecidableEq α] (index : α)
    {left right : List (α × β)} (h : left.Sublist right) :
    (atIndex index left).Sublist (atIndex index right) := h.filterMap _

theorem bucketMass_sublist {left right : List (Fin 16)} (h : left.Sublist right)
    (bucket : Fin 16) : bucketMass left bucket ≤ bucketMass right bucket := by
  unfold bucketMass
  exact_mod_cast Nat.descFactorial_le 3 (Nat.mul_le_mul_left 3 (h.count_le bucket))

theorem coordinateEnvelope_sublist {left right : List (Fin 16)} (h : left.Sublist right) :
    coordinateEnvelope left ≤ coordinateEnvelope right := by
  unfold coordinateEnvelope
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun bucket _ => bucketMass_sublist h bucket

theorem wordEnvelope_sublist {left right : List Buckets} (h : left.Sublist right) :
    wordEnvelope left ≤ wordEnvelope right := by
  unfold wordEnvelope
  apply ENNReal.div_le_div_right
  exact Finset.prod_le_prod' fun c _ => coordinateEnvelope_sublist (h.map (fun row => row c))

theorem nearCoordinateEnvelope_sublist {left right : List (Fin 16)} (h : left.Sublist right) :
    Numeric.nearCoordinateEnvelope left ≤ Numeric.nearCoordinateEnvelope right := by
  unfold Numeric.nearCoordinateEnvelope
  apply ENNReal.div_le_div_right
  apply Finset.sum_le_sum
  intro bucket _
  exact_mod_cast Nat.descFactorial_le 2 (Nat.mul_le_mul_left 3 (h.count_le bucket))

theorem nearWordEnvelope_sublist (missing : Fin 7) {left right : List Buckets}
    (h : left.Sublist right) : nearWordEnvelope missing left ≤ nearWordEnvelope missing right := by
  unfold nearWordEnvelope
  apply ENNReal.div_le_div_right
  apply Finset.prod_le_prod'
  intro c _
  split
  · exact nearCoordinateEnvelope_sublist (h.map (fun row => row c))
  · exact coordinateEnvelope_sublist (h.map (fun row => row c))

theorem fullPrice_sublist {left right : List Proposal} (h : left.Sublist right) :
    fullPrice left ≤ fullPrice right := by
  unfold fullPrice
  apply mul_le_mul' le_rfl
  exact Finset.sum_le_sum fun index _ => wordEnvelope_sublist (atIndex_sublist index h)

theorem fullNearPrice_sublist {left right : List Proposal} (h : left.Sublist right) :
    fullNearPrice left ≤ fullNearPrice right := by
  unfold fullNearPrice
  apply mul_le_mul' le_rfl
  apply Finset.sum_le_sum
  intro index _
  exact Finset.sum_le_sum fun missing _ => nearWordEnvelope_sublist missing (atIndex_sublist index h)

/-- The same concrete BPORS moment controls a history selected adaptively from
the coupled proposal trace. Neither the selected positions nor the stopping
rule have to be independent of the observed labels. -/
theorem adaptive_selected_full_excess {ι State Result : Type} {spec : OracleSpec ι}
    (model : Adaptive.ProposalModel spec State Proposal)
    (hbase : model.base=PMF.uniformOfFintype Proposal)
    (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Proposal × State) → List Proposal)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ Numeric.proposalLength
        then fullPrice (selected result)-1 else 0) ≤ 11324/100000000 := by
  apply le_trans (model.capped_selected_expectation Numeric.proposalLength computation state selected
    hselected (fun word => fullPrice word-1)
    (fun _ _ h => tsub_le_tsub_right (fullPrice_sublist h) 1))
  rw [hbase,Adaptive.ProposalModel.uniform_word_expectation]
  exact fullPrice_excess_bound

theorem adaptive_selected_near_price {ι State Result : Type} {spec : OracleSpec ι}
    (model : Adaptive.ProposalModel spec State Proposal)
    (hbase : model.base=PMF.uniformOfFintype Proposal)
    (computation : OracleComp spec Result) (state : State)
    (selected : Result × (List Proposal × State) → List Proposal)
    (hselected : ∀ result,(selected result).Sublist result.2.1) :
    expectedValue ((simulateQ model.traced computation).run ([],state))
      (fun result => if result.2.1.length ≤ Numeric.proposalLength
        then fullNearPrice (selected result) else 0) ≤ 404 := by
  apply le_trans (model.capped_selected_expectation Numeric.proposalLength computation state selected
    hselected fullNearPrice (fun _ _ h => fullNearPrice_sublist h))
  rw [hbase,Adaptive.ProposalModel.uniform_word_expectation]
  exact fullNearPrice_bound

end SigGolfCandidate.T3.BPORS.History



namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The original signing continuation after the bounded digest search. -/
def payloadAfterDigest (cache : Cache) (rho : Digest) (output : HashOutput) : M (Option Signature) := do
  let index := output.toNat % 2^31
  let chosen := selections output
  let state ← (List.range 7).foldlM
    (fun (state : List Digest × List Digest × List Digest) coord => do
      let sel := chosen.getD coord ⟨0,[]⟩
      let (levels,secrets) ← buildFts index coord
      let selected := sel.leaves.map (fun s => sel.bucket*128+s)
      let opened := selected.map (fun s => secrets.getD s 0)
      let inner := (frontier selected 7 sel.bucket).map fun p => (levels.getD p.1 []).getD p.2 0
      let outer := (List.range 4).map fun j => (levels.getD (7+j) []).getD (sel.bucket/2^j ^^^ 1) 0
      pure (state.1 ++ opened,state.2.1 ++ inner ++ outer,
        state.2.2 ++ [(levels.getD 11 []).getD 0 0])) ([],[],[])
  let root ← forestPk index state.2.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho,fun i => state.1.getD i.val 0,fun i => state.2.1.getD i.val 0,
    fun lay => piecesSignature lay (layers.getD lay.val ([],[]))⟩)

/-- The selected digest is a ghost observation: it is retained even when a later
encoding search fails, and is not returned to the external adversary. -/
def payloadRecordForNonce (cache : Cache) (rho : Digest) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let found ← digestSearch rho message 0 attemptLimit
  match found with
  | none => pure (none,none)
  | some (_,output) => do
      let signature ← payloadAfterDigest cache rho output
      pure (signature,some output)

def payloadRecord (cache : Cache) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let rho ← privateNonce message
  payloadRecordForNonce cache rho message

def signingRecord (cache : Cache) (message : Message) :
    M (Option Signature × Option HashOutput) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return (none,none)
  payloadRecord cache message

theorem signPayload_factor (cache : Cache) (message : Message) :
    signPayload cache message=(do
      let rho ← privateNonce message
      let found ← digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_,output) => payloadAfterDigest cache rho output) := by
  unfold signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found => cases found;rfl

attribute [local irreducible] digestSearch privateNonce privateMac payloadAfterDigest

theorem payloadRecord_erasure (cache : Cache) (message : Message) :
    Prod.fst <$> payloadRecord cache message=signPayload cache message := by
  rw [signPayload_factor]
  unfold payloadRecord payloadRecordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  cases found with
  | none => rfl
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [map_bind,map_pure]
      exact bind_pure (payloadAfterDigest cache rho output)

theorem signingRecord_erasure (cache : Cache) (message : Message) :
    Prod.fst <$> signingRecord cache message=sign cache message := by
  unfold signingRecord sign
  simp only [map_bind]
  apply bind_congr
  intro tag
  split
  · rfl
  · exact payloadRecord_erasure cache message

theorem realized_signingRecord_erasure (secret : BitVec 256) (cache : Cache) (message : Message) :
    Prod.fst <$> realize secret (signingRecord cache message)=realize secret (sign cache message) := by
  rw [← Cost.realize_map,signingRecord_erasure]

/-- Observing the selected digest does not alter the random-oracle execution,
including its final cache. -/
theorem roRun_signingRecord_erasure (secret : BitVec 256) (cache : Cache) (message : Message)
    (oracleCache : RCache) :
    (fun result => (result.1.1,result.2)) <$> roRun secret (signingRecord cache message) oracleCache=
      roRun secret (sign cache message) oracleCache := by
  rw [← roRun_map,signingRecord_erasure]

noncomputable def selectedLabelWeight (payoff : IndexBuckets → ENNReal)
    (record : Option Signature × Option HashOutput) : ENNReal :=
  record.2.elim 0 (fun output => payoff (samplingData output).1)

/-- All work after digest selection preserves the observed label. It cannot
increase a nonnegative label weight, even without a losslessness assumption. -/
theorem payloadRecordForNonce_label_le (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache) (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤
    expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
      (fun result => result.1.elim 0 (fun found => payoff (samplingData found.2).1)) := by
  rw [payloadRecordForNonce,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp [selectedLabelWeight]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [roRun_bind,expectedValue_bind,roRun_pure,expectedValue_pure,selectedLabelWeight,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl

/-- Concrete signing records inherit the source search's label cap once the
nonce is fixed and all previously cached trials reject. -/
theorem payloadRecordForNonce_label_cap (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache)
    (hreject : CachedTrialsReject (digestTrial rho message) digestDecode 0 (2^32) oracleCache)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff :=
  (payloadRecordForNonce_label_le secret cache rho message oracleCache payoff).trans
    (digestSearch_label_weight_le_of_cached_reject secret rho message attemptLimit 0
      (by decide) oracleCache hreject payoff)

theorem payloadRecord_selected_valid (answers : Correctness.Answers) (cache : Cache)
    (rho : Digest) (message : Message) (output : HashOutput)
    (hrecord : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).2=some output) :
    ∃ counter,evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit)=some (counter,output) ∧
      admissible (selections output)=true := by
  unfold payloadRecordForNonce at hrecord
  simp only [evalWithAnswerFn_bind] at hrecord
  cases hd : evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,reduceCtorEq] at hrecord
  | some found =>
      rcases found with ⟨counter,value⟩
      simp only [hd,evalWithAnswerFn_bind,evalWithAnswerFn_pure,Option.some.injEq] at hrecord
      subst output
      exact ⟨counter,rfl,(Correctness.digestSearch_some answers rho message attemptLimit 0
        counter value (by decide) hd).2.2.2⟩

/-- Every recorded successful signature carries the selected digest, including
when the caller supplied a malicious cache. -/
theorem payloadRecord_success_has_digest (answers : Correctness.Answers) (cache : Cache)
    (rho : Digest) (message : Message)
    (hs : (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).1 ≠ none) :
    (evalWithAnswerFn answers (payloadRecordForNonce cache rho message)).2 ≠ none := by
  unfold payloadRecordForNonce at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs ⊢
  cases hd : evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) with
  | none => simp only [hd,evalWithAnswerFn_pure,ne_eq,not_true_eq_false] at hs
  | some found =>
      rcases found with ⟨counter,value⟩
      simp only [hd,evalWithAnswerFn_bind,evalWithAnswerFn_pure,ne_eq,reduceCtorEq,not_false_eq_true]

theorem payloadRecord_label_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache)
    (hreject : ∀ nonce ∈ support (roRun secret (privateNonce message) oracleCache),
      CachedTrialsReject (digestTrial nonce.1 message) digestDecode 0 (2^32) nonce.2)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (payloadRecord cache message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff := by
  rw [payloadRecord,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro nonce hn
  exact payloadRecordForNonce_label_cap secret cache nonce.1 message nonce.2 (hreject nonce hn) payoff

/-- The complete source signing operation obeys the record-label cap on every
reachable authenticated branch whose cached digest trials reject. The MAC and
nonce queries are included in the state at which the condition is required. -/
theorem signingRecord_label_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache)
    (hreject : ∀ auth ∈ support (roRun secret (privateMac cache.region) oracleCache),
      auth.1=cache.tag → ∀ nonce ∈ support (roRun secret (privateNonce message) auth.2),
      CachedTrialsReject (digestTrial nonce.1 message) digestDecode 0 (2^32) nonce.2)
    (payoff : IndexBuckets → ENNReal) :
    expectedValue (roRun secret (signingRecord cache message) oracleCache)
      (fun result => selectedLabelWeight payoff result.1) ≤ BPORS.finiteAverage payoff := by
  rw [signingRecord,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro auth ha
  split
  · simp [selectedLabelWeight]
  · rename_i htag
    apply payloadRecord_label_cap secret cache message auth.2 _ payoff
    exact hreject auth ha (by simpa only [ne_eq,not_not] using htag)

end SigGolfCandidate.T3.Security






namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestSearch payloadAfterDigest Finset.univ BPORS.finiteAverage DigestSampling.samplingData

theorem payloadRecordForNonce_completed_label_le (secret : BitVec 256) (cache : Cache)
    (rho : Digest) (message : Message) (oracleCache : RCache) (payoff : IndexBuckets → ENNReal) (fallback : ENNReal) :
    expectedValue (roRun secret (payloadRecordForNonce cache rho message) oracleCache)
      (fun result => result.1.2.elim fallback
        (fun output => payoff (samplingData output).1)) ≤
    expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
      (fun result => result.1.elim fallback
        (fun found => payoff (samplingData found.2).1)) := by
  rw [payloadRecordForNonce,roRun_bind,expectedValue_bind]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [roRun_pure,expectedValue_pure,Option.elim_none,le_refl]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [roRun_bind,expectedValue_bind,roRun_pure,expectedValue_pure,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl

/-- An exact source payload record, with a fresh uniform nonce supplied by the
caller and a total ghost label even on digest-search exhaustion. -/
noncomputable def freshNoncePayloadRecord (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    ProbComp (((Option Signature × Option HashOutput) × RCache) × IndexBuckets) :=
  completeRecord (fun result => result.1.2) do
    let rho ← $ᵗ Digest
    roRun secret (payloadRecordForNonce cache rho message) oracleCache

theorem freshNoncePayloadRecord_erasure (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    𝒮[Prod.fst <$> freshNoncePayloadRecord secret cache message oracleCache]=
      𝒮[($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (payloadRecordForNonce cache rho message) oracleCache] :=
  completeRecord_erasure _ _

theorem freshNoncePayloadRecord_target_bound (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (targets : Finset IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | freshNoncePayloadRecord secret cache message oracleCache] ≤
      targets.card/(2 : ENNReal)^59+cachedTargetCount targets oracleCache/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (completeRecord _ _) (fun result => targetWeight targets result.2) ≤ _
  rw [completeRecord_expected,expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (roRun secret (digestSearch rho message 0 attemptLimit) oracleCache)
          (fun result => completedTargetScore targets result.1)) :=
      expectedValue_mono _ fun rho => payloadRecordForNonce_completed_label_le secret cache rho message oracleCache _ _
    _ ≤ _ := by
      rw [← expectedValue_bind]
      exact uniform_nonce_completed_target_bound secret message attemptLimit (by decide) oracleCache targets

theorem freshNoncePayloadRecord_point_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    Pr[fun result => result.2=point | freshNoncePayloadRecord secret cache message oracleCache] ≤
      (1025/1024 : ENNReal)/(2 : ENNReal)^59 := by
  have h := freshNoncePayloadRecord_target_bound secret cache message oracleCache {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  exact h.trans (clean_point_bound_arithmetic oracleCache hfinite budget hsize hbudget hclean haccept point)

noncomputable def freshNoncePayloadLaw (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    PMF (((Option Signature × Option HashOutput) × RCache) × IndexBuckets) :=
  liftM (freshNoncePayloadRecord secret cache message oracleCache)

theorem freshNoncePayloadLaw_label_probability (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (point : IndexBuckets) :
    ((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point=
      Pr[fun result => result.2=point | freshNoncePayloadRecord secret cache message oracleCache] := by
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map]
  rfl

theorem freshNoncePayloadLaw_erasure (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) :
    (freshNoncePayloadLaw secret cache message oracleCache).map Prod.fst=
      (liftM (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
        roRun secret (payloadRecordForNonce cache rho message) oracleCache) :
        PMF ((Option Signature × Option HashOutput) × RCache)) := by
  apply PMF.ext
  intro result
  have h := evalSPMF_ext_iff.mp (freshNoncePayloadRecord_erasure secret cache message oracleCache) result
  rw [probOutput_map] at h
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map]
  rw [← PMF.probOutput_eq_apply]
  exact h

/-- The required ProposalModel point cap for a total source payload record.
Nonce freshness, cache cleanliness and the source acceptance upper bound remain
explicit caller obligations; failure-label mass has been accounted for. -/
theorem freshNoncePayloadLaw_scaled_cap (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (haccept : acceptanceProbability ≤ 1/16)
    (point : IndexBuckets) :
    (1024/1025 : ENNReal)*((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point ≤
      (PMF.uniformOfFintype IndexBuckets) point := by
  have hc : Fintype.card IndexBuckets=2^59 := by
    norm_num [IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  rw [freshNoncePayloadLaw_label_probability,PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) :=
      mul_le_mul' le_rfl (freshNoncePayloadRecord_point_cap secret cache message oracleCache
        hfinite budget hsize hbudget hclean haccept point)
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

end SigGolfCandidate.T3.Security



namespace SigGolfCandidate.T3.Security
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling DigestSampling

/-- Total source-payload label domination. The source acceptance bound is
discharged; the caller supplies a fresh uniform nonce and a clean finite cache. -/
theorem freshNoncePayloadLaw_scaled_cap_source (secret : BitVec 256) (cache : Cache)
    (message : Message) (oracleCache : RCache) (hfinite : SphincsSecurity.Finite oracleCache)
    (budget : Nat) (hsize : QueryCache.enncard oracleCache ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬TargetCacheExceptional oracleCache) (point : IndexBuckets) :
    (1024/1025 : ENNReal)*((freshNoncePayloadLaw secret cache message oracleCache).map Prod.snd) point ≤
      (PMF.uniformOfFintype IndexBuckets) point :=
  freshNoncePayloadLaw_scaled_cap secret cache message oracleCache hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point

end SigGolfCandidate.T3.Security

end

/-! Integrated checked SEC07726a4 and overflow0222a4f additions. -/

/-! Adaptive source-game private tables and nonce freshness. -/
section
namespace SigGolfCandidate.T3.Security.PrivateTable
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {ι D R State : Type} {base : OracleSpec ι}
variable [DecidableEq D] [SampleableType R]

abbrev Cache (D R : Type) := QueryCache (D →ₒ R)

/-- Complete a partial private-coordinate cache by a fixed total table. -/
def fill (cache : Cache D R) (table : D → R) : D → R :=
  fun input => (cache input).getD (table input)

omit [DecidableEq D] [SampleableType R] in
theorem fill_empty (table : D → R) : fill (∅ : Cache D R) table=table := by
  funext input
  rfl

omit [DecidableEq D] [SampleableType R] in
theorem fill_cached (cache : Cache D R) (table : D → R) (input : D) (value : R)
    (h : cache input=some value) : fill cache table input=value := by
  simp only [fill,h,Option.getD_some]

omit [SampleableType R] in
theorem cacheQuery_cached (cache : Cache D R) (input : D) (value : R)
    (h : cache input=some value) : cache.cacheQuery input value=cache := by
  funext other
  by_cases he : other=input
  · subst other
    rw [QueryCache.cacheQuery_self,h]
  · exact QueryCache.cacheQuery_of_ne cache value he

omit [SampleableType R] in
theorem fill_update (cache : Cache D R) (table : D → R) (input : D) (value : R)
    (h : cache input=none) :
    fill (cache.cacheQuery input value) table=fill cache (Function.update table input value) := by
  funext other
  by_cases he : other=input
  · subst other
    simp only [fill,QueryCache.cacheQuery_self,Option.getD_some,h,Option.getD_none,
      Function.update_self]
  · simp only [fill,QueryCache.cacheQuery_of_ne cache value he,Function.update_of_ne he]

/-- Public interactions retain their own state. Private calls use an independent
lazy cache and return exactly the same answer on repeated coordinates. -/
noncomputable def lazyImpl (handler : QueryImpl base (StateT State ProbComp)) :
    QueryImpl (base+(D →ₒ R)) (StateT (Cache D R × State) ProbComp)
  | .inl input => StateT.mk fun state => do
      let result ← (handler input).run state.2
      pure (result.1,(state.1,result.2))
  | .inr input => StateT.mk fun state => do
      let result ← (randomOracle (spec := D →ₒ R) input).run state.1
      pure (result.1,(result.2,state.2))

/-- Fixed-table interpretation with the same ghost private cache as the lazy
interpreter. This cache records all private queries, including repetitions. -/
noncomputable def eagerImpl (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) : QueryImpl (base+(D →ₒ R)) (StateT (Cache D R × State) ProbComp)
  | .inl input => StateT.mk fun state => do
      let result ← (handler input).run state.2
      pure (result.1,(state.1,result.2))
  | .inr input => StateT.mk fun state =>
      pure (table input,(state.1.cacheQuery input (table input),state.2))

noncomputable def lazyRun {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (cache : Cache D R) (state : State) :
    ProbComp (α × (Cache D R × State)) :=
  (simulateQ (lazyImpl handler) program).run (cache,state)

noncomputable def eagerRun {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) (program : OracleComp (base+(D →ₒ R)) α)
    (cache : Cache D R) (state : State) : ProbComp (α × (Cache D R × State)) :=
  (simulateQ (eagerImpl handler table) program).run (cache,state)

variable [Finite D] [Finite R] [Nonempty R] [SampleableType (D → R)]

theorem refresh_table {α : Type} (input : D) (next : (D → R) → ProbComp α) :
    𝒮[do let value ← $ᵗ R; let table ← $ᵗ (D → R); next (Function.update table input value)]=
      𝒮[do let table ← $ᵗ (D → R); next table] := by
  symm
  rw [evalSPMF_bind,← evalSPMF_uniformSample_bind_update input,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]

/-- Lazy private sampling agrees with a uniformly completed private table for
every adaptive source program, preserving its output and both final caches. -/
theorem lazyRun_eq_completed_table {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (cache : Cache D R) (state : State) :
    𝒮[lazyRun handler program cache state]=
      𝒮[do let table ← $ᵗ (D → R); eagerRun handler (fill cache table) program cache state] := by
  induction program using OracleComp.inductionOn generalizing cache state with
  | pure value =>
      apply evalSPMF_ext
      intro result
      simp [lazyRun,eagerRun]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun,eagerRun,simulateQ_bind,simulateQ_spec_query,lazyImpl,eagerImpl,
            StateT.run_bind,StateT.run_mk,bind_assoc,pure_bind]
          rw [evalSPMF_bind_bind_swap]
          apply evalSPMF_bind_congr'
          intro result
          exact ih result.1 cache result.2
      | inr input =>
          simp only [lazyRun,eagerRun,simulateQ_bind,simulateQ_spec_query,lazyImpl,eagerImpl,
            StateT.run_bind,StateT.run_mk,bind_assoc,pure_bind]
          cases hc : cache input with
          | some value =>
              rw [QueryImpl.withCaching_run_some _ hc,pure_bind]
              simp_rw [fill_cached cache _ input value hc,cacheQuery_cached cache input value hc]
              exact ih value cache state
          | none =>
              rw [QueryImpl.withCaching_run_none _ hc]
              simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_apply]
              trans 𝒮[do
                let value ← $ᵗ R
                let table ← $ᵗ (D → R)
                eagerRun handler (fill (cache.cacheQuery input value) table)
                  (next value) (cache.cacheQuery input value) state]
              · apply evalSPMF_bind_congr'
                intro value
                exact ih value (cache.cacheQuery input value) state
              · simp_rw [fill_update cache _ input _ hc]
                let continuation : (D → R) → ProbComp (α × (Cache D R × State)) :=
                  fun table => eagerRun handler (fill cache table)
                    (next (table input)) (cache.cacheQuery input (table input)) state
                have hpoint : ∀ value table,
                    eagerRun handler (fill cache (Function.update table input value))
                      (next value) (cache.cacheQuery input value) state=
                    continuation (Function.update table input value) := by
                  intro value table
                  simp only [continuation,Function.update_self]
                simp_rw [hpoint]
                rw [refresh_table input continuation]
                simp only [continuation,fill,hc,Option.getD_none]
                rfl

theorem lazyRun_empty_eq_uniform_table {α : Type}
    (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (state : State) :
    𝒮[lazyRun handler program ∅ state]=
      𝒮[do let table ← $ᵗ (D → R); eagerRun handler table program ∅ state] := by
  simpa only [fill_empty] using lazyRun_eq_completed_table handler program ∅ state

noncomputable def fixedImpl (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) : QueryImpl (base+(D →ₒ R)) (StateT State ProbComp) :=
  handler+(fun input => (pure (table input) : StateT State ProbComp R))

omit [SampleableType R] [Finite D] [Finite R] [Nonempty R] [SampleableType (D → R)] in
theorem eagerRun_erasure {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (table : D → R) (program : OracleComp (base+(D →ₒ R)) α)
    (cache : Cache D R) (state : State) :
    Prod.map id Prod.snd <$> eagerRun handler table program cache state=
      (simulateQ (fixedImpl handler table) program).run state := by
  apply map_run_simulateQ_eq_of_query_map_eq (eagerImpl handler table)
    (fixedImpl handler table) Prod.snd _ program (cache,state)
  intro input current
  cases input with
  | inl input =>
      change Prod.map id Prod.snd <$> (do
        let result ← (handler input).run current.2
        pure (result.1,(current.1,result.2)))=(handler input).run current.2
      simp only [map_bind,map_pure,Prod.map,id_eq,Prod.mk.eta,bind_pure]
  | inr input =>
      change Prod.map id Prod.snd <$>
        (pure (table input,(current.1.cacheQuery input (table input),current.2)) : ProbComp _)=
        pure (table input,current.2)
      rw [map_pure]
      rfl

/-- Marginal form of the lazy-table identity; the public state is retained. -/
theorem lazyRun_erasure {α : Type} (handler : QueryImpl base (StateT State ProbComp))
    (program : OracleComp (base+(D →ₒ R)) α) (state : State) :
    𝒮[Prod.map id Prod.snd <$> lazyRun handler program ∅ state]=
      𝒮[do let table ← $ᵗ (D → R); (simulateQ (fixedImpl handler table) program).run state] := by
  have h := congrArg (Functor.map (Prod.map id Prod.snd))
    (lazyRun_empty_eq_uniform_table handler program state)
  simpa only [← evalSPMF_map,map_bind,eagerRun_erasure] using h

end SigGolfCandidate.T3.Security.PrivateTable

namespace SigGolfCandidate.T3.Security.LazyPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance : Fintype Coordinate := coordinateFintype
noncomputable local instance : SampleableType (Coordinate → HashOutput) :=
  Derivation.outputSampler Coordinate

abbrev PCache := QueryCache (Coordinate →ₒ HashOutput)
abbrev State := PCache × Sampling.RCache

/-- The actual source program with independent lazy private and public tables. -/
noncomputable def run {α : Type} (program : M α) (state : State) : ProbComp (α × State) :=
  PrivateTable.lazyRun SphincsSecurity.romImpl program state.1 state.2

theorem fixedImpl_eq (outputs : Coordinate → HashOutput) :
    PrivateTable.fixedImpl SphincsSecurity.romImpl outputs=
      QueryImpl.compose SphincsSecurity.romImpl (Derivation.tableHandler outputs) := by
  funext input
  cases input with
  | inl input => simp only [PrivateTable.fixedImpl,QueryImpl.compose,
      Derivation.tableHandler,simulateQ_spec_query];rfl
  | inr input => simp only [PrivateTable.fixedImpl,QueryImpl.compose,
      Derivation.tableHandler,simulateQ_pure];rfl

/-- Exact source-game bridge. It preserves the final public cache and allows
arbitrary repetitions of private coordinates, including messages and MAC regions. -/
theorem run_eq_table {α : Type} (program : M α) (cache : Sampling.RCache) :
    𝒮[Prod.map id Prod.snd <$> run program (∅,cache)]=
      𝒮[do
        let outputs ← $ᵗ (Coordinate → HashOutput)
        (simulateQ SphincsSecurity.romImpl (Derivation.tableRun outputs program)).run cache] := by
  rw [run,PrivateTable.lazyRun_erasure]
  simp only [fixedImpl_eq,QueryImpl.simulateQ_compose,Derivation.tableRun]

noncomputable def experiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option (Bool × Nat)) :=
  Prod.fst <$> run (Derivation.cap (game adversary) q) (∅,∅)

theorem tableExperiment_eq (adversary : Adversary) (q : Nat) :
    𝒮[tableExperiment adversary q]=𝒮[experiment adversary q] := by
  have h := congrArg (Functor.map Prod.fst)
    (run_eq_table (Derivation.cap (game adversary) q) ∅)
  simp only [← evalSPMF_map,map_bind,Functor.map_map,Prod.map,
    id_eq,← StateT.run'_eq] at h
  unfold tableExperiment experiment
  simp only [evalSPMF_bind,evalSPMF_uniformSample] at h ⊢
  exact h.symm

/-- The existing real-game reduction now targets an exact lazy private-table
game, rather than assuming nonce independence inside the original execution. -/
theorem real_event_bound (adversary : Adversary) (q : Nat) (hq : q < 2^256) :
    Pr[fun result => result.1=true ∧ result.2≤q | realExperiment adversary] ≤
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
        experiment adversary q]+q/((2^256 : Nat) : ENNReal) := by
  have h := private_derivation_event_bound adversary q hq
  have he : Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
      tableExperiment adversary q]=
      Pr[fun outcome => ∃ result,outcome=some result ∧ result.1=true |
        experiment adversary q] :=
    probEvent_congr' (fun _ _ => Iff.rfl) (tableExperiment_eq adversary q)
  rw [he] at h
  exact h

@[simp] theorem run_pure {α : Type} (value : α) (state : State) :
    run (pure value : M α) state=pure (value,state) := by
  simp only [run,PrivateTable.lazyRun,simulateQ_pure,StateT.run_pure,Prod.mk.eta]

theorem run_bind {α β : Type} (program : M α) (next : α → M β) (state : State) :
    run (program >>= next) state=run program state >>= fun result => run (next result.1) result.2 := by
  simp only [run,PrivateTable.lazyRun,simulateQ_bind,StateT.run_bind]

theorem run_map {α β : Type} (f : α → β) (program : M α) (state : State) :
    run (f <$> program) state=Prod.map f id <$> run program state := by
  simp only [run,PrivateTable.lazyRun,simulateQ_map,StateT.run_map]
  rfl

theorem run_query (input : T3.Spec.Domain) (state : State) :
    run (liftM (T3.Spec.query input)) state=
      (PrivateTable.lazyImpl SphincsSecurity.romImpl input).run state := by
  simp only [run,PrivateTable.lazyRun,simulateQ_spec_query]

theorem run_publicQuery (input : HashInput) (state : State) :
    run (Sampling.publicHandler input) state=(do
      let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
      pure (result.1,(state.1,result.2))) := by
  rw [Sampling.publicHandler,run_query]
  simp only [PrivateTable.lazyImpl,StateT.run_mk,SphincsSecurity.romImpl,
    QueryImpl.add_apply_inr]
  rfl

theorem run_publicProgram {α : Type} (program : Sampling.RawM α) (state : State) :
    run (Sampling.publicProgram program) state=
      (fun result => (result.1,(state.1,result.2))) <$>
        (simulateQ (randomOracle (spec := SphincsSecurity.HashSpec)) program).run state.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [Sampling.publicProgram]
  | query_bind input next ih =>
      simp only [Sampling.publicProgram,simulateQ_bind,simulateQ_spec_query,run_bind]
      rw [run_publicQuery]
      change ((do
        let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
        pure (result.1,(state.1,result.2))) >>= fun result =>
          run (Sampling.publicProgram (next result.1)) result.2)=_
      simp only [bind_assoc,pure_bind,StateT.run_bind,map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (state.1,result.2)

theorem run_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) (state : State) :
    run (digestSearch rho message counter fuel) state=
      (fun result => (result.1,(state.1,result.2))) <$>
        Sampling.roRun 0 (digestSearch rho message counter fuel) state.2 := by
  rw [Sampling.digestSearch_public,run_publicProgram,Sampling.roRun,Sampling.public_randomOracle]

/-- The actual nonce query samples a uniform hash answer exactly when its
private coordinate has not been queried. Both cache updates are explicit. -/
theorem run_privateNonce_fresh (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) :
    run (privateNonce message) state=(do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (output.extractLsb' 0 128,
        (state.1.cacheQuery (.inr (.inl message)) output,state.2))) := by
  unfold privateNonce privateHash
  rw [run_bind,run_query]
  change ((do
    let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) (.inr (.inl message))).run state.1
    pure (result.1,(result.2,state.2))) >>= fun result =>
      run (pure (result.1.extractLsb' 0 128)) result.2)=_
  rw [QueryImpl.withCaching_run_none _ hfresh]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,run_pure,Function.comp_apply]
  rfl

theorem payloadForNonce_completed_label_le (cache : T3.Cache) (rho : Digest) (message : Message)
    (state : State) (payoff : DigestSampling.IndexBuckets → ENNReal) (fallback : ENNReal) :
    expectedValue (run (payloadRecordForNonce cache rho message) state)
      (fun result => result.1.2.elim fallback
        (fun output => payoff (DigestSampling.samplingData output).1)) ≤
    expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
      (fun result => result.1.elim fallback
        (fun found => payoff (DigestSampling.samplingData found.2).1)) := by
  rw [payloadRecordForNonce,run_bind,expectedValue_bind,run_digestSearch,expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [run_pure,expectedValue_pure,Option.elim_none,le_refl]
  | some found =>
      rcases found with ⟨counter,output⟩
      simp only [run_bind,expectedValue_bind,run_pure,expectedValue_pure,Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl

theorem uniform_hash_low_expectation (payoff : Digest → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => payoff (output.extractLsb' 0 128))=
      expectedValue ($ᵗ Digest : ProbComp Digest) payoff := by
  rw [← expectedValue_map]
  exact expectedValue_congr (evalSPMF_ext_iff.mp
    (SphincsSecurity.evalDist_hashOutput_extract_uniform (by decide : 128 ≤ SphincsSecurity.hashOutputBits))) payoff

/-- The completed-label bound now uses the actual private nonce query. Its
freshness is a concrete property of the private cache, not supplied randomness. -/
theorem payload_completed_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (payloadRecord cache message) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [payloadRecord,run_bind,run_privateNonce_fresh message state hfresh]
  simp only [bind_assoc,pure_bind,expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
        expectedValue (Sampling.roRun 0
          (digestSearch (output.extractLsb' 0 128) message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1)) :=
      expectedValue_mono _ fun output => payloadForNonce_completed_label_le cache _ message
        (state.1.cacheQuery (.inr (.inl message)) output,state.2)
        (Sampling.targetWeight targets) (BPORS.finiteAverage (Sampling.targetWeight targets))
    _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1)) :=
      uniform_hash_low_expectation (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => Sampling.completedTargetScore targets result.1))
    _ ≤ targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
      rw [← expectedValue_bind]
      exact Sampling.uniform_nonce_completed_target_bound 0 message attemptLimit (by decide) state.2 targets

theorem run_privateHash (coordinate : Coordinate) (state : State) :
    run (privateHash coordinate) state=(do
      let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) coordinate).run state.1
      pure (result.1,(result.2,state.2))) := by
  rw [privateHash,run_query]
  rfl

theorem privateHash_preserves_other (coordinate other : Coordinate) (hne : other ≠ coordinate)
    (state : State) (result : HashOutput × State) (hresult : result ∈ support (run (privateHash coordinate) state)) :
    result.2.1 other=state.1 other ∧ result.2.2=state.2 := by
  rw [run_privateHash] at hresult
  cases hc : state.1 coordinate with
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc,pure_bind,support_pure,Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨rfl,rfl⟩
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc] at hresult
      simp only [bind_map_left,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hresult
      obtain ⟨output,_,rfl⟩ := hresult
      exact ⟨QueryCache.cacheQuery_of_ne state.1 output hne,rfl⟩

theorem privateMac_preserves_nonce (region : Region) (message : Message)
    (state : State) (result : HashOutput × State)
    (hresult : result ∈ support (run (privateMac region) state)) :
    result.2.1 (.inr (.inl message))=state.1 (.inr (.inl message)) ∧ result.2.2=state.2 := by
  unfold privateMac privateMacKey at hresult
  simp only [bind_assoc,pure_bind,run_bind,mem_support_bind_iff] at hresult
  obtain ⟨first,hfirst,second,hsecond,htail⟩ := hresult
  rw [run_pure,support_pure,Set.mem_singleton_iff] at htail
  subst result
  have h0 := privateHash_preserves_other (.inl (header 14 0 0 0 0))
    (.inr (.inl message)) (by simp) state first hfirst
  have h1 := privateHash_preserves_other (.inl (header 14 0 0 0 1))
    (.inr (.inl message)) (by simp) first.2 second hsecond
  exact ⟨h1.1.trans h0.1,h1.2.trans h0.2⟩

theorem signing_completed_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    expectedValue (run (signingRecord cache message) state)
      (fun result => result.1.2.elim (BPORS.finiteAverage (Sampling.targetWeight targets))
        (fun output => Sampling.targetWeight targets (DigestSampling.samplingData output).1)) ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [signingRecord,run_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro result hresult
  have hp := privateMac_preserves_nonce cache.region message state result hresult
  split_ifs with htag
  · simp only [run_pure,expectedValue_pure,Option.elim_none,Sampling.targetWeight_average]
    exact le_add_right le_rfl
  · have h := payload_completed_target_bound cache message result.2 (hp.1.trans hfresh) targets
    rw [hp.2] at h
    exact h

noncomputable def signingRecordLaw (cache : T3.Cache) (message : Message) (state : State) :
    PMF (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets) :=
  liftM (Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state))

theorem signingRecordLaw_target_bound (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (targets : Finset DigestSampling.IndexBuckets) :
    Pr[fun result => result.2 ∈ targets | signingRecordLaw cache message state] ≤
      targets.card/(2 : ENNReal)^59+Sampling.cachedTargetCount targets state.2/(2 : ENNReal)^128 := by
  rw [← expectedValue_ite_one]
  change expectedValue (Sampling.completeRecord (fun result => result.1.2)
    (run (signingRecord cache message) state)) (fun result => Sampling.targetWeight targets result.2) ≤ _
  rw [Sampling.completeRecord_expected]
  exact signing_completed_target_bound cache message state hfresh targets

/-- Local proposal domination for the actual signer, including MAC rejection,
digest exhaustion, and later encoding failure, under concrete cache conditions. -/
theorem signingRecordLaw_scaled_cap (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message))=none) (hfinite : SphincsSecurity.Finite state.2)
    (budget : Nat) (hsize : QueryCache.enncard state.2 ≤ budget) (hbudget : budget ≤ 2^127)
    (hclean : ¬Sampling.TargetCacheExceptional state.2) (point : DigestSampling.IndexBuckets) :
    (1024/1025 : ENNReal)*((signingRecordLaw cache message state).map Prod.snd) point ≤
      (PMF.uniformOfFintype DigestSampling.IndexBuckets) point := by
  have hc : Fintype.card DigestSampling.IndexBuckets=2^59 := by
    norm_num [DigestSampling.IndexBuckets,Fintype.card_prod,Fintype.card_fun]
  have h := signingRecordLaw_target_bound cache message state hfresh {point}
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one] at h
  have hpoint := h.trans (Sampling.clean_point_bound_arithmetic state.2 hfinite budget hsize hbudget
    hclean Acceptance.acceptanceProbability_le_one_sixteenth point)
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,hc,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ (1024/1025 : ENNReal)*((1025/1024 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

/-- Erasing the observation and ghost label recovers the actual signer response
and both final caches, including failures and malicious cache requests. -/
theorem signingRecordLaw_erasure (cache : T3.Cache) (message : Message) (state : State) :
    (signingRecordLaw cache message state).map (fun result => (result.1.1.1,result.1.2))=
      (liftM (run (sign cache message) state) : PMF (Option Signature × State)) := by
  have hsign : Prod.map Prod.fst id <$> run (signingRecord cache message) state=
      run (sign cache message) state := by
    rw [← run_map,signingRecord_erasure]
  have hg :
      𝒮[(fun result => (result.1.1.1,result.1.2)) <$>
        Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state)]=
      𝒮[run (sign cache message) state] := by
    trans 𝒮[Prod.map Prod.fst id <$>
      (Prod.fst <$> Sampling.completeRecord (fun result => result.1.2) (run (signingRecord cache message) state))]
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

abbrev Interaction := SphincsSecurity.OracleWorld+Requests

def interactionSource : QueryImpl Interaction M
  | .inl input => forwardWorld input
  | .inr request => sign request.cache request.message

def InteractionOutcome : Interaction.Domain → Type
  | .inl input => SphincsSecurity.OracleWorld.Range input × State
  | .inr _ => (((Option Signature × Option HashOutput) × State) × DigestSampling.IndexBuckets)

noncomputable def interactionRecord : (input : Interaction.Domain) → State → PMF (InteractionOutcome input)
  | .inl input,state => liftM (run (forwardWorld input) state)
  | .inr request,state => signingRecordLaw request.cache request.message state

def interactionResponse : (input : Interaction.Domain) → InteractionOutcome input → Interaction.Range input
  | .inl _,result => result.1
  | .inr _,result => result.1.1.1

def interactionAdvance : (input : Interaction.Domain) → State → InteractionOutcome input → State
  | .inl _,_,result => result.2
  | .inr _,_,result => result.1.2

def interactionLabel : (input : Interaction.Domain) → InteractionOutcome input → DigestSampling.IndexBuckets
  | .inl _,_ => default
  | .inr _,result => result.2

noncomputable def interactionActive (budget : Nat) : Interaction.Domain → State → Bool
  | .inl _,_ => false
  | .inr request,state => decide (
      state.1 (.inr (.inl request.message))=none ∧ SphincsSecurity.Finite state.2 ∧
      QueryCache.enncard state.2 ≤ budget ∧ ¬Sampling.TargetCacheExceptional state.2)

/-- Concrete proposal model for the actual adaptive signing interface. Activity
marks fresh nonce requests in clean bounded public states; the record law itself
always executes the actual source signer and retains the full state. -/
noncomputable def proposalModel (budget : Nat) (hbudget : budget ≤ 2^127) :
    BPORS.Adaptive.ProposalModel Interaction State DigestSampling.IndexBuckets where
  Outcome := InteractionOutcome
  record := interactionRecord
  response := interactionResponse
  advance := interactionAdvance
  label := interactionLabel
  active := interactionActive budget
  base := PMF.uniformOfFintype DigestSampling.IndexBuckets
  accept := 1024/1025
  positive := by norm_num
  lt_one := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  cap := by
    intro input state hactive point
    cases input with
    | inl input => simp [interactionActive] at hactive
    | inr request =>
        change decide (_ ∧ _ ∧ _ ∧ _)=true at hactive
        obtain ⟨hfresh,hfinite,hsize,hclean⟩ := of_decide_eq_true hactive
        exact signingRecordLaw_scaled_cap request.cache request.message state
          hfresh hfinite budget hsize hbudget hclean point

theorem proposal_query_erasure (budget : Nat) (hbudget : budget ≤ 2^127)
    (input : Interaction.Domain) (state : State) :
    (((proposalModel budget hbudget).original input).run state)=
      (liftM (run (interactionSource input) state) : PMF (Interaction.Range input × State)) := by
  cases input with
  | inl input =>
      change (fun result : SphincsSecurity.OracleWorld.Range input × State => (result.1,result.2)) <$>
        (liftM (run (forwardWorld input) state) : PMF _)=_
      change id <$> (liftM (run (forwardWorld input) state) : PMF _)=_
      rw [id_map]
      rfl
  | inr request =>
      exact signingRecordLaw_erasure request.cache request.message state

/-- The concrete model preserves the complete response/state law of every
adaptive interaction program, not just individual signing requests. -/
theorem proposal_execution_erasure {α : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction α) (state : State) :
    (simulateQ (proposalModel budget hbudget).original program).run state=
      (liftM (run (simulateQ interactionSource program) state) : PMF (α × State)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [run_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,proposal_query_erasure]
      rw [simulateQ_bind,simulateQ_spec_query,run_bind,liftM_bind]
      apply bind_congr
      intro result
      exact ih result.1 result.2

theorem proposal_trace_erasure {α : Type} (budget : Nat) (hbudget : budget ≤ 2^127)
    (program : OracleComp Interaction α) (history : List DigestSampling.IndexBuckets) (state : State) :
    Prod.map id Prod.snd <$>
      (simulateQ (proposalModel budget hbudget).traced program).run (history,state)=
      (liftM (run (simulateQ interactionSource program) state) : PMF (α × State)) := by
  rw [(proposalModel budget hbudget).traced_erasure,proposal_execution_erasure]

end SigGolfCandidate.T3.Security.LazyPrivate

namespace SigGolfCandidate.T3.Security.NonceFreshness
open OracleComp OracleSpec
open LazyPrivate
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def nonceQuery (message : Message) : T3.Spec.Domain := .inr (.inr (.inl message))
abbrev Avoids {α : Type} (message : Message) (program : M α) : Prop :=
  AllQueriesSatisfy program (fun input => input ≠ nonceQuery message)

variable (protectedMessage : Message)

theorem avoids_pure {α : Type} (value : α) : Avoids protectedMessage (pure value) :=
  allQueriesSatisfy_pure _ _

theorem avoids_bind {α β : Type} {program : M α} {next : α → M β}
    (hp : Avoids protectedMessage program) (hn : ∀ value,Avoids protectedMessage (next value)) :
    Avoids protectedMessage (program >>= next) := allQueriesSatisfy_bind hp hn

theorem avoids_map {α β : Type} (f : α → β) {program : M α}
    (hp : Avoids protectedMessage program) : Avoids protectedMessage (f <$> program) := by
  rw [map_eq_bind_pure_comp]
  exact avoids_bind protectedMessage hp fun _ => avoids_pure _ _

theorem avoids_foldlM {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,Avoids protectedMessage (f a b)) (initial : α) :
    Avoids protectedMessage (items.foldlM f initial) := by
  induction items generalizing initial with
  | nil => exact avoids_pure _ _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact avoids_bind protectedMessage (h initial a) ih

theorem avoids_mapM {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,Avoids protectedMessage (f a)) : Avoids protectedMessage (items.mapM f) := by
  induction items with
  | nil => exact avoids_pure _ _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact avoids_bind protectedMessage (h a) fun _ =>
        avoids_bind protectedMessage ih fun _ => avoids_pure _ _

theorem avoids_publicHash (input : HashInput) : Avoids protectedMessage (publicHash input) := by
  exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])

theorem avoids_privatePair (tag lay tree position index : Nat) :
    Avoids protectedMessage (privatePair tag lay tree position index) := by
  unfold privatePair
  apply avoids_bind protectedMessage
  · exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
  · intro _
    exact avoids_pure _ _

theorem avoids_privateMac (region : Region) : Avoids protectedMessage (privateMac region) := by
  have hk (i : Nat) : Avoids protectedMessage (privateHash (.inl (header 14 0 0 0 i))) :=
    (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
  unfold privateMac privateMacKey
  simp only [bind_assoc,pure_bind]
  exact avoids_bind protectedMessage (hk 0) fun _ =>
    avoids_bind protectedMessage (hk 1) fun _ => avoids_pure _ _

theorem avoids_privateNonce (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (privateNonce message) := by
  unfold privateNonce
  apply avoids_bind protectedMessage
  · exact (allQueriesSatisfy_query_iff _ _).mpr (by simpa [nonceQuery] using hne)
  · intro _
    exact avoids_pure _ _

attribute [local aesop safe apply] avoids_pure avoids_bind avoids_map avoids_foldlM avoids_mapM
  avoids_publicHash avoids_privatePair avoids_privateMac avoids_privateNonce
macro "nonce_safe" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

theorem avoids_shortHash (input : HashInput) : Avoids protectedMessage (shortHash input) := by
  unfold shortHash; nonce_safe
attribute [local aesop safe apply] avoids_shortHash
theorem avoids_mask (level index : Nat) : Avoids protectedMessage (mask level index) := by
  unfold mask pairedMask; nonce_safe
attribute [local aesop safe apply] avoids_mask
theorem avoids_chain (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    Avoids protectedMessage (chain lay tree leaf i start count value) := by
  unfold chain; nonce_safe
attribute [local aesop safe apply] avoids_chain
theorem avoids_leafHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    Avoids protectedMessage (leafHash lay tree leaf ends) := by
  unfold leafHash; nonce_safe
attribute [local aesop safe apply] avoids_leafHash
theorem avoids_nodeHash (tag lay tree heap : Nat) (left right : Digest) :
    Avoids protectedMessage (nodeHash tag lay tree heap left right) := by
  unfold nodeHash; nonce_safe
attribute [local aesop safe apply] avoids_nodeHash
theorem avoids_buildLeaf (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    Avoids protectedMessage (buildLeaf lay tree leaf digits signatureOnly) := by
  unfold buildLeaf; nonce_safe
attribute [local aesop safe apply] avoids_buildLeaf
theorem avoids_buildLevel (tag lay tree h level : Nat) (nodes : List Digest) :
    Avoids protectedMessage (buildLevel tag lay tree h level nodes) := by
  unfold buildLevel; nonce_safe
attribute [local aesop safe apply] avoids_buildLevel
theorem avoids_buildLevels (tag lay tree h : Nat) (leaves : List Digest) :
    Avoids protectedMessage (buildLevels tag lay tree h leaves) := by
  unfold buildLevels; nonce_safe
attribute [local aesop safe apply] avoids_buildLevels
theorem avoids_buildTree (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    Avoids protectedMessage (buildTree lay tree selected digits) := by
  unfold buildTree; nonce_safe
attribute [local aesop safe apply] avoids_buildTree
theorem avoids_keygenPayload : Avoids protectedMessage keygenPayload := by
  unfold keygenPayload maskedLevel pairedMask; nonce_safe
attribute [local aesop safe apply] avoids_keygenPayload
theorem avoids_keygen : Avoids protectedMessage keygen := by
  unfold keygen; nonce_safe

theorem avoids_counterSearch (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    Avoids protectedMessage (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; nonce_safe
  | succ fuel ih => unfold counterSearch; nonce_safe
attribute [local aesop safe apply] avoids_counterSearch
theorem avoids_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Avoids protectedMessage (digest rho message counter) := by
  unfold digest; nonce_safe
attribute [local aesop safe apply] avoids_digest
theorem avoids_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids protectedMessage (digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; nonce_safe
  | succ fuel ih => unfold digestSearch; nonce_safe
attribute [local aesop safe apply] avoids_digestSearch
theorem avoids_ftsLeaf (index coord leaf : Nat) (secret : Digest) :
    Avoids protectedMessage (ftsLeaf index coord leaf secret) := by
  unfold ftsLeaf; nonce_safe
attribute [local aesop safe apply] avoids_ftsLeaf
theorem avoids_buildFts (index coord : Nat) : Avoids protectedMessage (buildFts index coord) := by
  unfold buildFts; nonce_safe
attribute [local aesop safe apply] avoids_buildFts
theorem avoids_forestPk (index : Nat) (roots : List Digest) :
    Avoids protectedMessage (forestPk index roots) := by
  unfold forestPk; nonce_safe
attribute [local aesop safe apply] avoids_forestPk
theorem avoids_topPath (cache : T3.Cache) (leaf : Nat) : Avoids protectedMessage (topPath cache leaf) := by
  unfold topPath; nonce_safe
attribute [local aesop safe apply] avoids_topPath
theorem avoids_signTop (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    Avoids protectedMessage (signTop cache leaf digits) := by
  unfold signTop; nonce_safe
attribute [local aesop safe apply] avoids_signTop
theorem avoids_signLayers (cache : T3.Cache) (index n : Nat) (message : Digest) :
    Avoids protectedMessage (signLayers cache index n message) := by
  induction n generalizing message with
  | zero => unfold signLayers; nonce_safe
  | succ n ih => unfold signLayers; nonce_safe
attribute [local aesop safe apply] avoids_signLayers
theorem avoids_signPayload (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (signPayload cache message) := by
  unfold signPayload; nonce_safe
attribute [local aesop safe apply] avoids_signPayload
theorem avoids_sign (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage) :
    Avoids protectedMessage (sign cache message) := by
  unfold sign; nonce_safe

/-- One query cannot change a different private nonce cell. Public queries
preserve the entire private cache. -/
theorem query_preserves (input : T3.Spec.Domain) (hinput : input ≠ nonceQuery protectedMessage)
    (state : LazyPrivate.State) (result : T3.Spec.Range input × LazyPrivate.State)
    (hresult : result ∈ support (run (liftM (T3.Spec.query input)) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) := by
  cases input with
  | inl input =>
      rw [run_query] at hresult
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,support_pure,
        Set.mem_singleton_iff] at hresult
      obtain ⟨_,_,rfl⟩ := hresult
      rfl
  | inr coordinate =>
      have hne : (.inr (.inl protectedMessage) : Coordinate) ≠ coordinate := by
        intro he
        apply hinput
        exact congrArg Sum.inr he.symm
      exact (privateHash_preserves_other coordinate _ hne state result hresult).1

theorem run_preserves {α : Type} (program : M α) (hprogram : Avoids protectedMessage program)
    (state : LazyPrivate.State) (result : α × LazyPrivate.State) (hresult : result ∈ support (run program state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [run_pure,support_pure,Set.mem_singleton_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hprogram
      rw [run_bind,mem_support_bind_iff] at hresult
      obtain ⟨intermediate,hstep,htailResult⟩ := hresult
      exact (ih intermediate.1 (htail intermediate.1) intermediate.2 htailResult).trans
        (query_preserves protectedMessage input hinput state intermediate hstep)

theorem keygen_nonce_fresh (result : (Digest × T3.Cache) × LazyPrivate.State)
    (hresult : result ∈ support (run keygen (∅,∅))) :
    result.2.1 (.inr (.inl protectedMessage))=none :=
  run_preserves protectedMessage keygen (avoids_keygen protectedMessage) (∅,∅) result hresult

theorem sign_preserves_other_nonce (cache : T3.Cache) (message : Message) (hne : message ≠ protectedMessage)
    (state : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (hresult : result ∈ support (run (sign cache message) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) :=
  run_preserves protectedMessage _ (avoids_sign protectedMessage cache message hne) state result hresult

def otherRequest (input : LazyPrivate.Interaction.Domain) : Prop :=
  match input with
  | .inl _ => True
  | .inr request => request.message ≠ protectedMessage

/-- Any adaptive prefix restricted to other signing messages can perform
arbitrary public queries without touching the protected nonce coordinate. -/
theorem interaction_avoids {α : Type} (program : OracleComp LazyPrivate.Interaction α)
    (hprogram : AllQueriesSatisfy program (otherRequest protectedMessage)) :
    Avoids protectedMessage (simulateQ LazyPrivate.interactionSource program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact avoids_pure _ _
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hprogram
      rw [simulateQ_bind,simulateQ_spec_query]
      apply avoids_bind protectedMessage _ (fun answer => ih answer (htail answer))
      cases input with
      | inl input =>
          exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [nonceQuery])
      | inr request => exact avoids_sign protectedMessage request.cache request.message hinput

theorem interaction_nonce_preserved {α : Type} (program : OracleComp LazyPrivate.Interaction α)
    (hprogram : AllQueriesSatisfy program (otherRequest protectedMessage))
    (state : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hresult : result ∈ support (run (simulateQ LazyPrivate.interactionSource program) state)) :
    result.2.1 (.inr (.inl protectedMessage))=state.1 (.inr (.inl protectedMessage)) :=
  run_preserves protectedMessage _ (interaction_avoids protectedMessage program hprogram) state result hresult

/-- Freshness after actual key generation and any adaptive interaction prefix
that has not requested this message. Repetition of every other message is allowed. -/
theorem keygen_interaction_nonce_fresh {α : Type}
    (program : Digest → T3.Cache → OracleComp LazyPrivate.Interaction α)
    (hprogram : ∀ publicKey cache,AllQueriesSatisfy (program publicKey cache) (otherRequest protectedMessage))
    (result : α × LazyPrivate.State)
    (hresult : result ∈ support (run (do
      let generated ← keygen
      simulateQ LazyPrivate.interactionSource (program generated.1 generated.2)) (∅,∅))) :
    result.2.1 (.inr (.inl protectedMessage))=none := by
  apply run_preserves protectedMessage _ _ (∅,∅) result hresult
  exact avoids_bind protectedMessage (avoids_keygen protectedMessage) fun generated =>
    interaction_avoids protectedMessage _ (hprogram generated.1 generated.2)

end SigGolfCandidate.T3.Security.NonceFreshness
end

/-! SourceInteractionReplay: base T3 replay and authentication security interfaces. -/
section

namespace SigGolfCandidate.T3.Security.SourceQueries
open OracleComp OracleSpec
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable (P : T3.Spec.Domain → Prop)

theorem pure_allowed {α : Type} (value : α) : AllQueriesSatisfy (pure value : M α) P :=
  allQueriesSatisfy_pure _ _

theorem bind_allowed {α β : Type} {program : M α} {next : α → M β}
    (hp : AllQueriesSatisfy program P) (hn : ∀ value, AllQueriesSatisfy (next value) P) :
    AllQueriesSatisfy (program >>= next) P := allQueriesSatisfy_bind hp hn

theorem map_allowed {α β : Type} (f : α → β) {program : M α}
    (hp : AllQueriesSatisfy program P) : AllQueriesSatisfy (f <$> program) P := by
  rw [map_eq_bind_pure_comp]
  exact bind_allowed P hp fun _ => pure_allowed _ _

theorem foldlM_allowed {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,AllQueriesSatisfy (f a b) P) (initial : α) :
    AllQueriesSatisfy (items.foldlM f initial) P := by
  induction items generalizing initial with
  | nil => exact pure_allowed _ _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact bind_allowed P (h initial a) ih

theorem mapM_allowed {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,AllQueriesSatisfy (f a) P) : AllQueriesSatisfy (items.mapM f) P := by
  induction items with
  | nil => exact pure_allowed _ _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact bind_allowed P (h a) fun _ => bind_allowed P ih fun _ => pure_allowed _ _

theorem map_allowed_iff {α β : Type} (f : α → β) (program : M α) :
    AllQueriesSatisfy (f <$> program) P ↔ AllQueriesSatisfy program P := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [map_pure,allQueriesSatisfy_pure]
  | query_bind input next ih =>
      simp only [map_bind,allQueriesSatisfy_query_bind_iff,ih]

theorem countWith_allowed {α : Type} (weight : T3.Spec.Domain → Nat) (program : M α)
    (h : AllQueriesSatisfy program P) : AllQueriesSatisfy (Cost.countWith weight program) P := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [Cost.countWith_pure]
      exact pure_allowed _ _
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [Cost.countWith_bind,Cost.countWith_query]
      apply bind_allowed P
      · exact map_allowed P _ ((allQueriesSatisfy_query_iff _ _).mpr hinput)
      · intro result
        exact map_allowed P _ (ih result.1 (htail result.1))

variable (hpublic : ∀ input, P (.inl (.inr input)))
variable (hpair : ∀ tweak, P (.inr (.inl tweak)))
variable (hnonce : ∀ message, P (.inr (.inr (.inl message))))
include hpublic hpair hnonce

omit hpair hnonce in
theorem publicHash_allowed (input : HashInput) : AllQueriesSatisfy (publicHash input) P :=
  (allQueriesSatisfy_query_iff _ _).mpr (hpublic _)

omit hpublic hnonce in
theorem privatePair_allowed (tag lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair tag lay tree position index) P := by
  unfold privatePair
  apply bind_allowed P
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hpair _)
  · intro _; exact pure_allowed _ _

omit hpublic hpair in
theorem privateNonce_allowed (message : Message) : AllQueriesSatisfy (privateNonce message) P := by
  unfold privateNonce
  apply bind_allowed P
  · exact (allQueriesSatisfy_query_iff _ _).mpr (hnonce _)
  · intro _; exact pure_allowed _ _

attribute [local aesop safe apply] pure_allowed bind_allowed map_allowed foldlM_allowed mapM_allowed
  publicHash_allowed privatePair_allowed privateNonce_allowed
macro "source_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

omit hpair hnonce in
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) P := by
  unfold shortHash; source_queries
attribute [local aesop safe apply] shortHash_allowed
omit hpublic hnonce in
theorem mask_allowed (level index : Nat) : AllQueriesSatisfy (mask level index) P := by
  unfold mask pairedMask; source_queries
attribute [local aesop safe apply] mask_allowed
theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) P := by
  unfold chain; source_queries
attribute [local aesop safe apply] chain_allowed
theorem leafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) P := by
  unfold leafHash; source_queries
attribute [local aesop safe apply] leafHash_allowed
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash; source_queries
attribute [local aesop safe apply] nodeHash_allowed
theorem buildLeaf_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) P := by
  unfold buildLeaf; source_queries
attribute [local aesop safe apply] buildLeaf_allowed
theorem buildLevel_allowed (tag lay tree h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) P := by
  unfold buildLevel; source_queries
attribute [local aesop safe apply] buildLevel_allowed
theorem buildLevels_allowed (tag lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) P := by
  unfold buildLevels; source_queries
attribute [local aesop safe apply] buildLevels_allowed
theorem buildTree_allowed (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) P := by
  unfold buildTree; source_queries
attribute [local aesop safe apply] buildTree_allowed
theorem keygenPayload_allowed : AllQueriesSatisfy keygenPayload P := by
  unfold keygenPayload maskedLevel pairedMask; source_queries

theorem counterSearch_allowed (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; source_queries
  | succ fuel ih => unfold counterSearch; source_queries
attribute [local aesop safe apply] counterSearch_allowed
omit hpair hnonce in
theorem digest_allowed (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) P := by
  unfold digest; source_queries
attribute [local aesop safe apply] digest_allowed
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; source_queries
  | succ fuel ih => unfold digestSearch; source_queries
attribute [local aesop safe apply] digestSearch_allowed
theorem ftsLeaf_allowed (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) P := by
  unfold ftsLeaf; source_queries
attribute [local aesop safe apply] ftsLeaf_allowed
theorem buildFts_allowed (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) P := by
  unfold buildFts; source_queries
attribute [local aesop safe apply] buildFts_allowed
theorem forestPk_allowed (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) P := by
  unfold forestPk; source_queries
attribute [local aesop safe apply] forestPk_allowed
theorem topPath_allowed (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) P := by
  unfold topPath; source_queries
attribute [local aesop safe apply] topPath_allowed
theorem signTop_allowed (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) P := by
  unfold signTop; source_queries
attribute [local aesop safe apply] signTop_allowed
theorem signLayers_allowed (cache : T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) P := by
  induction n generalizing message with
  | zero => unfold signLayers; source_queries
  | succ n ih => unfold signLayers; source_queries
attribute [local aesop safe apply] signLayers_allowed
theorem signPayload_allowed (cache : T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) P := by
  unfold signPayload; source_queries

omit hpublic hnonce in
theorem privateMac_allowed (region : Region) : AllQueriesSatisfy (privateMac region) P := by
  have hk (i : Nat) : AllQueriesSatisfy (privateHash (.inl (header 14 0 0 0 i))) P :=
    (allQueriesSatisfy_query_iff _ _).mpr (hpair _)
  unfold privateMac privateMacKey
  simp only [bind_assoc,pure_bind]
  exact bind_allowed P (hk 0) fun _ => bind_allowed P (hk 1) fun _ => pure_allowed _ _

theorem keygen_allowed (hmac : ∀ region,P (.inr (.inr (.inr region)))) :
    AllQueriesSatisfy keygen P := by
  unfold keygen
  apply bind_allowed P (keygenPayload_allowed P hpublic hpair hnonce)
  intro generated
  apply bind_allowed P (privateMac_allowed P hpair _)
  intro _; exact pure_allowed _ _

theorem sign_allowed (hmac : ∀ region,P (.inr (.inr (.inr region))))
    (cache : T3.Cache) (message : Message) : AllQueriesSatisfy (sign cache message) P := by
  unfold sign
  apply bind_allowed P (privateMac_allowed P hpair _)
  intro tag
  split_ifs
  · exact pure_allowed _ _
  · exact signPayload_allowed P hpublic hpair hnonce cache message

end SigGolfCandidate.T3.Security.SourceQueries

namespace SigGolfCandidate.T3.Security.SourceReplay
open OracleComp OracleSpec LazyPrivate
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def IsHash : T3.Spec.Domain → Prop
  | .inl (.inl _) => False
  | _ => True

abbrev HashOnly {α : Type} (program : M α) := AllQueriesSatisfy program IsHash

theorem sign_hashOnly (cache : T3.Cache) (message : Message) : HashOnly (sign cache message) :=
  SourceQueries.sign_allowed IsHash (fun _ => trivial) (fun _ => trivial)
    (fun _ => trivial) (fun _ => trivial) cache message

theorem keygen_hashOnly : HashOnly keygen :=
  SourceQueries.keygen_allowed IsHash (fun _ => trivial) (fun _ => trivial)
    (fun _ => trivial) (fun _ => trivial)

theorem signingRecord_hashOnly (cache : T3.Cache) (message : Message) :
    HashOnly (signingRecord cache message) := by
  apply (SourceQueries.map_allowed_iff IsHash Prod.fst _).mp
  rw [signingRecord_erasure]
  exact sign_hashOnly cache message

/-- The product order means that all previously sampled public and private answers persist. -/
abbrev Extends (before after : LazyPrivate.State) : Prop := before ≤ after

def known (state : LazyPrivate.State) : QueryCache T3.Spec
  | .inl (.inl _) => none
  | .inl (.inr input) => state.2 input
  | .inr coordinate => state.1 coordinate

theorem known_mono (before after : LazyPrivate.State) (hle : Extends before after) :
    known before ≤ known after := by
  intro input answer h
  cases input with
  | inl input =>
      cases input with
      | inl input => cases h
      | inr input => exact hle.2 h
  | inr coordinate => exact hle.1 h

theorem query_extends (input : T3.Spec.Domain) (before : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (run (liftM (T3.Spec.query input)) before)) : Extends before result.2 := by
  rw [run_query] at h
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      refine ⟨le_rfl,?_⟩
      cases input with
      | inl input =>
          change step ∈ support ((fun answer => (answer,before.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl input)) : ProbComp _)) at hstep
          rw [support_map] at hstep
          obtain ⟨_,_,rfl⟩ := hstep
          exact le_rfl
      | inr input => exact QueryImpl.withCaching_cache_le _ input before.2 step hstep
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      exact ⟨QueryImpl.withCaching_cache_le _ coordinate before.1 step hstep,le_rfl⟩

theorem run_extends {α : Type} (program : M α) (before : LazyPrivate.State)
    (result : α × LazyPrivate.State) (h : result ∈ support (run program before)) :
    Extends before result.2 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [run_pure,mem_support_pure_iff] at h
      subst result
      exact le_rfl
  | query_bind input next ih =>
      rw [run_bind,mem_support_bind_iff] at h
      obtain ⟨step,hstep,htail⟩ := h
      exact (query_extends input before step hstep).trans (ih step.1 step.2 htail)

theorem hash_query_caches (input : T3.Spec.Domain) (hhash : IsHash input)
    (before : LazyPrivate.State) (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (run (liftM (T3.Spec.query input)) before)) :
    known result.2 input=some result.1 := by
  cases input with
  | inl input =>
      cases input with
      | inl input => exact False.elim hhash
      | inr input =>
          rw [run_query] at h
          simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
            support_pure,Set.mem_singleton_iff] at h
          obtain ⟨step,hstep,rfl⟩ := h
          exact DeterministicSigning.query_caches input before.2 step hstep
  | inr coordinate =>
      rw [run_query] at h
      simp only [PrivateTable.lazyImpl,StateT.run_mk,mem_support_bind_iff,
        support_pure,Set.mem_singleton_iff] at h
      obtain ⟨step,hstep,rfl⟩ := h
      exact DeterministicSigning.query_caches coordinate before.1 step hstep

/-- Every hash reached along this deterministic execution is present in the state. -/
inductive Resolves (state : LazyPrivate.State) {α : Type} : M α → α → Prop
  | pure (value : α) : Resolves state (pure value) value
  | query (input : T3.Spec.Domain) (answer : T3.Spec.Range input)
      (hanswer : known state input=some answer) (next : T3.Spec.Range input → M α)
      (value : α) (tail : Resolves state (next answer) value) :
      Resolves state (liftM (T3.Spec.query input) >>= next) value

theorem Resolves.mono {α : Type} {before after : LazyPrivate.State}
    {program : M α} {value : α} (h : Resolves before program value) (hle : Extends before after) :
    Resolves after program value := by
  induction h with
  | pure value => exact .pure value
  | query input answer hanswer next value _ ih =>
      exact .query input answer (known_mono before after hle hanswer) next value ih

theorem resolves_of_run {α : Type} (program : M α) (hhash : HashOnly program)
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (h : result ∈ support (run program before)) : Resolves result.2 program result.1 := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [run_pure,mem_support_pure_iff] at h
      subst result
      exact .pure value
  | query_bind input next ih =>
      obtain ⟨hinput,hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hhash
      rw [run_bind,mem_support_bind_iff] at h
      obtain ⟨step,hstep,htail⟩ := h
      have hle := run_extends (next step.1) step.2 result htail
      exact .query input step.1
        (known_mono step.2 result.2 hle (hash_query_caches input hinput before step hstep))
        next result.1 (ih step.1 (hn step.1) step.2 htail)

theorem known_query_run (state : LazyPrivate.State) (input : T3.Spec.Domain)
    (answer : T3.Spec.Range input) (h : known state input=some answer) :
    run (liftM (T3.Spec.query input)) state=pure (answer,state) := by
  rw [run_query]
  cases input with
  | inl input =>
      cases input with
      | inl input => cases h
      | inr input =>
          change (do
            let result ← (randomOracle (spec := SphincsSecurity.HashSpec) input).run state.2
            pure (result.1,(state.1,result.2)))=pure (answer,state)
          simp only [known] at h
          rw [QueryImpl.withCaching_run_some _ h,pure_bind]
  | inr coordinate =>
      change (do
        let result ← (randomOracle (spec := Coordinate →ₒ HashOutput) coordinate).run state.1
        pure (result.1,(result.2,state.2)))=pure (answer,state)
      simp only [known] at h
      rw [QueryImpl.withCaching_run_some _ h,pure_bind]

theorem Resolves.run_eq_pure {α : Type} {state : LazyPrivate.State}
    {program : M α} {value : α} (h : Resolves state program value) :
    run program state=Pure.pure (value,state) := by
  induction h with
  | pure value => exact run_pure _ _
  | query input answer hanswer next value _ ih =>
      rw [run_bind,known_query_run state input answer hanswer,pure_bind,ih]

/-- Exact replay after arbitrary intervening source queries, including private queries. -/
theorem replay_run {α : Type} (program : M α) (hhash : HashOnly program)
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (h : result ∈ support (run program before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) : run program after=pure (result.1,after) :=
  ((resolves_of_run program hhash before result h).mono hle).run_eq_pure

/-- Repeating the same cache/message pair returns the same response, including failure,
without sampling any new private or public answer. All previous hash calls still count
in a separately instrumented cost game; this theorem does not erase their charge. -/
theorem sign_replay (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (h : result ∈ support (run (sign cache message) before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) : run (sign cache message) after=pure (result.1,after) :=
  replay_run _ (sign_hashOnly cache message) before result h after hle

/-- Selected digests, including those from requests that fail later, also replay exactly. -/
theorem signingRecord_replay (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (h : result ∈ support (run (signingRecord cache message) before)) (after : LazyPrivate.State)
    (hle : Extends result.2 after) :
    run (signingRecord cache message) after=pure (result.1,after) :=
  replay_run _ (signingRecord_hashOnly cache message) before result h after hle

/-- Replay preserves the complete query charge; it does not treat cached calls as free. -/
theorem counted_sign_replay (weight : T3.Spec.Domain → Nat) (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : (Option Signature × Nat) × LazyPrivate.State)
    (h : result ∈ support (run (Cost.countWith weight (sign cache message)) before))
    (after : LazyPrivate.State) (hle : Extends result.2 after) :
    run (Cost.countWith weight (sign cache message)) after=pure (result.1,after) :=
  replay_run _ (SourceQueries.countWith_allowed IsHash weight _ (sign_hashOnly cache message))
    before result h after hle

theorem sign_after_intervening {α : Type} (cache : T3.Cache) (message : Message)
    (before : LazyPrivate.State) (result : Option Signature × LazyPrivate.State)
    (h : result ∈ support (run (sign cache message) before)) (intervening : M α)
    (later : α × LazyPrivate.State) (hlater : later ∈ support (run intervening result.2)) :
    run (sign cache message) later.2=pure (result.1,later.2) :=
  sign_replay cache message before result h later.2 (run_extends intervening result.2 later hlater)

end SigGolfCandidate.T3.Security.SourceReplay

end

