import SigGolfCandidate.ClaudeWCT.Bank.GameBank
import SigGolfCandidate.ClaudeWCT.Bank.Kernel
import SigGolfCandidate.ClaudeWCT.Bank.WCTSpec
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.Bank.GameInv
import SigGolfCandidate.ClaudeWCT.Bank.GameInvL
import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
import SigGolfCandidate.ClaudeWCT.WCT9.Limits

section

namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_exists_admissible : ∃ x, digestAdmissible x = true := by
  obtain ⟨x, hx⟩ := CaseC.admissibleSet_nonempty
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩
theorem bpors_acceptance_eq :
    Pr[fun x : HashOutput => digestAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) CaseC.admInd := by
  unfold CaseC.admInd
  rw [expectedValue_ite_one]
theorem bpors_one_le_score (X : List HashOutput) (N : HashOutput) (hadm : digestAdmissible N = true)
    (hcov : ∀ c, CaseC.CoordCovered X N c) : 1 ≤ CaseC.score X N := by
  unfold digestAdmissible at hadm
  rw [Bool.and_eq_true] at hadm
  exact CaseC.one_le_score X N (CaseC.outLeaves_injective N hadm.1) hadm.2 hcov
noncomputable def bporsSpec : FtsBankSpec BPORS.History.Proposal where
  admissible := digestAdmissible
  exists_admissible := bpors_exists_admissible
  acceptance_le := bpors_acceptance_eq ▸ CaseC.expected_admInd_tight
  proposal := CaseC.label
  accepted_proposal g := by
    rw [Sampling.digest_acceptanceProbability]
    exact accepted_samplingData g
  score := CaseC.score
  covered X N := ∀ c, CaseC.CoordCovered X N c
  one_le_score := bpors_one_le_score
  score_append_mono := CaseC.score_append_mono
  price := BPORS.History.fullPrice
  average_score := CaseC.average_score
  horizon := BPORS.Numeric.proposalLength
  excessRate := 11324 / 100000000
  excess_le := CaseC.excess_three_quarters
theorem bpors_decode : bporsSpec.decode = Sampling.digestDecode := rfl
theorem bpors_acceptance : bporsSpec.acceptance = acceptanceProbability := Sampling.digest_acceptanceProbability
theorem bpors_freshPrice (w : HashOutput → ENNReal) :
    bporsSpec.freshPrice w = Sampling.WeightedSelection.freshPrice w := by
  unfold FtsBankSpec.freshPrice Sampling.WeightedSelection.freshPrice
  rw [bpors_acceptance]
  rfl
theorem bpors_search (rho : Digest) (m : Message) (counter fuel : Nat) :
    bporsSpec.search rho m counter fuel = digestSearch rho m counter fuel :=
  (Sampling.digestSearch_public rho m fuel counter).symm
theorem bpors_admissibleSet : bporsSpec.admissibleSet = CaseC.admissibleSet := by
  ext x
  simp [FtsBankSpec.admissibleSet, CaseC.admissibleSet, bporsSpec]
theorem bpors_accepted : bporsSpec.accepted = CaseC.accepted := by
  unfold FtsBankSpec.accepted CaseC.accepted
  congr 1
theorem bpors_forecast : bporsSpec.forecast = CaseC.forecast := by
  funext R X N
  unfold FtsBankSpec.forecast CaseC.forecast
  rw [bpors_accepted]
  rfl
theorem bpors_excessForecast : bporsSpec.excessForecast = CaseC.excessForecast := rfl
theorem bpors_ledger : bporsSpec.ledger = CaseC.ledger := by
  funext R targets X slack
  unfold FtsBankSpec.ledger CaseC.ledger
  rw [bpors_forecast, bpors_excessForecast]
theorem bpors_corePotential : bporsSpec.corePotential = CaseC.corePotential := by
  funext b
  unfold FtsBankSpec.corePotential CaseC.corePotential
  rw [bpors_ledger]
  rfl
theorem bpors_Reuse : bporsSpec.Reuse = CaseC.Reuse := rfl
theorem bpors_admissibleEntry : bporsSpec.admissibleEntry = CaseC.admissibleEntry := by
  funext cache input
  unfold FtsBankSpec.admissibleEntry CaseC.admissibleEntry
  cases cache input <;> simp [bporsSpec]
theorem bpors_reuseMass : bporsSpec.reuseMass = CaseC.reuseMass := by
  funext cache m
  unfold FtsBankSpec.reuseMass CaseC.reuseMass
  rw [bpors_admissibleEntry]
theorem bpors_admInd : bporsSpec.admInd = CaseC.admInd := by
  funext a
  simp [FtsBankSpec.admInd, CaseC.admInd, bporsSpec]
theorem bpors_recordForNonce (cache : T3.Cache) (rho : Digest) (m : Message) :
    bporsSpec.recordForNonce payloadAfterDigest cache rho m = payloadRecordForNonce cache rho m := by
  unfold FtsBankSpec.recordForNonce payloadRecordForNonce
  rw [bpors_search]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem bpors_record (published : T3.Cache) (request : Request) :
    bporsSpec.authenticatedRecord payloadAfterDigest published request =
      FullGame.authenticatedRecord published request := by
  unfold FtsBankSpec.authenticatedRecord FullGame.authenticatedRecord
  apply bind_congr
  intro tag
  by_cases h : request.cache = published
  · simp only [h, if_true]
    unfold FtsBankSpec.payloadRecord payloadRecord
    apply bind_congr
    intro rho
    exact bpors_recordForNonce _ rho _
  · simp only [h, if_false]
theorem t3_core_sign (b : CaseC.BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + CaseC.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if CaseC.Reuse cache rho m then CaseC.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => CaseC.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ CaseC.corePotential b := by
  have h := bporsSpec.core_sign b cache m C' (by rw [bpors_reuseMass]; exact hC) secret fuel hfuel
  simp only [bpors_corePotential, bpors_Reuse, bpors_search] at h
  exact h
theorem t3_core_birth (b : CaseC.BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + CaseC.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => CaseC.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      CaseC.corePotential b + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  have h := bporsSpec.core_birth b s hs C' (by rw [bpors_admInd]; exact hC)
  simp only [bpors_corePotential] at h
  exact h
theorem t3_core_initial (budget : Nat) :
    CaseC.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h := bporsSpec.core_initial budget
  rw [bpors_corePotential] at h
  exact h
theorem t3_core_win (b : CaseC.BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N = true ∧
      CaseC.CoveredBy b.exposures N) :
    1 ≤ CaseC.corePotential b := by
  rw [← bpors_corePotential]
  apply bporsSpec.core_win b halive
  rcases h with h | ⟨N, hN, hadm, hgate, hcov⟩
  · exact Or.inl h
  · refine Or.inr ⟨N, hN, ?_, ?_⟩
    · change digestAdmissible N = true
      unfold digestAdmissible
      rw [Bool.and_eq_true]
      exact ⟨hadm, hgate⟩
    · exact fun c => CaseC.coordCovered_of_opened b.exposures N c fun j => hcov _ (CaseC.opened_mem N c j)
theorem t3_fresh_signing_kernel (published : T3.Cache) (m : Message) (state : LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P : ENNReal) (hP : Sampling.WeightedSelection.freshPrice w ≤ P)
    (hF : ∀ result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state),
      F result ≤ if CaseC.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P w) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state) F ≤
      P + CaseC.reuseMass state.2 m := by
  have h := bporsSpec.fresh_signing_kernel payloadAfterDigest published m state hfresh F w P
    (by rw [bpors_freshPrice]; exact hP) (by rw [bpors_record]; exact hF)
  rw [bpors_record, bpors_reuseMass] at h
  exact h
theorem bpors_payNotDigest : PayNotDigest payloadAfterDigest := BPB.payloadAfterDigest_ok
theorem bpors_source (published : T3.Cache) :
    bporsSpec.source payloadAfterDigest published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      change Prod.fst <$> bporsSpec.authenticatedRecord payloadAfterDigest published request =
        FullGame.authenticatedSign published request
      rw [bpors_record, FullGame.authenticatedRecord_erasure]
end ClaudeWCT.Bank.BPORSRegression
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression2 : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_payAvoids : PayAvoids payloadAfterDigest := by
  intro m cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(NonceFreshness.avoids_pure m), (NonceFreshness.avoids_bind m), (NonceFreshness.avoids_map m),
      (NonceFreshness.avoids_foldlM m), (NonceFreshness.avoids_mapM m), (NonceFreshness.avoids_buildFts m),
      (NonceFreshness.avoids_forestPk m), (NonceFreshness.avoids_signLayers m)])
theorem bpors_recordedExperiment (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      bporsSpec.recordedExperiment payloadAfterDigest (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpec.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [bpors_source]
  exact ht
theorem bpors_birthWeight (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    birthWeight (Sig := Signature) budget input state.2 =
      (CreationGame.classWeight CaseC.IsDigestInput budget input state : ENNReal) := by
  rcases input with (n | x) | request
  · simp [birthWeight, CreationGame.classWeight]
  · simp only [birthWeight, CreationGame.classWeight]
    by_cases h : CaseC.Birth budget x state.2
    · have h' : state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none :=
        ⟨h.2.2, h.1, h.2.1⟩
      rw [if_pos h, if_pos h', Nat.cast_one]
    · have h' : ¬(state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none) :=
        fun h' => h ⟨h'.2.1, h'.2.2, h'.1⟩
      rw [if_neg h, if_neg h', Nat.cast_zero]
  · simp [birthWeight, CreationGame.classWeight]
theorem bpors_expectedBirths (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    bporsSpec.expectedBirths payloadAfterDigest (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpec.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (bporsSpec.recordedImpl payloadAfterDigest generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← bpors_source]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact bpors_birthWeight budget input state
theorem t3_bank_potential_le (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bporsSpec.bankExperiment payloadAfterDigest (CreationGame.rest adversary) budget)
        (fun r => bporsSpec.potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  rw [← bpors_expectedBirths adversary budget hbudget]
  exact bporsSpec.bank_potential_le payloadAfterDigest bpors_payNotDigest bpors_payAvoids
    (CreationGame.rest adversary) budget
end ClaudeWCT.Bank.BPORSRegression
end

section



namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (Coord Child Rank child rank digit Opening wctHeader buildChild buildCoordinate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wct_digestSearch_public {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.admissible = WCT9.admissible) (rho : Digest) (message : Message) :
    ∀ fuel counter, WCT9.digestSearch rho message counter fuel = S.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [WCT9.digestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode, hadm]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]
def payAfterDigest (cache : T3.Cache) (rho : Digest) (output : HashOutput) : M (Option WCT9.Signature) := do
  let index := output.toNat % 2 ^ 31
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List Digest) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening], state.2 ++ [(levels.getD 7 []).getD 0 0])) ([], [])
  let root ← WCT9.forestPk index state.2
  let some layers ← signLayers cache index 4 (root, 0, 0) | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
theorem signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem payloadRecord_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.admissible = WCT9.admissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayload cache message := by
  rw [signPayload_factor]
  unfold FtsBankSpec.payloadRecord FtsBankSpec.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
section avoids
variable (m : Message)
theorem avoids_chain (index coord selected i start count : Nat) (value : Digest) :
    NonceFreshness.Avoids m (WCT9.chain index coord selected i start count value) := by
  unfold WCT9.chain
  exact NonceFreshness.avoids_foldlM m _ _ (fun _ _ => NonceFreshness.avoids_shortHash m _) _
theorem avoids_leafHash (index coord selected : Nat) (ends : List Digest) :
    NonceFreshness.Avoids m (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_forestPk (index : Nat) (roots : List Digest) : NonceFreshness.Avoids m (WCT9.forestPk index roots) := by
  unfold WCT9.forestPk
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_buildChild (index coord selected : Nat) (word : Rank) :
    NonceFreshness.Avoids m (buildChild index coord selected word) := by
  unfold buildChild
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state pair
    apply NonceFreshness.avoids_bind m (NonceFreshness.avoids_privatePair m _ _ _ _ _)
    intro seeds
    apply NonceFreshness.avoids_foldlM m
    intro state half
    split
    · apply NonceFreshness.avoids_bind m (avoids_chain m _ _ _ _ _ _ _)
      intro value
      apply NonceFreshness.avoids_bind m (avoids_chain m _ _ _ _ _ _ _)
      intro _
      exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
  · intro state
    exact NonceFreshness.avoids_bind m (avoids_leafHash m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
theorem avoids_buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    NonceFreshness.Avoids m (buildCoordinate index coord selected word) := by
  unfold buildCoordinate
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state j
    exact NonceFreshness.avoids_bind m (avoids_buildChild m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m
    · apply NonceFreshness.avoids_foldlM m
      intro nodes heap
      exact NonceFreshness.avoids_bind m (NonceFreshness.avoids_nodeHash m _ _ _ _ _ _)
        fun _ => NonceFreshness.avoids_pure m _
    · intro _
      exact NonceFreshness.avoids_pure m _
end avoids
theorem wct_payAvoids : PayAvoids payAfterDigest := by
  intro m cache rho output
  unfold payAfterDigest
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state coord
    exact NonceFreshness.avoids_bind m (avoids_buildCoordinate m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m (avoids_forestPk m _ _)
    intro root
    apply NonceFreshness.avoids_bind m (NonceFreshness.avoids_signLayers m _ _ _ _)
    intro layers
    split
    · exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
theorem wctHeader_value_lt (tag lay tree position index : Nat) :
    1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
      position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 < 2 ^ 128 := by
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wctHeader_value_lt _ _ _ _ _)]
theorem wctHeader_byte1 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0).toNat = tag % 256 := by
  have h : (bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0 =
      ⟨(wctHeader tag lay tree position index).extractLsb' 8 8⟩ := rfl
  rw [h]
  show ((wctHeader tag lay tree position index).extractLsb' 8 8).toNat = tag % 256
  rw [BitVec.extractLsb'_toNat, wctHeader_toNat, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  norm_num at h4 h5 h6 ⊢
  omega
theorem hdrBlock_pad64_prefix (a h rest : HashInput) (ha : a.length = 16) (hh : h.length = 16) :
    T3M.Extract.hdrBlock (pad64 (a ++ h ++ rest)) = h := by
  rw [T3M.Extract.hdrBlock_pad64 _ (by simp [ha, hh]; omega)]
  unfold T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hh]
theorem shortHash_wct_ok (a rest : HashInput) (tag lay tree position index : Nat) (ha : a.length = 16)
    (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (shortHash (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) BPB.NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrTag (pad64 (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) ≠ 12
    unfold BPB.hdrTag
    rw [hdrBlock_pad64_prefix _ _ _ ha (bytesLE_length _ _), wctHeader_byte1]
    split <;> simp_all
  · intro _; exact SourceQueries.pure_allowed _ _
theorem chain_ok (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) BPB.NotDigestQ := by
  unfold WCT9.chain
  refine SourceQueries.foldlM_allowed BPB.NotDigestQ _ _ (fun v step => ?_) _
  unfold WCT9.chainInput
  rw [List.append_assoc (zero16 ++ _)]
  exact shortHash_wct_ok zero16 _ 5 _ _ _ _ (by simp [zero16]) (by decide)
theorem leafHash_ok (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) BPB.NotDigestQ := by
  unfold WCT9.leafHash
  exact shortHash_wct_ok _ _ 6 _ _ _ _ (bytesLE_length _ _) (by decide)
theorem forest_header_plain (index : Nat) : header 15 0 index 0 0 = wctHeader 15 0 index 0 0 := by
  unfold wctHeader header
  rw [if_neg (by decide)]
  simp only [Nat.add_assoc]
theorem forestPk_ok (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (WCT9.forestPk index roots) BPB.NotDigestQ := by
  unfold WCT9.forestPk
  rw [forest_header_plain]
  exact shortHash_wct_ok _ _ 15 _ _ _ _ (bytesLE_length _ _) (by decide)
theorem buildChild_ok (index coord selected : Nat) (word : Rank) :
    AllQueriesSatisfy (buildChild index coord selected word) BPB.NotDigestQ := by
  unfold buildChild
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state pair
    apply SourceQueries.bind_allowed _ (BPB.privatePair_ok _ _ _ _ _)
    intro seeds
    apply SourceQueries.foldlM_allowed
    intro state half
    split
    · apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
      intro value
      apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
      intro _
      exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHash_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem buildCoordinate_ok (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) BPB.NotDigestQ := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChild_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · apply SourceQueries.foldlM_allowed
      intro nodes heap
      exact SourceQueries.bind_allowed _ (BPB.nodeHash_ok 11 _ _ _ _ _ (by decide))
        fun _ => SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
theorem wct_payNotDigest : PayNotDigest payAfterDigest := by
  intro cache rho output
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinate_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (forestPk_ok _ _)
    intro root
    apply SourceQueries.bind_allowed _ (BPB.signLayers_ok _ _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.Bank.WCT
end

section


namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctBank : DecidableEq T3.Cache := Classical.decEq _
variable (hacc : AcceptedProposalUniform) (hle : AcceptanceBound) (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.signPayload request.cache request.message else pure none
theorem wct_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpec hacc hle horizon rate hexc).authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpec.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ rfl _ _
  · rfl
theorem wct_source_sign (published : T3.Cache) (request : Request) :
    (wctSpec hacc hle horizon rate hexc).source payAfterDigest published (.inr request) =
      authenticatedSign published request :=
  wct_record_erasure hacc hle horizon rate hexc published request
noncomputable def interactionSource (published : T3.Cache) : QueryImpl (Interaction' WCT9.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request
theorem wct_source (published : T3.Cache) :
    (wctSpec hacc hle horizon rate hexc).source payAfterDigest published = interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact wct_source_sign hacc hle horizon rate hexc published request
theorem wct_recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) :
    (wctSpec hacc hle horizon rate hexc).recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (interactionSource generated.1.2) (rest generated.1.1 generated.1.2))
        generated.2) : PMF _)) := by
  unfold FtsBankSpec.recordedExperiment
  simp only [wct_source]
theorem wct_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpec hacc hle horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec hacc hle horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec hacc hle horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wct_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpec hacc hle horizon rate hexc).potential budget st :=
  (wctSpec hacc hle horizon rate hexc).potential_win budget st halive hcount h
theorem wct_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpec hacc hle horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpec hacc hle horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec hacc hle horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec hacc hle horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
end ClaudeWCT.Bank.WCT
end

section



namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChild buildCoordinate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section allowed
variable (Q : T3.Spec.Domain → Prop) (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak))) (hnonce : ∀ message, Q (.inr (.inr (.inl message))))
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) Q := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => SourceQueries.shortHash_allowed Q hpublic _) _
include hpublic hpair in
theorem buildChild_allowed (index coord selected : Nat) (word : Rank) :
    AllQueriesSatisfy (buildChild index coord selected word) Q := by
  unfold buildChild
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state pair
    apply SourceQueries.bind_allowed _ (SourceQueries.privatePair_allowed Q hpair _ _ _ _ _)
    intro seeds
    apply SourceQueries.foldlM_allowed
    intro state half
    split
    · apply SourceQueries.bind_allowed _ (chain_allowed Q hpublic _ _ _ _ _ _ _)
      intro value
      apply SourceQueries.bind_allowed _ (chain_allowed Q hpublic _ _ _ _ _ _ _)
      intro _
      exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
  · intro state
    unfold WCT9.leafHash
    exact SourceQueries.bind_allowed _ (SourceQueries.shortHash_allowed Q hpublic _)
      fun _ => SourceQueries.pure_allowed _ _
include hpublic hpair hnonce in
theorem buildCoordinate_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) Q := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChild_allowed Q hpublic hpair _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · apply SourceQueries.foldlM_allowed
      intro nodes heap
      exact SourceQueries.bind_allowed _ (SourceQueries.nodeHash_allowed Q hpublic hpair hnonce _ _ _ _ _ _)
        fun _ => SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
include hpublic hpair hnonce in
theorem payAfterDigest_allowed (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q := by
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinate_allowed Q hpublic hpair hnonce _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    unfold WCT9.forestPk
    apply SourceQueries.bind_allowed _ (SourceQueries.shortHash_allowed Q hpublic _)
    intro root
    apply SourceQueries.bind_allowed _ (SourceQueries.signLayers_allowed Q hpublic hpair hnonce _ _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end allowed
theorem wct_payHashOnly : PayHashOnly payAfterDigest :=
  payAfterDigest_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
theorem wct_payRho : PayRho payAfterDigest WCT9.Signature.rho := by
  intro A cache rho output σ h
  unfold payAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
variable (hacc : AcceptedProposalUniform) (hle : AcceptanceBound) (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
theorem wct_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpec hacc hle horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpec hacc hle horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
end ClaudeWCT.Bank.WCT
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bpors_payHashOnly : PayHashOnly payloadAfterDigest := by
  intro cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(SourceQueries.pure_allowed Security.SourceReplay.IsHash),
      (SourceQueries.bind_allowed Security.SourceReplay.IsHash),
      (SourceQueries.foldlM_allowed Security.SourceReplay.IsHash),
      (SourceQueries.map_allowed Security.SourceReplay.IsHash),
      (SourceQueries.buildFts_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.forestPk_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.signLayers_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial))])
theorem bpors_payRho : PayRho payloadAfterDigest Signature.rho :=
  CaseC.eval_payloadAfterDigest_rho
end ClaudeWCT.Bank.BPORSRegression
end

section




namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctRev3 : DecidableEq T3.Cache := Classical.decEq _
theorem signPayloadWith_factor (limit : Nat) (cache : T3.Cache) (message : Message) :
    WCT9.signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 limit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayloadWith
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem rev3_signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) :=
  signPayloadWith_factor WCT9.digestAttemptLimit cache message
theorem payloadRecordL_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
    (hadm : S.admissible = WCT9.admissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayloadWith S.limit cache message := by
  rw [signPayloadWith_factor]
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S.toFtsBankSpec hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
noncomputable def wctSpecL (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpecL WProposal :=
  (wctSpec' horizon rate hexc).atLimit WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
@[simp] theorem wctSpecL_limit : (wctSpecL horizon rate hexc).limit = WCT9.digestAttemptLimit := rfl
theorem wctSpecL_admissible : (wctSpecL horizon rate hexc).admissible = WCT9.admissible := rfl
@[simp] theorem wctSpecL_horizon : (wctSpecL horizon rate hexc).horizon = horizon := rfl
noncomputable def rev3AuthenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.Rev3.signPayload request.cache request.message else pure none
theorem wctL_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpecL horizon rate hexc).authenticatedRecord payAfterDigest published request =
      rev3AuthenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord rev3AuthenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecordL_erasure _ rfl _ _
  · rfl
theorem excess_of_excessBound (h : ExcessBound horizon rate) :
    uniformWordAverage (wctSpecL horizon rate hexc).horizon
      (fun W : List WProposal => (wctSpecL horizon rate hexc).price W - CaseC.theta) ≤ rate := h
theorem wctL_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpecL horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wctL_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).potential budget st :=
  (wctSpecL horizon rate hexc).potential_win budget st halive hcount h
theorem wctL_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpecL horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpecL horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
theorem wctL_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpecL horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpecL horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
theorem wctL_search (rho : Digest) (m : Message) :
    (wctSpecL horizon rate hexc).search rho m 0 (wctSpecL horizon rate hexc).limit =
      WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit :=
  (wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl rho m _ 0).symm
end ClaudeWCT.Bank.WCT
end
