import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.CreationSharedLaw
import SigGolfCandidate.ClaudeWCT.Bank.GameBank
import SigGolfCandidate.ClaudeWCT.Bank.WCTRev3

section


namespace ClaudeWCT.W9.T3.Security.CreationGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CreationGame (publicClass prefixCount prefixCount_eq_classCharge)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem completed_trace_expectation (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2^127) (payoff : PaddedGame.TraceResult → ENNReal) :
    expectedValue (SeccLaw.completedExperiment adversary budget hbudget) (fun z => payoff z.1) =
      expectedValue (PaddedGame.tracedExperiment adversary budget hbudget) payoff := by
  unfold SeccLaw.completedExperiment
  rw [← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext result
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  exact expectedValue_const (mx := PMF.uniformOfFintype SigGolfCandidate.T3.Security.SeccLaw.CompletionTables)
    (by simp) (payoff result)
theorem expectedClassCount_eq_shared (cls : SigGolfCandidate.T3.Spec.Domain → Prop)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedClassCount cls adversary budget hbudget =
      SeccLaw.expectedCharge adversary budget hbudget (fun _ => cls) := by
  rw [expectedClassCount, ← completed_trace_expectation]
  unfold SeccLaw.expectedCharge expectedValue
  apply tsum_congr
  intro z
  rw [PMF.probOutput_eq_apply]
  congr 1
  change (prefixCount cls budget z.1.2.2.events : ENNReal) =
    (SigGolfCandidate.T3.Security.SeccLaw.classCharge cls budget z.1.2.2.events : ENNReal)
  exact_mod_cast prefixCount_eq_classCharge cls budget z.1.2.2.events
theorem expectedBirths_le_shared (cls : HashInput → Prop)
    (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2^127) :
    expectedBirths cls adversary budget hbudget ≤
      SeccLaw.expectedCharge adversary budget hbudget (fun _ => publicClass cls) := by
  rw [← expectedClassCount_eq_shared]
  exact expectedBirths_le_classCount cls adversary budget hbudget
end ClaudeWCT.W9.T3.Security.CreationGame
end

section


namespace ClaudeWCT.W9.T3.Security.BankLink
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open ClaudeWCT.Bank (FtsBankSpec birthWeight)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option Signature))
def RecordMatches : Prop :=
  ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    FullGame.authenticatedSign published request
theorem source_eq (hrecord : RecordMatches S pay) (published : SigGolfCandidate.T3.Cache) :
    S.source pay published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact hrecord published request
theorem recordedExperiment_eq (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      S.recordedExperiment pay (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpec.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [source_eq S pay hrecord]
  exact ht
theorem birthWeight_eq (budget : Nat) (input : LazyPrivate.Interaction.Domain)
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
theorem expectedBirths_eq (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    S.expectedBirths pay (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpec.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (S.recordedImpl pay generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← source_eq S pay hrecord]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact birthWeight_eq budget input state
theorem expectedBirths_le_shared (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    S.expectedBirths pay (CreationGame.rest adversary) budget ≤
      SeccLaw.expectedCharge adversary budget hbudget
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) := by
  rw [expectedBirths_eq S pay hrecord adversary budget hbudget]
  exact CreationGame.expectedBirths_le_shared CaseC.IsDigestInput adversary budget hbudget
end ClaudeWCT.W9.T3.Security.BankLink
end

section


namespace ClaudeWCT.W9.T3.Security.BankLinkL
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open ClaudeWCT.Bank (FtsBankSpecL birthWeight)
open ClaudeWCT.Bank.WCT (WProposal ExcessBound wctSpecL payAfterDigest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section generic
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
  (pay : SigGolfCandidate.T3.Cache → Digest → HashOutput → M (Option Signature))
def RecordMatches : Prop :=
  ∀ published request, Prod.fst <$> S.authenticatedRecord pay published request =
    FullGame.authenticatedSign published request
theorem source_eq (hrecord : RecordMatches S pay) (published : SigGolfCandidate.T3.Cache) :
    S.source pay published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact hrecord published request
theorem recordedExperiment_eq (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      S.recordedExperiment pay (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpecL.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [source_eq S pay hrecord]
  exact ht
theorem expectedBirths_eq (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    S.expectedBirths pay (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpecL.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (S.recordedImpl pay generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← source_eq S pay hrecord]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact BankLink.birthWeight_eq budget input state
theorem expectedBirths_le_shared (hrecord : RecordMatches S pay) (adversary : AdversaryP) (budget : Nat)
    (hbudget : budget ≤ 2 ^ 127) :
    S.expectedBirths pay (CreationGame.rest adversary) budget ≤
      SeccLaw.expectedCharge adversary budget hbudget
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) := by
  rw [expectedBirths_eq S pay hrecord adversary budget hbudget]
  exact CreationGame.expectedBirths_le_shared CaseC.IsDigestInput adversary budget hbudget
end generic
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
theorem wct_recordMatches : RecordMatches (wctSpecL horizon rate hexc) payAfterDigest :=
  fun published request => ClaudeWCT.Bank.WCT.wctL_record_erasure horizon rate hexc published request
theorem wct_source (published : SigGolfCandidate.T3.Cache) :
    (wctSpecL horizon rate hexc).source payAfterDigest published = MonitoredPrivate.interactionSource published :=
  source_eq _ _ (wct_recordMatches horizon rate hexc) published
theorem wct_recordedExperiment_eq (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      (wctSpecL horizon rate hexc).recordedExperiment payAfterDigest (CreationGame.rest adversary) :=
  recordedExperiment_eq _ _ (wct_recordMatches horizon rate hexc) adversary budget hbudget
theorem wct_expectedBirths_eq (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (wctSpecL horizon rate hexc).expectedBirths payAfterDigest (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget :=
  expectedBirths_eq _ _ (wct_recordMatches horizon rate hexc) adversary budget hbudget
theorem wct_expectedBirths_le_shared (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (wctSpecL horizon rate hexc).expectedBirths payAfterDigest (CreationGame.rest adversary) budget ≤
      SeccLaw.expectedCharge adversary budget hbudget
        (fun _ => SigGolfCandidate.T3.Security.CreationGame.publicClass CaseC.IsDigestInput) :=
  expectedBirths_le_shared _ _ (wct_recordMatches horizon rate hexc) adversary budget hbudget
end ClaudeWCT.W9.T3.Security.BankLinkL
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (theta IsDigestInput countOf lazyOf)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open ClaudeWCT.Bank (FtsBankSpecL Ghost Interaction')
open ClaudeWCT.Bank.WCT (WProposal ExcessBound wctSpecL payAfterDigest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def horizon : Nat := 2 ^ 32
theorem horizon_eq : horizon = 4294967296 := by norm_num [horizon]
theorem excessBound_top : ExcessBound horizon ⊤ := le_top
noncomputable def bankSpec : FtsBankSpecL WProposal := wctSpecL horizon ⊤ excessBound_top
@[simp] theorem bankSpec_horizon : bankSpec.horizon = horizon := rfl
@[simp] theorem bankSpec_limit : bankSpec.limit = WCT9.digestAttemptLimit := rfl
theorem bankSpec_admissible : bankSpec.admissible = WCT9.admissible := rfl
abbrev BankState := ClaudeWCT.Bank.BankState Signature
noncomputable def bankImpl (published : SigGolfCandidate.T3.Cache) (budget : Nat) :
    QueryImpl (Interaction' Signature) (StateT BankState PMF) :=
  bankSpec.bankImpl payAfterDigest published budget
noncomputable def bankExperiment (adversary : AdversaryP) (budget : Nat) : PMF (Bool × BankState) :=
  bankSpec.bankExperiment payAfterDigest (CreationGame.rest adversary) budget
noncomputable def potential (budget : Nat) (st : BankState) : ENNReal := bankSpec.potential budget st
def BankInv (published : SigGolfCandidate.T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (st : BankState) : Prop :=
  bankSpec.BankInv payAfterDigest WCT9.Signature.rho published budget kg st
theorem bankExperiment_eq (adversary : AdversaryP) (budget : Nat) :
    bankExperiment adversary budget = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (simulateQ (bankImpl generated.1.2 budget) (CreationGame.rest adversary generated.1.1 generated.1.2)).run
        (Ghost.empty, generated.2)) := rfl
theorem source_eq (published : SigGolfCandidate.T3.Cache) :
    bankSpec.source payAfterDigest published = MonitoredPrivate.interactionSource published :=
  BankLinkL.wct_source horizon ⊤ excessBound_top published
theorem bank_project {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState) :
    Prod.map id Prod.snd <$> (simulateQ (bankImpl published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  rw [← source_eq]
  exact bankSpec.bank_project payAfterDigest published budget program st
theorem bank_traced (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : Bool × BankState => (r.1, r.2.2)) <$> bankExperiment adversary budget =
      (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget :=
  (bankSpec.bank_experiment_project payAfterDigest (CreationGame.rest adversary) budget).trans
    (BankLinkL.wct_recordedExperiment_eq horizon ⊤ excessBound_top adversary budget hbudget).symm
theorem bankInv_run {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState) (hinv : BankInv published budget kg st)
    (r : α × BankState) (hr : r ∈ ((simulateQ (bankImpl published budget) program).run st).support) :
    BankInv published budget kg r.2 :=
  bankSpec.bankInv_run payAfterDigest WCT9.Signature.rho ClaudeWCT.Bank.WCT.wct_payHashOnly
    ClaudeWCT.Bank.WCT.wct_payRho ClaudeWCT.Bank.WCT.wct_payAvoids published budget kg program st hinv r hr
theorem bankInv_initial (published : SigGolfCandidate.T3.Cache) (budget : Nat)
    (generated : (Digest × SigGolfCandidate.T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    BankInv published budget generated.2.events (Ghost.empty, generated.2) :=
  bankSpec.bankInv_initial payAfterDigest WCT9.Signature.rho published budget generated hg
theorem bank_potential_le (rate : ENNReal) (hexc : ExcessBound horizon rate) (adversary : AdversaryP)
    (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bankExperiment adversary budget) (fun r => potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  rw [← BankLinkL.wct_expectedBirths_eq horizon ⊤ excessBound_top adversary budget hbudget]
  exact bankSpec.bank_potential_le_rate payAfterDigest ClaudeWCT.Bank.WCT.wct_payNotDigest
    ClaudeWCT.Bank.WCT.wct_payAvoids (CreationGame.rest adversary) budget rate hexc
end ClaudeWCT.W9.T3.Security.CaseC
end
