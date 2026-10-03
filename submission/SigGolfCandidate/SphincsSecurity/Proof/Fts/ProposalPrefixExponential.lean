import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalProposalExecution
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TerminalProposalWord
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateGame
import Mathlib.Analysis.Complex.ExponentialBounds

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem originalProposalImpl_complete {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    ((originalProposalImpl key spent enabled update input).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  simp only [originalProposalImpl, proposalRecordImpl, StateT.run_mk]
  by_cases hactive : originalProposalActive key spent enabled input state.2 = true
  · rw [if_pos hactive, PMF.bind_map]
    cases input with
    | inl world => simp only [originalProposalActive, Bool.false_eq_true] at hactive
    | inr message =>
        have hcache : ProposalCacheBound key state.2.1 (spent state.2) := by
          by_contra hcache
          simp [originalProposalActive, hcache] at hactive
        rw [originalRejectedProposal, dif_pos hcache]
        simpa only [cappedRecordProposalBridge, List.append_assoc, Function.comp_def] using
          complete_cappedRecordProposalBridge_prefix (PMF.uniformOfFintype Index)
            (originalProposalRecord key (.inr message) state.2.1) (fun record => record.index)
            targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one
            (originalProposalRecord_cap key message state.2.1 (spent state.2) hcache) total state.1
  · rw [if_neg hactive, PMF.bind_map]
    simp only [Function.comp_def]
    exact PMF.bind_const _ _
theorem simulateQ_originalProposalImpl_complete {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    ((simulateQ (originalProposalImpl key spent enabled update) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
      simp_rw [ih]
      exact originalProposalImpl_complete key spent enabled update total input state
noncomputable def terminalProposalPotential {α : Type} (base : PMF α) (total : Nat)
    (payoff : List α → ENNReal) (consumed : List α) : ENNReal :=
  ∑' word, Pr[= word | completeProposalWord base total consumed] * payoff word
theorem expected_originalProposalImpl_terminalPotential {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × (QueryCache HashSpec × μ)) :
    (∑' result, Pr[= result | (originalProposalImpl key spent enabled update input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (originalProposalImpl_complete key spent enabled update total input state)
  rw [← PMF.monad_bind_eq_bind, tsum_probOutput_bind_mul] at h
  exact h
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem simulateQ_certificateProposalImpl_complete {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (total : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 :=
  simulateQ_originalProposalImpl_complete key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total computation state
theorem expected_certificateProposalImpl_terminalPotential (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 :=
  expected_originalProposalImpl_terminalPotential key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total payoff input state
theorem certificateGame_complete (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateGame adversary budget required stopAfter stopped).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.bind_bind]
  simp_rw [simulateQ_certificateProposalImpl_complete, completeProposalWord_nil]
  exact PMF.bind_const _ _
noncomputable def certificateTerminalGame (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    PMF (CertificateGameResult × List Index) :=
  (certificateGame adversary budget required stopAfter stopped).bind fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (fun word => (result, word))
theorem certificateTerminalGame_game (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.fst =
      certificateGame adversary budget required stopAfter stopped := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (Function.const _ result)) = _
  simp only [PMF.map_const, PMF.bind_pure]
theorem certificateTerminalGame_word (adversary : Adversary) (budget : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.snd =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map id) = _
  simp only [PMF.map_id]
  exact certificateGame_complete adversary budget required stopAfter stopped total
theorem certificateTerminalGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset IndexGroup)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult × List Index)
    (hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support) :
    result.1.2.2.2.spent ≤ q ∧ result.1.2.2.2.creationMass ≤ q := by
  have hm := (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨result, hr, rfl⟩
  rw [certificateTerminalGame_game] at hm
  exact certificateGame_cost_le adversary q required stopAfter stopped hbound result.1 hm
theorem expected_certificateTerminalGame_mass_payoff_le (adversary : Adversary) (q : Nat)
    (required : Finset IndexGroup) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
        (result.1.2.2.2.creationMass * payoff result.2)) ≤
      (q : ENNReal) * ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff word := by
  have hword := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (certificateTerminalGame_word adversary q required stopAfter stopped total)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hword
  calc
    _ ≤ ∑' result, (q : ENNReal) *
        (Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] * payoff result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hzero : Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] = 0
      · rw [hzero, zero_mul, zero_mul, mul_zero]
      · have hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support := by
          simpa only [PMF.mem_support_iff, PMF.probOutput_eq_apply] using hzero
        have hmass := (certificateTerminalGame_cost_le adversary q required stopAfter stopped total hbound result hr).2
        calc
          _ ≤ Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
              ((q : ENNReal) * payoff result.2) := mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)
          _ = _ := by ring
    _ = _ := by rw [ENNReal.tsum_mul_left, hword]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def proposalPrefixStop : CertificateStopRule :=
  fun input state length record => decide (
    targetProposalOverhead * (state.2.log ++ signingLogFragment input record.output).length + (proposalPrefixSlack : ENNReal) <
      ((state.2.proposals + length : Nat) : ENNReal))
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
def ProposalPrefixExceptional (proposals completed : Nat) : Prop :=
  targetProposalOverhead * completed + (proposalPrefixSlack : ENNReal) < (proposals : ENNReal)
theorem proposalPrefixStop_eq_after_exception (key : SecretKey) (budget : Nat)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    proposalPrefixStop input state length record =
      decide (ProposalPrefixExceptional
        (certificateMonitorUpdate key budget required stopAfter input state length record).proposals
        (certificateMonitorUpdate key budget required stopAfter input state length record).log.length) := by
  simp only [proposalPrefixStop, ProposalPrefixExceptional, certificateMonitorUpdate, if_pos hactive,
    proposalRecordLogState]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp ENNReal
noncomputable def proposalTailBase : ENNReal := 1025 / 1024
noncomputable def proposalTailMoment : ENNReal := 6885376000 / 6865219987
theorem proposalBlockLength_power_moment (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (base : ENNReal) :
    (∑' length, proposalBlockLength accept hpos hle length * base ^ length) =
      accept * base / (1 - (1 - accept) * base) := by
  rw [tsum_eq_zero_add' ENNReal.summable, proposalBlockLength_zero, zero_mul, zero_add]
  simp only [proposalBlockLength_succ, pow_succ]
  calc
    _ = ∑' failures, (accept * base) * ((1 - accept) * base) ^ failures := by
      apply tsum_congr
      intro failures
      rw [mul_pow]
      ac_rfl
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; rfl
theorem proposalTailMoment_eq : proposalTailMoment =
    targetProposalAcceptance * proposalTailBase ^ 2 / (1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2) := by
  have hrem : (1 - targetProposalAcceptance).toReal = 1 - targetProposalAcceptance.toReal := by
    rw [ENNReal.toReal_sub_of_le targetProposalAcceptance_lt_one.le (by finiteness), ENNReal.toReal_one]
  have hlt : (1 - targetProposalAcceptance) * proposalTailBase ^ 2 < 1 := by
    apply (ENNReal.toReal_lt_toReal (by unfold proposalTailBase; finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, hrem]
    norm_num [ENNReal.toReal_pow, targetProposalAcceptance, targetProposalOverhead,
      proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hnz : 1 - (1 - targetProposalAcceptance) * proposalTailBase ^ 2 ≠ 0 := (tsub_pos_iff_lt.mpr hlt).ne'
  have haccept : targetProposalAcceptance ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) targetProposalAcceptance_lt_one.le
  apply (ENNReal.toReal_eq_toReal_iff' (by unfold proposalTailMoment; finiteness)
    (ENNReal.div_ne_top (ENNReal.mul_ne_top haccept (by unfold proposalTailBase; finiteness)) hnz)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le hlt.le (by finiteness)]
  simp only [ENNReal.toReal_mul, hrem]
  norm_num [proposalTailMoment, ENNReal.toReal_pow, targetProposalAcceptance,
    targetProposalOverhead, proposalTailBase, ENNReal.toReal_inv, ENNReal.toReal_div]
theorem proposalTailMoment_ge_cube : proposalTailBase ^ 3 ≤ proposalTailMoment := by
  apply (ENNReal.toReal_le_toReal (by unfold proposalTailBase; finiteness) (by unfold proposalTailMoment; finiteness)).mp
  norm_num [proposalTailBase, proposalTailMoment, ENNReal.toReal_pow, ENNReal.toReal_div]
theorem proposalTailBase_one_le : 1 ≤ proposalTailBase := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold proposalTailBase; finiteness)).mp
  norm_num [proposalTailBase, ENNReal.toReal_div]
noncomputable def proposalPrefixWeight (proposals completed : Nat) : ENNReal :=
  proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - completed) /
    proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack)
theorem proposalPrefixWeight_bad (proposals completed : Nat) (hcap : completed ≤ signatureLimit)
    (hbad : ProposalPrefixExceptional proposals completed) : 1 ≤ proposalPrefixWeight proposals completed := by
  have hcount : 3 * completed + 2 * proposalPrefixSlack ≤ 2 * proposals := by
    have h := (ENNReal.toReal_lt_toReal (by unfold targetProposalOverhead; finiteness) (by finiteness)).mpr hbad
    rw [ENNReal.toReal_add (by unfold targetProposalOverhead; finiteness) (by finiteness), ENNReal.toReal_mul] at h
    norm_num [targetProposalOverhead, ENNReal.toReal_div] at h
    have hc : (0 : ℝ) ≤ completed := Nat.cast_nonneg _
    have h' : (3 : ℝ) * completed + 2 * proposalPrefixSlack ≤ 2 * proposals := by linarith
    exact_mod_cast h'
  have hexp : 3 * signatureLimit + 2 * proposalPrefixSlack ≤ 2 * proposals + 3 * (signatureLimit - completed) := by omega
  have hbase : proposalTailBase ≠ 0 := by norm_num [proposalTailBase]
  have hfinite : proposalTailBase ≠ ⊤ := by unfold proposalTailBase; finiteness
  rw [proposalPrefixWeight]
  calc
    1 = proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack) /
        proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack) := (ENNReal.div_self (pow_ne_zero _ hbase) (by finiteness)).symm
    _ ≤ _ := ENNReal.div_le_div_right (calc
      _ ≤ proposalTailBase ^ (2 * proposals + 3 * (signatureLimit - completed)) :=
        pow_le_pow_right₀ proposalTailBase_one_le hexp
      _ = proposalTailBase ^ (2 * proposals) * (proposalTailBase ^ 3) ^ (signatureLimit - completed) := by simp only [pow_add, pow_mul]
      _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left₀ (by positivity) proposalTailMoment_ge_cube _)) _
theorem expected_proposalPrefixWeight (proposals completed : Nat) (hcap : completed < signatureLimit) :
    (∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
      proposalPrefixWeight (proposals + length) (completed + 1)) = proposalPrefixWeight proposals completed := by
  have hremaining : signatureLimit - completed = (signatureLimit - (completed + 1)) + 1 := by omega
  simp only [proposalPrefixWeight, Nat.mul_add]
  calc
    _ = (proposalTailBase ^ (2 * proposals) * proposalTailMoment ^ (signatureLimit - (completed + 1)) /
        proposalTailBase ^ (3 * signatureLimit + 2 * proposalPrefixSlack)) *
        ∑' length, proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le length *
          (proposalTailBase ^ 2) ^ length := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro length
      simp only [pow_add, pow_mul, div_eq_mul_inv]
      ac_rfl
    _ = _ := by
      rw [proposalBlockLength_power_moment, ← proposalTailMoment_eq, hremaining]
      simp only [pow_add, pow_one, div_eq_mul_inv]
      ac_rfl
theorem proposalPrefixWeight_initial_le : proposalPrefixWeight 0 0 ≤ proposalPrefixExceptionBound := by
  rw [proposalPrefixExceptionBound_def]
  let z : ℝ := 1025 / 1024
  let ratio : ℝ := 35184372088832 / 35184252433375
  have hz : 0 < z := by norm_num [z]
  have hr : 0 < ratio := by norm_num [ratio]
  have hlog : (signatureLimit : ℝ) * Real.log ratio - 2 * 2 ^ 23 * Real.log z ≤ -700 * Real.log 2 := by
    have hratio := Real.log_le_sub_one_of_pos hr
    have hbase := Real.one_sub_inv_le_log_of_pos hz
    have htwo := Real.log_two_lt_d9
    norm_num [ratio, z, signatureLimit] at hratio hbase ⊢
    linarith
  have hreal : (ratio * z ^ 3) ^ signatureLimit / z ^ (3 * signatureLimit + 2 * 2 ^ 23) ≤ (2 ^ 700 : ℝ)⁻¹ := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hr.ne' (by positivity),
      Real.log_pow, Real.log_pow, Real.log_inv, Real.log_pow]
    push_cast
    nlinarith only [hlog]
  have hmoment : proposalTailMoment.toReal = ratio * z ^ 3 := by
    norm_num [proposalTailMoment, ENNReal.toReal_div, ratio, z]
  have hbase : proposalTailBase.toReal = z := by norm_num [proposalTailBase, ENNReal.toReal_div, z]
  have hfinite : proposalPrefixWeight 0 0 ≠ ⊤ := by
    unfold proposalPrefixWeight
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by unfold proposalTailBase; finiteness))
        (ENNReal.pow_ne_top (by unfold proposalTailMoment; finiteness))
    · exact pow_ne_zero _ (by norm_num [proposalTailBase])
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  simpa only [proposalPrefixWeight, proposalPrefixSlack_def, Nat.mul_zero, pow_zero, one_mul, Nat.sub_zero, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, hmoment, hbase] using hreal
end SphincsSecurity.Concrete
end
