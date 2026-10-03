import SigGolfCandidate.ClaudeWCT.Bank.Spec
import SigGolfCandidate.T3.Secc.CaseCSearch
import SigGolfCandidate.T3.Secc.CaseCBankReuse
import SigGolfCandidate.T3.Secc.CaseCBankStep

section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def forecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord S.accepted R) (fun F => S.score (X ++ F) N)
theorem forecast_zero (X : List HashOutput) (N : HashOutput) : S.forecast 0 X N = S.score X N := by
  unfold forecast
  change expectedValue (pure [] : PMF (List HashOutput)) _ = _
  rw [expectedValue_pure, List.append_nil]
theorem forecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue S.accepted (fun A => S.forecast R (X ++ [A]) N) = S.forecast (R + 1) X N := by
  unfold forecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem score_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    S.score X N ≤ S.forecast R X N := by
  unfold forecast
  calc
    S.score X N = expectedValue (independentProposalWord S.accepted R) (fun _ => S.score X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => S.score_append_mono X F N
theorem expected_word_proposals (R : Nat) (g : List P → ENNReal) :
    expectedValue (independentProposalWord S.accepted R) (fun F => g (S.proposals F)) = uniformWordAverage R g := by
  induction R generalizing g with
  | zero =>
      change expectedValue (pure [] : PMF (List HashOutput)) _ = _
      rw [expectedValue_pure]
      simp [uniformWordAverage, SphincsSecurity.Concrete.sampleUniformProposalWord, proposals]
  | succ R ih =>
      rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind, BPORS.uniformWordAverage_succ]
      have hstep (A : HashOutput) : expectedValue ((independentProposalWord S.accepted R).map (A :: ·))
          (fun F => g (S.proposals F)) = uniformWordAverage R (fun W => g (S.proposal A :: W)) := by
        rw [← PMF.monad_map_eq_map, expectedValue_map]
        exact ih (fun W => g (S.proposal A :: W))
      simp_rw [hstep]
      exact S.expected_accepted_proposal (fun p => uniformWordAverage R (fun W => g (p :: W)))
theorem average_forecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) =
      uniformWordAverage R (fun W => S.price (S.proposals X ++ W)) / 2 ^ 128 := by
  unfold forecast
  rw [CaseC.finiteAverage_expectedValue]
  have hav : ∀ F : List HashOutput, BPORS.finiteAverage (fun N : HashOutput => S.score (X ++ F) N) =
      S.price (S.proposals X ++ S.proposals F) / 2 ^ 128 := by
    intro F
    rw [S.average_score, ← S.proposals_append]
    rfl
  simp_rw [hav]
  refine (S.expected_word_proposals R (fun W => S.price (S.proposals X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => S.price (S.proposals X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * S.price (S.proposals X ++ W) by
    funext W; exact mul_comm _ _, SphincsSecurity.Concrete.uniformWordAverage_mul_left, mul_comm]
noncomputable def excessForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  uniformWordAverage R (fun W => S.price (S.proposals X ++ W) - CaseC.theta)
theorem excessForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue S.accepted (fun A => S.excessForecast R (X ++ [A])) = S.excessForecast (R + 1) X := by
  unfold excessForecast
  rw [BPORS.uniformWordAverage_succ]
  have hA (A : HashOutput) : uniformWordAverage R
      (fun W => S.price (S.proposals (X ++ [A]) ++ W) - CaseC.theta) =
      (fun p : P => uniformWordAverage R
        (fun W => S.price (S.proposals X ++ p :: W) - CaseC.theta)) (S.proposal A) := by
    simp [proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact S.expected_accepted_proposal (fun p => uniformWordAverage R
    (fun W => S.price (S.proposals X ++ p :: W) - CaseC.theta))
theorem average_forecast_le (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => S.forecast R X N) ≤
      (CaseC.theta + S.excessForecast R X) / 2 ^ 128 := by
  rw [average_forecast]
  apply ENNReal.div_le_div_right
  unfold excessForecast
  calc
    _ ≤ uniformWordAverage R (fun W => CaseC.theta + (S.price (S.proposals X ++ W) - CaseC.theta)) :=
      SphincsSecurity.Concrete.uniformWordAverage_mono R fun W => le_add_tsub
    _ = _ := by
      rw [SphincsSecurity.Concrete.uniformWordAverage_add, BPORS.History.uniformWordAverage_constant]
theorem excessForecast_initial : S.excessForecast S.horizon [] ≤ S.excessRate := by
  unfold excessForecast
  simpa [proposals] using S.excess_le
end FtsBankSpec
end ClaudeWCT.Bank
end

section



namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
def search (rho : Digest) (message : Message) (counter fuel : Nat) : M (Option (BitVec 32 × HashOutput)) :=
  Sampling.publicProgram (searchLoop (Sampling.digestTrial rho message) S.decode
    (fun c output => pure (BitVec.ofNat 32 c, output)) fuel counter)
theorem step_le (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P') :
    Sampling.acceptedWeight S.decode w + failMass S.decode * P' ≤ P' := by
  calc
    _ = S.acceptance * S.freshPrice w + (1 - S.acceptance) * P' := by
      have hw : Sampling.acceptedWeight S.decode w = S.acceptance * S.freshPrice w := by
        unfold freshPrice
        rw [div_eq_mul_inv, mul_comm, mul_assoc, ENNReal.inv_mul_cancel S.acceptance_ne_zero S.acceptance_ne_top,
          mul_one]
      rw [S.failMass_decode, hw]
    _ ≤ S.acceptance * P' + (1 - S.acceptance) * P' := add_le_add (mul_le_mul' le_rfl hP) le_rfl
    _ = P' := by rw [← add_mul, add_tsub_cancel_of_le S.acceptance_le_one, one_mul]
theorem search_le_price (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) S.decode 0 (2 ^ 32) cache)
    (w : HashOutput → ENNReal) (base P' : ENNReal) (hbase : base ≤ P') (hP : S.freshPrice w ≤ P') :
    expectedValue (Sampling.roRun secret (S.search rho message 0 fuel) cache)
      (fun result => result.1.elim base (fun found => w found.2)) ≤ P' := by
  exact CaseC.search_le_price secret (Sampling.digestTrial rho message) S.decode
    (fun c output => (BitVec.ofNat 32 c, output)) (fun found => w found.2) w (fun _ _ => rfl) base P' hbase
    (S.step_le w P' hP) (2 ^ 32)
    (fun _ _ hl hr he => Sampling.digestTrial_injective rho message hl hr he) fuel 0 (by omega) cache hreject
def Reuse (cache : Sampling.RCache) (rho : Digest) (m : Message) : Prop :=
  ¬Sampling.CachedTrialsReject (Sampling.digestTrial rho m) S.decode 0 (2 ^ 32) cache
noncomputable def admissibleEntry (cache : Sampling.RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if S.admissible answer = true then 1 else 0)
noncomputable def reuseMass (cache : Sampling.RCache) (m : Message) : ENNReal :=
  (∑' p : Digest × Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128
theorem reuse_indicator_le (cache : Sampling.RCache) (rho : Digest) (m : Message) :
    (if S.Reuse cache rho m then (1 : ENNReal) else 0) ≤
      ∑ c : Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial rho m c.val) := by
  split_ifs with h
  · unfold Reuse Sampling.CachedTrialsReject at h
    push Not at h
    obtain ⟨c, -, hc, answer, ha, hd⟩ := h
    have hadm : S.admissible answer = true := by
      unfold decode at hd
      by_contra hn
      exact hd (by simp [hn])
    calc
      (1 : ENNReal) = S.admissibleEntry cache (Sampling.digestTrial rho m (⟨c, hc⟩ : Fin (2 ^ 32)).val) := by
        simp [admissibleEntry, ha, hadm]
      _ ≤ _ := Finset.single_le_sum (f := fun c : Fin (2 ^ 32) =>
          S.admissibleEntry cache (Sampling.digestTrial rho m c.val)) (fun _ _ => bot_le) (Finset.mem_univ _)
  · exact bot_le
theorem reuse_probability_le (cache : Sampling.RCache) (m : Message) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse cache rho m then 1 else 0) ≤
      S.reuseMass cache m := by
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage reuseMass
  simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  calc
    _ ≤ ∑ rho : Digest, ∑ c : Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial rho m c.val) :=
      Finset.sum_le_sum fun rho _ => S.reuse_indicator_le cache rho m
    _ = ∑' p : Digest × Fin (2 ^ 32), S.admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val) := by
      rw [tsum_fintype, Fintype.sum_prod_type]
noncomputable def admInd (a : HashOutput) : ENNReal := if S.admissible a = true then 1 else 0
theorem expected_admInd : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd = S.acceptance := by
  unfold admInd
  rw [expectedValue_ite_one]
  rfl
theorem expected_admInd_tight : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd ≤ 1 / 64 := by
  rw [expected_admInd]
  exact S.acceptance_le
theorem admissibleEntry_cacheQuery (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (y : HashInput) :
    S.admissibleEntry (cache.cacheQuery x a) y = S.admissibleEntry cache y + if y = x then S.admInd a else 0 := by
  by_cases hy : y = x
  · subst hy
    simp [admissibleEntry, hx, admInd]
  · simp [admissibleEntry, hy]
theorem reuseMass_cacheQuery_le (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (m : Message) :
    S.reuseMass (cache.cacheQuery x a) m ≤
      S.reuseMass cache m + (if CaseC.DigestRowOf x m then S.admInd a else 0) / 2 ^ 128 := by
  unfold reuseMass
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  simp_rw [S.admissibleEntry_cacheQuery cache x a hx]
  rw [ENNReal.tsum_add]
  apply add_le_add le_rfl
  by_cases hrow : CaseC.DigestRowOf x m
  · rw [if_pos hrow]
    apply CaseC.tsum_indicator_le_of_subsingleton
    intro p q hp hq
    exact Sampling.WeightedSelection.digest_nonce_trials_injective m (2 ^ 32) le_rfl (hp.trans hq.symm)
  · rw [if_neg hrow]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    rw [if_neg]
    intro he
    exact hrow ⟨p, he.symm⟩
end FtsBankSpec
end ClaudeWCT.Bank
end

section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open CaseC (BankCore BankCore.expose theta)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => S.forecast R X N).sum + (slack : ENNReal) * S.excessForecast R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    S.ledger R targets X (slack + 1) = S.ledger R targets X slack + S.excessForecast R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_slack_mono (R : Nat) (targets X : List HashOutput) {slack slack' : Nat} (h : slack ≤ slack') :
    S.ledger R targets X slack ≤ S.ledger R targets X slack' := by
  unfold ledger
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' _ le_rfl
  exact_mod_cast h
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => S.ledger R (targets ++ [a]) X slack) ≤
      S.ledger R targets X (slack + 1) + theta / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => S.forecast R X a) ≤
      (theta + S.excessForecast R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact S.average_forecast_le R X
  have hsplit : ∀ a, S.ledger R (targets ++ [a]) X slack = S.ledger R targets X slack + S.forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue S.accepted (fun A => S.ledger R targets (X ++ [A]) slack) = S.ledger (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, CaseC.expectedValue_list_sum']
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    exact S.forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * S.excessForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * S.excessForecast R (X ++ [A]) by
      funext A; ring]
    rw [CaseC.pmf_expectedValue_left_mul, S.excessForecast_step]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    S.freshPrice (fun A => S.ledger R targets (X ++ [A]) slack) = S.ledger (R + 1) targets X slack := by
  rw [← S.expected_accepted, ledger_expose]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) S.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (S.search rho message 0 fuel) cache)
      (fun result => result.1.elim (S.ledger (R + 1) targets X slack)
        (fun found => S.ledger R targets (X ++ [found.2]) slack)) ≤ S.ledger (R + 1) targets X slack :=
  S.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (S.ledger_freshPrice R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : S.admissible N = true) (hcov : S.covered X N) : 1 ≤ S.ledger R targets X slack :=
  calc
    (1 : ENNReal) ≤ S.score X N := S.one_le_score X N hadm hcov
    _ ≤ S.forecast R X N := S.score_le_forecast R X N
    _ ≤ (targets.map fun N => S.forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem ledger_initial (budget : Nat) :
    S.ledger S.horizon [] [] budget ≤ (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold ledger
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  exact mul_le_mul' le_rfl S.excessForecast_initial
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if S.horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else S.ledger (S.horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem corePotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    S.corePotential b' ≤ S.corePotential b := by
  unfold corePotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (S.ledger_slack_mono _ _ _ hs) hC
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + S.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => S.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      S.corePotential b + (theta + 1 / 64) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => S.admInd N / 2 ^ 128) ≤
      (1 / 64) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using S.expected_admInd_tight) le_rfl
  unfold corePotential
  simp only
  by_cases hd : S.horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => S.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (1 / 64) / 2 ^ 128 + (1 + b.reuse) :=
        (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        apply add_le_add le_rfl
        apply ENNReal.div_le_div_right
        exact le_add_self
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := S.horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (S.ledger R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => S.ledger R (b.targets ++ [N]) b.exposures s + S.admInd N / 2 ^ 128) + b.reuse :=
        CaseC.expectedValue_add_const_le _ _ _
      _ ≤ (S.ledger R b.targets b.exposures (s + 1) + theta / 2 ^ 128 + (1 / 64) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (S.ledger_birth R b.targets b.exposures s) hadm) le_rfl
      _ = _ := by
        rw [hs, ENNReal.add_div]
        ring
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + S.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if S.Reuse cache rho m then S.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => S.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ S.corePotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : S.horizon < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), S.corePotential (b.expose C' o) = 0 := by
      intro o
      unfold corePotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : S.corePotential b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), S.corePotential (b.expose C' o) ≤ 1 + b.reuse := by
      intro o
      unfold corePotential BankCore.expose
      simp only [hr, if_true]
      split_ifs
      · exact bot_le
      · exact add_le_add le_rfl (le_of_add_le_left hC)
    split_ifs
    · unfold corePotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
    · exact expectedValue_le_of_le _ fun result => hle _
  have hr' : b.reused = false := by simpa using hr
  set R0 := S.horizon - b.exposures.length with hR0
  have hb : S.corePotential b = S.ledger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬S.Reuse cache rho m →
      expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
        (fun result => S.corePotential (b.expose C' (result.1.map Prod.snd))) ≤
          S.ledger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) S.decode 0 (2 ^ 32) cache := by
      unfold Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < S.horizon
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (S.search rho m 0 fuel) cache)
            (fun result => result.1.elim (S.ledger (R + 1) b.targets b.exposures b.slack)
              (fun found => S.ledger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold corePotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold corePotential BankCore.expose
            have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
            have hnd : ¬S.horizon < (b.exposures ++ [found.2]).length := by omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show S.horizon - (b.exposures ++ [found.2]).length = R by omega]
        _ ≤ S.ledger (R + 1) b.targets b.exposures b.slack + C' :=
          (CaseC.expectedValue_add_const_le _ _ _).trans
            (add_le_add (S.ledger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold corePotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold corePotential BankCore.expose
        have hnd : S.horizon < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if S.Reuse cache rho m then 1 else 0) + (S.ledger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : S.Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold corePotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ S.reuseMass cache m + (S.ledger R0 b.targets b.exposures b.slack + C') :=
      (CaseC.expectedValue_add_const_le _ _ _).trans (add_le_add (S.reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (S.ledger _ _ _ _), ← add_assoc, add_comm (S.reuseMass cache m), add_comm _ (S.ledger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem core_win (b : BankCore) (halive : ¬S.horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, S.admissible N = true ∧ S.covered b.exposures N) :
    1 ≤ S.corePotential b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (S.ledger_win _ _ _ _ N hN hadm hcov).trans le_self_add
theorem core_initial (budget : Nat) :
    S.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold corePotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact S.ledger_initial budget
end FtsBankSpec
end ClaudeWCT.Bank
end

section


namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankKernel : DecidableEq T3.Cache := Classical.decEq _
def PayNotDigest {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) : Prop :=
  ∀ cache rho output, AllQueriesSatisfy (pay cache rho output) BPB.NotDigestQ
def PayAvoids {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) : Prop :=
  ∀ m cache rho output, NonceFreshness.Avoids m (pay cache rho output)
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
variable {Sig : Type}
def recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (rho : Digest)
    (message : Message) : M (Option Sig × Option HashOutput) := do
  let found ← S.search rho message 0 attemptLimit
  match found with
  | none => pure (none, none)
  | some (_, output) => do
      let signature ← pay cache rho output
      pure (signature, some output)
def payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (message : Message) :
    M (Option Sig × Option HashOutput) := do
  let rho ← privateNonce message
  S.recordForNonce pay cache rho message
noncomputable def authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) : M (Option Sig × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then S.payloadRecord pay request.cache request.message else pure (none, none)
theorem run_search (rho : Digest) (message : Message) (counter fuel : Nat) (state : LazyPrivate.State) :
    LazyPrivate.run (S.search rho message counter fuel) state =
      (fun result => (result.1, (state.1, result.2))) <$> Sampling.roRun 0 (S.search rho message counter fuel) state.2 := by
  rw [search, LazyPrivate.run_publicProgram, Sampling.roRun, Sampling.public_randomOracle]
theorem recordForNonce_le_search (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache)
    (rho : Digest) (message : Message) (state : LazyPrivate.State) (w : HashOutput → ENNReal) (base : ENNReal) :
    expectedValue (LazyPrivate.run (S.recordForNonce pay cache rho message) state)
      (fun result => result.1.2.elim base w) ≤
    expectedValue (Sampling.roRun 0 (S.search rho message 0 attemptLimit) state.2)
      (fun result => result.1.elim base (fun found => w found.2)) := by
  rw [recordForNonce, LazyPrivate.run_bind, expectedValue_bind, run_search, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [LazyPrivate.run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [LazyPrivate.run_bind, expectedValue_bind, LazyPrivate.run_pure, expectedValue_pure,
        Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem fresh_signing_kernel (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (state : LazyPrivate.State) (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P')
    (hF : ∀ result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state),
      F result ≤ if S.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P' w) :
    expectedValue (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state) F ≤
      P' + S.reuseMass state.2 m := by
  have hrun : LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state =
      LazyPrivate.run (privateMac published.region) state >>= fun mac =>
        LazyPrivate.run (S.payloadRecord pay published m) mac.2 := by
    rw [authenticatedRecord, LazyPrivate.run_bind]
    simp only [if_true]
  rw [hrun, expectedValue_bind]
  have hmac : ∀ mac ∈ support (LazyPrivate.run (privateMac published.region) state),
      expectedValue (LazyPrivate.run (S.payloadRecord pay published m) mac.2) F ≤ P' + S.reuseMass state.2 m := by
    intro mac hmac
    have hp := LazyPrivate.privateMac_preserves_nonce published.region m state mac hmac
    have hfresh1 : mac.2.1 (.inr (.inl m)) = none := hp.1.trans hfresh
    rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
    simp only [bind_assoc, pure_bind, expectedValue_bind]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
          (if S.Reuse state.2 (output.extractLsb' 0 128) m then 1 else 0) + P') := by
        apply expectedValue_mono
        intro output
        set s2 : LazyPrivate.State := (mac.2.1.cacheQuery (.inr (.inl m)) output, mac.2.2) with hs2
        have hsupp : ∀ result ∈ support (LazyPrivate.run
            (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2),
            F result ≤ if S.Reuse state.2 (output.extractLsb' 0 128) m then 1
              else result.1.2.elim P' w := by
          intro result hr
          have hmem : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩)
              state) := by
            rw [hrun, mem_support_bind_iff]
            refine ⟨mac, hmac, ?_⟩
            rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
            simp only [bind_assoc, pure_bind, mem_support_bind_iff]
            exact ⟨output, by simp, hr⟩
          have hn := CaseC.nonceOf_cacheQuery mac.2 m output result.2
            (SourceReplay.run_extends _ s2 result hr)
          have := hF result hmem
          rwa [hn] at this
        by_cases hreuse : S.Reuse state.2 (output.extractLsb' 0 128) m
        · refine le_trans (expectedValue_le_of_support (c := 1) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          · simp [hreuse]
        · refine le_trans (expectedValue_mono_of_support (h := fun result => result.1.2.elim P' w) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          calc
            expectedValue (LazyPrivate.run (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P' w) ≤
                expectedValue (Sampling.roRun 0 (S.search (output.extractLsb' 0 128) m 0 attemptLimit) s2.2)
                (fun result => result.1.elim P' (fun found => w found.2)) :=
              S.recordForNonce_le_search pay published _ m s2 w P'
            _ ≤ P' := by
              apply S.search_le_price 0 _ m attemptLimit (by decide) s2.2 _ w P' P' le_rfl hP
              have hc : s2.2 = state.2 := by rw [hs2]; exact hp.2
              rw [hc]
              exact not_not.mp hreuse
            _ ≤ _ := by simp [hreuse]
      _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse state.2 rho m then 1 else 0) + P' := by
        rw [expectedValue_add, expectedValue_const (by simp)]
        congr 1
        exact LazyPrivate.uniform_hash_low_expectation (fun rho => if S.Reuse state.2 rho m then 1 else 0)
      _ ≤ S.reuseMass state.2 m + P' := add_le_add (S.reuse_probability_le state.2 m) le_rfl
      _ = P' + S.reuseMass state.2 m := add_comm _ _
  exact expectedValue_le_of_support hmac
theorem search_allowed (rho : Digest) (m : Message) (Q : T3.Spec.Domain → Prop)
    (hQ : ∀ c, c < 2 ^ 32 → Q (.inl (.inr (Sampling.digestTrial rho m c)))) :
    ∀ fuel counter, counter + fuel ≤ 2 ^ 32 → AllQueriesSatisfy (S.search rho m counter fuel) Q := by
  intro fuel
  induction fuel with
  | zero => intro counter _; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter hlimit
      rw [search, Sampling.publicSearch_succ]
      apply SourceQueries.bind_allowed
      · exact (allQueriesSatisfy_query_iff _ _).mpr (hQ counter (by omega))
      · intro answer
        split
        · exact ih (counter + 1) (by omega)
        · exact SourceQueries.pure_allowed _ _
theorem privateMac_avoids (region : Region) (m : Message) : NonceFreshness.Avoids m (privateMac region) :=
  SourceQueries.privateMac_allowed _ (fun tweak h => by cases h) region
theorem authenticatedRecord_signerQ (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) :
    AllQueriesSatisfy (S.authenticatedRecord pay published request) (CaseC.SignerQ request.message) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · apply SourceQueries.privateMac_allowed (CaseC.SignerQ request.message)
    intro tweak x hx
    cases hx
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · unfold privateNonce
        apply SourceQueries.bind_allowed
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          intro x hx
          cases hx
        · intro _; exact SourceQueries.pure_allowed _ _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun c hc x hx _ => by
            simp only [Sum.inl.injEq, Sum.inr.injEq] at hx
            rw [← hx]
            exact CaseC.digestTrial_rowOf rho request.message c hc) attemptLimit 0 (by decide))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · apply SourceQueries.bind_allowed
          · exact CaseC.allQueriesSatisfy_mono _ _ _ (CaseC.notDigestQ_signerQ request.message) (hpay _ _ _)
          · intro _; exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
theorem signer_new_rows (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (before : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) before))
    (x : HashInput) (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) (hdig : CaseC.IsDigestInput x) :
    CaseC.DigestRowOf x request.message :=
  CaseC.run_new_public _ (fun x => CaseC.IsDigestInput x → CaseC.DigestRowOf x request.message)
    (CaseC.allQueriesSatisfy_mono _ _ _ (fun _ hq x hx => hq x hx)
      (S.authenticatedRecord_signerQ pay hpay published request))
    before result hr x hx hnew hdig
theorem authenticatedRecord_avoids (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (message : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache ≠ published ∨ request.message ≠ message) :
    NonceFreshness.Avoids message (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply NonceFreshness.avoids_bind message (privateMac_avoids _ message)
  intro tag
  split
  · rename_i hc
    have hm : request.message ≠ message := hrequest.resolve_left (fun h => h hc)
    unfold payloadRecord recordForNonce
    apply NonceFreshness.avoids_bind message
    · unfold privateNonce
      apply NonceFreshness.avoids_bind message
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        intro he
        apply hm
        unfold NonceFreshness.nonceQuery at he
        simp only [Sum.inr.injEq, Sum.inl.injEq] at he
        exact he
      · intro _; exact NonceFreshness.avoids_pure _ _
    · intro rho
      apply NonceFreshness.avoids_bind message
        (S.search_allowed rho request.message _ (fun c _ h => by cases h) attemptLimit 0 (by decide))
      intro found
      split
      · exact NonceFreshness.avoids_pure _ _
      · exact NonceFreshness.avoids_bind message (hpay _ _ _ _) fun _ => NonceFreshness.avoids_pure _ _
  · exact NonceFreshness.avoids_pure _ _
theorem sign_other_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    result.2.1 (.inr (.inl m')) = lz.1 (.inr (.inl m')) :=
  NonceFreshness.run_preserves m' _
    (S.authenticatedRecord_avoids pay hpay m' published request (Or.inr (Ne.symm hm'))) lz result hr
theorem sign_other_reuseMass (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    S.reuseMass result.2.2 m' = S.reuseMass lz.2 m' := by
  have hext := SourceReplay.run_extends _ lz result hr
  unfold reuseMass
  congr 1
  apply tsum_congr
  intro p
  unfold admissibleEntry
  cases hc : lz.2 (Sampling.digestTrial p.1 m' p.2.val) with
  | some a =>
      rw [hext.2 hc]
  | none =>
      have hn : result.2.2 (Sampling.digestTrial p.1 m' p.2.val) = none := by
        by_contra hne
        have hrow := S.signer_new_rows pay hpay published request lz result hr _ hc hne
          (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)
        exact hm' (CaseC.digestRowOf_unique ⟨p, rfl⟩ hrow)
      rw [hn]
theorem sign_published_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) lz)) :
    result.2.1 (.inr (.inl m)) ≠ none := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, _, hr⟩ := hr
  simp only [if_true] at hr
  rw [payloadRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨nonce, hnonce, hr⟩ := hr
  have hext := SourceReplay.run_extends _ nonce.2 result hr
  unfold privateNonce at hnonce
  rw [LazyPrivate.run_bind, mem_support_bind_iff] at hnonce
  obtain ⟨hashed, hhashed, hn⟩ := hnonce
  rw [LazyPrivate.run_pure, mem_support_pure_iff] at hn
  have hc := SourceReplay.hash_query_caches (.inr (.inr (.inl m))) trivial mac.2 hashed hhashed
  have hc' : nonce.2.1 (.inr (.inl m)) = some hashed.1 := by rw [hn]; exact hc
  rw [hext.1 hc']
  simp
theorem sign_unpublished (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) (hc : request.cache ≠ published)
    (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz)) :
    result.2.1 (.inr (.inl request.message)) = lz.1 (.inr (.inl request.message)) ∧ result.2.2 = lz.2 := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, hmac, hr⟩ := hr
  simp only [hc, if_false, LazyPrivate.run_pure, mem_support_pure_iff] at hr
  subst hr
  exact LazyPrivate.privateMac_preserves_nonce request.cache.region request.message lz mac hmac
noncomputable def reusePotential (s : LazyPrivate.State) : ENNReal :=
  ∑' m : Message, if s.1 (.inr (.inl m)) = none then S.reuseMass s.2 m else 0
theorem reusePotential_public_le (s : LazyPrivate.State) (x : HashInput) (a : HashOutput) (hx : s.2 x = none) :
    S.reusePotential (s.1, s.2.cacheQuery x a) ≤ S.reusePotential s + S.admInd a / 2 ^ 128 := by
  unfold reusePotential
  calc
    (∑' m : Message, if s.1 (.inr (.inl m)) = none then S.reuseMass (s.2.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if s.1 (.inr (.inl m)) = none then S.reuseMass s.2 m else 0) +
          (if CaseC.DigestRowOf x m then S.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using S.reuseMass_cacheQuery_le s.2 x a hx m
      · simpa [h2] using S.reuseMass_cacheQuery_le s.2 x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl
      (CaseC.tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => CaseC.digestRowOf_unique h h') _)
theorem reusePotential_public_nondigest (s : LazyPrivate.State) (x : HashInput) (a : HashOutput)
    (hx : s.2 x = none) (hnd : ¬CaseC.IsDigestInput x) :
    S.reusePotential (s.1, s.2.cacheQuery x a) ≤ S.reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m
  split_ifs with h
  · have h1 := S.reuseMass_cacheQuery_le s.2 x a hx m
    rw [if_neg (fun hr => hnd (CaseC.digestRowOf_isDigest hr)), ENNReal.zero_div, add_zero] at h1
    exact h1
  · exact le_rfl
theorem reusePotential_sign_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) = none) (hm' : s'.1 (.inr (.inl m)) ≠ none)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → S.reuseMass s'.2 m' = S.reuseMass s.2 m') :
    S.reusePotential s' + S.reuseMass s.2 m ≤ S.reusePotential s := by
  unfold reusePotential
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if s.1 (.inr (.inl m')) = none then S.reuseMass s.2 m' else 0)]
  simp only [hm', if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, hother m' he, hrows m' he]
theorem reusePotential_sign_stale_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) ≠ none → s'.1 (.inr (.inl m)) ≠ none)
    (hnone : s.1 (.inr (.inl m)) = none → s'.1 (.inr (.inl m)) = none ∧ S.reuseMass s'.2 m = S.reuseMass s.2 m)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → S.reuseMass s'.2 m' = S.reuseMass s.2 m') :
    S.reusePotential s' ≤ S.reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m'
  by_cases he : m' = m
  · subst he
    by_cases hc : s.1 (.inr (.inl m')) = none
    · obtain ⟨h1, h2⟩ := hnone hc
      simp [h1, h2, hc]
    · simp [hm hc, hc]
  · simp only [hother m' he, hrows m' he, le_refl]
theorem reuseMass_of_noDigest (cache : Sampling.RCache) (h : ∀ x, CaseC.IsDigestInput x → cache x = none)
    (m : Message) : S.reuseMass cache m = 0 := by
  unfold reuseMass
  rw [ENNReal.div_eq_zero_iff]
  left
  apply ENNReal.tsum_eq_zero.mpr
  intro p
  simp [admissibleEntry, h _ (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)]
theorem reusePotential_of_noDigest (s : LazyPrivate.State) (h : ∀ x, CaseC.IsDigestInput x → s.2 x = none) :
    S.reusePotential s = 0 := by
  unfold reusePotential
  apply ENNReal.tsum_eq_zero.mpr
  intro m
  split_ifs
  · exact S.reuseMass_of_noDigest _ h m
  · rfl
end FtsBankSpec
end ClaudeWCT.Bank
end
