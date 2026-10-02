import SigGolfCandidate.SphincsSecurity.Proof.Event.Deterministic
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MacElimination
import SigGolfCandidate.SphincsSecurity.Proof.Event.ReserveArithmetic
/-!
# From the independent scheme to the statement, in event form

Everything but the ideal bound itself: the event-form statement for the experiment of `Statement.lean`,
given the event-form bound for the table-secret scheme.

1. `experiment_event_le_cachedTable`: the seed is erased (every derivation, masks and MAC answers
   included, is presampled), at one query less and a `2^-207` seed-hit bound per query.
2. `cachedTable_le_simulated`: the cache's masks and MAC are eliminated. The masked region is uniform and
   independent of the tree, so the simulating adversary publishes a uniform region and tag itself and
   answers every request with another cache by `none`; a request with another cache that passes the MAC
   check costs `2^-256`, and a winning run has at most `2^32` requests.
3. Memoizing the signing requests turns the table game into the independent scheme's game. The ideal
   bound retains a proportional reserve for seed hits; the one-query gap pays for the cache MAC.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The event-form claim for the scheme of the ideal proof. -/
def IndependentEventStatement : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : SphincsSecurity.Adversary,
    Concrete.forgeEventAdvantage Concrete.scheme adversary q ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞)

/-- The proportional reserve used to pay for the shorter hidden seed prefix. -/
def IndependentEventStatementReserve : Prop :=
  ∀ q, 1 ≤ q → q < 2 ^ 127 → ∀ adversary : SphincsSecurity.Adversary,
    Concrete.forgeEventAdvantage Concrete.scheme adversary q +
      (q : ℝ≥0∞) / ((2 ^ 200 : Nat) : ℝ≥0∞) ≤
      q / ((2 ^ 127 : Nat) : ℝ≥0∞)

theorem forgeEventAdvantage_mono {Key : Type} (scheme : SphincsSecurity.Scheme Key) (adversary : SphincsSecurity.Adversary)
    {q r : Nat} (h : q ≤ r) :
    Concrete.forgeEventAdvantage scheme adversary q ≤ Concrete.forgeEventAdvantage scheme adversary r :=
  probEvent_mono fun _ _ hresult => ⟨hresult.1, hresult.2.trans h⟩

open Seeded in
attribute [local irreducible] cachedTableGameAfterSecrets tableGameAfterSecrets sampleSecretOutputs
  sampleRandomizerOutputs sampleMaskOutputs sampleMacOutputs in
/-- The experiment against the independent scheme, in event form. -/
theorem experiment_event_le_independent (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤
      Concrete.forgeEventAdvantage Concrete.scheme (memoAdversary (simAdversary adversary)) (q - 1) +
        (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 + ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 207 : Nat) : ℝ≥0∞) := by
  refine (experiment_event_le_cachedTable adversary q).trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ Pr[fun result => result.1 = true ∧ result.2 ≤ q - 1 | do
          let outputs ← sampleSecretOutputs
          let randomizers ← sampleRandomizerOutputs
          (simulateQ romImpl (countHashQueries
            (tableGameAfterSecrets (simAdversary adversary) outputs randomizers))).run' ∅] +
          (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 := by
      apply probEvent_bind_congr_le_add
      intro outputs _
      apply probEvent_bind_congr_le_add
      intro randomizers _
      exact cachedTable_le_simulated adversary outputs randomizers (q - 1)
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      unfold Concrete.forgeEventAdvantage
      rw [← simulateQ_countHashQueries]
      refine le_trans (probEvent_bind_mono fun outputs _ => probEvent_bind_mono fun randomizers _ =>
        probEvent_tableGameAfterSecrets_memo_counted (simAdversary adversary) outputs randomizers ∅ (q - 1))
        (le_of_eq ?_)
      exact probEvent_of_evalSPMF_eq (evalDist_independentTable_memo_counted (simAdversary adversary)) _

theorem transfer_loss_absorbed (q : Nat) (hq : 1 ≤ q) (ideal : ENNReal)
    (hideal : ideal + ((q - 1 : Nat) : ENNReal) / 2 ^ 200 ≤
      ((q - 1 : Nat) : ENNReal) / 2 ^ 127) :
    ideal + (2 ^ 32 : ENNReal) / 2 ^ 256 +
      ((q - 1 : Nat) : ENNReal) / 2 ^ 207 ≤ (q : ENNReal) / 2 ^ 127 :=
  transferReserveArithmetic q hq ideal hideal

theorem security127_event_of_independent (hideal : IndependentEventStatementReserve)
    (hzero : ∀ adversary : SphincsSecurity.Adversary, Concrete.forgeEventAdvantage Concrete.scheme adversary 0 = 0)
    (q : Nat) (hq : 1 ≤ q) (adversary : Adversary) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hsmall : q < 2 ^ 127
  · refine (experiment_event_le_independent adversary q).trans ?_
    by_cases hone : q = 1
    · subst q
      rw [Nat.sub_self, hzero, Nat.cast_zero, ENNReal.zero_div, add_zero, zero_add]
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using macLoss_le_oneQuery
    · have hreserve := hideal (q - 1) (by omega) (by omega)
        (Seeded.memoAdversary (Seeded.simAdversary adversary))
      have hreserve' :
          Concrete.forgeEventAdvantage Concrete.scheme
              (Seeded.memoAdversary (Seeded.simAdversary adversary)) (q - 1) +
            ((q - 1 : Nat) : ENNReal) / 2 ^ 200 ≤
            ((q - 1 : Nat) : ENNReal) / 2 ^ 127 := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hreserve
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (transfer_loss_absorbed q hq _ hreserve')
  · have hlarge : 2 ^ 127 ≤ q := Nat.le_of_not_gt hsmall
    calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl

theorem probEvent_win_le_event (experimentLaw : ProbComp (Bool × Nat)) (q : Nat)
    (hbound : ∀ result ∈ support experimentLaw, result.2 ≤ q) :
    Pr[fun result => result.1 = true | experimentLaw] ≤ Pr[fun result => result.1 = true ∧ result.2 ≤ q | experimentLaw] :=
  probEvent_mono fun result hresult hwin => ⟨hwin, hbound result hresult⟩

/-- Under a pointwise query bound the budget event is the whole winning event. -/
theorem hasClassicalSecurityBits_of_event (bits : Nat)
    (hevent : ∀ q, 1 ≤ q → ∀ adversary : Adversary,
      Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)) :
    HasClassicalSecurityBits bits := by
  intro q hq adversary hbound
  exact (probEvent_win_le_event (experiment adversary) q hbound).trans (hevent q hq adversary)

end SphincsSecurity.Security
