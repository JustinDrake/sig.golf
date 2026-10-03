import SigGolfCandidate.T3.Secc.CaseCSplit
import SigGolfCandidate.T3.Secc.CaseCFullBound
import SigGolfCandidate.T3.Secc.CaseCCore
import SigGolfCandidate.T3.Secc.WotsSmallContract

/-!
# Stream CC: the case-(C) small-route contract `Wots.CaseCSmallBound`

`caseC_small_bound (hnear : NearBound) : Wots.CaseCSmallBound`:

    Pr[CleanWin ∧ CaseCFreshPinned] ≤ Pr[CleanWin ∧ PinnedC FullQ] + Pr[CleanWin ∧ PinnedC NearQ] + Pr[CleanWin ∧ PairGuess]

(`caseC_three_way`), with

* full: `full_bound_births` + SEC's `expectedBirths_le_shared` (digest births ≤ the shared-law digest-class charge),
  `theta + 1/16 ≤ 1 ≤ 1 + cacheRate`, `q ≤ 201·q`, `excessRate = 11324/10^8`;
* near: the hypothesis `NearBound` (≤ `Wots.nearTerm q`; open, see `plan/CC-INTERFACE.md` §2c);
* pair: B-PAIR's `pair_guess_bound` (≤ `BPair.pairTerm q`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **The near-certificate-plus-one-guess bound** (open hypothesis): a clean pinned case-(C) sample whose forgery
digest has exactly one undisclosed opened position, probed by the final verifier, has probability at most A's
`nearTerm q`. -/
def NearBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | SeccLaw.completedExperiment adversary q hq] ≤
      Wots.nearTerm q

theorem pmf_probEvent_mono_support {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]

theorem pmf_probEvent_or_le {α : Type} (p : PMF α) (F G : α → Prop) :
    Pr[fun x => F x ∨ G x | p] ≤ Pr[F | p] + Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hF : F x <;> by_cases hG : G x <;> simp [hF, hG]

/-- SEC's public digest class is A's `digestClass`. -/
theorem publicClass_digest : (fun _ => CreationGame.publicClass IsDigestInput) = Wots.digestClass := by
  funext z input
  apply propext
  rcases input with (coin | x) | priv
  · exact ⟨fun h => h.elim, fun ⟨_, _, _, h⟩ => by cases h⟩
  · constructor
    · rintro ⟨rho, m, ctr, rfl⟩
      exact ⟨rho, m, ctr, rfl⟩
    · rintro ⟨rho, m, ctr, h⟩
      cases h
      exact ⟨rho, m, ctr, rfl⟩
  · exact ⟨fun h => h.elim, fun ⟨_, _, _, h⟩ => by cases h⟩

/-- **The full case on A's scale.** -/
theorem full_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
        ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 := by
  refine (full_bound_births adversary q hq).trans (add_le_add ?_ ?_)
  · apply mul_le_mul'
    · apply ENNReal.div_le_div_right
      exact theta_add_sixteenth_le_one.trans le_self_add
    · rw [← publicClass_digest]
      exact CreationGame.expectedBirths_le_shared IsDigestInput adversary q hq
  · rw [SeccClosing.excessRate_def]
    apply ENNReal.div_le_div_right
    apply mul_le_mul' _ le_rfl
    exact_mod_cast (by unfold Wots.signRatio; omega : q ≤ Wots.signRatio * q)

/-- **Stream CC's case-(C) small-route contract** (A's `Wots.CaseCSmallBound`), from the near bound. -/
theorem caseC_small_bound (hnear : NearBound) : Wots.CaseCSmallBound := by
  intro adversary q hq h1 hsplit
  set P := SeccLaw.completedExperiment adversary q hq
  calc
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ Wots.CaseCFreshPinned adversary z | P] ≤
        Pr[fun z => (QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z) ∨
          ((QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z) ∨
            (QueryRecorded.CleanWin q z.1 ∧ BPair.PairGuess adversary z)) | P] := by
      apply pmf_probEvent_mono_support
      intro z hz hzC
      rcases caseC_three_way adversary q hq z hz hzC.1 hzC.2 with h | h | h
      · exact Or.inl ⟨hzC.1, h⟩
      · exact Or.inr (Or.inl ⟨hzC.1, h⟩)
      · exact Or.inr (Or.inr ⟨hzC.1, h⟩)
    _ ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary FullQ z | P] +
        (Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | P] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ BPair.PairGuess adversary z | P]) :=
      (pmf_probEvent_or_le _ _ _).trans (add_le_add le_rfl (pmf_probEvent_or_le _ _ _))
    _ ≤ ((1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
          ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128) +
        (Wots.nearTerm q + BPair.pairTerm q) :=
      add_le_add (full_bound adversary q hq)
        (add_le_add (hnear adversary q hq h1 hsplit) (BPair.pair_guess_bound adversary q hq))
    _ ≤ _ := by
      rw [← add_assoc]
      exact le_self_add

end SigGolfCandidate.T3.Security.CaseC
