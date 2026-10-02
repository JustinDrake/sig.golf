import SigGolfCandidate.T3.Secc.CaseCNearCounts
import SigGolfCandidate.T3.Secc.PairGuessLazyGhost
import SigGolfCandidate.T3.Secc.PairGuessLazy

/-!
# Stream CC: B-PAIR's compiled §8 facts, in CC's hypothesis shapes

* `bpairLaw`: B-PAIR's `fixed_worldGameL` is `BPairLaw`;
* `bpairGhostsCore_of_trials`: B-PAIR's `worldGameL_ghosts` and `worldGameL_tracking` give `BPairGhostsCore` up to
  CC-4's G3 (`BPairTrials`);
* `small_route_of_chain_trials`: the small route from B-PAIR's `near_chain` and G3 only.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem bpairLaw : BPairLaw := fun adversary ω fts =>
  BPair.fixed_worldGameL (BPair.canon_subset adversary) ω fts adversary

/-- B-PAIR's `near_chain` (with `L := omegaLaw adversary`) is `BPairNearChain`. -/
theorem bpairNearChain : BPairNearChain := by
  intro adversary q hq P hshort hmono payoff hevent
  exact ⟨BPair.omegaLaw adversary, BPair.near_chain adversary q hq P hshort hmono payoff hevent⟩

/-- **CC-4's G3**: every signer trial row is an honest signer digest query of a logged signing. -/
def BPairTrials : Prop :=
  ∀ (adversary : AdversaryP) ω fts r, fixedL adversary ω fts r ≠ 0 →
    let A := BPair.Omega.answers (BPair.canon_subset adversary) ω fts
    ∀ x ∈ r.2.memory.trials, ∃ entry ∈ r.1.2.1, (.inl (.inr x) : T3.Spec.Domain) ∈
      SecurityExtraction.queried A (FullGame.authenticatedSign (evalWithAnswerFn A keygen).2 entry.1)

theorem bpairGhostsCore_of_trials (htr : BPairTrials) : BPairGhostsCore := by
  intro adversary ω fts r hr
  obtain ⟨g1, g2⟩ := BPair.worldGameL_ghosts (BPair.canon_subset adversary) ω fts adversary r hr
  obtain ⟨-, g3⟩ := BPair.worldGameL_tracking (BPair.canon_subset adversary) ω fts adversary r hr
  exact ⟨g1, g2, g3, htr adversary ω fts r hr⟩

/-- **The small route from G3 alone** (everything else is B-PAIR's compiled §8). -/
theorem small_route_of_trials (htr : BPairTrials) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_of_bpair_core bpairNearChain (bpairGhostsCore_of_trials htr) bpairLaw

/-- **The small route from B-PAIR's `near_chain` and G3.** -/
theorem small_route_of_chain_trials (hchain : BPairNearChain) (htr : BPairTrials) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_of_bpair_core hchain (bpairGhostsCore_of_trials htr) bpairLaw

end SigGolfCandidate.T3.Security.CaseC
