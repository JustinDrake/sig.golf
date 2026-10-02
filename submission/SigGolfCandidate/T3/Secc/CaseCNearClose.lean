import SigGolfCandidate.T3.Secc.CaseCNearTrials
import SigGolfCandidate.T3.Secc.PairGuessLazyCount

/-!
# Stream CC: the near bound, closed (B-PAIR's §8 link proofs, moved from sig-t3-secc/checks/BP2_cc_link.lean)

* `bpair_nearChain`, `bpair_ghosts`, `bpair_law`: CC's three link hypotheses, by B-PAIR's `near_chain`
  (ω-law `omegaLaw adversary`), `worldGameL_bank` and `fixed_worldGameL` (CC's own `bpairTrials` +
  `worldGameCore_counts` give `bpair_ghosts` independently, see `CaseCNearTrials`);
* **`nearBound104 : NearBoundK 204`** — the near certificate × one guess at near price `K = 204 ≥ 203 + 1/16`;
* `caseC_small_bound_104 : CaseCSmallBoundK 204`, and the small route `small_route_closed`.

Divergence from A's frozen contract: `Wots.CaseCSmallBound` charges the near term with `nearTerm q` (near price
`203`); CC's bound is `nearTermK 204 q` (the extra `1/16` per birth pays the cache-reuse exception of the near bank).
The closing is re-checked for every `K ≤ 2000` by `CaseCSmallK.small_route_K` (second order `2002 + 2 ≤ 2^11`), so the
small route uses `small_route_K 204` instead of `Wots.small_route`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem bpair_nearChain : BPairNearChain := fun adversary q hq P hshort hmono payoff hevent =>
  ⟨BPair.omegaLaw adversary, BPair.near_chain adversary q hq P hshort hmono payoff hevent⟩

theorem bpair_ghosts : BPairGhosts := fun adversary ω fts r hr => BPair.worldGameL_bank adversary ω fts r hr

theorem bpair_law : BPairLaw := fun adversary ω fts =>
  BPair.fixed_worldGameL (BPair.canon_subset adversary) ω fts adversary

/-- **The near bound at near price `204`.** -/
theorem nearBound104 : NearBoundK 204 :=
  nearBoundK_of_nearChainHyp 204 near_price_le_104 (nearChainHyp_of_bpair bpair_nearChain bpair_ghosts bpair_law)

/-- **The case-(C) contract at near price `204`.** -/
theorem caseC_small_bound_104 : CaseCSmallBoundK 204 := caseC_small_bound_K 204 nearBound104

/-- **The small route** (A's closing re-checked at `K = 204`). -/
theorem small_route_closed :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q :=
  small_route_K 204 (by norm_num) caseC_small_bound_104

end SigGolfCandidate.T3.Security.CaseC
