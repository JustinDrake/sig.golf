import SigGolfCandidate.T3.Secc.CaseCNearSign

/-!
# Stream CC: the near bank bound in B-PAIR's lazy forced world

`forced_payoff_le`: for every slot, `ω`, adversary and budget `q`, the expected near payoff of the lazy forced run of
the world game is at most `q·(404 + 1/16)/2^128`:

    E_{forcedRun envL slot (worldGameCore hU ω adversary) initL}[nearPayoff q]
      = E_{ghost run}[nearPayoff q ∘ proj]   (run_project)
      ≤ E_{ghost run}[ΦI q]                  (payoff_le_ΦI)
      ≤ ΦI q initG                           (worldGame_ΦI: the handler-level supermartingale)
      ≤ q·(404 + 1/16)/2^128                 (ΦI_initial).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- **The world game is a supermartingale of the bank potential.** -/
theorem worldGame_ΦI {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    SuperProg (implG slot) (ΦI q) (BPair.worldGameCore hU ω adversary) :=
  worldGameCore_super hU (implG slot) (ΦI q) ω adversary (coin_ΦI slot q) (hashL_ΦI hU slot q ω)
    (fun published request => signL_ΦI hU slot q ω published request)

/-- **The near bank in the lazy forced world.** -/
theorem forced_payoff_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    expectedValue (SecretGuessObservation.forcedRun BPair.envL slot (BPair.worldGameCore hU ω adversary) BPair.initL)
      (nearPayoff q) ≤ (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128 := by
  unfold SecretGuessObservation.forcedRun
  rw [← projS_initG, expectedValue_project BPair.envL slot _ initG (nearPayoff q)]
  calc
    _ ≤ expectedValue (SecretGuessObservation.runWith (implG slot) (BPair.worldGameCore hU ω adversary) initG)
        (fun r => ΦI q r.2) := expectedValue_mono _ fun r => payoff_le_ΦI q r
    _ ≤ ΦI q initG := worldGame_ΦI hU ω adversary slot q initG
    _ ≤ _ := ΦI_initial q

/-- The same in B-PAIR's sum form. -/
theorem forced_payoff_sum_le {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot (BPair.worldGameCore hU ω adversary) BPair.initL] *
      nearPayoff q r ≤ (q : ENNReal) * (404 + 1 / 16) / 2 ^ 128 :=
  forced_payoff_le hU ω adversary slot q

end SigGolfCandidate.T3.Security.CaseC
