import SigGolfCandidate.T3.Secc.CaseCNearClose

/-!
# Stream CC: the near price at the gate 135/1024 (`≤ 872505/2048`), plus the reuse charge, hence A's exact `NearBound`

At the gate 135/1024 the near price is `≤ 6463/16 · 135/128 = 872505/2048` (reference-gate Poisson arithmetic
times the gate ratio); with the near bank's reuse charge `1/16` per birth the near constant is `872633/2048`:

* `poisson_near_bound_tight`, `uniform_history_near_bound_tight`, `fullNearPrice_bound_tight` (SEC's proofs, final
  constant `872505/2048`);
* `nearLedger_initial_tight` → `near_initial_tight` → `mem_initial_tight` → `ΦI_initial_tight` (`≤ q·(872633/2048)/2^128`);
* `forced_payoff_le_tight`: the near bank in the lazy forced world at `q·(872633/2048)/2^128`;
* **`nearBound : NearBound`** (A's exact form) and `caseC_small_bound_closed : Wots.CaseCSmallBound`.
-/

namespace SigGolfCandidate.T3.BPORS.Numeric
open OracleComp OracleSpec ENNReal
open OracleComp.EvalDist SphincsSecurity.Concrete
open scoped BigOperators
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

theorem poisson_near_bound_tight :
    21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 ≤ 872505 / 2048 := by
  refine poisson_near_tight_bound.trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  norm_num

/-- The near price at the gate 135/1024 (`6463/16 · 135/128 = 872505/2048`). -/
theorem uniform_history_near_bound_tight (missing : Fin 7) :
    21*(2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤ 872505 / 2048 :=
  uniform_history_near_bound missing

end SigGolfCandidate.T3.BPORS.Numeric

namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem fullNearPrice_bound_tight : uniformWordAverage Numeric.proposalLength fullNearPrice ≤ 872505 / 2048 :=
  fullNearPrice_bound

end SigGolfCandidate.T3.BPORS.History

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem nearLedger_initial_tight (budget : Nat) :
    nearLedger BPORS.Numeric.proposalLength [] [] budget ≤ (budget : ENNReal) * (872505 / 2048) / 2 ^ 128 := by
  unfold nearLedger nearPriceForecast
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  simpa [labels] using BPORS.History.fullNearPrice_bound_tight

theorem near_initial_tight (budget : Nat) :
    nearPotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (872505 / 2048) / 2 ^ 128 := by
  unfold nearPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact nearLedger_initial_tight budget

theorem mem_initial_tight (q : Nat) :
    nearMemPotential q [] [] false ∅ (fun _ => none) ≤ (q : ENNReal) * (872633 / 2048) / 2 ^ 128 := by
  unfold nearMemPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
  have hC : reuseC ∅ (fun _ => none) = 0 := by
    unfold reuseC reuseMass admissibleEntry
    simp
  rw [show (⟨[], [], false, reuseC ∅ (fun _ => none), q⟩ : BankCore) = ⟨[], [], false, 0, q⟩ by rw [hC]]
  calc
    _ ≤ (q : ENNReal) * (872505 / 2048) / 2 ^ 128 + (q : ENNReal) * ((1 / 16) / 2 ^ 128) :=
      add_le_add (near_initial_tight q) le_rfl
    _ = (q : ENNReal) * (872505 / 2048 + 1 / 16) / 2 ^ 128 := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      congr 2
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
        ENNReal.toReal_one]
      norm_num

theorem ΦI_initial_tight (q : Nat) : ΦI q initG ≤ (q : ENNReal) * (872633 / 2048) / 2 ^ 128 := by
  unfold ΦI
  rw [if_pos (show InvM initG.memory from invM_empty)]
  exact mem_initial_tight q

/-- **The near bank in the lazy forced world, at `q·404/2^128`.** -/
theorem forced_payoff_le_tight {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : BPair.Omega U)
    (adversary : AdversaryP) (slot q : Nat) :
    ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot (BPair.worldGameCore hU ω adversary) BPair.initL] *
      nearPayoff q r ≤ (q : ENNReal) * (872633 / 2048) / 2 ^ 128 := by
  change expectedValue _ (nearPayoff q) ≤ _
  unfold SecretGuessObservation.forcedRun
  rw [← projS_initG, expectedValue_project BPair.envL slot _ initG (nearPayoff q)]
  calc
    _ ≤ expectedValue (SecretGuessObservation.runWith (implG slot) (BPair.worldGameCore hU ω adversary) initG)
        (fun r => ΦI q r.2) := expectedValue_mono _ fun r => payoff_le_ΦI q r
    _ ≤ ΦI q initG := worldGame_ΦI hU ω adversary slot q initG
    _ ≤ _ := ΦI_initial_tight q

/-- **A's exact near bound** (`NearBound`, near price `404`). -/
theorem nearBound : NearBound := by
  rw [← nearBoundK_103]
  intro adversary q hq _ _
  obtain ⟨L, hL⟩ := nearChainHyp_of_bpair bpair_nearChain bpair_ghosts bpair_law adversary q hq
  have hslot : ∀ slot, (∑' ω, Pr[= ω | L] *
      ∑' r, Pr[= r | SecretGuessObservation.forcedRun BPair.envL slot
        (BPair.worldGameL (BPair.canon_subset adversary) ω adversary) BPair.initL] * nearPayoff q r) ≤
      (q : ENNReal) * (872633 / 2048) / 2 ^ 128 :=
    fun slot => omega_avg_le L _ _ fun ω => forced_payoff_le_tight (BPair.canon_subset adversary) ω adversary slot q
  calc
    _ ≤ Pr[NearAll adversary q | SeccLaw.completedExperiment adversary q hq] := near_le_all adversary q hq
    _ ≤ _ := hL
    _ ≤ ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * ∑ _slot ∈ Finset.range q, (q : ENNReal) * (872633 / 2048) / 2 ^ 128 :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun slot _ => hslot slot)
    _ = (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ * (872633 / 2048 * q / 2 ^ 128) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := nearTermK_ge (872633 / 2048) q

/-- **A's case-(C) small-route contract, proved.** -/
theorem caseC_small_bound_closed : Wots.CaseCSmallBound := caseC_small_bound nearBound

end SigGolfCandidate.T3.Security.CaseC
