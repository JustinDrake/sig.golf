import SigGolfCandidate.T3.Secc.CaseCSmall
import SigGolfCandidate.T3.Secc.WotsSmall

/-!
# Stream CC: the case-(C) contract with a general near price `K` (and the closing re-check)

Stream A's `CaseCSmallBound` charges the near certificate × one guess with `nearTerm q`, whose near price is
`nearPrice = 872633/2048`. The closing only needs the second-order coefficient below `smallQuadratic = 430`, so any near
price `K ≤ 872633/2048` closes:

* `nearTermK K q`: `nearTerm` with `nearPrice` replaced by `K` (`nearTermK_103 : nearTermK (872633/2048) = Wots.nearTerm`);
* `CaseCSmallBoundK K` / `NearBoundK K`: the contract and the near hypothesis with `nearTermK K`;
* `caseC_small_bound_K (hnear : NearBoundK K) : CaseCSmallBoundK K` (same proof as `caseC_small_bound`);
* `small_route_K (hK : K ≤ 872633/2048) (hC : CaseCSmallBoundK K)`: A's small route re-closed (`427·x² + 2·x² ≤ 430·x²`).
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Security.Wots SigGolfCandidate.T3.Security.Wots.SmallR
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable

/-- `Wots.nearTerm` with the near price `nearPrice` replaced by `K`. -/
noncomputable def nearTermK (K : ENNReal) (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (K * q / 2 ^ 128 + 21 * (Wots.signRatio * q : Nat) * SeccClosing.cacheRate / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700)

theorem nearTermK_103 : nearTermK (872633 / 2048) = Wots.nearTerm := by
  funext q
  unfold nearTermK Wots.nearTerm Wots.nearPrice
  rfl

theorem nearTermK_mono {K K' : ENNReal} (h : K ≤ K') (q : Nat) : nearTermK K q ≤ nearTermK K' q := by
  unfold nearTermK
  gcongr

/-- **The case-(C) contract with near price `K`.** -/
def CaseCSmallBoundK (K : ENNReal) : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ Wots.CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq Wots.digestClass +
        ((Wots.signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTermK K q +
          BPair.pairTerm q + (2 : ENNReal)⁻¹ ^ 700

/-- The near-certificate-plus-one-guess bound with near price `K`. -/
def NearBoundK (K : ENNReal) : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ PinnedC adversary NearQ z | SeccLaw.completedExperiment adversary q hq] ≤
      nearTermK K q

theorem nearBoundK_103 : NearBoundK (872633 / 2048) ↔ NearBound := by
  unfold NearBoundK NearBound
  rw [nearTermK_103]

theorem caseCSmallBoundK_103 : CaseCSmallBoundK (872633 / 2048) ↔ Wots.CaseCSmallBound := by
  unfold CaseCSmallBoundK Wots.CaseCSmallBound
  rw [nearTermK_103]

/-- **The contract from the near bound**, for any near price `K`. -/
theorem caseC_small_bound_K (K : ENNReal) (hnear : NearBoundK K) : CaseCSmallBoundK K := by
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
        (nearTermK K q + BPair.pairTerm q) :=
      add_le_add (full_bound adversary q hq)
        (add_le_add (hnear adversary q hq h1 hsplit) (BPair.pair_guess_bound adversary q hq))
    _ ≤ _ := by
      rw [← add_assoc]
      exact le_self_add

/-- The near term with price `K ≤ 872633/2048` below the split. -/
theorem nearTermK_le (K : ENNReal) (hK : K ≤ 872633 / 2048) (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    nearTermK K q ≤ 427 * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 1000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  unfold nearTermK Wots.signRatio
  rw [SeccClosing.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : K * q / 2 ^ 128 + 21 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700 =
      (K + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 21 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((K + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (1048576 / 1048433 * x) *
          ((872633 / 2048 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (1048576 / 1048433 * (872633 / 2048 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (1048576 / 1048433 * (21 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ 427 * x ^ 2 + (1 / 1000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num

/-- **The small route with near price `K ≤ 872633/2048`** (stream A's closing, re-checked). -/
theorem small_route_K (K : ENNReal) (hK : K ≤ 872633 / 2048) (hC : CaseCSmallBoundK K) :
    ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.smallBound q := by
  intro adversary q hq hq1 hs
  have hq128 : q < 2 ^ 128 := lt_of_le_of_lt hq (by norm_num)
  have hbudget := reference_class_budget adversary q hq
  have hab := (caseABSrc_le_reference adversary q hq).trans (reference_primitive_le adversary q hq128
    (twoContactsBound adversary q hq128) (contactFirstBound adversary q) (markerSumBound adversary q))
  have hc := hC adversary q hq hq1 hs
  have k1 : prefixCoeff q / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact prefixCoeff_le q hs
  have k2 : encodingCoeff q / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact encodingCoeff_le q hs
  have k3 : (2 ^ 128 : ENNReal)⁻¹ ≤ classRate / 2 ^ 128 := by
    rw [← one_div]; exact ENNReal.div_le_div_right one_le_classRate _
  have k4 : (1 + SeccClosing.cacheRate) / 2 ^ 128 ≤ classRate / 2 ^ 128 := by gcongr; exact digestRate_le
  generalize refExpect adversary q prefixClassCount = EP at hbudget hab
  generalize refExpect adversary q encodingCount = EE at hbudget hab
  generalize refExpect adversary q otherCount = EO at hbudget hab
  generalize SeccLaw.expectedCharge adversary q hq digestClass = EM at hbudget hc
  have hcq : classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ classRate * ((q : ENNReal) / 2 ^ 128) := by
    calc classRate / 2 ^ 128 * (EP + EE + EO + EM) ≤ classRate / 2 ^ 128 * q := by gcongr
      _ = classRate * ((q : ENNReal) / 2 ^ 128) := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hex := excess_le q
  have hnear := nearTermK_le K hK q hs
  have hpair := pairTerm_le q hs
  apply SeccClosing.smallBound_of_le q _ (classRate + 27 / 1000 + 1 / 1000) 429 ((2 : ENNReal)⁻¹ ^ 700)
  · rw [SeccClosing.smallCoefficient_def]
    unfold classRate
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  · rw [SeccClosing.smallQuadratic_def]
    exact_mod_cast (by norm_num : (429 : ℕ) ≤ 430)
  · rw [SeccClosing.smallAbsolute_def, ← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ one_le_two (by norm_num : 132 ≤ 700))
  generalize (q : ENNReal) / 2 ^ 128 = x at hcq hex hnear hpair
  calc Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq]
      ≤ Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z |
            SeccLaw.completedExperiment adversary q hq] +
          Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
            SeccLaw.completedExperiment adversary q hq] := cleanWin_le_cases adversary q hq
    _ ≤ (prefixCoeff q / 2 ^ 128 * EP + encodingCoeff q / 2 ^ 128 * EE + (2 ^ 128 : ENNReal)⁻¹ * EO) +
          ((1 + SeccClosing.cacheRate) / 2 ^ 128 * EM +
            ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTermK K q +
              BPair.pairTerm q + (2 : ENNReal)⁻¹ ^ 700) := add_le_add hab hc
    _ ≤ (classRate / 2 ^ 128 * EP + classRate / 2 ^ 128 * EE + classRate / 2 ^ 128 * EO) +
          (classRate / 2 ^ 128 * EM + 27 / 1000 * x + (427 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 +
            (2 : ENNReal)⁻¹ ^ 700) := by gcongr
    _ = classRate / 2 ^ 128 * (EP + EE + EO + EM) +
          (27 / 1000 * x + (427 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by ring
    _ ≤ classRate * x + (27 / 1000 * x + (427 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (classRate + 27 / 1000 + 1 / 1000) * x + 429 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700 := by ring

/-- `SecurityP` from the `K`-contract and any large-route bound. -/
theorem securityP_of_small_K (K : ENNReal) (hK : K ≤ 872633 / 2048) (hC : CaseCSmallBoundK K)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.largeBound q) :
    SecurityP :=
  SeccClosing.securityP_of_routes (small_route_K K hK hC) hlarge

end SigGolfCandidate.T3.Security.CaseC
