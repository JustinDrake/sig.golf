import SigGolfCandidate.T3.Secc.WotsSmallPrimitive
import SigGolfCandidate.T3.Secc.WotsSmallTransport
import SigGolfCandidate.T3.Secc.WotsTwoContacts
import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.T3.Secc.WotsEncodingContact

/-!
# Stream A: the small route (`small_route`)

For `1 ≤ q ≤ budgetSplit` (x = q/2^128 ≤ 2^-13):

    Pr[CleanWin q | tracedExperiment]
      = Pr[CleanWin | completedExperiment]                                (SeccLaw.completed_trace_event)
      ≤ Pr[CleanWin ∧ CaseABSrc] + Pr[CleanWin ∧ CaseCFreshPinned]        (completed_split_src; signed case impossible)
      ≤ Pr_R3[WotsPrimitiveSrc] + (1+cache)/n·E[M] + rest                 (caseABSrc_le_reference; CaseCSmallBound)
      ≤ c_P/n·E[P] + c_E/n·E[E] + n⁻¹·E[O] + (1+cache)/n·E[M] + rest      (reference_primitive_le)
      ≤ (181/100)·x + rest                                                 (rates ≤ 181/100; reference_class_budget)
      ≤ smallBound q,

with `rest = r·q·e/n + nearTerm q + pairTerm q + 2^-700 ≤ (1/40 + 1/1000)·x + 407·x² + 2^-700`; the closing allowances
are `37/20`, `2^9`, `2^-132` (first order `181/100 + 1/40 + 1/1000 ≤ 37/20`).

Every primitive bound is imported (C: two-edge, contacts, two contacts, marker-first restart; E: encoding match, marker
sum, contact-first; S: structural; F2: transport, counts). The only hypothesis is the case-(C) contract
`CaseCSmallBound` (`WotsSmallContract`), stream CC's.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 1024
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame

namespace SmallR

noncomputable def classRate : ENNReal := 181 / 100

theorem inv_one_sub_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ 8192 / 8191 := by
  calc (1 - (q : ENNReal) / 2 ^ 128)⁻¹ ≤ (8191 / 8192 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv.mpr (SeccClosing.one_sub_x_ge_of_small q hs)
    _ = 8192 / 8191 := ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))

theorem prefixCoeff_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) : prefixCoeff q ≤ classRate := by
  have hx := SeccClosing.x_le_of_small q hs
  have hu := inv_one_sub_le q hs
  unfold prefixCoeff classRate
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x), div_eq_mul_inv _ ((1 - x) ^ 2), div_eq_mul_inv _ (1 - x), ENNReal.inv_pow]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc ((3 / 2 : ENNReal) + 4 * x + 2 * x ^ 2) * u + 4 * x * u ^ 2 + 2 * 57 * x * u
      ≤ ((3 / 2 : ENNReal) + 4 * ((2:ENNReal)^13)⁻¹ + 2 * (((2:ENNReal)^13)⁻¹)^2) * (8192/8191) +
          4 * ((2:ENNReal)^13)⁻¹ * (8192/8191)^2 + 2 * 57 * ((2:ENNReal)^13)⁻¹ * (8192/8191) := by
        gcongr
    _ ≤ 181 / 100 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num

theorem encodingCoeff_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) : encodingCoeff q ≤ classRate := by
  have hx := SeccClosing.x_le_of_small q hs
  have hu := inv_one_sub_le q hs
  unfold encodingCoeff classRate
  generalize (q : ENNReal) / 2 ^ 128 = x at hx hu ⊢
  rw [div_eq_mul_inv _ (1 - x)]
  generalize (1 - x)⁻¹ = u at hu ⊢
  calc (1 : ENNReal) + 2 * 3306 * x * u ≤ 1 + 2 * 3306 * ((2:ENNReal)^13)⁻¹ * (8192/8191) := by gcongr
    _ ≤ 181 / 100 := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
        norm_num

theorem one_le_classRate : (1 : ENNReal) ≤ classRate := by
  unfold classRate
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

theorem digestRate_le : 1 + SeccClosing.cacheRate ≤ classRate := by
  unfold classRate
  rw [SeccClosing.cacheRate_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num

/-! ## The remaining terms below the split -/

theorem excess_le (q : Nat) :
    ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 ≤ (1 / 40) * ((q : ENNReal) / 2 ^ 128) := by
  rw [SeccClosing.excessRate_def]
  unfold signRatio
  push_cast
  simp only [div_eq_mul_inv]
  calc (201 : ENNReal) * q * (11324 * 100000000⁻¹) * (2 ^ 128)⁻¹
      = (201 * (11324 * 100000000⁻¹)) * (q * (2 ^ 128)⁻¹) := by ring
    _ ≤ (1 * 40⁻¹) * (q * (2 ^ 128)⁻¹) := by
        gcongr ?_ * _
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
          ENNReal.toReal_one]
        norm_num

theorem nearTerm_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    nearTerm q ≤ 405 * ((q : ENNReal) / 2 ^ 128) ^ 2 + (1 / 1000) * ((q : ENNReal) / 2 ^ 128) := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  unfold nearTerm nearPrice signRatio
  rw [SeccClosing.cacheRate_def, ← div_eq_mul_inv (q : ENNReal)]
  have hinner : (404 : ENNReal) * q / 2 ^ 128 + 21 * ((201 * q : ℕ) : ENNReal) * ((2 : ENNReal) ^ 25)⁻¹ / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700 =
      (404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * ((q : ENNReal) / 2 ^ 128) + 21 * (2 : ENNReal)⁻¹ ^ 700 := by
    push_cast
    simp only [div_eq_mul_inv]
    ring
  rw [hinner]
  generalize (q : ENNReal) / 2 ^ 128 = x at hg ⊢
  generalize (q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal) = g at hg ⊢
  calc g * ((404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700)
      ≤ (8192 / 8191 * x) * ((404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹) * x + 21 * (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (8192 / 8191 * (404 + 21 * 201 * ((2 : ENNReal) ^ 25)⁻¹)) * x ^ 2 +
          (8192 / 8191 * (21 * (2 : ENNReal)⁻¹ ^ 700)) * x := by ring
    _ ≤ 405 * x ^ 2 + (1 / 1000) * x := by
        gcongr
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          norm_num
        · apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
          simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div,
            ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one]
          norm_num

theorem pairTerm_le (q : Nat) (hs : q ≤ SeccClosing.budgetSplit) :
    BPair.pairTerm q ≤ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
  have hg := SeccClosing.div_sub_le_of_small q hs
  have hc : (q.choose 2 : ENNReal) ≤ (q : ENNReal) * q := by
    have : q.choose 2 ≤ q * q := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  unfold BPair.pairTerm
  calc (q.choose 2 : ENNReal) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2
      ≤ ((q : ENNReal) * q) * ((2 ^ 128 - q : ℕ) : ENNReal)⁻¹ ^ 2 := by gcongr
    _ = ((q : ENNReal) / ((2 ^ 128 - q : ℕ) : ENNReal)) ^ 2 := by rw [div_eq_mul_inv]; ring
    _ ≤ (8192 / 8191 * ((q : ENNReal) / 2 ^ 128)) ^ 2 := by gcongr
    _ = (8192 / 8191 : ENNReal) ^ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := mul_pow _ _ _
    _ ≤ 2 * ((q : ENNReal) / 2 ^ 128) ^ 2 := by
        gcongr
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
        norm_num

end SmallR

open SmallR

/-! ## The small route -/

/-- C's `reference_twoContacts_le` is A's `TwoContactsBound`. -/
theorem twoContactsBound (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) : TwoContactsBound adversary q :=
  reference_twoContacts_le adversary q hq

/-- E's `reference_marker_sum_le` is A's `MarkerSumBound`. -/
theorem markerSumBound (adversary : AdversaryP) (q : Nat) : MarkerSumBound adversary q :=
  reference_marker_sum_le adversary q

/-- E's `reference_contactFirst_le` is A's `ContactFirstBound`. -/
theorem contactFirstBound (adversary : AdversaryP) (q : Nat) : ContactFirstBound adversary q :=
  reference_contactFirst_le adversary q

/-- A clean win is in case (A)+(B) (source-sized) or in the fresh pinned case (C); the signed case never happens. -/
theorem cleanWin_le_cases (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseABSrc adversary z | SeccLaw.completedExperiment adversary q hq] +
      Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  refine le_trans (Ref.pmf_probEvent_mono _ ?_) (probEvent_or_le _ _ _)
  intro z hz hclean
  rcases completed_split_src adversary q hq z hz hclean with h | h | h
  · exact Or.inl ⟨hclean, h⟩
  · exact Or.inr ⟨hclean, h⟩
  · exact absurd h (caseCSignedPinned_impossible adversary q hq z hz hclean)

/-- **The small route**: below the split, a clean traced win has probability at most `smallBound q`. -/
theorem small_route (hC : CaseCSmallBound) :
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
  have hnear := nearTerm_le q hs
  have hpair := pairTerm_le q hs
  apply SeccClosing.smallBound_of_le q _ (classRate + 1 / 40 + 1 / 1000) 407 ((2 : ENNReal)⁻¹ ^ 700)
  · rw [SeccClosing.smallCoefficient_def]
    unfold classRate
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_one]
    norm_num
  · rw [SeccClosing.smallQuadratic_def]
    exact_mod_cast (by norm_num : (407 : ℕ) ≤ 2 ^ 9)
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
            ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
            (2 : ENNReal)⁻¹ ^ 700) := add_le_add hab hc
    _ ≤ (classRate / 2 ^ 128 * EP + classRate / 2 ^ 128 * EE + classRate / 2 ^ 128 * EO) +
          (classRate / 2 ^ 128 * EM + 1 / 40 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 +
            (2 : ENNReal)⁻¹ ^ 700) := by gcongr
    _ = classRate / 2 ^ 128 * (EP + EE + EO + EM) +
          (1 / 40 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by ring
    _ ≤ classRate * x + (1 / 40 * x + (405 * x ^ 2 + 1 / 1000 * x) + 2 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700) := by
        gcongr
    _ = (classRate + 1 / 40 + 1 / 1000) * x + 407 * x ^ 2 + (2 : ENNReal)⁻¹ ^ 700 := by ring

/-- **SecurityP from the routes**: the small route (with the case-(C) contract) and any large-route bound give `SecurityP` (`SeccClosing.securityP_of_routes`). -/
theorem securityP_of_small (hC : CaseCSmallBound)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ SeccClosing.largeBound q) :
    SecurityP :=
  SeccClosing.securityP_of_routes (small_route hC) hlarge

end SigGolfCandidate.T3.Security.Wots
