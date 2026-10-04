import SigGolfCandidate.ClaudeWCT.Numerics.WCTPrice
import SigGolfCandidate.ClaudeWCT.GuessV2.NearScore
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCFull
import SigGolfCandidate.T3.Secc.CaseCCore
import SigGolfCandidate.T3.Secc.CaseCBankReuse

section


namespace ClaudeWCT.Numerics.WCTPrice
open Finset ENNReal
open ClaudeWCT.Numerics.Kernel ClaudeWCT.Numerics.WCTEnvelope ClaudeWCT.Numerics.PoissonReflect
open ClaudeWCT.Numerics.Thinning (ListCovExcept)
open SphincsSecurity.Concrete (uniformWordAverage binomialAverage uniformWordAverage_mono
  uniformWordAverage_mul_left uniformWordAverage_sum uniformWordAverage_add)
open SigGolfResearch.Gate6.Moments (finiteAverage)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.Bank.WCT (WProposal proposal outIdx SlotCoveredP)
open ClaudeWCT.WCT9 (digit)
open ClaudeWCT.Guess (nearScore nearPrice NearCoveredAt)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem guess_slotCovered_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    ClaudeWCT.Guess.SlotCovered X N k t ↔ ClaudeWCT.Bank.WCT.SlotCovered X N k t := by
  unfold ClaudeWCT.Guess.SlotCovered ClaudeWCT.Bank.WCT.SlotCovered
  refine exists_congr fun x => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  simp only [outIdx, Fin.mk.injEq]
theorem slotCoveredP_iff_atIndex (W : List WProposal) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    SlotCoveredP W N k t ↔
      ∃ e ∈ atIndex (outIdx N) W, (e k).1 = ((proposal N).2 k).1 ∧
        digit ((proposal N).2 k).2 t ≤ digit (e k).2 t := by
  constructor
  · rintro ⟨p, hp, h1, h2, h3⟩
    refine ⟨p.2, (mem_atIndex _ _ _).mpr ?_, h2, h3⟩
    rw [← h1]
    exact hp
  · rintro ⟨e, he, h2, h3⟩
    exact ⟨(outIdx N, e), (mem_atIndex _ _ _).mp he, rfl, h2, h3⟩
theorem nearCoveredAt_iff (X : List HashOutput) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    NearCoveredAt X N k t ↔
      ListCovExcept digit k t (atIndex (outIdx N) (X.map proposal)) (proposal N).2 := by
  unfold NearCoveredAt ListCovExcept
  refine forall_congr' fun k' => forall_congr' fun t' => imp_congr_right fun _ => ?_
  rw [guess_slotCovered_iff, ClaudeWCT.Bank.WCT.slotCovered_iff, slotCoveredP_iff_atIndex]
noncomputable def nearPriceP (W : List WProposal) : ENNReal :=
  ((5 * 1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 7 *
    ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 7, wctNearEnv k t (atIndex index W)
theorem nearPrice_eq_nearPriceP (X : List HashOutput) :
    nearPrice X = nearPriceP (X.map proposal) := by
  classical
  set W : List WProposal := X.map proposal with hW
  set g : WProposal → ENNReal := fun p => ∑ k : Fin 9, ∑ t : Fin 7,
    if ListCovExcept digit k t (atIndex p.1 W) p.2 then 1 else 0 with hg
  have hs : ∀ N, nearScore X N = if ClaudeWCT.WCT9.admissible N = true then g (proposal N) else 0 := by
    intro N
    unfold nearScore
    by_cases hadm : ClaudeWCT.WCT9.admissible N = true
    · simp only [hadm, if_true, hg]
      exact sum_congr rfl fun k _ => sum_congr rfl fun t _ =>
        if_congr (nearCoveredAt_iff X N k t) rfl rfl
    · simp [hadm]
  have hsum : ∑ p, g p = ((Q ^ 9 : ℕ) : ENNReal) *
      ∑ index : Fin (2 ^ 31), ∑ k : Fin 9, ∑ t : Fin 7, wctNearEnv k t (atIndex index W) := by
    simp only [hg]
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun index _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    have hT : Fintype.card Coords = Q ^ 9 := Thinning.card_table (by simp) (by simp)
    unfold wctNearEnv Thinning.nearEnv finiteAverage
    rw [hT, ENNReal.mul_div_cancel (by simp [Q]) (by simp)]
  unfold nearPrice nearPriceP finiteAverage
  simp_rw [hs]
  rw [admissibleFibre g, hsum, Fintype.card_bitVec, ← price_scale]
  simp only [div_eq_mul_inv]
  ring
theorem scale_eq_A :
    ((5 * 1001 ^ 9 : ℕ) : ENNReal) / 2 ^ 7 * ((2 ^ 31 : ℕ) : ENNReal) = 5 / 4 * (A : ENNReal) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [A, ENNReal.toReal_mul, ENNReal.toReal_div]
theorem near_summand_le_one (r : ℕ) :
    ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal) ≤ 1 :=
  (wctNearEnv_moment 0 0 r).symm.le.trans (wctNearEnv_moment_le_one 0 0 r)
theorem nearPriceP_mean (steps : ℕ) :
    uniformWordAverage steps nearPriceP =
      5 / 4 * (63 * (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
        (fun r => ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal))) := by
  unfold nearPriceP
  rw [uniformWordAverage_mul_left, uniformWordAverage_sum]
  simp_rw [uniformWordAverage_sum, wct_near_index_mean]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  set B := binomialAverage (2 ^ 31 : ENNReal)⁻¹ steps
    (fun r => ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal))
  rw [show (5 / 4 : ENNReal) * (63 * (A : ENNReal) * B) = 5 / 4 * (A : ENNReal) * (63 * B) by ring,
    ← scale_eq_A]
  push_cast
  ring
theorem near_bound_check_W (Mn Md : ℕ) (hMd : 0 < Md)
    (hcheck : poissonCheckG 271 2000 513 256 (fun r => xNum r ^ 8 * xfNum r)
      (fun r => xOk r && xfOk r) (Nn ^ 9) (63 * A) 1 Mn Md 80 = true)
    {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23) (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ nearPay r) (htail : ∀ r, 80 < r → g r ≤ 1) :
    63 * (A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ T g ≤ (Mn : ENNReal) / Md := by
  have h := poissonCheckW_sound (f := fun r => xNum r ^ 8 * xfNum r) (ok := fun r => xOk r && xfOk r)
    (dbase := Nn ^ 9) (sn := 63 * A) (sd := 1) (Mn := Mn) (Md := Md) hcheck
    (by decide) (by norm_num) hMd hT1 hT2 g
    (fun r hr => (hpay r hr).trans_eq (nearPay_eq r)) htail
  simpa only [Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_ofNat] using h
def nearCheckW32 : Bool :=
  poissonCheckG 271 2000 513 256 (fun r => xNum r ^ 8 * xfNum r) (fun r => xOk r && xfOk r)
    (Nn ^ 9) (63 * A) 1 32 1 80
theorem nearW32_ok : nearCheckW32 = true := by decide +kernel
section Window3
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem wct_near_bound_tight_window : uniformWordAverage T nearPriceP ≤ 40 := by
  rw [nearPriceP_mean]
  have h := near_bound_check_W 32 1 (by norm_num) nearW32_ok hT1 hT2
    (fun r => ((xNum r ^ 8 * xfNum r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal))
    (fun r _ => (nearPay_eq r).ge) (fun r _ => near_summand_le_one r)
  simp only [Nat.cast_ofNat, Nat.cast_one, div_one] at h
  calc
    _ ≤ (5 / 4 : ENNReal) * 32 := mul_le_mul' le_rfl h
    _ = 40 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
theorem wct_near_bound_window : uniformWordAverage T nearPriceP ≤ 6463 / 16 := by
  refine (wct_near_bound_tight_window hT1 hT2).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]
end Window3
theorem near_bound_add_charge : (6463 / 16 : ENNReal) + 1 / 16 = 404 := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div]
theorem near_bound_eq_sub : (6463 / 16 : ENNReal) = 404 - 1 / 16 := by
  rw [← near_bound_add_charge]
  exact (ENNReal.add_sub_cancel_right (by finiteness)).symm
theorem wct_near_bound : uniformWordAverage wctHorizon nearPriceP ≤ 6463 / 16 :=
  wct_near_bound_window wctHorizon_ge wctHorizon_le
theorem wct_near_bound_tight : uniformWordAverage wctHorizon nearPriceP ≤ 40 :=
  wct_near_bound_tight_window wctHorizon_ge wctHorizon_le
theorem wct_near_bound_sub : uniformWordAverage wctHorizon nearPriceP ≤ 404 - 1 / 16 := by
  rw [← near_bound_eq_sub]
  exact wct_near_bound
theorem wctSpecFinal_nearPrice (X : List HashOutput) :
    nearPrice X = nearPriceP ((wctSpecFinal).proposals X) := nearPrice_eq_nearPriceP X
theorem wct_near_bound_2_32 : uniformWordAverage (2 ^ 32) nearPriceP ≤ 6463 / 16 :=
  wct_near_bound_window le_rfl (by norm_num)
theorem wct_near_bound_tight_2_32 : uniformWordAverage (2 ^ 32) nearPriceP ≤ 40 :=
  wct_near_bound_tight_window le_rfl (by norm_num)
theorem wct_near_bound_sub_2_32 : uniformWordAverage (2 ^ 32) nearPriceP ≤ 404 - 1 / 16 := by
  rw [← near_bound_eq_sub]
  exact wct_near_bound_2_32
theorem wctSpecFinal32_nearPrice (X : List HashOutput) :
    nearPrice X = nearPriceP ((wctSpecFinal32).proposals X) := nearPrice_eq_nearPriceP X
end ClaudeWCT.Numerics.WCTPrice
end

section





namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le
  pmf_expectedValue_left_mul expectedValue_list_sum' finiteAverage_expectedValue)
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
open ClaudeWCT.Bank.WCT (WProposal)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable abbrev nearSpec : ClaudeWCT.Bank.FtsBankSpec WProposal := bankSpec.toFtsBankSpec
theorem nearSpec_admissible : nearSpec.admissible = WCT9.admissible := rfl
theorem nearSpec_proposals (X : List HashOutput) : nearSpec.proposals X = X.map ClaudeWCT.Bank.WCT.proposal := rfl
theorem nearPrice_proposals (X : List HashOutput) :
    Guess.nearPrice X = ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X) :=
  ClaudeWCT.Numerics.WCTPrice.nearPrice_eq_nearPriceP X
noncomputable def nearForecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord nearSpec.accepted R) (fun F => Guess.nearScore (X ++ F) N)
theorem nearForecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearForecast R (X ++ [A]) N) = nearForecast (R + 1) X N := by
  unfold nearForecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]
theorem nearScore_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    Guess.nearScore X N ≤ nearForecast R X N := by
  unfold nearForecast
  calc
    Guess.nearScore X N = expectedValue (independentProposalWord nearSpec.accepted R) (fun _ => Guess.nearScore X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => Guess.nearScore_append_mono X F N
noncomputable def nearPriceForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  uniformWordAverage R (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ W))
theorem average_nearForecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => nearForecast R X N) = nearPriceForecast R X / 2 ^ 128 := by
  unfold nearForecast nearPriceForecast
  rw [finiteAverage_expectedValue]
  have hav : ∀ F : List HashOutput, BPORS.finiteAverage (fun N : HashOutput => Guess.nearScore (X ++ F) N) =
      ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ nearSpec.proposals F) / 2 ^ 128 := by
    intro F
    rw [Guess.average_nearScore, nearPrice_proposals, nearSpec.proposals_append]
  simp_rw [hav]
  refine (nearSpec.expected_word_proposals R
    (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ W) by
    funext W; exact mul_comm _ _, SphincsSecurity.Concrete.uniformWordAverage_mul_left, mul_comm]
theorem nearPriceForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue nearSpec.accepted (fun A => nearPriceForecast R (X ++ [A])) = nearPriceForecast (R + 1) X := by
  unfold nearPriceForecast
  rw [BPORS.uniformWordAverage_succ]
  have hA (A : HashOutput) : uniformWordAverage R
      (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals (X ++ [A]) ++ W)) =
      (fun p : WProposal => uniformWordAverage R
        (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ p :: W))) (nearSpec.proposal A) := by
    simp [ClaudeWCT.Bank.FtsBankSpec.proposals, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact nearSpec.expected_accepted_proposal (fun p => uniformWordAverage R
    (fun W => ClaudeWCT.Numerics.WCTPrice.nearPriceP (nearSpec.proposals X ++ p :: W)))
noncomputable def nearLedger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => nearForecast R X N).sum + (slack : ENNReal) * nearPriceForecast R X / 2 ^ 128
theorem nearLedger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearLedger R targets X (slack + 1) = nearLedger R targets X slack + nearPriceForecast R X / 2 ^ 128 := by
  unfold nearLedger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem nearLedger_slack_mono (R : Nat) (targets X : List HashOutput) {slack slack' : Nat} (h : slack ≤ slack') :
    nearLedger R targets X slack ≤ nearLedger R targets X slack' := by
  unfold nearLedger
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' _ le_rfl
  exact_mod_cast h
theorem nearLedger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearLedger R (targets ++ [a]) X slack) =
      nearLedger R targets X (slack + 1) := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => nearForecast R X a) =
      nearPriceForecast R X / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_nearForecast R X
  have hsplit : ∀ a, nearLedger R (targets ++ [a]) X slack = nearLedger R targets X slack + nearForecast R X a := by
    intro a
    simp only [nearLedger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0), hfa,
    nearLedger_slack_succ]
theorem nearLedger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue nearSpec.accepted (fun A => nearLedger R targets (X ++ [A]) slack) =
      nearLedger (R + 1) targets X slack := by
  unfold nearLedger
  rw [expectedValue_add, expectedValue_list_sum']
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    exact nearForecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * nearPriceForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * nearPriceForecast R (X ++ [A]) by
      funext A; ring]
    rw [pmf_expectedValue_left_mul, nearPriceForecast_step]
    ring
theorem nearLedger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    nearSpec.freshPrice (fun A => nearLedger R targets (X ++ [A]) slack) = nearLedger (R + 1) targets X slack := by
  rw [← nearSpec.expected_accepted, nearLedger_expose]
theorem nearLedger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) nearSpec.decode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (nearSpec.search rho message 0 fuel) cache)
      (fun result => result.1.elim (nearLedger (R + 1) targets X slack)
        (fun found => nearLedger R targets (X ++ [found.2]) slack)) ≤ nearLedger (R + 1) targets X slack :=
  nearSpec.search_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (nearLedger_freshPrice R targets X slack).le
theorem nearLedger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : WCT9.admissible N = true) (hcov : Guess.NearCoveredBy X N) : 1 ≤ nearLedger R targets X slack :=
  calc
    (1 : ENNReal) ≤ Guess.nearScore X N := Guess.one_le_nearScore hadm hcov
    _ ≤ nearForecast R X N := nearScore_le_forecast R X N
    _ ≤ (targets.map fun N => nearForecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem nearLedger_initial (budget : Nat) :
    nearLedger horizon [] [] budget ≤ (budget : ENNReal) * (6463 / 16) / 2 ^ 128 := by
  unfold nearLedger nearPriceForecast
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  have h := ClaudeWCT.Numerics.WCTPrice.wct_near_bound_2_32
  simpa [ClaudeWCT.Bank.FtsBankSpec.proposals, horizon] using h
noncomputable def nearPotential (b : BankCore) : ENNReal :=
  if horizon < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else nearLedger (horizon - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem nearPotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    nearPotential b' ≤ nearPotential b := by
  unfold nearPotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (nearLedger_slack_mono _ _ _ hs) hC
theorem expected_admInd_sixteenth :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) nearSpec.admInd ≤ 1 / 16 :=
  nearSpec.expected_admInd_tight.trans (ENNReal.div_le_div_left (by norm_num) 1)
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + nearSpec.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => nearPotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      nearPotential b + (1 / 16) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => nearSpec.admInd N / 2 ^ 128) ≤
      (1 / 16) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using expected_admInd_sixteenth) le_rfl
  unfold nearPotential
  simp only
  by_cases hd : horizon < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearSpec.admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (1 / 16) / 2 ^ 128 + (1 + b.reuse) := (expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ = _ := add_comm _ _
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := horizon - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearLedger R (b.targets ++ [N]) b.exposures s + nearSpec.admInd N / 2 ^ 128) + b.reuse :=
        expectedValue_add_const_le _ _ _
      _ ≤ (nearLedger R b.targets b.exposures (s + 1) + (1 / 16) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add, nearLedger_birth]
        exact add_le_add (add_le_add le_rfl hadm) le_rfl
      _ = _ := by
        rw [hs]
        ring
theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + nearSpec.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if nearSpec.Reuse cache rho m then nearPotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd)))) ≤ nearPotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : horizon < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) = 0 := by
      intro o
      unfold nearPotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold nearPotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : nearPotential b = 1 + b.reuse := by unfold nearPotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), nearPotential (b.expose C' o) ≤ 1 + b.reuse := by
      intro o
      unfold nearPotential BankCore.expose
      simp only [hr, if_true]
      split_ifs
      · exact bot_le
      · exact add_le_add le_rfl (le_of_add_le_left hC)
    split_ifs
    · unfold nearPotential; simp only [hd, if_false, if_true]; exact add_le_add le_rfl (le_of_add_le_left hC)
    · exact expectedValue_le_of_le _ fun result => hle _
  have hr' : b.reused = false := by simpa using hr
  set R0 := horizon - b.exposures.length with hR0
  have hb : nearPotential b = nearLedger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold nearPotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬nearSpec.Reuse cache rho m →
      expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd))) ≤
          nearLedger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) nearSpec.decode 0 (2 ^ 32) cache := by
      unfold ClaudeWCT.Bank.FtsBankSpec.Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < horizon
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)
            (fun result => result.1.elim (nearLedger (R + 1) b.targets b.exposures b.slack)
              (fun found => nearLedger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold nearPotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold nearPotential BankCore.expose
            have hnd : ¬horizon < (b.exposures ++ [found.2]).length := by simp; omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show horizon - (b.exposures ++ [found.2]).length = R by simp; omega]
        _ ≤ nearLedger (R + 1) b.targets b.exposures b.slack + C' :=
          (expectedValue_add_const_le _ _ _).trans
            (add_le_add (nearLedger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold nearPotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold nearPotential BankCore.expose
        have hnd : horizon < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if nearSpec.Reuse cache rho m then 1 else 0) + (nearLedger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : nearSpec.Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold nearPotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ nearSpec.reuseMass cache m + (nearLedger R0 b.targets b.exposures b.slack + C') :=
      (expectedValue_add_const_le _ _ _).trans (add_le_add (nearSpec.reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (nearLedger _ _ _ _), ← add_assoc, add_comm (nearSpec.reuseMass cache m),
        add_comm _ (nearLedger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem near_win (b : BankCore) (halive : ¬horizon < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, WCT9.admissible N = true ∧ Guess.NearCoveredBy b.exposures N) :
    1 ≤ nearPotential b := by
  unfold nearPotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hcov⟩ := h.resolve_left hr
    exact (nearLedger_win _ _ _ _ N hN hadm hcov).trans le_self_add
theorem near_initial (budget : Nat) :
    nearPotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (6463 / 16) / 2 ^ 128 := by
  unfold nearPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact nearLedger_initial budget
end ClaudeWCT.W9.T3.Security.CaseC
end

section

namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (BankCore BankCore.expose expectedValue_add_const_le DigestRowOf
  digestRowOf_unique tsum_indicator_le_of_subsingleton)
open SphincsSecurity.Completeness (searchLoop)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable def reuseC (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  ∑' m : Message, if nonces m = none then nearSpec.reuseMass rows m else 0
theorem reuseC_birth_le (rows : Sampling.RCache) (nonces : Message → Option Digest) (x : HashInput) (a : HashOutput)
    (hx : rows x = none) : reuseC (rows.cacheQuery x a) nonces ≤ reuseC rows nonces + nearSpec.admInd a / 2 ^ 128 := by
  unfold reuseC
  calc
    (∑' m : Message, if nonces m = none then nearSpec.reuseMass (rows.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if nonces m = none then nearSpec.reuseMass rows m else 0) +
          (if DigestRowOf x m then nearSpec.admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · simpa [h2] using nearSpec.reuseMass_cacheQuery_le rows x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)
theorem reuseC_sign_le (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message) (v : Digest)
    (hm : nonces m = none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' (Function.update nonces m (some v)) + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
  unfold reuseC
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if nonces m' = none then nearSpec.reuseMass rows m' else 0)]
  simp only [Function.update_self, reduceCtorEq, if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, Function.update_of_ne he, hrows m' he]
theorem reuseC_signed_eq (rows rows' : Sampling.RCache) (nonces : Message → Option Digest) (m : Message)
    (hm : nonces m ≠ none) (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    reuseC rows' nonces = reuseC rows nonces := by
  unfold reuseC
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · subst he; simp [hm]
  · simp only [hrows m' he]
theorem search_cache_frame {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) :
    ∀ fuel counter (cache : Sampling.RCache) r,
      r ∈ support (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache) →
      ∀ y, (∀ k, y ≠ inputs k) → r.2 y = cache y := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter cache r hr y _
      simp only [searchLoop, Sampling.publicProgram, simulateQ_pure] at hr
      change r ∈ support (Sampling.roRun secret (pure none) cache) at hr
      rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | succ fuel ih =>
      intro counter cache r hr y hy
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      have hfc : first.2 y = cache y := by
        rw [randomOracle.run_eq] at hfirst
        cases hc : cache (inputs counter) with
        | some a =>
            rw [hc, support_pure, Set.mem_singleton_iff] at hfirst
            rw [hfirst]
        | none =>
            rw [hc, mem_support_bind_iff] at hfirst
            obtain ⟨a, -, hfa⟩ := hfirst
            rw [support_pure, Set.mem_singleton_iff] at hfa
            rw [hfa]
            exact QueryCache.cacheQuery_of_ne cache a (hy counter)
      cases hd : decoder first.1 with
      | none =>
          rw [hd] at hr
          exact (ih (counter + 1) first.2 r hr y hy).trans hfc
      | some value =>
          rw [hd] at hr
          change r ∈ support (Sampling.roRun secret (pure _) first.2) at hr
          rw [Sampling.roRun_pure, support_pure, Set.mem_singleton_iff] at hr
          rw [hr]
          exact hfc
theorem digestSearch_cache_frame (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ y, (∀ k, y ≠ Sampling.digestTrial rho m k) → r.2 y = cache y := by
  unfold ClaudeWCT.Bank.FtsBankSpec.search at hr
  exact search_cache_frame secret (Sampling.digestTrial rho m) nearSpec.decode _ fuel 0 cache r hr
theorem digestTrial_ne_of_message {rho rho' : Digest} {m m' : Message} (hm : m' ≠ m) (c c' : Nat)
    (hc' : c' < 2 ^ 32) : Sampling.digestTrial rho' m' c' ≠ Sampling.digestTrial rho m c := by
  intro he
  have h1 : DigestRowOf (Sampling.digestTrial rho' m' c') m' := ⟨(rho', ⟨c', hc'⟩), rfl⟩
  have h2 : DigestRowOf (Sampling.digestTrial rho m (c % 2 ^ 32)) m :=
    ⟨(rho, ⟨c % 2 ^ 32, Nat.mod_lt _ (by decide)⟩), rfl⟩
  have h3 : Sampling.digestTrial rho m (c % 2 ^ 32) = Sampling.digestTrial rho m c := by
    unfold Sampling.digestTrial
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofNat]
  rw [h3, ← he] at h2
  exact hm (digestRowOf_unique h1 h2)
theorem digestSearch_reuseMass (secret : BitVec 256) (rho : Digest) (m : Message) (fuel : Nat)
    (cache : Sampling.RCache) (r) (hr : r ∈ support (Sampling.roRun secret (nearSpec.search rho m 0 fuel) cache)) :
    ∀ m', m' ≠ m → nearSpec.reuseMass r.2 m' = nearSpec.reuseMass cache m' := by
  intro m' hm
  unfold ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
  congr 1
  apply tsum_congr
  intro p
  rw [digestSearch_cache_frame secret rho m fuel cache r hr _
    (fun k => digestTrial_ne_of_message hm k p.2.val p.2.isLt)]
noncomputable def nearMemPotential (q : Nat) (births exposures : List HashOutput) (reused : Bool)
    (rows : Sampling.RCache) (nonces : Message → Option Digest) : ENNReal :=
  if q < births.length then 0
  else nearPotential ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ +
    ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128)
theorem mem_birth (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (x : HashInput) (hx : rows x = none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun a : HashOutput => nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : births.length < q
  · obtain ⟨s, hs⟩ : ∃ s, q - births.length = s + 1 := ⟨q - births.length - 1, by omega⟩
    have hb : nearMemPotential q births exposures reused rows nonces =
        nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + ((s + 1 : Nat) : ENNReal) *
          ((1 / 16) / 2 ^ 128) := by
      unfold nearMemPotential
      rw [if_neg (by omega), hs]
    have ha : ∀ a : HashOutput, nearMemPotential q (births ++ [a]) exposures reused (rows.cacheQuery x a) nonces =
        nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
          targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces } +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
      intro a
      unfold nearMemPotential
      have hl : (births ++ [a]).length = births.length + 1 := by simp
      rw [if_neg (by omega), show q - (births ++ [a]).length = s by omega]
    simp_rw [ha]
    rw [hb]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
            nearPotential { (⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ : BankCore) with
              targets := births ++ [a], slack := s, reuse := reuseC (rows.cacheQuery x a) nonces }) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := expectedValue_add_const_le _ _ _
      _ ≤ (nearPotential ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ + (1 / 16) / 2 ^ 128) +
          (s : ENNReal) * ((1 / 16) / 2 ^ 128) := by
        apply add_le_add _ le_rfl
        exact near_birth ⟨births, exposures, reused, reuseC rows nonces, s + 1⟩ s rfl _
          (fun a => reuseC_birth_le rows nonces x a hx)
      _ = _ := by
        push_cast
        ring
  · apply expectedValue_le_of_le
    intro a
    unfold nearMemPotential
    rw [if_pos (by simp; omega)]
    exact bot_le
theorem mem_sign_fresh (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m = none) (secret : BitVec 256) (fuel : Nat)
    (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
      expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
        nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)))) ≤
      nearMemPotential q births exposures reused rows nonces := by
  by_cases hq : q < births.length
  · apply expectedValue_le_of_le
    intro v
    apply expectedValue_le_of_le
    intro r
    unfold nearMemPotential
    rw [if_pos hq]
    exact bot_le
  push Not at hq
  set C0 := reuseC rows (Function.update nonces m (some 0)) with hC0
  have hupd : ∀ v : Digest, reuseC rows (Function.update nonces m (some v)) = C0 := by
    intro v
    unfold reuseC
    apply tsum_congr
    intro m'
    by_cases he : m' = m
    · subst he; simp
    · simp only [Function.update_of_ne he]
  have hafter : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      reuseC r.2 (Function.update nonces m (some v)) = C0 := by
    intro v r hr
    rw [reuseC_signed_eq rows r.2 _ m (by simp) (digestSearch_reuseMass secret v m fuel rows r hr), hupd]
  have hC : C0 + nearSpec.reuseMass rows m ≤ reuseC rows nonces := by
    rw [← hupd 0]
    exact reuseC_sign_le rows rows nonces m 0 hm (fun _ _ => rfl)
  set b : BankCore := ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ with hb
  set extra : ENNReal := ((q - births.length : Nat) : ENNReal) * ((1 / 16) / 2 ^ 128) with hextra
  have hbefore : nearMemPotential q births exposures reused rows nonces = nearPotential b + extra := by
    unfold nearMemPotential
    rw [if_neg (by omega)]
  have hpoint : ∀ v r, r ∈ support (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) →
      nearMemPotential q births (exposures ++ (r.1.map Prod.snd).toList)
          (reused || decide (nearSpec.Reuse rows v m)) r.2 (Function.update nonces m (some v)) =
        nearPotential ⟨births, exposures ++ (r.1.map Prod.snd).toList,
          reused || decide (nearSpec.Reuse rows v m), C0, q - births.length⟩ + extra := by
    intro v r hr
    unfold nearMemPotential
    rw [if_neg (by omega), hafter v r hr]
  have hreuse : ∀ (o : Option HashOutput), nearPotential ⟨births, exposures ++ o.toList, true, C0,
      q - births.length⟩ ≤ nearPotential { b with reused := true, reuse := C0 } := by
    intro o
    have hl : exposures.length ≤ (exposures ++ o.toList).length := by simp
    unfold nearPotential
    rw [hb]
    simp only [if_true]
    by_cases h2 : horizon < exposures.length
    · rw [if_pos (lt_of_lt_of_le h2 hl)]; exact bot_le
    · by_cases h1 : horizon < (exposures ++ o.toList).length
      · rw [if_pos h1]; exact bot_le
      · rw [if_neg h1, if_neg h2]
  rw [hbefore]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra) := by
      apply expectedValue_mono
      intro v
      calc
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd))) + extra) := by
          apply expectedValue_mono_of_support
          intro r hr
          rw [hpoint v r hr]
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, decide_true, Bool.or_true, if_true]
            exact hreuse _
          · simp only [hre, decide_false, Bool.or_false, if_false]
            exact le_of_eq rfl
        _ ≤ expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows) (fun r =>
            (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
              else nearPotential (b.expose C0 (r.1.map Prod.snd)))) + extra := expectedValue_add_const_le _ _ _
        _ ≤ _ := by
          apply add_le_add _ le_rfl
          by_cases hre : nearSpec.Reuse rows v m
          · simp only [hre, if_true]
            exact expectedValue_le_of_le _ fun _ => le_rfl
          · simp only [hre, if_false]
            exact le_rfl
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest) (fun v =>
        (if nearSpec.Reuse rows v m then nearPotential { b with reused := true, reuse := C0 }
          else expectedValue (Sampling.roRun secret (nearSpec.search v m 0 fuel) rows)
            (fun r => nearPotential (b.expose C0 (r.1.map Prod.snd))))) + extra := expectedValue_add_const_le _ _ _
    _ ≤ _ := add_le_add (near_sign b rows m C0 hC secret fuel hfuel) le_rfl
theorem mem_sign_repeat (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows rows' : Sampling.RCache)
    (nonces : Message → Option Digest) (m : Message) (hm : nonces m ≠ none)
    (hrows : ∀ m', m' ≠ m → nearSpec.reuseMass rows' m' = nearSpec.reuseMass rows m') :
    nearMemPotential q births exposures reused rows' nonces = nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [reuseC_signed_eq rows rows' nonces m hm hrows]
theorem mem_initial (q : Nat) :
    nearMemPotential q [] [] false ∅ (fun _ => none) ≤ (q : ENNReal) * 404 / 2 ^ 128 := by
  unfold nearMemPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Nat.sub_zero]
  have hC : reuseC ∅ (fun _ => none) = 0 := by
    unfold reuseC ClaudeWCT.Bank.FtsBankSpec.reuseMass ClaudeWCT.Bank.FtsBankSpec.admissibleEntry
    simp
  have hn := near_initial q
  rw [show (⟨[], [], false, reuseC ∅ (fun _ => none), q⟩ : BankCore) = ⟨[], [], false, 0, q⟩ by rw [hC]]
  calc
    _ ≤ (q : ENNReal) * (6463 / 16) / 2 ^ 128 + (q : ENNReal) * ((1 / 16) / 2 ^ 128) := add_le_add hn le_rfl
    _ = (q : ENNReal) * ((6463 / 16) + 1 / 16) / 2 ^ 128 := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [ClaudeWCT.Numerics.WCTPrice.near_bound_add_charge]
theorem mem_win (q : Nat) (births exposures : List HashOutput) (reused : Bool) (rows : Sampling.RCache)
    (nonces : Message → Option Digest) (hq : births.length ≤ q) (hlen : exposures.length ≤ horizon)
    (h : reused = true ∨ ∃ N ∈ births, WCT9.admissible N = true ∧ Guess.NearCoveredBy exposures N) :
    1 ≤ nearMemPotential q births exposures reused rows nonces := by
  unfold nearMemPotential
  rw [if_neg (by omega)]
  exact (near_win ⟨births, exposures, reused, reuseC rows nonces, q - births.length⟩ (by simp only; omega) h).trans
    le_self_add
end ClaudeWCT.W9.T3.Security.CaseC
end
