import SigGolfCandidate.T3.Secc.CaseCSearch
import SigGolfCandidate.T3.Secc.CaseCExcess
import SigGolfCandidate.T3.Secc.CaseCCover

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem pmf_expectedValue_left_mul {α : Type} (law : PMF α) (factor : ENNReal) (payoff : α → ENNReal) :
    expectedValue law (fun result => factor * payoff result) = factor * expectedValue law payoff := by
  unfold expectedValue
  simp_rw [mul_left_comm _ factor]
  exact ENNReal.tsum_mul_left
noncomputable def ledger (R : Nat) (targets X : List HashOutput) (slack : Nat) : ENNReal :=
  (targets.map fun N => forecast R X N).sum + (slack : ENNReal) * excessForecast R X / 2 ^ 128
theorem ledger_slack_succ (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    ledger R targets X (slack + 1) = ledger R targets X slack + excessForecast R X / 2 ^ 128 := by
  unfold ledger
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div, add_assoc]
theorem ledger_slack_mono (R : Nat) (targets X : List HashOutput) {slack slack' : Nat} (h : slack ≤ slack') :
    ledger R targets X slack ≤ ledger R targets X slack' := by
  unfold ledger
  apply add_le_add le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' _ le_rfl
  exact_mod_cast h
theorem ledger_birth (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => ledger R (targets ++ [a]) X slack) ≤
      ledger R targets X (slack + 1) + theta / 2 ^ 128 := by
  have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => forecast R X a) ≤
      (theta + excessForecast R X) / 2 ^ 128 := by
    rw [BPORS.expected_uniform_eq_finiteAverage]
    exact average_forecast_le R X
  have hsplit : ∀ a, ledger R (targets ++ [a]) X slack = ledger R targets X slack + forecast R X a := by
    intro a
    simp only [ledger, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero]
    ring
  simp_rw [hsplit]
  rw [expectedValue_add, expectedValue_const (by simp : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0),
    ledger_slack_succ, add_assoc]
  exact add_le_add le_rfl (hfa.trans (by rw [ENNReal.add_div, add_comm]))
theorem expectedValue_list_sum' {α β : Type} (law : PMF α) (l : List β) (f : β → α → ENNReal) :
    expectedValue law (fun a => (l.map fun b => f b a).sum) = (l.map fun b => expectedValue law (f b)).sum := by
  induction l with
  | nil => simp [expectedValue]
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [expectedValue_add, ih]
theorem ledger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue accepted (fun A => ledger R targets (X ++ [A]) slack) = ledger (R + 1) targets X slack := by
  unfold ledger
  rw [expectedValue_add, expectedValue_list_sum']
  congr 1
  · congr 1
    apply List.map_congr_left
    intro N _
    exact forecast_step R X N
  · simp only [div_eq_mul_inv]
    rw [show (fun A : HashOutput => (slack : ENNReal) * excessForecast R (X ++ [A]) * (2 ^ 128 : ENNReal)⁻¹) =
        fun A => (slack : ENNReal) * (2 ^ 128 : ENNReal)⁻¹ * excessForecast R (X ++ [A]) by
      funext A; ring]
    rw [pmf_expectedValue_left_mul, excessForecast_step]
    ring
theorem ledger_freshPrice (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    Sampling.WeightedSelection.freshPrice (fun A => ledger R targets (X ++ [A]) slack) =
      ledger (R + 1) targets X slack := by
  rw [← expected_accepted, ledger_expose]
theorem ledger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat) (hlimit : fuel ≤ 2 ^ 32)
    (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) Sampling.digestDecode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => result.1.elim (ledger (R + 1) targets X slack)
        (fun found => ledger R targets (X ++ [found.2]) slack)) ≤ ledger (R + 1) targets X slack :=
  digestSearch_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (ledger_freshPrice R targets X slack).le
theorem ledger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : admissible (selections N) = true) (hgate : digestGate N=true) (hcov : ∀ c, CoordCovered X N c) : 1 ≤ ledger R targets X slack :=
  calc
    (1 : ENNReal) ≤ score X N := one_le_score X N (outLeaves_injective N hadm) hgate hcov
    _ ≤ forecast R X N := score_le_forecast R X N
    _ ≤ (targets.map fun N => forecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add
theorem ledger_win_opened (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : admissible (selections N) = true) (hgate : digestGate N=true)
    (hopen : ∀ f ∈ BPair.openedPositions N, ∃ out ∈ X, f ∈ BPair.openedPositions out) :
    1 ≤ ledger R targets X slack :=
  ledger_win R targets X slack N hN hadm hgate fun c =>
    coordCovered_of_opened X N c fun j => hopen _ (opened_mem N c j)
theorem ledger_initial (budget : Nat) :
    ledger BPORS.Numeric.proposalLength [] [] budget ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  unfold ledger
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  unfold excessForecast
  simpa [labels] using excess_three_quarters
theorem theta_add_sixteenth_le_one : theta + 1 / 64 ≤ 1 := by
  unfold theta
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
noncomputable def admInd (a : HashOutput) : ENNReal := if digestAdmissible a = true then 1 else 0
theorem acceptance_le_sixteenth : DigestSampling.acceptanceProbability ≤ 1 / 16 :=
  Acceptance.acceptanceProbability_le_one_sixteenth
theorem expected_admInd : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd ≤ 1 / 16 := by
  have h : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd = DigestSampling.acceptanceProbability := by
    rw [← Sampling.digest_acceptanceProbability, ← expectedValue_ite_one]
    rfl
  rw [h]
  exact acceptance_le_sixteenth
def CoveredBy (X : List HashOutput) (N : HashOutput) : Prop :=
  ∀ f ∈ BPair.openedPositions N, ∃ out ∈ X, f ∈ BPair.openedPositions out
theorem expected_admInd_tight : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd ≤ 1/64 := by
  have he : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) admInd=DigestSampling.acceptanceProbability := by
    rw [←Sampling.digest_acceptanceProbability,←expectedValue_ite_one]
    rfl
  rw [he]
  unfold DigestSampling.acceptanceProbability SigGolfResearch.Gate6.acceptance
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_one]
  norm_num
structure BankCore where
  targets : List HashOutput
  exposures : List HashOutput
  reused : Bool
  reuse : ENNReal
  slack : Nat
noncomputable def corePotential (b : BankCore) : ENNReal :=
  if BPORS.Numeric.proposalLength < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else ledger (BPORS.Numeric.proposalLength - b.exposures.length) b.targets b.exposures b.slack + b.reuse
theorem expectedValue_add_const_le {α : Type} (p : ProbComp α) (f : α → ENNReal) (c : ENNReal) :
    expectedValue p (fun x => f x + c) ≤ expectedValue p f + c := by
  rw [expectedValue_add]
  exact add_le_add le_rfl (expectedValue_le_of_le p fun _ => le_rfl)
theorem corePotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    corePotential b' ≤ corePotential b := by
  unfold corePotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (ledger_slack_mono _ _ _ hs) hC
theorem core_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      corePotential b + (theta + 1 / 64) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => admInd N / 2 ^ 128) ≤ (1 / 64) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using expected_admInd_tight) le_rfl
  unfold corePotential
  simp only
  by_cases hd : BPORS.Numeric.proposalLength < b.exposures.length
  · simp only [hd, if_true]
    exact (expectedValue_le_of_le _ fun _ => le_rfl).trans bot_le
  simp only [hd, if_false]
  by_cases hr : b.reused = true
  · simp only [hr, if_true]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => admInd N / 2 ^ 128 + (1 + b.reuse)) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ (1 / 64) / 2 ^ 128 + (1 + b.reuse) := (expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ ≤ _ := by
        rw [add_comm]
        apply add_le_add le_rfl
        apply ENNReal.div_le_div_right
        exact le_add_self
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := BPORS.Numeric.proposalLength - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (ledger R (b.targets ++ [N]) b.exposures s + admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => ledger R (b.targets ++ [N]) b.exposures s + admInd N / 2 ^ 128) + b.reuse :=
        expectedValue_add_const_le _ _ _
      _ ≤ (ledger R b.targets b.exposures (s + 1) + theta / 2 ^ 128 + (1 / 64) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add]
        exact add_le_add (add_le_add (ledger_birth R b.targets b.exposures s) hadm) le_rfl
      _ = _ := by
        rw [hs, ENNReal.add_div]
        ring
def BankCore.expose (b : BankCore) (C' : ENNReal) (o : Option HashOutput) : BankCore :=
  { b with exposures := b.exposures ++ o.toList, reuse := C' }
theorem core_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if Reuse cache rho m then corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ corePotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : BPORS.Numeric.proposalLength < b.exposures.length
  · apply expectedValue_le_of_le
    intro rho
    have h0 : ∀ (o : Option HashOutput), corePotential (b.expose C' o) = 0 := by
      intro o
      unfold corePotential BankCore.expose
      simp only
      rw [if_pos (lt_of_lt_of_le hd (hlenA o))]
    split_ifs
    · unfold corePotential; simp only; rw [if_pos hd]; exact bot_le
    · exact (expectedValue_le_of_le _ fun result => (h0 _).le).trans bot_le
  by_cases hr : b.reused = true
  · have hb : corePotential b = 1 + b.reuse := by unfold corePotential; simp [hd, hr]
    rw [hb]
    apply expectedValue_le_of_le
    intro rho
    have hle : ∀ (o : Option HashOutput), corePotential (b.expose C' o) ≤ 1 + b.reuse := by
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
  set R0 := BPORS.Numeric.proposalLength - b.exposures.length with hR0
  have hb : corePotential b = ledger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold corePotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬Reuse cache rho m →
      expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => corePotential (b.expose C' (result.1.map Prod.snd))) ≤
          ledger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) Sampling.digestDecode 0 (2 ^ 32) cache := by
      unfold Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < BPORS.Numeric.proposalLength
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
            (fun result => result.1.elim (ledger (R + 1) b.targets b.exposures b.slack)
              (fun found => ledger R b.targets (b.exposures ++ [found.2]) b.slack) + C') := by
          apply expectedValue_mono
          intro result
          rcases result with ⟨_ | found, cache'⟩
          · unfold corePotential BankCore.expose
            simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr',
              Bool.false_eq_true, Option.elim_none]
            rw [← hR]
          · unfold corePotential BankCore.expose
            have hl1 : (b.exposures ++ [found.2]).length = b.exposures.length + 1 := by simp
            have hnd : ¬BPORS.Numeric.proposalLength < (b.exposures ++ [found.2]).length := by omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show BPORS.Numeric.proposalLength - (b.exposures ++ [found.2]).length = R by omega]
        _ ≤ ledger (R + 1) b.targets b.exposures b.slack + C' :=
          (expectedValue_add_const_le _ _ _).trans
            (add_le_add (ledger_search secret rho m fuel hfuel cache hrej R b.targets b.exposures b.slack) le_rfl)
        _ = _ := by rw [hR]
    · apply expectedValue_le_of_le
      intro result
      rcases result with ⟨_ | found, cache'⟩
      · unfold corePotential BankCore.expose
        simp only [Option.map_none, Option.toList_none, List.append_nil, hd, if_false, hr', Bool.false_eq_true]
        exact le_rfl
      · unfold corePotential BankCore.expose
        have hnd : BPORS.Numeric.proposalLength < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if Reuse cache rho m then 1 else 0) + (ledger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold corePotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ reuseMass cache m + (ledger R0 b.targets b.exposures b.slack + C') :=
      (expectedValue_add_const_le _ _ _).trans (add_le_add (reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (ledger _ _ _ _), ← add_assoc, add_comm (reuseMass cache m), add_comm _ (ledger _ _ _ _)]
      exact add_le_add le_rfl hC
theorem core_win (b : BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N=true ∧ CoveredBy b.exposures N) :
    1 ≤ corePotential b := by
  unfold corePotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hgate, hcov⟩ := h.resolve_left hr
    exact (ledger_win_opened _ _ _ _ N hN hadm hgate hcov).trans le_self_add
theorem core_initial (budget : Nat) :
    corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  unfold corePotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact ledger_initial budget
end SigGolfCandidate.T3.Security.CaseC
