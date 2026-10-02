import SigGolfCandidate.T3.Secc.CaseCNearScore
import SigGolfCandidate.T3.Secc.CaseCCore

/-!
# Stream CC: the near-score bank (world-independent)

The near analogue of `CaseCCore`: forecasts of the near score under future accepted exposures, priced by SEC's
`fullNearPrice` (no excess split is needed: every birth is prepaid at its forecast price, which is a martingale).

    nearLedger R T X slack = Σ_{N ∈ T} nearForecast R X N + slack · nearPriceForecast R X / 2^128

* `nearLedger_birth` (**exact**): a fresh uniform target consumes one unit of slack;
* `nearLedger_expose` / `nearLedger_search`: accepted exposures are a martingale, the digest rejection search a
  supermartingale;
* `nearLedger_win`: an admissible target with 20 of its 21 openings exposed (`NearCoveredBy`) holds a full unit;
* `nearLedger_initial`: `≤ budget · 203 / 2^128` (`fullNearPrice_bound`).

The macro-step bank `nearPotential` on `BankCore` (same abstract state as `corePotential`): `near_birth` (charge
`(1/16)/2^128`, the reuse mass of the new row), `near_sign`, `nearPotential_mono`, `near_win`, `near_initial`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Concrete (independentProposalWord uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Near forecasts -/

/-- **Near forecast** of `N`: its expected near score after `R` more independent accepted selections. -/
noncomputable def nearForecast (R : Nat) (X : List HashOutput) (N : HashOutput) : ENNReal :=
  expectedValue (independentProposalWord accepted R) (fun F => nearScore (X ++ F) N)

theorem nearForecast_step (R : Nat) (X : List HashOutput) (N : HashOutput) :
    expectedValue accepted (fun A => nearForecast R (X ++ [A]) N) = nearForecast (R + 1) X N := by
  unfold nearForecast
  rw [independentProposalWord, ← PMF.monad_bind_eq_bind, expectedValue_bind]
  apply congrArg
  funext A
  rw [← PMF.monad_map_eq_map, expectedValue_map]
  apply congrArg
  funext F
  simp only [List.append_assoc, List.singleton_append]

theorem nearScore_le_forecast (R : Nat) (X : List HashOutput) (N : HashOutput) :
    nearScore X N ≤ nearForecast R X N := by
  unfold nearForecast
  calc
    nearScore X N = expectedValue (independentProposalWord accepted R) (fun _ => nearScore X N) :=
      (expectedValue_const (by simp) _).symm
    _ ≤ _ := expectedValue_mono _ fun F => nearScore_append_mono X F N

/-- The completed-word near price of the exposures. -/
noncomputable def nearPriceForecast (R : Nat) (X : List HashOutput) : ENNReal :=
  uniformWordAverage R (fun W => BPORS.History.fullNearPrice (labels X ++ W))

theorem average_nearForecast (R : Nat) (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => nearForecast R X N) = nearPriceForecast R X / 2 ^ 128 := by
  unfold nearForecast nearPriceForecast
  rw [finiteAverage_expectedValue]
  simp_rw [average_nearScore, labels_append]
  refine (expected_word_labels R (fun W => BPORS.History.fullNearPrice (labels X ++ W) / 2 ^ 128)).trans ?_
  simp only [div_eq_mul_inv]
  rw [show (fun W => BPORS.History.fullNearPrice (labels X ++ W) * (2 ^ 128 : ENNReal)⁻¹) =
      fun W => (2 ^ 128 : ENNReal)⁻¹ * BPORS.History.fullNearPrice (labels X ++ W) by
    funext W; exact mul_comm _ _, SphincsSecurity.Concrete.uniformWordAverage_mul_left, mul_comm]

theorem nearPriceForecast_step (R : Nat) (X : List HashOutput) :
    expectedValue accepted (fun A => nearPriceForecast R (X ++ [A])) = nearPriceForecast (R + 1) X := by
  unfold nearPriceForecast
  rw [BPORS.uniformWordAverage_succ]
  have hA (A : HashOutput) : uniformWordAverage R
      (fun W => BPORS.History.fullNearPrice (labels (X ++ [A]) ++ W)) =
      (fun p : BPORS.History.Proposal => uniformWordAverage R
        (fun W => BPORS.History.fullNearPrice (labels X ++ p :: W))) (label A) := by
    simp [labels, List.map_append, List.append_assoc]
  simp_rw [hA]
  exact expected_accepted_label (fun p => uniformWordAverage R
    (fun W => BPORS.History.fullNearPrice (labels X ++ p :: W)))

/-! ## The near ledger -/

/-- **The near ledger**: near forecasts of the targets plus the prepaid near price of `slack` future births. -/
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

/-- **Birth step** (exact): a fresh uniform target consumes one unit of slack. -/
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

/-- **Exposure step**: an accepted exposure is an exact martingale step. -/
theorem nearLedger_expose (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue accepted (fun A => nearLedger R targets (X ++ [A]) slack) = nearLedger (R + 1) targets X slack := by
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
    Sampling.WeightedSelection.freshPrice (fun A => nearLedger R targets (X ++ [A]) slack) =
      nearLedger (R + 1) targets X slack := by
  rw [← expected_accepted, nearLedger_expose]

/-- **Search step**: the digest rejection search (cached trials rejecting) is a supermartingale step. -/
theorem nearLedger_search (secret : BitVec 256) (rho : Digest) (message : Message) (fuel : Nat)
    (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) Sampling.digestDecode 0 (2 ^ 32) cache)
    (R : Nat) (targets X : List HashOutput) (slack : Nat) :
    expectedValue (Sampling.roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => result.1.elim (nearLedger (R + 1) targets X slack)
        (fun found => nearLedger R targets (X ++ [found.2]) slack)) ≤ nearLedger (R + 1) targets X slack :=
  digestSearch_le_price secret rho message fuel hlimit cache hreject _ _ _ le_rfl
    (nearLedger_freshPrice R targets X slack).le

/-! ## Near-covered targets -/

/-- **The near-certificate shape**: all openings of `N` but one are opened by some exposure. -/
def NearCoveredBy (X : List HashOutput) (N : HashOutput) : Prop :=
  ∃ f ∈ BPair.openedPositions N, ∀ g ∈ BPair.openedPositions N, g ≠ f →
    ∃ out ∈ X, g ∈ BPair.openedPositions out

theorem slot_of_opened (X : List HashOutput) (N : HashOutput) (c : Fin 7) (j : Fin 3) (out : HashOutput)
    (hout : out ∈ X)
    (h : ((outIdx N, c, BPair.leafIndex (outBucket N c).val (outLeaves N c j).val) : BPair.FtsCoord) ∈
      BPair.openedPositions out) :
    ∃ s : Slot X (outIdx N) c (outBucket N c), slotValue X (outIdx N) c (outBucket N c) s = outLeaves N c j := by
  obtain ⟨hidx, j', hj'⟩ := mem_openedPositions out _ h
  obtain ⟨hb, hl⟩ := leafIndex_inj hj'
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hout
  refine ⟨⟨(k, j'), ?_, ?_⟩, ?_⟩
  · rw [hk]; exact hidx.symm
  · rw [hk]; exact hb.symm
  · simp only [slotValue]
    rw [hk]
    exact hl.symm

theorem one_le_nearScore (X : List HashOutput) (N : HashOutput) (hadm : admissible (selections N) = true) (hgate : digestGate N=true)
    (h : NearCoveredBy X N) : 1 ≤ nearScore X N := by
  obtain ⟨f, hf, hcov⟩ := h
  have hinj := outLeaves_injective N hadm
  obtain ⟨-, jf, hjf⟩ := mem_openedPositions N f hf
  refine (one_le_nearTermAt X N f.2.1 jf hinj hgate ?_).trans (nearTermAt_le_nearScore X N f.2.1 jf)
  intro c j hcj
  have hne : ((outIdx N, c, BPair.leafIndex (outBucket N c).val (outLeaves N c j).val) : BPair.FtsCoord) ≠ f := by
    intro he
    apply hcj
    have h1 : c = f.2.1 := by rw [← he]
    subst h1
    have h2 := congrArg (fun x : BPair.FtsCoord => x.2.2) he
    simp only at h2
    rw [hjf] at h2
    exact Prod.ext rfl (hinj _ (leafIndex_inj h2).2)
  obtain ⟨out, hout, hopen⟩ := hcov _ (opened_mem N c j) hne
  exact slot_of_opened X N c j out hout hopen

theorem nearLedger_win (R : Nat) (targets X : List HashOutput) (slack : Nat) (N : HashOutput) (hN : N ∈ targets)
    (hadm : admissible (selections N) = true) (hgate : digestGate N=true) (hcov : NearCoveredBy X N) : 1 ≤ nearLedger R targets X slack :=
  calc
    (1 : ENNReal) ≤ nearScore X N := one_le_nearScore X N hadm hgate hcov
    _ ≤ nearForecast R X N := nearScore_le_forecast R X N
    _ ≤ (targets.map fun N => nearForecast R X N).sum := List.le_sum_of_mem (List.mem_map_of_mem hN)
    _ ≤ _ := le_self_add

theorem nearLedger_initial (budget : Nat) :
    nearLedger BPORS.Numeric.proposalLength [] [] budget ≤ (budget : ENNReal) * 203 / 2 ^ 128 := by
  unfold nearLedger nearPriceForecast
  simp only [List.map_nil, List.sum_nil, zero_add]
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  simpa [labels] using BPORS.History.fullNearPrice_bound

/-! ## The macro-step near bank (abstract state `BankCore`) -/

/-- **The near potential** (dead beyond the horizon; `1 + C` after a reuse). -/
noncomputable def nearPotential (b : BankCore) : ENNReal :=
  if BPORS.Numeric.proposalLength < b.exposures.length then 0
  else if b.reused = true then 1 + b.reuse
  else nearLedger (BPORS.Numeric.proposalLength - b.exposures.length) b.targets b.exposures b.slack + b.reuse

theorem nearPotential_mono (b b' : BankCore) (ht : b'.targets = b.targets) (hx : b'.exposures = b.exposures)
    (hr : b'.reused = b.reused) (hC : b'.reuse ≤ b.reuse) (hs : b'.slack ≤ b.slack) :
    nearPotential b' ≤ nearPotential b := by
  unfold nearPotential
  rw [ht, hx, hr]
  split_ifs
  · exact le_rfl
  · exact add_le_add le_rfl hC
  · exact add_le_add (nearLedger_slack_mono _ _ _ hs) hC

/-- **Birth macro-step**: charge `(1/16)/2^128` (the reuse mass of the new row). -/
theorem near_birth (b : BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => nearPotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      nearPotential b + (1 / 16) / 2 ^ 128 := by
  have hadm : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun N => admInd N / 2 ^ 128) ≤
      (1 / 16) / 2 ^ 128 := by
    simp only [div_eq_mul_inv]
    rw [expectedValue_mul_const]
    exact mul_le_mul' (by simpa [div_eq_mul_inv] using expected_admInd) le_rfl
  unfold nearPotential
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
      _ ≤ (1 / 16) / 2 ^ 128 + (1 + b.reuse) := (expectedValue_add_const_le _ _ _).trans (add_le_add hadm le_rfl)
      _ = _ := add_comm _ _
  · simp only [hr, Bool.false_eq_true, if_false]
    set R := BPORS.Numeric.proposalLength - b.exposures.length
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => (nearLedger R (b.targets ++ [N]) b.exposures s + admInd N / 2 ^ 128) + b.reuse) :=
        expectedValue_mono _ fun N => (add_le_add le_rfl (hC N)).trans (le_of_eq (by ring))
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
          (fun N => nearLedger R (b.targets ++ [N]) b.exposures s + admInd N / 2 ^ 128) + b.reuse :=
        expectedValue_add_const_le _ _ _
      _ ≤ (nearLedger R b.targets b.exposures (s + 1) + (1 / 16) / 2 ^ 128) + b.reuse := by
        rw [expectedValue_add, nearLedger_birth]
        exact add_le_add (add_le_add le_rfl hadm) le_rfl
      _ = _ := by
        rw [hs]
        ring

/-- **Fresh-signing macro-step** (as `core_sign`). -/
theorem near_sign (b : BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if Reuse cache rho m then nearPotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd)))) ≤ nearPotential b := by
  have hlenA : ∀ (o : Option HashOutput), b.exposures.length ≤ (b.exposures ++ o.toList).length := by
    intro o; simp
  by_cases hd : BPORS.Numeric.proposalLength < b.exposures.length
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
  set R0 := BPORS.Numeric.proposalLength - b.exposures.length with hR0
  have hb : nearPotential b = nearLedger R0 b.targets b.exposures b.slack + b.reuse := by
    unfold nearPotential; simp only [hd, hr', if_false, Bool.false_eq_true]; rfl
  have hsearch : ∀ rho, ¬Reuse cache rho m →
      expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => nearPotential (b.expose C' (result.1.map Prod.snd))) ≤
          nearLedger R0 b.targets b.exposures b.slack + C' := by
    intro rho hnr
    have hrej : Sampling.CachedTrialsReject (Sampling.digestTrial rho m) Sampling.digestDecode 0 (2 ^ 32) cache := by
      unfold Reuse at hnr; push Not at hnr; exact hnr
    by_cases hlen : b.exposures.length < BPORS.Numeric.proposalLength
    · obtain ⟨R, hR⟩ : ∃ R, R0 = R + 1 := ⟨R0 - 1, by omega⟩
      calc
        _ ≤ expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
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
            have hnd : ¬BPORS.Numeric.proposalLength < (b.exposures ++ [found.2]).length := by simp; omega
            simp only [Option.map_some, Option.toList_some, hnd, if_false, hr', Bool.false_eq_true,
              Option.elim_some]
            rw [show BPORS.Numeric.proposalLength - (b.exposures ++ [found.2]).length = R by simp; omega]
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
        have hnd : BPORS.Numeric.proposalLength < (b.exposures ++ [found.2]).length := by simp; omega
        simp only [Option.map_some, Option.toList_some, hnd, if_true]
        exact bot_le
  rw [hb]
  calc
    _ ≤ expectedValue ($ᵗ Digest : ProbComp Digest)
        (fun rho => (if Reuse cache rho m then 1 else 0) + (nearLedger R0 b.targets b.exposures b.slack + C')) := by
      apply expectedValue_mono
      intro rho
      by_cases hre : Reuse cache rho m
      · rw [if_pos hre, if_pos hre]
        unfold nearPotential
        simp only [hd, if_false, if_true]
        exact add_le_add le_rfl le_add_self
      · rw [if_neg hre, if_neg hre, zero_add]
        exact hsearch rho hre
    _ ≤ reuseMass cache m + (nearLedger R0 b.targets b.exposures b.slack + C') :=
      (expectedValue_add_const_le _ _ _).trans (add_le_add (reuse_probability_le cache m) le_rfl)
    _ ≤ _ := by
      rw [add_comm (nearLedger _ _ _ _), ← add_assoc, add_comm (reuseMass cache m), add_comm _ (nearLedger _ _ _ _)]
      exact add_le_add le_rfl hC

/-- **Win**: an alive bank with a reuse or a near-covered admissible target holds a full unit. -/
theorem near_win (b : BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N=true ∧ NearCoveredBy b.exposures N) :
    1 ≤ nearPotential b := by
  unfold nearPotential
  rw [if_neg halive]
  by_cases hr : b.reused = true
  · rw [if_pos hr]; exact le_self_add
  · rw [if_neg hr]
    obtain ⟨N, hN, hadm, hgate, hcov⟩ := h.resolve_left hr
    exact (nearLedger_win _ _ _ _ N hN hadm hgate hcov).trans le_self_add

/-- **Initial near potential.** -/
theorem near_initial (budget : Nat) :
    nearPotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * 203 / 2 ^ 128 := by
  unfold nearPotential
  simp only [List.length_nil, Nat.not_lt_zero, if_false, Bool.false_eq_true, Nat.sub_zero, add_zero]
  exact nearLedger_initial budget

end SigGolfCandidate.T3.Security.CaseC
