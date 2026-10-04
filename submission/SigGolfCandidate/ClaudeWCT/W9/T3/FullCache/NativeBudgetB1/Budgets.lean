import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.FullCache.NativeBudget
import SigGolfCandidate.T3.Gate6.SourceBudget
import SigGolfCandidate.Budget.Numeric
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Presampling
import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
section
namespace ClaudeWCT.W9.T3.Correctness
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit honestForest eval_signForest)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers EncodingSearchesSucceed EncodingFamily DigestFamily
  signLayers_succeeds KeygenCorrect)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def DigestSearchesSucceed (answers : Answers) : Prop :=
  ∀ family : DigestFamily, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = some found
def SearchesSucceed (answers : Answers) : Prop :=
  DigestSearchesSucceed answers ∧ EncodingSearchesSucceed answers
theorem signPayload_succeeds (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceed answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message), message)
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayers_succeeds answers cache (output.toNat % 2 ^ 31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (honestForest answers (output.toNat % 2 ^ 31), 0, 0)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
def SigningComplete (answers : Answers) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
    evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
    evalWithAnswerFn answers (verify message keys.1 w) = true
theorem signing_complete_at (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message)
    (hpayload : ∃ sig, evalWithAnswerFn answers (signPayload keys.2 message) = some sig) :
    ∃ sig : Signature, ∃ w : Witness,
      evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
      evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true := by
  obtain ⟨sig, hs⟩ := hpayload
  have hs' : evalWithAnswerFn answers (sign keys.2 message) = some sig := by
    rw [show sign keys.2 message = ClaudeWCT.WCT9.signWith digestAttemptLimit keys.2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers keys message hkeys.2.2]
    exact hs
  obtain ⟨w, he, hv⟩ := ClaudeWCT.WCT9.signingWith_success_valid digestAttemptLimit
    ClaudeWCT.WCT9.digestAttemptLimit_le answers keys hkeys message sig hs'
  exact ⟨sig, w, hs', he, hv⟩
theorem signing_complete_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceed answers) :
    SigningComplete answers keys :=
  fun message => signing_complete_at answers keys hkeys message
    (signPayload_succeeds answers keys.2 message hgood)
theorem honest_signing_complete_of_searches (answers : Answers) (hgood : SearchesSucceed answers) :
    SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_searches answers _ (SigGolfCandidate.T3.Correctness.keygen_correct answers) hgood
def RealizedSigningComplete (answers : QueryImpl SphincsSecurity.OracleWorld Id)
    (secret : BitVec 256) (keys : Digest × Cache) : Prop :=
  ∀ message : Message, ∃ sig : Signature, ∃ w : Witness,
    evalWithAnswerFn answers (realize secret (sign keys.2 message)) = some sig ∧
    evalWithAnswerFn answers (realize secret (expand message keys.1 sig)) = some w ∧
    evalWithAnswerFn answers (realize secret (verify message keys.1 w)) = true
theorem realized_honest_signing_complete_of_searches
    (answers : QueryImpl SphincsSecurity.OracleWorld Id) (secret : BitVec 256)
    (hgood : SearchesSucceed (answers.compose (realHandler secret))) :
    RealizedSigningComplete answers secret (evalWithAnswerFn answers (realize secret keygen)) := by
  unfold RealizedSigningComplete
  simp only [SigGolfCandidate.T3.Correctness.realize_eval]
  exact honest_signing_complete_of_searches (answers.compose (realHandler secret)) hgood
def SearchesSucceedFor (answers : Answers) (message : Message) : Prop :=
  (∀ rho : Digest, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceed answers
theorem signPayload_succeedsFor (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 (evalWithAnswerFn answers (privateNonce message))
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayers_succeeds answers cache (output.toNat % 2 ^ 31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (honestForest answers (output.toNat % 2 ^ 31), 0, 0)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
theorem signing_complete_for_of_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (message : Message)
    (hgood : SearchesSucceedFor answers message) :
    ∃ sig : Signature, ∃ w : Witness,
      evalWithAnswerFn answers (sign keys.2 message) = some sig ∧
      evalWithAnswerFn answers (expand message keys.1 sig) = some w ∧
      evalWithAnswerFn answers (verify message keys.1 w) = true :=
  signing_complete_at answers keys hkeys message (signPayload_succeedsFor answers keys.2 message hgood)
def SearchesSucceedSelected (answers : Answers) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch
      (evalWithAnswerFn answers (privateNonce message)) message 0 digestAttemptLimit) = some found) ∧
  EncodingSearchesSucceed answers
theorem signPayload_succeedsSelected (answers : Answers) (cache : Cache) (message : Message)
    (hgood : SearchesSucceedSelected answers) :
    ∃ sig, evalWithAnswerFn answers (signPayload cache message) = some sig := by
  obtain ⟨⟨counter, output⟩, hd⟩ := hgood.1 message
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind, hd, eval_signForest]
  obtain ⟨pieces, hp⟩ := signLayers_succeeds answers cache (output.toNat % 2 ^ 31)
    (Nat.mod_lt _ (by positivity)) hgood.2 4
    (honestForest answers (output.toNat % 2 ^ 31), 0, 0)
  simp only [hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl⟩
theorem signing_complete_of_selected_searches (answers : Answers) (keys : Digest × Cache)
    (hkeys : KeygenCorrect answers keys) (hgood : SearchesSucceedSelected answers) :
    SigningComplete answers keys :=
  fun message => signing_complete_at answers keys hkeys message
    (signPayload_succeedsSelected answers keys.2 message hgood)
end ClaudeWCT.W9.T3.Correctness
end
section
namespace ClaudeWCT.W9.T3.BaseAudit
open SigGolfCandidate.T3.BaseAudit (zU b1 b2 b3 b4 step_1 step_2 step_3 step_4)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
def p0 : ℚ := 16016 ^ 9 / 2 ^ 138
def b0 : ℚ := 10273002 / 10000000
theorem step_0 : zU * ((1 - p0) * b0 + p0) ≤ b0 := by
  norm_num [zU, p0, b0]
theorem probability_floor : 1 / 5026 ≤ p0 ∧ p0 ≤ 1 / 5025 := by
  norm_num [p0]
theorem p0_nonneg : 0 ≤ p0 := by norm_num [p0]
theorem p0_le_one : p0 ≤ 1 := by norm_num [p0]
theorem signing_envelope :
    (2 : ℝ) ^ ((118176 : ℝ) / 131072) * ((b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) ≤ 2 := by
  have hsplit : (2 : ℝ) ^ ((118176 : ℝ) / 131072) = 2 / (2 : ℝ) ^ ((12896 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  have hlo := SigGolfCandidate.Budget.rpow_two_ge (12896 / 131072) (by norm_num)
  have hn : (b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ) ≤
      1 + 0.6931471803 * (12896 / 131072) + (0.6931471803 * (12896 / 131072)) ^ 2 / 2 := by
    norm_num [b0, SigGolfCandidate.T3.BaseAudit.b1, SigGolfCandidate.T3.BaseAudit.b2,
      SigGolfCandidate.T3.BaseAudit.b3, SigGolfCandidate.T3.BaseAudit.b4]
  rw [hsplit, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith
end ClaudeWCT.W9.T3.BaseAudit
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Completeness (failMass failMass_eq_probEvent)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Correctness (Answers EncodingFamily DigestFamily EncodingSearchesSucceed
  encodingFamily_card digestFamily_card KeygenCorrect)
open SigGolfCandidate.T3.Budgets (EncodingFailed zeroAnswers failMass_eq_one_sub_accept
  rejection_power_le ofReal_inv_two_pow encoding_failure_power finite_family_failure_le)
open ClaudeWCT.W9.T3.Correctness (SearchesSucceed DigestSearchesSucceed SigningComplete SearchesSucceedFor
  SearchesSucceedSelected signing_complete_of_searches honest_signing_complete_of_searches
  signing_complete_for_of_searches signing_complete_of_selected_searches)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem digest_probability_eq_p0 :
    Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.p0 : ℝ) := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.admissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [h, ClaudeWCT.Bank.WCT.acceptance_eq]
  have hq : ((BaseAudit.p0 : ℚ) : ℝ) = (16016 : ℝ) ^ 9 / 2 ^ 138 := by
    norm_num [BaseAudit.p0]
  rw [hq, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  simp
theorem digest_failure_power_of_acceptance (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 := by
  have hm : failMass digestDecode = ENNReal.ofReal (1 - p) := by
    rw [failMass_eq_one_sub_accept, haccept, ENNReal.ofReal_sub 1 (by linarith)]
    simp
  rw [hm, ← ENNReal.ofReal_pow (by linarith)]
  have hreal := rejection_power_le p hp1 digestAttemptLimit 450
    (by have hl := Real.log_two_lt_d9
        change (450 : ℝ) * Real.log 2 ≤ 2097152 * p
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
theorem digest_failure_power :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 450 :=
  digest_failure_power_of_acceptance (BaseAudit.p0 : ℝ)
    (by norm_num [BaseAudit.p0]) (by norm_num [BaseAudit.p0]) digest_probability_eq_p0
theorem digest_failMass_eq : failMass digestDecode = 1 - (16016 ^ 9 : ENNReal) / 2 ^ 138 := by
  have h : (fun answer : HashOutput => (digestDecode answer).isSome = true) =
      fun x => ClaudeWCT.WCT9.admissible x = true := by
    funext x
    simp only [digestDecode]
    split <;> simp_all
  rw [failMass_eq_one_sub_accept, h, ClaudeWCT.Bank.WCT.acceptance_eq]
theorem digest_failure_explicit :
    (1 - (16016 ^ 9 : ENNReal) / 2 ^ 138) ^ (2 ^ 21) ≤ 1 / (2 : ENNReal) ^ 450 := by
  rw [← digest_failMass_eq]
  exact digest_failure_power
theorem digest_failure_power_602 :
    failMass digestDecode ^ digestAttemptLimit ≤ 1 / (2 : ENNReal) ^ 602 := by
  have hp : (5 : ℝ) / 25126 ≤ (BaseAudit.p0 : ℝ) := by norm_num [BaseAudit.p0]
  have hm : failMass digestDecode = ENNReal.ofReal (1 - (BaseAudit.p0 : ℝ)) := by
    rw [failMass_eq_one_sub_accept, digest_probability_eq_p0,
      ENNReal.ofReal_sub 1 (by norm_num [BaseAudit.p0])]
    simp
  rw [hm, ← ENNReal.ofReal_pow (by norm_num [BaseAudit.p0])]
  have hreal := rejection_power_le (BaseAudit.p0 : ℝ) (by norm_num [BaseAudit.p0]) digestAttemptLimit 602
    (by have hl := Real.log_two_lt_d9
        change (602 : ℝ) * Real.log 2 ≤ 2097152 * (BaseAudit.p0 : ℝ)
        nlinarith)
  have hcast := ENNReal.ofReal_le_ofReal hreal
  simpa only [ofReal_inv_two_pow] using hcast
def DigestFailed (family : DigestFamily) (answers : Answers) : Prop :=
  evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none
theorem incomplete_implies_failed_search (answers : Answers)
    (h : ¬SigningComplete answers (evalWithAnswerFn answers keygen)) :
    (∃ family, DigestFailed family answers) ∨ (∃ family, EncodingFailed family answers) := by
  classical
  by_contra hnone
  obtain ⟨hd, he⟩ := not_or.mp hnone
  apply h
  apply honest_signing_complete_of_searches
  constructor
  · intro family
    cases hx : evalWithAnswerFn answers
        (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) with
    | none => exact False.elim (hd ⟨family, hx⟩)
    | some found => exact ⟨found, rfl⟩
  · intro family
    cases hx : evalWithAnswerFn answers (counterSearch family.1 family.2.1.val
      family.2.2.1.val family.2.2.2 0 counterLimit) with
    | none => exact False.elim (he ⟨family, hx⟩)
    | some found => exact ⟨found, rfl⟩
theorem signing_incomplete_probability_le (law : ProbComp Answers) (digestFail encodingFail : ENNReal)
    (hd : ∀ family, Pr[DigestFailed family | law] ≤ digestFail)
    (he : ∀ family, Pr[EncodingFailed family | law] ≤ encodingFail) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      (2 : ENNReal) ^ 384 * digestFail + (2 : ENNReal) ^ 397 * encodingFail := by
  have hm := probEvent_mono (mx := law) (fun answers _ => incomplete_implies_failed_search answers)
  have hd' := finite_family_failure_le law DigestFailed digestFail hd
  have he' := finite_family_failure_le law EncodingFailed encodingFail he
  rw [digestFamily_card, Nat.cast_pow, Nat.cast_ofNat] at hd'
  rw [encodingFamily_card, Nat.cast_pow, Nat.cast_ofNat] at he'
  exact hm.trans ((probEvent_or_le law _ _).trans (add_le_add hd' he'))
theorem signing_incomplete_probability_small (law : ProbComp Answers)
    (hd : ∀ family, Pr[DigestFailed family | law] ≤ 1 / (2 : ENNReal) ^ 450)
    (he : ∀ family, Pr[EncodingFailed family | law] ≤ 1 / (2 : ENNReal) ^ 1024) :
    Pr[fun answers => ¬SigningComplete answers (evalWithAnswerFn answers keygen) | law] ≤
      1 / (2 : ENNReal) ^ 65 := by
  refine (signing_incomplete_probability_le law _ _ hd he).trans ?_
  have hreal : (2 : ℝ) ^ 384 * (1 / 2 ^ 450) + 2 ^ 397 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 65 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ 384 * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 397 * (1 / 2 ^ 1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 384 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
noncomputable local instance : SampleableType (SearchKey → HashOutput) := Presampling.tableSampler
def SearchAgreement (outputs : SearchKey → HashOutput) (answers : Answers) : Prop :=
  ∀ key, answers (.inl (.inr (searchQuery key))) = outputs key
def tableGood (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
theorem counterSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : EncodingFamily) :
    evalWithAnswerFn answers
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit) = none ↔
    ∀ c : Fin (2 ^ 22), SigGolfCandidate.T3.Sampling.encodingDecode family.1 (outputs (.inl (family, c))) = none := by
  rw [SigGolfCandidate.T3.Correctness.counterSearch_none_iff]
  have hv (c : Nat) (hc : c < counterLimit) :
      evalWithAnswerFn answers
        (shortHash (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
          (BitVec.ofNat 32 (0 + c)))) = (outputs (.inl (family, ⟨c, hc⟩))).extractLsb' 0 128 := by
    rw [SigGolfCandidate.T3.Presampling.eval_shortHash]
    have hinput : pad64 (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
        (BitVec.ofNat 32 (0 + c))) = searchQuery (.inl (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inl, SigGolfCandidate.T3.QuerySpace.encodingQuery,
        SigGolfCandidate.T3.Sampling.encodingTrial, Nat.zero_add]
    rw [hinput, hagree]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c, hc⟩
theorem digestSearch_none_agreement (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) (family : DigestFamily) :
    evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none ↔
    ∀ c : Fin (2 ^ 21), digestDecode (outputs (.inr (family, c))) = none := by
  rw [ClaudeWCT.WCT9.digestSearch_none_iff]
  have hv (c : Nat) (hc : c < digestAttemptLimit) :
      evalWithAnswerFn answers (digest family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        outputs (.inr (family, ⟨c, hc⟩)) := by
    rw [SigGolfCandidate.T3.Presampling.eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        searchQuery (.inr (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inr, ClaudeWCT.W9.T3.QuerySpace.digestQuery,
        SigGolfCandidate.T3.Sampling.digestTrial, Nat.zero_add]
    rw [hinput, hagree]
  constructor
  · intro h c
    rw [ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff _).mp (h ⟨c, hc⟩)
theorem tableGood_iff_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGood outputs ↔ SearchesSucceed answers := by
  unfold tableGood SearchesSucceed DigestSearchesSucceed EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers family).trans
      (digestSearch_none_agreement outputs answers hagree family).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)
theorem tableGood_searchesSucceed (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGood outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceed answers := (tableGood_iff_searchesSucceed outputs answers hagree).mp hgood
theorem tableGood_fallback_iff (outputs : SearchKey → HashOutput) (fallback : Answers) :
    tableGood outputs ↔ SearchesSucceed (Presampling.tableAnswers outputs fallback) :=
  tableGood_iff_searchesSucceed outputs _ (Presampling.tableAnswers_apply outputs fallback)
theorem not_searchesSucceed_iff (answers : Answers) :
    ¬ SearchesSucceed answers ↔
      (∃ family, DigestFailed family answers) ∨ (∃ family, EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceed, DigestSearchesSucceed, EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailed]
theorem tableGood_failure_le (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (SigGolfCandidate.T3.Sampling.encodingDecode lay) ^ counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 384 * digestFail + (2 : ENNReal) ^ 397 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun family outputs => DigestFailed family (Presampling.tableAnswers outputs zeroAnswers)) digestFail
    (fun family => (Presampling.digestSearch_table_failure zeroAnswers family).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [digestFamily_card, Nat.cast_pow, Nat.cast_ofNat] at hd'
  rw [encodingFamily_card, Nat.cast_pow, Nat.cast_ofNat] at he'
  simp only [tableGood, not_searchesSucceed_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGood_failure_small_of_acceptance (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 65 := by
  refine (tableGood_failure_le _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ) ^ 384 * (1 / 2 ^ 450) + 2 ^ 397 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 65 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ 384 * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 397 * (1 / 2 ^ 1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 384 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
def tableGoodFor (message : Message) (outputs : SearchKey → HashOutput) : Prop :=
  SearchesSucceedFor (Presampling.tableAnswers outputs zeroAnswers) message
theorem tableGoodFor_iff_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hagree : SearchAgreement outputs answers) :
    tableGoodFor message outputs ↔ SearchesSucceedFor answers message := by
  unfold tableGoodFor SearchesSucceedFor EncodingSearchesSucceed
  simp only [← Option.ne_none_iff_exists']
  apply and_congr
  · apply forall_congr'; intro rho
    exact not_congr ((Presampling.digestSearch_none_table outputs zeroAnswers (rho, message)).trans
      (digestSearch_none_agreement outputs answers hagree (rho, message)).symm)
  · apply forall_congr'; intro family
    exact not_congr ((Presampling.counterSearch_none_table outputs zeroAnswers family).trans
      (counterSearch_none_agreement outputs answers hagree family).symm)
theorem tableGoodFor_searchesSucceedFor (message : Message) (outputs : SearchKey → HashOutput)
    (answers : Answers) (hgood : tableGoodFor message outputs) (hagree : SearchAgreement outputs answers) :
    SearchesSucceedFor answers message :=
  (tableGoodFor_iff_searchesSucceedFor message outputs answers hagree).mp hgood
theorem not_searchesSucceedFor_iff (answers : Answers) (message : Message) :
    ¬ SearchesSucceedFor answers message ↔
      (∃ rho : Digest, DigestFailed (rho, message) answers) ∨ (∃ family, EncodingFailed family answers) := by
  classical
  simp only [SearchesSucceedFor, EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailed]
theorem tableGoodFor_failure_le (message : Message) (digestFail encodingFail : ENNReal)
    (hd : failMass digestDecode ^ digestAttemptLimit ≤ digestFail)
    (he : ∀ lay, failMass (SigGolfCandidate.T3.Sampling.encodingDecode lay) ^ counterLimit ≤ encodingFail) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 128 * digestFail + (2 : ENNReal) ^ 397 * encodingFail := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (rho : Digest) outputs => DigestFailed (rho, message) (Presampling.tableAnswers outputs zeroAnswers))
    digestFail
    (fun rho => (Presampling.digestSearch_table_failure zeroAnswers (rho, message)).le.trans hd)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) encodingFail
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans (he family.1))
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at hd'
  rw [encodingFamily_card, Nat.cast_pow, Nat.cast_ofNat] at he'
  simp only [tableGoodFor, not_searchesSucceedFor_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodFor_failure_small_of_acceptance (message : Message) (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 321 := by
  refine (tableGoodFor_failure_le message _ _
    (digest_failure_power_of_acceptance p hp hp1 haccept) encoding_failure_power).trans ?_
  have hreal : (2 : ℝ) ^ 128 * (1 / 2 ^ 450) + 2 ^ 397 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 321 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ 128 * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 397 * (1 / 2 ^ 1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 128 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
theorem tableGood_failure_small :
    Pr[fun outputs => ¬tableGood outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 65 :=
  tableGood_failure_small_of_acceptance (BaseAudit.p0 : ℝ) (by norm_num [BaseAudit.p0])
    (by norm_num [BaseAudit.p0]) digest_probability_eq_p0
theorem tableGoodFor_failure_small (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 321 :=
  tableGoodFor_failure_small_of_acceptance message (BaseAudit.p0 : ℝ) (by norm_num [BaseAudit.p0])
    (by norm_num [BaseAudit.p0]) digest_probability_eq_p0
theorem tableGoodFor_failure_128 (message : Message) :
    Pr[fun outputs => ¬tableGoodFor message outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 128 := by
  refine (tableGoodFor_failure_small message).trans ?_
  simp only [one_div, ENNReal.inv_le_inv]
  exact pow_le_pow_right₀ (by norm_num) (by decide)
def tableGoodForNonces (nonces : Message → HashOutput) (outputs : SearchKey → HashOutput) : Prop :=
  (∀ message : Message, ∃ found,
    evalWithAnswerFn (Presampling.tableAnswers outputs zeroAnswers)
      (ClaudeWCT.WCT9.digestSearch ((nonces message).extractLsb' 0 128) message 0 digestAttemptLimit) =
        some found) ∧
  EncodingSearchesSucceed (Presampling.tableAnswers outputs zeroAnswers)
def NonceAgreement (nonces : Message → HashOutput) (answers : Answers) : Prop :=
  ∀ message, evalWithAnswerFn answers (privateNonce message) = (nonces message).extractLsb' 0 128
theorem tableGoodForNonces_searchesSucceedSelected (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) : SearchesSucceedSelected answers := by
  constructor
  · intro message
    rw [hnonce]
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.digestSearch_none_table outputs zeroAnswers
      ((nonces message).extractLsb' 0 128, message)).mpr
      ((digestSearch_none_agreement outputs answers hagree
        ((nonces message).extractLsb' 0 128, message)).mp hnone)
    obtain ⟨found, hfound⟩ := hgood.1 message
    rw [hfound] at hnone'
    cases hnone'
  · intro family
    apply Option.ne_none_iff_exists'.mp
    intro hnone
    have hnone' := (Presampling.counterSearch_none_table outputs zeroAnswers family).mpr
      ((counterSearch_none_agreement outputs answers hagree family).mp hnone)
    obtain ⟨found, hfound⟩ := hgood.2 family
    rw [hfound] at hnone'
    cases hnone'
theorem tableGoodForNonces_signingComplete (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) (answers : Answers)
    (hgood : tableGoodForNonces nonces outputs) (hagree : SearchAgreement outputs answers)
    (hnonce : NonceAgreement nonces answers) :
    SigningComplete answers (evalWithAnswerFn answers keygen) :=
  signing_complete_of_selected_searches answers _ (SigGolfCandidate.T3.Correctness.keygen_correct answers)
    (tableGoodForNonces_searchesSucceedSelected nonces outputs answers hgood hagree hnonce)
theorem not_tableGoodForNonces_iff (nonces : Message → HashOutput)
    (outputs : SearchKey → HashOutput) :
    ¬tableGoodForNonces nonces outputs ↔
    (∃ message : Message, DigestFailed ((nonces message).extractLsb' 0 128, message)
      (Presampling.tableAnswers outputs zeroAnswers)) ∨
    (∃ family, EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers)) := by
  classical
  simp only [tableGoodForNonces, EncodingSearchesSucceed,
    ← Option.ne_none_iff_exists', not_and_or, not_forall, not_not, DigestFailed, EncodingFailed]
theorem tableGoodForNonces_failure_le (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤
      (2 : ENNReal) ^ 256 * (1 / 2 ^ 450) + (2 : ENNReal) ^ 397 * (1 / 2 ^ 1024) := by
  let law := ($ᵗ (SearchKey → HashOutput) : ProbComp _)
  have hd' := finite_family_failure_le law
    (fun (message : Message) outputs => DigestFailed ((nonces message).extractLsb' 0 128, message)
      (Presampling.tableAnswers outputs zeroAnswers)) (1 / (2 : ENNReal) ^ 450)
    (fun message => (Presampling.digestSearch_table_failure zeroAnswers
      ((nonces message).extractLsb' 0 128, message)).le.trans digest_failure_power)
  have he' := finite_family_failure_le law
    (fun family outputs => EncodingFailed family (Presampling.tableAnswers outputs zeroAnswers))
      (1 / (2 : ENNReal) ^ 1024)
    (fun family => (Presampling.counterSearch_table_failure zeroAnswers family).le.trans
      (encoding_failure_power family.1))
  rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] at hd'
  rw [encodingFamily_card, Nat.cast_pow, Nat.cast_ofNat] at he'
  simp only [not_tableGoodForNonces_iff]
  exact (probEvent_or_le law _ _).trans (add_le_add hd' he')
theorem tableGoodForNonces_failure_small (nonces : Message → HashOutput) :
    Pr[fun outputs => ¬tableGoodForNonces nonces outputs |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] ≤ 1 / (2 : ENNReal) ^ 193 := by
  refine (tableGoodForNonces_failure_le nonces).trans ?_
  have hreal : (2 : ℝ) ^ 256 * (1 / 2 ^ 450) + 2 ^ 397 * (1 / 2 ^ 1024) ≤ 1 / 2 ^ 193 := by
    set_option exponentiation.threshold 2048 in norm_num
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add (show 0 ≤ (2 : ℝ) ^ 256 * (1 / 2 ^ 450) by positivity)
    (show 0 ≤ (2 : ℝ) ^ 397 * (1 / 2 ^ 1024) by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 256 by positivity),
    ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ 397 by positivity)] at hcast
  simpa only [ENNReal.ofReal_pow (show 0 ≤ (2 : ℝ) by norm_num),
    ENNReal.ofReal_ofNat, ofReal_inv_two_pow] using hcast
end ClaudeWCT.W9.T3.Budgets
end
