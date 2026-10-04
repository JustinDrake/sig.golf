import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Presampling
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.SourceReplay
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.FullCache.ExpansionCost
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.T3.FullCache.NativeBudget
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots
import SigGolfCandidate.T3M.Images.Keygen
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SecurityP
section
namespace ClaudeWCT.W9.T3.NonceSampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev NonceOutputs := Message → HashOutput
abbrev SearchOutputs := SearchKey → HashOutput
abbrev QueryKey := Message ⊕ SearchKey
@[irreducible] noncomputable def nonceSampler : SampleableType NonceOutputs :=
  Derivation.outputSampler Message
@[irreducible] noncomputable def combinedSampler : SampleableType (QueryKey → HashOutput) :=
  Derivation.outputSampler QueryKey
noncomputable local instance : SampleableType NonceOutputs := nonceSampler
noncomputable local instance : SampleableType SearchOutputs := Presampling.tableSampler
noncomputable local instance : SampleableType (QueryKey → HashOutput) := combinedSampler
def nonceInputs (secret : BitVec 256) (message : Message) : HashInput :=
  privateInput secret (.inr (.inl message))
theorem nonceInputs_injective (secret : BitVec 256) : Function.Injective (nonceInputs secret) := by
  intro a b he
  exact Sum.inl.inj (Sum.inr.inj (privateInput_injective secret he))
theorem nonceInputs_length (secret : BitVec 256) (message : Message) :
    (nonceInputs secret message).length = 128 := by
  simp only [nonceInputs, privateInput_nonce, List.length_append, SphincsSecurity.bytesLE_length,
    zero16, List.length_replicate]
theorem nonceInputs_ne_searchQuery (secret : BitVec 256) (message : Message) (key : SearchKey) :
    nonceInputs secret message ≠ searchQuery key := by
  intro he
  have hl := congrArg List.length he
  rw [nonceInputs_length, searchQuery_length] at hl
  omega
def combinedInputs (secret : BitVec 256) : QueryKey → HashInput :=
  Sum.elim (nonceInputs secret) searchQuery
theorem combinedInputs_injective (secret : BitVec 256) : Function.Injective (combinedInputs secret) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (nonceInputs_injective secret he)
    | inr b => exact False.elim (nonceInputs_ne_searchQuery secret a b he)
  | inr a =>
    cases b with
    | inl b => exact False.elim (nonceInputs_ne_searchQuery secret b a he.symm)
    | inr b => exact congrArg Sum.inr (searchQuery_injective he)
noncomputable def preparedCache (secret : BitVec 256)
    (nonceOutputs : NonceOutputs) (searchOutputs : SearchOutputs) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ (combinedInputs secret) (Sum.elim nonceOutputs searchOutputs)
theorem preparedCache_nonce (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (message : Message) :
    preparedCache secret nonceOutputs searchOutputs (nonceInputs secret message) = some (nonceOutputs message) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inl message)
theorem preparedCache_search (secret : BitVec 256) (nonceOutputs : NonceOutputs)
    (searchOutputs : SearchOutputs) (key : SearchKey) :
    preparedCache secret nonceOutputs searchOutputs (searchQuery key) = some (searchOutputs key) :=
  cacheTable_apply ∅ (combinedInputs secret) (combinedInputs_injective secret)
    (Sum.elim nonceOutputs searchOutputs) (.inr key)
theorem combined_uniform :
    𝒮[($ᵗ (QueryKey → HashOutput) : ProbComp _)] =
    𝒮[do
      let nonces ← ($ᵗ NonceOutputs : ProbComp _)
      let searches ← ($ᵗ SearchOutputs : ProbComp _)
      pure (Sum.elim nonces searches)] := by
  classical
  let : Fintype SearchOutputs := @Pi.instFintype SearchKey (fun _ => HashOutput)
    (Classical.decEq SearchKey) inferInstance (fun _ => inferInstance)
  let : Fintype NonceOutputs := @Pi.instFintype Message (fun _ => HashOutput)
    (Classical.decEq Message) inferInstance (fun _ => inferInstance)
  let split : (QueryKey → HashOutput) ≃ NonceOutputs × SearchOutputs :=
    Equiv.sumArrowEquivProdArrow Message SearchKey HashOutput
  have he := evalSPMF_map_bijective_uniform_cross
    (α := NonceOutputs × SearchOutputs) (β := QueryKey → HashOutput) split.symm split.symm.bijective
  have hp := evalDist_independent_uniform_pair (α := NonceOutputs) (β := SearchOutputs)
  rw [evalSPMF_map, ← hp] at he
  simpa only [evalSPMF_bind, evalSPMF_pure, map_bind, map_pure, split,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk] using he.symm
theorem presample_combined {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (QueryKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (cacheTable ∅ (combinedInputs secret) outputs)] := by
  let : SampleableType (QueryKey → SphincsSecurity.HashOutput) := combinedSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (QueryKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret))).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec))
        (queryTable (R := SphincsSecurity.HashOutput) (combinedInputs secret)))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput)
      (combinedInputs secret) (combinedInputs_injective secret) ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let nonceOutputs ← ($ᵗ NonceOutputs : ProbComp _)
      let searchOutputs ← ($ᵗ SearchOutputs : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (preparedCache secret nonceOutputs searchOutputs)] := by
  rw [presample_combined, evalSPMF_bind, combined_uniform]
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  rfl
end ClaudeWCT.W9.T3.NonceSampling
end
section
namespace ClaudeWCT.W9.T3.Completeness
open OracleComp OracleSpec ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_foldlM hashOnly_keygen
  fixedAnswers fixed_replay)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand hashOnly_verify)
open ClaudeWCT.W9.T3.QuerySpace (SearchKey searchQuery)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestProgram (message : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 message
  match sig with
  | none => pure false
  | some sig =>
    let witness ← expand message keys.1 sig
    match witness with
    | none => pure false
    | some witness => verify message keys.1 witness
noncomputable def everyMessageProgram : M Bool :=
  (Finset.univ : Finset Message).toList.foldlM (fun accepted message => do
    let result ← honestProgram message
    pure (accepted && result)) true
theorem honestProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceed answers) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.honest_signing_complete_of_searches answers hgood message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem honestProgram_true_for (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message)
    (hgood : Correctness.SearchesSucceedFor answers message) :
    evalWithAnswerFn answers (honestProgram message) = true := by
  obtain ⟨sig, witness, hs, he, hv⟩ := Correctness.signing_complete_for_of_searches answers
    (evalWithAnswerFn answers keygen) (SigGolfCandidate.T3.Correctness.keygen_correct answers) message hgood
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
theorem hashOnly_honestProgram (message : Message) : HashOnly (honestProgram message) := by
  unfold honestProgram
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (hashOnly_sign keys.2 message)
  intro sig
  cases sig with
  | none => exact hashOnly_pure false
  | some sig =>
    apply hashOnly_bind (hashOnly_expand message keys.1 sig)
    intro witness
    cases witness with
    | none => exact hashOnly_pure false
    | some witness => exact hashOnly_verify message keys.1 witness
theorem hashOnly_everyMessageProgram : HashOnly everyMessageProgram := by
  apply hashOnly_foldlM
  intro accepted message
  exact hashOnly_bind (hashOnly_honestProgram message) fun _ => hashOnly_pure _
theorem everyMessageProgram_true (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hall : ∀ message, evalWithAnswerFn answers (honestProgram message) = true) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  have hf : ∀ messages : List Message, ∀ accepted : Bool,
      evalWithAnswerFn answers (messages.foldlM (fun accepted message => do
        let result ← honestProgram message
        pure (accepted && result)) accepted) = accepted := by
    intro messages
    induction messages with
    | nil => intro accepted; rfl
    | cons message messages ih =>
      intro accepted
      simp only [List.foldlM_cons, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hall, Bool.and_true]
      exact ih accepted
  exact hf _ true
theorem everyMessageProgram_true_of_complete (answers : SigGolfCandidate.T3.Correctness.Answers)
    (hcomplete : Correctness.SigningComplete answers (evalWithAnswerFn answers keygen)) :
    evalWithAnswerFn answers everyMessageProgram = true := by
  apply everyMessageProgram_true
  intro message
  obtain ⟨sig, witness, hs, he, hv⟩ := hcomplete message
  simp only [honestProgram, evalWithAnswerFn_bind, hs, he, hv]
noncomputable local instance : SampleableType (SearchKey → HashOutput) :=
  Presampling.tableSampler
theorem failure_le_bad_table (secret : BitVec 256) (program : M Bool)
    (good : (SearchKey → HashOutput) → Prop)
    (hzero : ∀ outputs, good outputs →
      Pr[fun value => value = false |
        (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
          (Presampling.preparedCache outputs)] = 0) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] ≤
    Pr[fun outputs => ¬good outputs | ($ᵗ (SearchKey → HashOutput) : ProbComp _)] := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (Presampling.presample_source secret program)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_probEvent
  intro outputs _ hgood
  exact hzero outputs (not_not.mp hgood)
theorem prepared_failure_zero (secret : BitVec 256) (program : M Bool)
    (outputs : SearchKey → HashOutput)
    (hgood : ∀ f : QueryImpl SphincsSecurity.HashSpec Id,
      (Presampling.preparedCache outputs).AgreesWithFn f →
      simulateQ (unifFwdAnswerImpl f) (realize secret program) = (pure true : ProbComp Bool)) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run'
        (Presampling.preparedCache outputs)] = 0 :=
  SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret program _ hgood
theorem honest_prepared_failure_zero (secret : BitVec 256) (message : Message)
    (outputs : SearchKey → HashOutput) (hgood : Budgets.tableGoodFor message outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run'
        (Presampling.preparedCache outputs)] = 0 := by
  refine prepared_failure_zero secret (honestProgram message) outputs ?_
  intro hash hagree
  have hsrc : Correctness.SearchesSucceedFor (fixedAnswers secret hash) message := by
    apply Budgets.tableGoodFor_searchesSucceedFor message outputs _ hgood
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (Presampling.preparedCache_apply outputs key)
  exact (fixed_replay secret hash _ (hashOnly_honestProgram message)).trans
    (congrArg (pure : Bool → ProbComp Bool) (honestProgram_true_for _ message hsrc))
theorem honest_failure_small_of_acceptance (secret : BitVec 256) (message : Message)
    (p : ℝ) (hp : 1 / 5026 ≤ p) (hp1 : p ≤ 1)
    (haccept : Pr[fun answer => (ClaudeWCT.W9.T3.Sampling.digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal p) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 321 := by
  exact (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans
    (Budgets.tableGoodFor_failure_small_of_acceptance message p hp hp1 haccept)
theorem honest_failure_small (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 321 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_small message)
theorem honest_failure_128 (secret : BitVec 256) (message : Message) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret (honestProgram message))).run' ∅] ≤
        1 / (2 : ENNReal) ^ 128 :=
  (failure_le_bad_table secret (honestProgram message) (Budgets.tableGoodFor message)
    (honest_prepared_failure_zero secret message)).trans (Budgets.tableGoodFor_failure_128 message)
noncomputable local instance : SampleableType NonceSampling.NonceOutputs := NonceSampling.nonceSampler
theorem everyMessage_prepared_failure_zero (secret : BitVec 256)
    (nonces : NonceSampling.NonceOutputs) (outputs : NonceSampling.SearchOutputs)
    (hgood : Budgets.tableGoodForNonces nonces outputs) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run'
        (NonceSampling.preparedCache secret nonces outputs)] = 0 := by
  refine SigGolfCandidate.T3.Completeness.failure_zero_of_fixed_replay secret everyMessageProgram _ ?_
  intro hash hagree
  have hsearch : Budgets.SearchAgreement outputs (fixedAnswers secret hash) := by
    intro key
    change hash (searchQuery key) = outputs key
    exact hagree (NonceSampling.preparedCache_search secret nonces outputs key)
  have hnonce : Budgets.NonceAgreement nonces (fixedAnswers secret hash) := by
    intro message
    have h := hagree (NonceSampling.preparedCache_nonce secret nonces outputs message)
    exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) h
  have hcomplete := Budgets.tableGoodForNonces_signingComplete nonces outputs
    (fixedAnswers secret hash) hgood hsearch hnonce
  exact (fixed_replay secret hash _ hashOnly_everyMessageProgram).trans
    (congrArg (pure : Bool → ProbComp Bool) (everyMessageProgram_true_of_complete _ hcomplete))
theorem everyMessage_failure_small (secret : BitVec 256) :
    Pr[fun value => value = false |
      (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] ≤
        1 / (2 : ENNReal) ^ 193 := by
  have hp := congrArg (fun law => probEvent law (fun value : Bool => value = false))
    (NonceSampling.presample_source secret everyMessageProgram)
  simp only [probEvent_evalSPMF] at hp
  rw [hp]
  apply probEvent_bind_le_of_forall_le
  intro nonces _
  refine (probEvent_bind_le_probEvent
    (p := fun outputs => ¬Budgets.tableGoodForNonces nonces outputs)
    (fun outputs _ hgood => everyMessage_prepared_failure_zero secret nonces outputs (not_not.mp hgood))).trans
    (Budgets.tableGoodForNonces_failure_small nonces)
theorem source_completeness (secret : BitVec 256) :
    1 - 1 / (2 : ENNReal) ^ 128 ≤
      Pr[= true | (simulateQ SphincsSecurity.romImpl (realize secret everyMessageProgram)).run' ∅] := by
  have hf := everyMessage_failure_small secret
  rw [probEvent_eq_eq_probOutput] at hf
  have hsmall : 1 / (2 : ENNReal) ^ 193 ≤ 1 / (2 : ENNReal) ^ 128 := by norm_num
  rw [probOutput_true_eq_sub]
  simp only [probFailure_eq_zero, tsub_zero]
  exact tsub_le_tsub_left (hf.trans hsmall) 1
end ClaudeWCT.W9.T3.Completeness
end
section
namespace ClaudeWCT.W9.T3.FullCacheExpansionCost
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge privatePair_cost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem buildChild_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) :
    4 ≤ cost answers (ClaudeWCT.WCT9.buildChild index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildChild
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) (pair : Fin 4) => do
      let seeds ← privatePair 8 coord index 0 (4 * selected + pair.val)
      (List.finRange 2).foldlM
        (fun (state : List Digest × List Digest) half => do
          if h : 2 * pair.val + half.val < 7 then
            let i : Fin 7 := ⟨2 * pair.val + half.val, h⟩
            let secret := if half.val = 0 then seeds.1 else seeds.2
            let deficit := ClaudeWCT.WCT9.digit word i
            let value ← ClaudeWCT.WCT9.chain index coord selected i.val 0 (3 - deficit) secret
            let last ← ClaudeWCT.WCT9.chain index coord selected i.val (3 - deficit) deficit value
            pure (state.1 ++ [last], state.2 ++ [value])
          else pure state) state) 1
    (fun state pair => by
      simp only [cost_bind, privatePair_cost]
      omega) (List.finRange 4) ([], [])
  simpa only [List.length_finRange, Nat.mul_one] using h
theorem buildCoordinate_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (coord : ClaudeWCT.WCT9.Coord) (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    512 ≤ cost answers (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) (j : Nat) => do
      let (root, values) ← ClaudeWCT.WCT9.buildChild index coord.val j word
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) 4
    (fun state j => by
      simp only [cost_bind, cost_pure, Nat.add_zero]
      exact buildChild_cost_ge answers index coord.val j word) (List.range 128) ([], [])
  simpa only [List.length_range] using h
theorem forestRows_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    4608 ≤ cost answers (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows
  apply (show 4608 = (List.finRange 9).length * 512 by decide).le.trans
  apply foldlM_cost_ge
  intro state coord
  unfold ClaudeWCT.WCT9.openingStep
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildCoordinate_cost_ge answers index coord _ _
theorem signForest_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    4608 ≤ cost answers (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest
  rw [cost_bind]
  exact (forestRows_cost_ge answers index output).trans (Nat.le_add_right _ _)
theorem signPayload_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) = some sig) :
    90 ≤ cost answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := signForest_cost_ge answers (output.toNat % 2 ^ 31) output
      omega
end ClaudeWCT.W9.T3.FullCacheExpansionCost
end
section
namespace ClaudeWCT.W9.T3.ExpansionBudget
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit assembledSignature honestForest
  signForest_root assembled_forest_recovery toT3Signature)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query cost_bound)
open SigGolfCandidate.T3.Correctness (Answers cacheRegion maskedTop PiecesAgree CacheTagCorrect
  keygen_correct keygen_cache_tag privateMac_count)
open SigGolfCandidate.T3.ExpansionBudget (expandLayers_cost_le)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (expand message pk sig) =
      cost answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output) +
      cost answers (expandLayers (toT3Signature sig) (output.toNat % 2 ^ 31) 4
        (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output), 0, 0)) := by
  simp only [ClaudeWCT.WCT9.Rev3.expand, ClaudeWCT.WCT9.expandWith, cost_bind, hd]
  split
  · split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
  · simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output) +
      cost answers (signLayers cache (output.toNat % 2 ^ 31) 4
        ((evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2, 0, 0)) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem expand_cost_le_payload_add (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers
    (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
      digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers
        (signLayers cache (output.toNat % 2 ^ 31) 4
          ((evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2, 0, 0)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          have hforest := assembled_forest_recovery answers
            (evalWithAnswerFn answers (privateNonce message)) (output.toNat % 2 ^ 31) output pieces
          have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
          have hlayer := expandLayers_cost_le answers cache (output.toNat % 2 ^ 31)
            hcache hindex 4 (by decide) _ pieces hl
            (toT3Signature (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces))
            (fun _ _ => rfl)
          rw [SigGolfCandidate.T3.Cost.recoveryLayersCost_four] at hlayer
          have hrec := cost_bound answers (ClaudeWCT.WCT9.Cost.bound_recoverFts
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            (output.toNat % 2 ^ 31) output)
          have hexpand := expand_cost_step answers message pk
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            counter output (by simpa only [ClaudeWCT.WCT9.assembledSignature_rho] using hd)
          rw [hexpand, signPayload_cost_step answers cache message counter output hd]
          simp only [ClaudeWCT.WCT9.assembledSignature_rho] at hrec hlayer ⊢
          rw [hforest]
          omega
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac, ← hvalid, ne_eq,
    not_true_eq_false, ite_false]
  rfl
theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) := by
  have hk := keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers keygen).2 message) =
      some sig := by
    rw [show sign (evalWithAnswerFn answers keygen).2 message =
      ClaudeWCT.WCT9.signWith digestAttemptLimit (evalWithAnswerFn answers keygen).2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers _ message
        (keygen_cache_tag answers)] at hs
    exact hs
  have h := expand_cost_le_payload_add answers (evalWithAnswerFn answers keygen).2 message sig
    hk.2.1 hs' (evalWithAnswerFn answers keygen).1
  have hmin := ClaudeWCT.W9.T3.FullCacheExpansionCost.signPayload_cost_ge answers
    (evalWithAnswerFn answers keygen).2 message sig hs'
  rw [sign_cost_honest]
  omega
end ClaudeWCT.W9.T3.ExpansionBudget
end
section
namespace ClaudeWCT.W9.T3.Budgets
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Completeness (failMass)
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V V_pure V_of_bound)
open SigGolfCandidate.T3.Budgets (signingZ EncodingFreshBelow AllSearchesFresh allSearchesFresh_empty
  layerMomentBound layerMomentBound_ge_one layerMomentBound_four encodingEnvelope encodingEnvelope_ge_one
  signing_z_le V_bind_bounded post_of_roRun V_signLayers_of_freshness signingZ_pow)
open SigGolfCandidate.T3.BaseAudit (zU b1 b2 b3 b4)
open SigGolfCandidate.T3.Cost (bound_privateNonce bound_privateMac)
open ClaudeWCT.W9.T3.Sampling (digestDecode)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable def digestEnvelope : ENNReal := ENNReal.ofReal (BaseAudit.b0 : ℝ)
theorem digestEnvelope_ge_one : 1 ≤ digestEnvelope := by
  rw [digestEnvelope, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  norm_num [BaseAudit.b0]
theorem digest_failMass_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.p0 : ℝ)) :
    failMass digestDecode = ENNReal.ofReal (1 - (BaseAudit.p0 : ℝ)) := by
  rw [SigGolfCandidate.T3.Budgets.failMass_eq_one_sub_accept, haccept,
    ENNReal.ofReal_sub 1 (by norm_num [BaseAudit.p0])]
  simp
theorem digest_moment_step_of_acceptance
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.p0 : ℝ)) :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope := by
  have hp0 : 0 ≤ (BaseAudit.p0 : ℝ) := by norm_num [BaseAudit.p0]
  have hp1 : 0 ≤ 1 - (BaseAudit.p0 : ℝ) := by norm_num [BaseAudit.p0]
  have hb0 : 0 ≤ (BaseAudit.b0 : ℝ) := by norm_num [BaseAudit.b0]
  have hz0 : 0 ≤ (zU : ℝ) := by norm_num [zU]
  have hs : 1 - (1 - (BaseAudit.p0 : ℝ)) = (BaseAudit.p0 : ℝ) := by ring
  rw [digest_failMass_of_acceptance haccept, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 hp1, hs, digestEnvelope]
  calc
    _ ≤ ENNReal.ofReal (zU : ℝ) *
      (ENNReal.ofReal (1 - (BaseAudit.p0 : ℝ)) * ENNReal.ofReal (BaseAudit.b0 : ℝ) +
        ENNReal.ofReal (BaseAudit.p0 : ℝ)) := mul_le_mul' signing_z_le (le_refl _)
    _ = ENNReal.ofReal ((zU : ℝ) *
        ((1 - (BaseAudit.p0 : ℝ)) * (BaseAudit.b0 : ℝ) + (BaseAudit.p0 : ℝ))) := by
      rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_add (mul_nonneg hp1 hb0) hp0,
        ← ENNReal.ofReal_mul hz0]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have h := BaseAudit.step_0
      have h' : ((zU * ((1 - BaseAudit.p0) * BaseAudit.b0 + BaseAudit.p0) : ℚ) : ℝ) ≤
          (BaseAudit.b0 : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'
theorem V_digestSearch_fresh_of_acceptance (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none)
    (haccept : Pr[fun answer => (digestDecode answer).isSome |
      ($ᵗ HashOutput : ProbComp HashOutput)] = ENNReal.ofReal (BaseAudit.p0 : ℝ)) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  ClaudeWCT.W9.T3.Sampling.V_digestSearch secret _ _ digestEnvelope_ge_one
    rho message (digest_moment_step_of_acceptance haccept) fuel counter hlimit cache hfresh
theorem digest_moment_step :
    SigGolfCandidate.Budget.zOf 131072 *
      (failMass digestDecode * digestEnvelope + (1 - failMass digestDecode)) ≤ digestEnvelope :=
  digest_moment_step_of_acceptance digest_probability_eq_p0
theorem V_digestSearch_fresh (secret : BitVec 256)
    (rho : Digest) (message : Message) (fuel counter : Nat)
    (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 →
      cache (SigGolfCandidate.T3.Sampling.digestTrial rho message c) = none) :
    V secret (SigGolfCandidate.Budget.zOf 131072)
      (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ digestEnvelope :=
  V_digestSearch_fresh_of_acceptance secret rho message fuel counter hlimit cache hfresh
    digest_probability_eq_p0
structure SourceFreshness (secret : BitVec 256) : Prop where
  layers : SigGolfCandidate.T3.Budgets.SourceFreshness secret
  digest : ∀ rho message cache, AllSearchesFresh cache →
    ∀ result ∈ support (roRun secret
      (ClaudeWCT.WCT9.digestSearch rho message 0 digestAttemptLimit) cache),
      EncodingFreshBelow 4 result.2
  forest : ∀ index output cache, EncodingFreshBelow 4 cache →
    ∀ result ∈ support (roRun secret (ClaudeWCT.WCT9.signForest index output) cache),
      EncodingFreshBelow 4 result.2
noncomputable def postDigestMoment : ENNReal := signingZ ^ 32250 * layerMomentBound 4
noncomputable def payloadMoment : ENNReal := signingZ ^ 2 * (digestEnvelope * postDigestMoment)
noncomputable def signingMoment : ENNReal := signingZ ^ 2 * payloadMoment
theorem postDigestMoment_ge_one : 1 ≤ postDigestMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _)) (layerMomentBound_ge_one 4)
theorem payloadMoment_ge_one : 1 ≤ payloadMoment :=
  one_le_mul (one_le_pow₀ (SigGolfCandidate.Budget.one_le_zOf _))
    (one_le_mul digestEnvelope_ge_one postDigestMoment_ge_one)
theorem V_signPayload_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (signPayload cache message) rcache ≤ payloadMoment := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateNonce message) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro nonce hn
  have hnFresh := hf.layers.nonce message rcache hc nonce hn
  refine V_bind_bounded secret signingZ _ _ nonce.2 _ _
    (V_digestSearch_fresh secret nonce.1 message digestAttemptLimit 0
      (by have := ClaudeWCT.WCT9.digestAttemptLimit_le; omega) nonce.2
      (fun c _ hlim => hnFresh.1 _ _ _ hlim)) ?_
  intro found hd
  have hdFresh := hf.digest nonce.1 message nonce.2 hnFresh found hd
  cases hx : found.1 with
  | none => simp only [V_pure]; exact postDigestMoment_ge_one
  | some pair =>
      obtain ⟨counter, output⟩ := pair
      refine V_bind_bounded secret signingZ _ _ found.2 _ _
        (V_of_bound (ClaudeWCT.WCT9.Cost.bound_signForest (output.toNat % 2 ^ 31) output) secret signingZ
          (SigGolfCandidate.Budget.one_le_zOf _) found.2) ?_
      intro forest hforest
      have hforestFresh := hf.forest _ _ found.2 hdFresh forest hforest
      refine V_bind_bounded secret signingZ _ _ forest.2 _ 1
        (V_signLayers_of_freshness secret hf.layers cache (output.toNat % 2 ^ 31) 4 (by decide)
          (forest.1.2, 0, 0) forest.2 hforestFresh) ?_ |>.trans_eq (mul_one _)
      intro pieces _
      cases pieces.1 <;> rw [V_pure]
theorem V_sign_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ signingMoment := by
  show V secret signingZ (ClaudeWCT.WCT9.signWith digestAttemptLimit cache message) rcache ≤ signingMoment
  unfold ClaudeWCT.WCT9.signWith
  refine V_bind_bounded secret signingZ _ _ rcache _ _
    (V_of_bound (bound_privateMac cache.region) secret signingZ
      (SigGolfCandidate.Budget.one_le_zOf _) rcache) ?_
  intro result hr
  have hmac := hf.layers.mac cache.region rcache hc result hr
  split
  · rw [V_pure]; exact payloadMoment_ge_one
  · exact V_signPayload_of_freshness secret hf cache message result.2 hmac
theorem signingMoment_eq : signingMoment = signingZ ^ 118176 *
    (digestEnvelope * encodingEnvelope 0 * encodingEnvelope 1 * encodingEnvelope 2 * encodingEnvelope 3) := by
  rw [signingMoment, payloadMoment, postDigestMoment, layerMomentBound_four]
  ring
theorem signingMoment_le_two : signingMoment ≤ 2 := by
  rw [signingMoment_eq, SigGolfCandidate.Budget.zOf_pow]
  have hreal := BaseAudit.signing_envelope
  have hcast := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) ^ ((118176 : ℝ) / 131072) by positivity)] at hcast
  norm_num only [ENNReal.ofReal_ofNat] at hcast
  have he : digestEnvelope * encodingEnvelope 0 * encodingEnvelope 1 * encodingEnvelope 2 *
      encodingEnvelope 3 =
      ENNReal.ofReal ((BaseAudit.b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) * (b4 : ℝ)) := by
    change ENNReal.ofReal (BaseAudit.b0 : ℝ) * ENNReal.ofReal (b1 : ℝ) *
      ENNReal.ofReal (b2 : ℝ) * ENNReal.ofReal (b3 : ℝ) * ENNReal.ofReal (b4 : ℝ) = _
    rw [← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ) by norm_num [BaseAudit.b0]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ) * (b1 : ℝ) by norm_num [BaseAudit.b0, b1]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) by
        norm_num [BaseAudit.b0, b1, b2]),
      ← ENNReal.ofReal_mul (show 0 ≤ (BaseAudit.b0 : ℝ) * (b1 : ℝ) * (b2 : ℝ) * (b3 : ℝ) by
        norm_num [BaseAudit.b0, b1, b2, b3])]
  rw [he]
  convert hcast using 1
  norm_num
theorem V_sign_le_two_of_freshness (secret : BitVec 256) (hf : SourceFreshness secret)
    (cache : Cache) (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_of_freshness secret hf cache message rcache hc).trans signingMoment_le_two
theorem realized_sign_exponential_budget_of_freshness (secret : BitVec 256)
    (hf : SourceFreshness secret) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFresh rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (SigGolfCandidate.T3.Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  have h := V_sign_le_two_of_freshness secret hf cache message rcache hc
  rw [SigGolfCandidate.T3.Sampling.V_realized] at h
  simp only [signingZ_pow] at h
  rw [StateT.run'_eq, expectedValue_map]
  exact h
end ClaudeWCT.W9.T3.Budgets
end
section
namespace ClaudeWCT.W9.T3.Freshness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery HasTag avoids_pure avoids_bind preserves
  preserves_encodingBelow tagged_ne_search hasTag_privatePair avoids_digest_encoding)
open ClaudeWCT.WCT9 (FtsQuery FtsInput FtsSeed digestAttemptLimit)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem avoidsQuery_of_fts (secret : BitVec 256) (target : HashInput)
    (ht : HasTag 4 target ∨ HasTag 12 target) (index : Nat) (q : Spec.Domain)
    (hq : FtsQuery index q) : avoidsQuery secret target q := by
  rcases q with (coin | input) | (tweak | other)
  · exact hq.elim
  · obtain ⟨tag, lay, position, idx, htag, hblock⟩ :=
      ClaudeWCT.WCT9.FtsInput.hdrBlock (show FtsInput index input from hq)
    have hmod := ClaudeWCT.WCT9.Wots.tag_mod htag
    exact tagged_ne_search (tag := tag) ⟨lay, index, position, idx, hblock⟩ ht hmod.2.2.1 hmod.2.2.2
  · obtain ⟨coord, selected, pair, -, -, -, rfl⟩ := (show FtsSeed index tweak from hq)
    exact tagged_ne_search (tag := 8) (hasTag_privatePair secret 8 coord index 0 (4 * selected + pair))
      ht (by decide) (by decide)
  · exact hq.elim
theorem avoids_signForest (secret : BitVec 256) (target : HashInput)
    (ht : HasTag 4 target ∨ HasTag 12 target) (index : Nat) (output : HashOutput) :
    Avoids secret target (ClaudeWCT.WCT9.signForest index output) :=
  ClaudeWCT.WCT9.Wots.allQueriesSatisfy_mono (ClaudeWCT.WCT9.signForest_queries index output)
    (fun q hq => avoidsQuery_of_fts secret target ht index q hq)
theorem avoids_digestSearch_encoding (secret : BitVec 256) (target : HashInput) (ht : HasTag 4 target)
    (rho : Digest) (message : Message) (counter fuel : Nat) :
    Avoids secret target (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; exact avoids_pure _ _ _
  | succ fuel ih =>
      unfold ClaudeWCT.WCT9.digestSearch
      refine avoids_bind (avoids_digest_encoding secret target ht rho message _) ?_
      intro output
      split
      · exact avoids_pure _ _ _
      · exact ih _
theorem sourceFreshness (secret : BitVec 256) : Budgets.SourceFreshness secret where
  layers := SigGolfCandidate.T3.Freshness.sourceFreshness secret
  digest := by
    intro rho message cache hc result hr
    exact preserves_encodingBelow secret _
      (fun target ht => avoids_digestSearch_encoding secret target ht rho message 0 digestAttemptLimit)
      4 cache hc.2 result hr
  forest := by
    intro index output cache hc result hr
    exact preserves_encodingBelow secret _
      (fun target ht => avoids_signForest secret target (Or.inl ht) index output)
      4 cache hc result hr
end ClaudeWCT.W9.T3.Freshness
end
section
namespace ClaudeWCT.W9.T3.BudgetClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V)
open ClaudeWCT.W9.T3.Budgets (V_sign_le_two_of_freshness realized_sign_exponential_budget_of_freshness)
open SigGolfCandidate.T3.Budgets (signingZ AllSearchesFresh signingZ_pow)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFresh rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  V_sign_le_two_of_freshness secret (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) cache message rcache hc
theorem realized_sign_exponential_budget (secret : BitVec 256) (cache : Cache)
    (message : Message) (rcache : RCache) (hc : AllSearchesFresh rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 :=
  realized_sign_exponential_budget_of_freshness secret
    (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) cache message rcache hc
def honestSignCount (message : Message) : M (Option Signature × Nat) := do
  let keys ← keygen
  Cost.countBlocks (sign keys.2 message)
theorem honestSignCount_realize (secret : BitVec 256) (message : Message) :
    realize secret (honestSignCount message) = (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message))) := by
  rw [honestSignCount, Cost.realize_bind]
  congr 1
  funext keys
  exact Cost.realize_count secret _
theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2 := by
  rw [honestSignCount, SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h := V_sign_le_two secret keys.1.2 message keys.2
    (SigGolfCandidate.T3.Freshness.keygen_fresh_from_empty secret keys hkeys)
  simpa only [V, signingZ_pow] using h
theorem realized_honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue ((simulateQ SphincsSecurity.romImpl (do
      let keys ← realize secret keygen
      Cost.World.countBlocks (realize secret (sign keys.2 message)))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [← honestSignCount_realize secret message, StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
theorem uniform_message_sign_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestSignCount message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_sign_exponential_budget secret message
end ClaudeWCT.W9.T3.BudgetClosure
end
section
namespace ClaudeWCT.W9.T3.ExpansionClosure
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun)
open SigGolfCandidate.T3.Cost (countBlocks)
open SigGolfCandidate.T3.ExpansionClosure (jointCounts eval_joint_cost_le)
open SigGolfCandidate.T3.SourceReplay (hashOnly_pure hashOnly_bind hashOnly_keygen)
open ClaudeWCT.W9.T3.SourceReplay (hashOnly_sign hashOnly_expand)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
def honestJointCounts (message : Message) : M (Nat × Nat) :=
  jointCounts keygen (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
theorem joint_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.1 : ℝ) / 131072)) ≤ 2 := by
  refine le_trans ?_ (ClaudeWCT.W9.T3.BudgetClosure.honest_sign_exponential_budget secret message)
  simp only [honestJointCounts, jointCounts, ClaudeWCT.W9.T3.BudgetClosure.honestSignCount,
    SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
  apply expectedValue_mono
  intro keys
  apply expectedValue_mono
  rintro ⟨⟨sig, signCost⟩, rcache⟩
  cases sig with
  | none => simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
  | some sig =>
    simp only [SigGolfCandidate.T3.Sampling.roRun_bind, expectedValue_bind]
    apply expectedValue_le_of_support
    intro expanded _
    simp only [SigGolfCandidate.T3.Sampling.roRun_pure, expectedValue_pure, le_refl]
theorem hashOnly_honestJointCounts (message : Message) :
    SigGolfCandidate.T3.SourceReplay.HashOnly (honestJointCounts message) := by
  unfold honestJointCounts jointCounts
  apply hashOnly_bind hashOnly_keygen
  intro keys
  apply hashOnly_bind (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_sign keys.2 message))
  intro signed
  cases signed.1 with
  | none => exact hashOnly_pure _
  | some sig =>
    apply hashOnly_bind
      (SigGolfCandidate.T3.CountedReplay.hashOnly_countBlocks _ (hashOnly_expand message keys.1 sig))
    intro expanded
    exact hashOnly_pure _
theorem joint_cost_le (answers : SigGolfCandidate.T3.Correctness.Answers) (message : Message) :
    (evalWithAnswerFn answers (honestJointCounts message)).2 ≤
      8 * (evalWithAnswerFn answers (honestJointCounts message)).1 := by
  exact eval_joint_cost_le (κ := Digest × Cache) (σ := Signature) (ω := Option Witness) answers keygen
    (fun keys => sign keys.2 message) (fun keys sig => expand message keys.1 sig)
    (ClaudeWCT.W9.T3.ExpansionBudget.expand_cost_le_eight_sign answers message)
theorem support_joint_cost_le (secret : BitVec 256) (message : Message)
    (result : (Nat × Nat) × RCache)
    (hr : result ∈ support (roRun secret (honestJointCounts message) ∅)) :
    result.1.2 ≤ 8 * result.1.1 := by
  obtain ⟨hash, _, heval⟩ := SigGolfCandidate.T3.CountedReplay.support_replay secret _
    (hashOnly_honestJointCounts message) ∅ result hr
  rw [heval]
  exact joint_cost_le _ message
theorem honest_expand_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestJointCounts message) ∅)
      (fun result => (2 : ENNReal) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2 := by
  refine le_trans ?_ (joint_sign_exponential_budget secret message)
  apply expectedValue_mono_of_support
  intro result hr
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (result.1.2 : ℝ) ≤ 8 * (result.1.1 : ℝ) := by
    exact_mod_cast support_joint_cost_le secret message result hr
  linarith
theorem uniform_message_expand_exponential_budget (secret : BitVec 256) :
    expectedValue (do
      let message ← ($ᵗ Message : ProbComp Message)
      (simulateQ SphincsSecurity.romImpl (realize secret (honestJointCounts message))).run' ∅)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 1048576)) ≤ 2 := by
  rw [expectedValue_bind]
  apply expectedValue_le_of_support
  intro message _
  rw [StateT.run'_eq, expectedValue_map]
  exact honest_expand_exponential_budget secret message
end ClaudeWCT.W9.T3.ExpansionClosure
end
section
namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy
structure Images where
  sign : Riscv.Image
  expand : Riscv.Image
  verify : Riscv.Image
def submission (I : Images) : Submission where
  sizes := ⟨5456, 25240, 131072⟩
  layout := ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩
  image
    | .keygen => SigGolfCandidate.T3M.Images.keygenImage
    | .sign => I.sign
    | .expand => I.expand
    | .verify => I.verify
variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5456, 25240, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x40, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩ := rfl
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl
end ClaudeWCT.W9.T3M
end
section
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open ClaudeWCT.W9.T3M (Images submission)
def verifyCycleBound : Nat := 7797
def claimedC : Nat := 7896
variable (I : Images)
def KeygenRunCounts : Prop := ∀ sk : SecretKey,
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .keygen sk =
    (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2.1, p.2.2)) <$> countBoth (mrealize sk keygen)
def KeygenRunWith : Prop := ∀ (hash : Hash) (sk : SecretKey),
  (submission I).runWith hash .keygen sk =
    ⟨some (((evalWithAnswerFn hash (mrealize sk keygen)).1 : PublicKey),
      cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2), true, 53919407, 995328, 1048576⟩
def SignRefines : Prop := ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .sign (sk, cache, m) =
    (fun p => (p.1.map sigB, p.2.1, p.2.2)) <$> countBoth (mrealize sk (sign (cacheDec cache) m))
def SignTerminates : Prop := ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
  ((submission I).runWith hash .sign (sk, cache, m)).finished = true ∧
    ((submission I).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def ExpandRefines : Prop := ∀ (m : Message) (pk : PublicKey) (s : Bytes 5456),
  (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (submission I).run .expand (m, pk, s) =
    (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
      countBoth (mrealize 0 (expandN m pk (sigDec s)))
def ExpandTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5456),
  ((submission I).runWith hash .expand (m, pk, s)).finished = true ∧
    ((submission I).runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 25240),
  (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240),
  ((submission I).runWith hash .verify (m, pk, w)).finished = true ∧
    ((submission I).runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 25240),
  ((submission I).runWith hash .verify (m, pk, w)).value.isSome = true →
    ((submission I).runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound
structure Pending : Prop where
  admissible : (submission I).Admissible
  keygen_run_counts : KeygenRunCounts I
  keygen_runWith : KeygenRunWith I
  sign_refines : SignRefines I
  sign_terminates : SignTerminates I
  expand_refines : ExpandRefines I
  expand_terminates : ExpandTerminates I
  verify_refines : VerifyRefines I
  verify_terminates : VerifyTerminates I
  verify_accept_cycles : VerifyAcceptCycles I
def SourceCompleteness : Prop := ∀ secret : BitVec 256,
  1 - 1 / (2 : ℝ≥0∞) ^ 128 ≤
    Pr[= true | (simulateQ SphincsSecurity.romImpl
      (realize secret ClaudeWCT.W9.T3.Completeness.everyMessageProgram)).run' ∅]
def SignMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) ≤ 2
def ExpandMoment : Prop := ∀ (secret : BitVec 256) (message : SigGolfCandidate.T3.Message),
  expectedValue (SigGolfCandidate.T3.Sampling.roRun secret
      (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts message) ∅)
    (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) ≤ 2
structure SourceFacts : Prop where
  source_completeness : SourceCompleteness
  honest_sign_exponential_budget : SignMoment
  honest_expand_exponential_budget : ExpandMoment
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (cache : Cache) (message : SigGolfCandidate.T3.Message),
    AllQueriesSatisfy (sign cache message) isHash
  hashOnly_expand : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (sig : Signature),
    AllQueriesSatisfy (expand message pk sig) isHash
  hashOnly_verify : ∀ (message : SigGolfCandidate.T3.Message) (pk : Digest) (w : Witness),
    AllQueriesSatisfy (verify message pk w) isHash
  securityP : SecurityP
end ClaudeWCT.W9.T3M.Final
end
