import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Presampling
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Moment
import SigGolfCandidate.ClaudeWCT.WCT9.QueriesWots
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.ExpansionBudget
import SigGolfCandidate.ClaudeWCT.W9.T3M.Submission
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries
import SigGolfCandidate.ClaudeWCT.W9.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.SecurityP

section


namespace ClaudeWCT.W9.T3.SourceReplay
open OracleComp OracleSpec
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM
  hashOnly_foldlM hashOnly_shortHash hashOnly_privatePair hashOnly_nodeHash fixedAnswers fixed_replay)
open ClaudeWCT.WCT9 (Signature Witness)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[aesop safe apply] theorem hashOnly_chain (index coord selected i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (index coord selected : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (pairs : List (Digest × Digest)) :
    HashOnly (ClaudeWCT.WCT9.forestPk index pairs) := by
  unfold ClaudeWCT.WCT9.forestPk; hashes
@[aesop safe apply] theorem hashOnly_buildChild (index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank) :
    HashOnly (ClaudeWCT.WCT9.buildChild index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildChild; hashes
@[aesop safe apply] theorem hashOnly_wctNodeHash (coord index heap : Nat) (left right : Digest) :
    HashOnly (ClaudeWCT.WCT9.wctNodeHash coord index heap left right) := by
  unfold ClaudeWCT.WCT9.wctNodeHash; exact hashOnly_nodeHash _ _ _ _ _ _
@[aesop safe apply] theorem hashOnly_heapBuild (index coord : Nat) (leaves : List Digest) :
    HashOnly (ClaudeWCT.WCT9.heapBuild index coord leaves) := by
  unfold ClaudeWCT.WCT9.heapBuild
  exact hashOnly_foldlM _ _ (fun nodes heap =>
    hashOnly_bind (hashOnly_wctNodeHash coord index heap _ _) fun _ => hashOnly_pure _) _
@[aesop safe apply] theorem hashOnly_buildCoordinate (index : Nat) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    HashOnly (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state j => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildChild index coord.val j word) fun r => ?_
    rcases r with ⟨root, values⟩
    exact hashOnly_pure _
  · exact hashOnly_bind (hashOnly_heapBuild index coord.val state.1) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.digestSearch; hashes
@[aesop safe apply] theorem hashOnly_openingStep (index : Nat) (output : HashOutput)
    (state : List ClaudeWCT.WCT9.Opening × List (Digest × Digest)) (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.openingStep index output state coord) := by
  unfold ClaudeWCT.WCT9.openingStep; hashes
@[aesop safe apply] theorem hashOnly_forestRows (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows; hashes
@[aesop safe apply] theorem hashOnly_signForest (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest; hashes
@[aesop safe apply] theorem hashOnly_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput)
    (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.recoverCoordinate sig index output coord) := by
  unfold ClaudeWCT.WCT9.recoverCoordinate; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.recoverFts sig index output) := by
  unfold ClaudeWCT.WCT9.recoverFts; hashes
@[aesop safe apply] theorem hashOnly_layerCounterSearch (lay : Layer) (tree leaf : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.layerCounterSearch; hashes
@[aesop safe apply] theorem hashOnly_signLayersBC (cache : Cache) (index n : Nat) (msg : ClaudeWCT.WCT9.LayerMsg) :
    HashOnly (ClaudeWCT.WCT9.signLayersBC cache index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.signLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.signLayersBC; hashes
@[aesop safe apply] theorem hashOnly_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer)
    (digits : List Nat) : HashOnly (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair; hashes
@[aesop safe apply] theorem hashOnly_expandLayersBC (sig : Signature) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.expandLayersBC sig index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.expandLayersBC; hashes
@[aesop safe apply] theorem hashOnly_verifyLayersBC (w : Witness) (index n : Nat)
    (msg : ClaudeWCT.WCT9.LayerMsg) : HashOnly (ClaudeWCT.WCT9.verifyLayersBC w index n msg) := by
  induction n generalizing msg with
  | zero => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
  | succ n ih => unfold ClaudeWCT.WCT9.verifyLayersBC; hashes
@[aesop safe apply] theorem hashOnly_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signPayloadWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signPayloadWith; hashes
@[aesop safe apply] theorem hashOnly_signWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signWith; hashes
@[aesop safe apply] theorem hashOnly_expandWith (limit : Nat) (message : Message) (pk : Digest)
    (sig : Signature) : HashOnly (ClaudeWCT.WCT9.expandWith limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandWith; hashes
@[aesop safe apply] theorem hashOnly_verifyWith (limit : Nat) (message : Message) (pk : Digest)
    (w : Witness) : HashOnly (ClaudeWCT.WCT9.verifyWith limit message pk w) := by
  unfold ClaudeWCT.WCT9.verifyWith; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.signPayload cache message) :=
  hashOnly_signPayloadWith _ cache message
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.sign cache message) :=
  hashOnly_signWith _ cache message
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.Rev3.expand message pk sig) :=
  hashOnly_expandWith _ message pk sig
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (ClaudeWCT.WCT9.Rev3.verify message pk w) :=
  hashOnly_verifyWith _ message pk w
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (cache : Cache) (message : Message) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.sign cache message)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.sign cache message)) :=
  fixed_replay secret hash _ (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (sig : Signature) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.expand message pk sig)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.expand message pk sig)) :=
  fixed_replay secret hash _ (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (w : Witness) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.verify message pk w)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.verify message pk w)) :=
  fixed_replay secret hash _ (hashOnly_verify message pk w)
end ClaudeWCT.W9.T3.SourceReplay
end

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


namespace ClaudeWCT.W9.T3.Freshness
open OracleComp OracleSpec
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.Freshness (Avoids avoidsQuery HasTag tagged_ne_search hasTag_privatePair)
open ClaudeWCT.WCT9 (FtsQuery FtsInput FtsSeed)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem avoidsQuery_of_fts (secret : BitVec 256) (target : HashInput)
    (ht : HasTag 4 target ∨ HasTag 12 target) (index : Nat) (q : Spec.Domain)
    (hq : FtsQuery index q) : avoidsQuery secret target q := by
  rcases q with (coin | input) | (tweak | other)
  · exact hq.elim
  · rcases ClaudeWCT.WCT9.FtsInput.hdrBlock (show FtsInput index input from hq) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨tag, lay, position, idx, htag, hblock⟩
    · intro he
      subst he
      rcases ht with ⟨l, tr, p, ix, hh⟩ | ⟨l, tr, p, ix, hh⟩
      · exact ClaudeWCT.WCT9.ftsChainHeaderP_ne_header index coord selected t step 0 4 l tr p ix
          (bytesLE_injective (hblock.symm.trans hh))
      · exact ClaudeWCT.WCT9.ftsChainHeaderP_ne_header index coord selected t step 0 12 l tr p ix
          (bytesLE_injective (hblock.symm.trans hh))
    · have hmod := ClaudeWCT.WCT9.Wots.tag_mod' htag
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
theorem sourceFreshness (secret : BitVec 256) : Budgets.SourceFreshness secret where
  forest := by
    intro index output cache hc result hr
    exact ClaudeWCT.W9.T3.PairRows.preserves_pairBelow secret _
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
open ClaudeWCT.W9.T3.Budgets (V_sign_of_freshness_for realized_sign_exponential_budget_of_freshness_for)
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.PairRows (AllSearchesFreshBC)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem V_sign_le_signingMoment (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ ClaudeWCT.W9.T3.Budgets.signingMoment :=
  V_sign_of_freshness_for secret (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) _
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message)
    (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    V secret signingZ (sign cache message) rcache ≤ 2 :=
  (V_sign_le_signingMoment secret cache message rcache hc).trans ClaudeWCT.W9.T3.Budgets.signingMoment_le_two
theorem realized_sign_exponential_budget (secret : BitVec 256) (cache : Cache)
    (message : Message) (rcache : RCache) (hc : AllSearchesFreshBC rcache) :
    expectedValue ((simulateQ SphincsSecurity.romImpl
      (Cost.World.countBlocks (realize secret (sign cache message)))).run' rcache)
      (fun result => (2 : ENNReal) ^ ((result.2 : ℝ) / 131072)) ≤ 2 :=
  realized_sign_exponential_budget_of_freshness_for secret
    (ClaudeWCT.W9.T3.Freshness.sourceFreshness secret) (by norm_num)
    (fun index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_signForest index output⟩) cache message rcache hc
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
    (ClaudeWCT.W9.T3.PairRows.keygen_fresh_from_empty_bc secret keys hkeys)
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







namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.T3 (keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize countBoth countCalls cacheB cacheDec isHash)
open ClaudeWCT.W9.T3M (Images submission)
def verifyCycleBound : Nat := 7623
def claimedC : Nat := 7718
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
def VerifyRefines : Prop := ∀ (m : Message) (pk : PublicKey) (w : Bytes 24264),
  (fun r => (r.value, r.hashCalls)) <$> (submission I).run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (mrealize 0 (verifyP m pk w))
def VerifyTerminates : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24264),
  ((submission I).runWith hash .verify (m, pk, w)).finished = true ∧
    ((submission I).runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT
def VerifyAcceptCycles : Prop := ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes 24264),
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
