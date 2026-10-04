import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.QuerySpace

namespace ClaudeWCT.W9.T3.Presampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.QuerySpace (DigestFamily)
open ClaudeWCT.W9.T3.PairRows (msgLeft msgRight layerCounterSearch_none_iff eval_shortHash_layer)
open SigGolfCandidate.T3.Presampling (eval_shortHash eval_digest uniform_table_forall)
open ClaudeWCT.WCT9 (digestAttemptLimit)
abbrev HashInput := SphincsSecurity.HashInput
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[irreducible] noncomputable def tableSampler : SampleableType (SearchKey → HashOutput) :=
  Derivation.outputSampler SearchKey
noncomputable local instance : SampleableType (SearchKey → HashOutput) := tableSampler
noncomputable def preparedCache (outputs : SearchKey → HashOutput) : QueryCache SphincsSecurity.HashSpec :=
  cacheTable ∅ searchQuery outputs
theorem preparedCache_apply (outputs : SearchKey → HashOutput) (key : SearchKey) :
    preparedCache outputs (searchQuery key) = some (outputs key) :=
  cacheTable_apply ∅ searchQuery searchQuery_injective outputs key
theorem presample_source {α : Type} (secret : BitVec 256) (program : M α) :
    𝒮[(simulateQ SphincsSecurity.romImpl (realize secret program)).run' ∅] =
    𝒮[do
      let outputs ← ($ᵗ (SearchKey → HashOutput) : ProbComp _)
      (simulateQ SphincsSecurity.romImpl (realize secret program)).run' (preparedCache outputs)] := by
  let : SampleableType (SearchKey → SphincsSecurity.HashOutput) := tableSampler
  let preparation : OracleComp SphincsSecurity.OracleWorld (SearchKey → HashOutput) :=
    liftM (queryTable (R := SphincsSecurity.HashOutput) searchQuery)
  have hprep : (simulateQ SphincsSecurity.romImpl preparation).run ∅ =
      (simulateQ randomOracle (queryTable (R := SphincsSecurity.HashOutput) searchQuery)).run ∅ := by
    exact congrArg (fun run => run.run (∅ : QueryCache SphincsSecurity.HashSpec))
      (QueryImpl.simulateQ_add_liftM_right (unifFwdImpl SphincsSecurity.HashSpec)
        (randomOracle (spec := SphincsSecurity.HashSpec)) (queryTable (R := SphincsSecurity.HashOutput) searchQuery))
  rw [evalDist_presample_computation (realize secret program) preparation ∅, hprep,
    evalSPMF_bind, evalDist_queryTable_fresh (R := SphincsSecurity.HashOutput) searchQuery searchQuery_injective
      ∅ (fun _ => rfl)]
  simp only [evalSPMF_map, bind_map_left]
  rw [evalSPMF_bind]
  congr 1
noncomputable def tableAnswers (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) : Correctness.Answers
  | .inl (.inr input) => (preparedCache outputs input).getD (fallback (.inl (.inr input)))
  | .inl (.inl input) => fallback (.inl (.inl input))
  | .inr input => fallback (.inr input)
theorem tableAnswers_apply (outputs : SearchKey → HashOutput) (fallback : Correctness.Answers)
    (key : SearchKey) : tableAnswers outputs fallback (.inl (.inr (searchQuery key))) = outputs key := by
  simp only [tableAnswers, preparedCache_apply, Option.getD_some]
theorem uniform_table_restriction_failure {J : Type} [Fintype J]
    [DecidableEq J] [SampleableType (J → HashOutput)] (e : J → SearchKey) (he : Function.Injective e)
    (p : HashOutput → Prop) :
    Pr[fun outputs : SearchKey → HashOutput => ∀ j, p (outputs (e j)) |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
      Pr[p | ($ᵗ HashOutput : ProbComp _)] ^ Fintype.card J := by
  have h := evalSPMF_uniformSample_map_comp_injective (R := HashOutput) he
  have hp := congrArg (fun law => probEvent law (fun outputs : J → HashOutput => ∀ j, p (outputs j))) h
  simpa only [probEvent_evalSPMF, bind_pure_comp, probEvent_map, Function.comp_def,
    uniform_table_forall] using hp
theorem layerCounterSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (lay : Layer) (tree : Fin (2 ^ 31)) (leaf : Fin 4096)
    (msg : ClaudeWCT.WCT9.LayerMsg) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf msg 0 counterLimit) = none ↔
    ∀ c : Fin (2 ^ 22), SigGolfCandidate.T3.Sampling.encodingDecode lay
      (outputs (.inl ((lay, tree, leaf, msgLeft msg, msgRight msg), c))) = none := by
  rw [layerCounterSearch_none_iff]
  have hv (c : Nat) (hc : c < counterLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (shortHash (ClaudeWCT.WCT9.layerEncodingInput lay tree leaf msg (BitVec.ofNat 32 (0 + c)))) =
        (outputs (.inl ((lay, tree, leaf, msgLeft msg, msgRight msg), ⟨c, hc⟩))).extractLsb' 0 128 := by
    rw [Nat.zero_add, eval_shortHash_layer]
    have hinput : PairRows.pairTrial lay tree leaf (msgLeft msg) (msgRight msg) c =
        searchQuery (.inl ((lay, tree, leaf, msgLeft msg, msgRight msg), ⟨c, hc⟩)) := rfl
    rw [hinput, tableAnswers_apply]
  constructor
  · intro h c
    have h := h c c.isLt
    rw [hv c c.isLt] at h
    exact h
  · intro h c hc
    rw [hv c hc]
    exact h ⟨c, hc⟩
theorem digestSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : DigestFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none ↔
    ∀ c : Fin (2 ^ 21), ClaudeWCT.W9.T3.Sampling.digestDecode (outputs (.inr (family, c))) = none := by
  rw [ClaudeWCT.WCT9.digestSearch_none_iff]
  have hv (c : Nat) (hc : c < digestAttemptLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (digest family.1 family.2 (BitVec.ofNat 32 (0 + c))) = outputs (.inr (family, ⟨c, hc⟩)) := by
    rw [eval_digest]
    have hinput : pad64 (digestInput family.1 family.2 (BitVec.ofNat 32 (0 + c))) =
        searchQuery (.inr (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inr, digestQuery, SigGolfCandidate.T3.Sampling.digestTrial,
        Nat.zero_add]
    rw [hinput, tableAnswers_apply]
  constructor
  · intro h c
    rw [ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff]
    have h := h c c.isLt
    rwa [hv c c.isLt] at h
  · intro h c hc
    rw [hv c hc]
    exact (ClaudeWCT.W9.T3.Sampling.digestDecode_eq_none_iff _).mp (h ⟨c, hc⟩)
theorem layerCounterSearch_table_failure (fallback : Correctness.Answers) (lay : Layer) (tree : Fin (2 ^ 31))
    (leaf : Fin 4096) (left right : Digest) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.layerCounterSearch lay tree leaf (.pair left right) 0 counterLimit) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (SigGolfCandidate.T3.Sampling.encodingDecode lay) ^ counterLimit := by
  simp_rw [layerCounterSearch_none_table, msgLeft, msgRight]
  have h := uniform_table_restriction_failure (fun c : Fin (2 ^ 22) => .inl ((lay, tree, leaf, left, right), c))
    (fun _ _ h => congrArg Prod.snd (Sum.inl.inj h))
    (fun x => SigGolfCandidate.T3.Sampling.encodingDecode lay x = none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent, Fintype.card_fin, counterLimit,
    HashOutput, SphincsSecurity.HashOutput, SphincsSecurity.hashOutputBits] using h
theorem digestSearch_table_failure (fallback : Correctness.Answers) (family : DigestFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (ClaudeWCT.WCT9.digestSearch family.1 family.2 0 digestAttemptLimit) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass ClaudeWCT.W9.T3.Sampling.digestDecode ^ digestAttemptLimit := by
  simp_rw [digestSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2 ^ 21) => .inr (family, c))
    (fun _ _ h => congrArg Prod.snd (Sum.inr.inj h))
    (fun x => ClaudeWCT.W9.T3.Sampling.digestDecode x = none)
  simpa only [SphincsSecurity.Completeness.failMass_eq_probEvent, Fintype.card_fin,
    ClaudeWCT.WCT9.digestAttemptLimit, HashOutput, SphincsSecurity.HashOutput,
    SphincsSecurity.hashOutputBits] using h
end ClaudeWCT.W9.T3.Presampling
