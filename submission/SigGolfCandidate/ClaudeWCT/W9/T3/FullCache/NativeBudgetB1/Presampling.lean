import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.T3.FullCache.NativeBudget

section


namespace ClaudeWCT.W9.T3.Sampling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 hiding digestSearch admissible
open SigGolfCandidate.T3.Sampling (RCache roRun V publicProgram digestTrial digestTrial_injective
  digestTrial_length V_publicSearch public_randomOracle)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
def digestDecode (answer : HashOutput) : Option HashOutput :=
  if ClaudeWCT.WCT9.admissible answer then some answer else none
theorem digestDecode_eq_none_iff (value : HashOutput) :
    digestDecode value = none ↔ ClaudeWCT.WCT9.admissible value = false := by
  simp [digestDecode]
theorem digestSearch_public (rho : Digest) (message : Message) :
    ∀ fuel counter, ClaudeWCT.WCT9.digestSearch rho message counter fuel =
      publicProgram (SphincsSecurity.Completeness.searchLoop
        (digestTrial rho message) digestDecode
        (fun c output => pure (BitVec.ofNat 32 c, output)) fuel counter) := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [ClaudeWCT.WCT9.digestSearch, SphincsSecurity.Completeness.searchLoop]
      simp only [publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, SigGolfCandidate.T3.Sampling.publicHandler,
        digest, publicHash, bind_assoc, pure_bind, digestTrial, digestDecode]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_map, simulateQ_pure, map_pure, ih, publicProgram]
theorem digestSearch_failure (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32)
    (cache : QueryCache SphincsSecurity.HashSpec)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    Pr[fun result => result.1 = none |
      (simulateQ SphincsSecurity.romImpl
        (realize secret (ClaudeWCT.WCT9.digestSearch rho message counter fuel))).run cache] ≤
      SphincsSecurity.Completeness.failMass digestDecode ^ fuel := by
  rw [digestSearch_public, public_randomOracle]
  exact SphincsSecurity.Completeness.probEvent_searchLoop _ _ _ (2 ^ 32)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    fuel counter hlimit cache hfresh
theorem V_digestSearch (secret : BitVec 256) (z b : ENNReal) (hb : 1 ≤ b)
    (rho : Digest) (message : Message)
    (hstep : z * (SphincsSecurity.Completeness.failMass digestDecode * b +
      (1 - SphincsSecurity.Completeness.failMass digestDecode)) ≤ b)
    (fuel counter : Nat) (hlimit : counter + fuel ≤ 2 ^ 32) (cache : RCache)
    (hfresh : ∀ c, counter ≤ c → c < 2 ^ 32 → cache (digestTrial rho message c) = none) :
    V secret z (ClaudeWCT.WCT9.digestSearch rho message counter fuel) cache ≤ b := by
  rw [digestSearch_public]
  exact V_publicSearch secret z b hb _ _ _ (2 ^ 32)
    (fun c _ => digestTrial_length rho message c)
    (fun _ _ hl hr he => digestTrial_injective rho message hl hr he)
    hstep fuel counter hlimit cache hfresh
end ClaudeWCT.W9.T3.Sampling
end

section

namespace ClaudeWCT.W9.T3.QuerySpace
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling (digestTrial encodingTrial)
open SigGolfCandidate.T3.QuerySpace (EncodingFamily DigestFamily EncodingKey encodingQuery
  encodingQuery_injective encodingTrial_ne_digestTrial digestTrial_coordinates)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
abbrev DigestKey := DigestFamily × Fin (2 ^ 21)
abbrev SearchKey := EncodingKey ⊕ DigestKey
def digestQuery (key : DigestKey) : HashInput := digestTrial key.1.1 key.1.2 key.2
def searchQuery : SearchKey → HashInput := Sum.elim encodingQuery digestQuery
theorem digestQuery_injective : Function.Injective digestQuery := by
  rintro ⟨⟨rho, msg⟩, counter⟩ ⟨⟨rho', msg'⟩, counter'⟩ he
  obtain ⟨a, b, c⟩ := digestTrial_coordinates
    (by have := counter.isLt; omega) (by have := counter'.isLt; omega) he
  have c := Fin.ext c
  cases a; cases b; cases c; rfl
theorem searchQuery_injective : Function.Injective searchQuery := by
  intro left right he
  cases left with
  | inl l =>
    cases right with
    | inl r => exact congrArg Sum.inl (encodingQuery_injective he)
    | inr r => exact False.elim (encodingTrial_ne_digestTrial l.1.1 l.1.2.1 l.1.2.2.1
        l.1.2.2.2 l.2 r.1.1 r.1.2 r.2 (by have := l.1.2.1.isLt; omega)
        (by have := l.1.2.2.1.isLt; omega) he)
  | inr l =>
    cases right with
    | inl r => exact False.elim (encodingTrial_ne_digestTrial r.1.1 r.1.2.1 r.1.2.2.1
        r.1.2.2.2 r.2 l.1.1 l.1.2 l.2 (by have := r.1.2.1.isLt; omega)
        (by have := r.1.2.2.1.isLt; omega) he.symm)
    | inr r => exact congrArg Sum.inr (digestQuery_injective he)
theorem searchQuery_length (key : SearchKey) : (searchQuery key).length = 64 := by
  cases key with
  | inl key => exact SigGolfCandidate.T3.Sampling.encodingTrial_length _ _ _ _ _
  | inr key => exact SigGolfCandidate.T3.Sampling.digestTrial_length _ _ _
end ClaudeWCT.W9.T3.QuerySpace
end

section

namespace ClaudeWCT.W9.T3.Presampling
open OracleComp OracleSpec ENNReal
open SphincsSecurity.Seeded
open SigGolfCandidate.T3 hiding digestSearch admissible
open ClaudeWCT.W9.T3.QuerySpace
open SigGolfCandidate.T3.QuerySpace (EncodingFamily DigestFamily)
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
theorem counterSearch_none_table (outputs : SearchKey → HashOutput)
    (fallback : Correctness.Answers) (family : EncodingFamily) :
    evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit) = none ↔
    ∀ c : Fin (2 ^ 22), SigGolfCandidate.T3.Sampling.encodingDecode family.1 (outputs (.inl (family, c))) = none := by
  rw [Correctness.counterSearch_none_iff]
  have hv (c : Nat) (hc : c < counterLimit) :
      evalWithAnswerFn (tableAnswers outputs fallback)
        (shortHash (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
          (BitVec.ofNat 32 (0 + c)))) = (outputs (.inl (family, ⟨c, hc⟩))).extractLsb' 0 128 := by
    rw [eval_shortHash]
    have hinput : pad64 (encodingInput family.1 family.2.1 family.2.2.1 family.2.2.2
        (BitVec.ofNat 32 (0 + c))) = searchQuery (.inl (family, ⟨c, hc⟩)) := by
      simp only [searchQuery, Sum.elim_inl, SigGolfCandidate.T3.QuerySpace.encodingQuery,
        SigGolfCandidate.T3.Sampling.encodingTrial, Nat.zero_add]
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
theorem counterSearch_table_failure (fallback : Correctness.Answers) (family : EncodingFamily) :
    Pr[fun outputs => evalWithAnswerFn (tableAnswers outputs fallback)
      (counterSearch family.1 family.2.1 family.2.2.1 family.2.2.2 0 counterLimit) = none |
      ($ᵗ (SearchKey → HashOutput) : ProbComp _)] =
    SphincsSecurity.Completeness.failMass (SigGolfCandidate.T3.Sampling.encodingDecode family.1) ^ counterLimit := by
  simp_rw [counterSearch_none_table]
  have h := uniform_table_restriction_failure (fun c : Fin (2 ^ 22) => .inl (family, c))
    (fun _ _ h => congrArg Prod.snd (Sum.inl.inj h))
    (fun x => SigGolfCandidate.T3.Sampling.encodingDecode family.1 x = none)
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
end
