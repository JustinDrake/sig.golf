import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FiniteHashWorld
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierGameProjection
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraphHonest
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingInputs
import SigGolfCandidate.SphincsSecurity.Proof.Reference.CausalFrontierGame
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceFamilyConditioning

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs boundaryEval fixedBoundaryRun
theorem simulateQ_fixedHashWorld_lift_prob {α : Type} (f : QueryImpl HashSpec Id) (computation : ProbComp α) :
    simulateQ (fixedHashWorld f) (liftM computation) = computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [liftM_bind, simulateQ_bind]
      have hquery : simulateQ (fixedHashWorld f)
          (liftM (liftM (unifSpec.query input) : ProbComp _)) = (liftM (unifSpec.query input) : ProbComp _) := by
        change simulateQ (fixedHashWorld f) (liftM (OracleWorld.query (.inl input))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hquery]
      exact bind_congr ih
noncomputable def boundaryGameCore (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  boundaryComputation parameter (gameAfterSecrets adversary parameter otsSecret ftsSecret)
theorem boundaryComputation_fst {α : Type} (parameter : PublicParameter) (computation : OracleComp OracleWorld α) :
    Prod.fst <$> boundaryComputation parameter computation = computation := by
  rw [boundaryComputation, QueryImpl.fst_map_run_withTrace, simulateQ_id']
theorem boundaryGameCore_fst (adversary : Adversary) :
    Prod.fst <$> boundaryGameCore adversary = gameCore scheme adversary := by
  rw [gameCore_eq_secrets, boundaryGameCore]
  simp only [map_bind, boundaryComputation_fst]
noncomputable def fixedFrontierGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, honestTop f parameter (otsSecret topLayer rootTree)⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalFrontierValues key f words) adversary
theorem simulateQ_boundaryGameCore_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) :
    simulateQ (fixedHashWorld f) (boundaryGameCore adversary) = fixedFrontierGame f dummy adversary := by
  rw [boundaryGameCore, fixedFrontierGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [← fixedBoundaryRun_eq_boundaryComputation, fixedBoundaryRun_gameAfterSecrets_canonical]
noncomputable def frontierOracleGame (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let table ← sampleHashTable inputs
  fixedFrontierGame (finiteHashAnswer ∅ inputs table) dummy adversary
theorem evalDist_boundaryGameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒮[frontierOracleGame inputs dummy adversary] := by
  rw [evalDist_romRun_eq_finiteHash _ inputs hinputs ∅, frontierOracleGame]
  apply evalSPMF_bind_congr_left
  intro table
  rw [simulateQ_boundaryGameCore_frontier _ dummy adversary]
theorem evalDist_gameCore_frontier (inputs : Finset HashInput) (dummy : OtsReferenceWords)
    (adversary : Adversary) (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒮[Prod.fst <$> frontierOracleGame inputs dummy adversary] := by
  rw [← boundaryGameCore_fst, simulateQ_map, StateT.run'_eq, StateT.run_map]
  simp only [← LawfulFunctor.comp_map, Function.comp_def]
  rw [evalSPMF_map]
  have h := congrArg (fun distribution : SPMF (Bool × SigningBoundaryTrace) => Prod.fst <$> distribution)
    (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs)
  simpa only [StateT.run'_eq, evalSPMF_map, ← LawfulFunctor.comp_map, Function.comp_def] using h
theorem boundaryGameCore_hashCalls_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support ((simulateQ romImpl (boundaryGameCore adversary)).run' ∅)) :
    result.2.hashCalls ≤ q := by
  rw [boundaryGameCore, simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨otsSecret, hots, hresult⟩ := hresult
  rw [simulateQ_romImpl_liftM_bind_run', mem_support_bind_iff] at hresult
  obtain ⟨ftsSecret, hfts, hresult⟩ := hresult
  rw [← boundaryRun_fst_eq_boundaryComputation, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact (hashQueryBound_iff_boundaryRun parameter _ ∅ q).mp
    (hashQueryBound_gameAfterSecrets adversary q hbound hparameter hots hfts) record hrecord
end SphincsSecurity.Concrete
end

section





namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalEncodingInputs
noncomputable def graphFrontierGameRest (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let key : SecretKey := ⟨parameter, canonicalGraphRoot labels, otsSecret, ftsSecret,
    honestTop f parameter (otsSecret topLayer rootTree)⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalGraphFrontier otsSecret labels words) adversary
theorem graphFrontierGameRest_canonical (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    graphFrontierGameRest parameter otsSecret ftsSecret
      (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary =
        fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [graphFrontierGameRest, canonicalGraphLabels_root,
    canonicalGraphLabels_frontier parameter otsSecret ftsSecret f _
      (evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)))
      (honestTop f parameter (otsSecret topLayer rootTree)),
    fixedBoundaryRun_gameAfterSecrets_canonical adversary parameter otsSecret ftsSecret f dummy]
noncomputable def fixedGraphGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  graphFrontierGameRest parameter otsSecret ftsSecret
    (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary
theorem fixedGraphGame_eq_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : fixedGraphGame f dummy adversary = fixedFrontierGame f dummy adversary := by
  rw [← simulateQ_boundaryGameCore_frontier f dummy adversary, boundaryGameCore, fixedGraphGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [graphFrontierGameRest_canonical, fixedBoundaryRun_eq_boundaryComputation]
noncomputable def canonicalGraphOracleGame (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let graph ← plantCanonicalGraph parameter otsSecret ftsSecret inputs (hgraph parameter)
  graphFrontierGameRest parameter otsSecret ftsSecret graph.1
    (finiteHashAnswer ∅ inputs graph.2) dummy adversary
theorem evalDist_frontier_eq_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒮[frontierOracleGame inputs dummy adversary] =
      𝒮[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  rw [frontierOracleGame, canonicalGraphOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame]
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro parameter
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro otsSecret
  rw [evalSPMF_bind_comm]
  apply evalSPMF_bind_congr_left
  intro ftsSecret
  exact evalDist_canonicalGraph_bind_eq_plant parameter otsSecret ftsSecret inputs (hgraph parameter)
    (fun labels table => graphFrontierGameRest parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs table) dummy adversary)
theorem evalDist_boundaryGameCore_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒮[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (evalDist_frontier_eq_canonicalGraph inputs hgraph dummy adversary)
noncomputable def canonicalGraphGameInputs (adversary : Adversary) : Finset HashInput :=
  ((hashInputs (boundaryGameCore adversary) ∪ Finset.univ.biUnion canonicalGraphInputs) ∪
    Finset.univ.biUnion canonicalEncodingInputs) ∪
    Finset.univ.biUnion fun code : KeyCode =>
      hashInputs (gameRest scheme adversary ⟨code.key.root, code.key.parameter⟩ code.key)
attribute [local irreducible] canonicalGraphGameInputs
theorem canonicalGraphInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalGraphInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩
theorem hashInputs_subset_canonicalGraphGameInputs (adversary : Adversary) :
    hashInputs (boundaryGameCore adversary) ⊆ canonicalGraphGameInputs adversary := by
  rw [canonicalGraphGameInputs]
  exact Finset.Subset.trans Finset.subset_union_left
    (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left)
theorem canonicalEncodingInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalEncodingInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩
theorem hashInputs_gameRest_subset_canonicalGraphGameInputs (adversary : Adversary) (key : SecretKey) :
    hashInputs (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  refine ⟨keyCode key, Finset.mem_univ _, ?_⟩
  rw [gameRest_keyCode]
  exact hinput
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false
def fixedReferenceDummyWord : Encoding := OtsCode.defaultWord
theorem fixedReferenceDummyWord_valid : OtsCode.Valid fixedReferenceDummyWord := OtsCode.defaultWord_valid
def fixedReferenceDummy : OtsReferenceWords := fun _ _ _ => fixedReferenceDummyWord
def referenceFamilyWords (selections : ReferenceFamily) (dummy : OtsReferenceWords) : OtsReferenceWords :=
  fun lay tree leaf => ((selections ⟨lay, tree, leaf⟩).map Prod.snd).getD (dummy lay tree leaf)
theorem referenceFamilyWords_selected (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) :
    referenceFamilyWords (referenceTableSelection key f) dummy = canonicalReferenceWords key f dummy := by
  funext lay tree leaf
  rw [referenceFamilyWords, canonicalReferenceWords,
    ← referenceSelectionResult_eq_search key f ⟨lay, tree, leaf⟩]
  simp only [referenceSelectionResult, Option.map_map, Function.comp_def]
theorem referenceFamilyOracleSample_words (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords) :
    referenceFamilyWords result.1 dummy = canonicalReferenceWords key (finiteHashAnswer ∅ inputs result.2) dummy := by
  rw [referenceFamilyOracleSample_selections key inputs hencoding hgraph result hresult, referenceFamilyWords_selected]
theorem referenceFamilyOracleSample_words_valid (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) :
    ∀ lay tree leaf, OtsCode.Valid (referenceFamilyWords result.1 dummy lay tree leaf) := by
  rw [referenceFamilyOracleSample_words key inputs hencoding hgraph result hresult dummy]
  exact canonicalReferenceWords_valid key (finiteHashAnswer ∅ inputs result.2) dummy hdummy
noncomputable def referenceFamilyFrontierRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  causalFrontierGame key.parameter f key.ftsSecret words (canonicalGraphFrontier key.otsSecret labels words) adversary
theorem referenceFamilyFrontierRest_selected (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceFamilyFrontierRest key f labels (referenceTableSelection key f) dummy adversary =
      graphFrontierGameRest key.parameter key.otsSecret key.ftsSecret labels f dummy adversary := by
  rw [referenceFamilyFrontierRest, referenceFamilyWords_selected, causalFrontierGame_eq, graphFrontierGameRest]
  rfl
noncomputable def referenceFamilyGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceFamilyFrontierRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (reference.1, result)
theorem referenceFamilyGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary = 𝒮[frontierOracleGame inputs dummy adversary] := by
  rw [referenceFamilyGame, frontierOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame, map_bind, map_pure, bind_pure]
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  rw [evalSPMF_bind_comm, evalSPMF_bind]
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  rw [referenceFamilyOracleSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩ inputs
    (hencoding parameter) (hgraph parameter) (fun selections table =>
      referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩ (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary)]
  simp only [referenceFamilyFrontierRest_selected]
theorem evalDist_boundaryGameCore_referenceFamily (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referenceFamilyGame inputs hencoding dummy adversary := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (referenceFamilyGame_erased inputs hencoding hgraph dummy adversary).symm
theorem forgeAdvantage_eq_referenceFamily (dummy : OtsReferenceWords) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr[fun result => result.2.1 = true |
        referenceFamilyGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] := by
  rw [forgeAdvantage, probOutput_def,
    evalDist_gameCore_frontier (canonicalGraphGameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)]
  simp only [evalSPMF_map]
  rw [← referenceFamilyGame_erased (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary,
    ← LawfulFunctor.comp_map]
  change Pr[= true | (Prod.fst ∘ Prod.snd) <$>
    referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _
  rw [probOutput_map]
  rfl
theorem referenceFamilyGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result.2
  apply (mem_support_iff_of_evalSPMF_eq
    (mx' := Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    (evalDist_boundaryGameCore_referenceFamily (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)) result.2).mpr
  rw [support_map]
  exact ⟨result, hresult, rfl⟩
end SphincsSecurity.Concrete
end
