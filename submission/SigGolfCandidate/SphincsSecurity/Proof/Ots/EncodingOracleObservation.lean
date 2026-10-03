import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingOracleSplit
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierSigningOracleCongruence
import SigGolfCandidate.SphincsSecurity.Proof.Reference.CausalFrontierProgram
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixAllocation
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingTablePrior
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservationErasure

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs frontierTreeNode referenceEncodingSearch boundaryEval publicDigestLoop
def AgreeOutsideEncoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id) : Prop :=
  ∀ input, input ∉ canonicalEncodingInputs parameter → f input = g input
theorem AgreeOutsideEncoding.domain {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
    (h : AgreeOutsideEncoding parameter f g) (domain : HashDomain)
    (htag : (hashDomainFields domain).tag ≠ 4#8) (payload : HashInput) :
    f (tweakableHashInput parameter domain payload) = g (tweakableHashInput parameter domain payload) := by
  apply h
  intro hinput
  rw [canonicalEncodingInputs] at hinput
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hinput
  obtain ⟨position, pair, heq⟩ := hinput
  exact htag (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain
    (.encoding position.lay position.tree position.leafIdx) payload _ heq.symm)
namespace AgreeOutsideEncoding
variable {parameter : PublicParameter} {f g : QueryImpl HashSpec Id}
  (h : AgreeOutsideEncoding parameter f g)
include h
theorem frontierTreeNode (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) =
      evalWithAnswerFn g (Concrete.frontierTreeNode parameter lay tree words frontier level nodeIdx) := by
  apply eval_frontierTreeNode_congr
  · intro leaf chainIdx step _ input
    exact congrArg truncateHash (h.domain (.chain lay tree leaf chainIdx step) (by simp only [hashDomainFields, tweakFields]; decide) (digestBytes input))
  · intro leaf payload
    exact congrArg truncateHash (h.domain (.leaf lay tree leaf) (by simp only [hashDomainFields, tweakFields]; decide) payload)
  · intro level nodeIdx payload
    exact congrArg truncateHash (h.domain (.node lay tree level nodeIdx) (by simp only [hashDomainFields, tweakFields]; decide) payload)
theorem frontierTreePath (lay : Layer) (tree : TreeIndex) (words : LeafIndex → Encoding)
    (frontier : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    evalWithAnswerFn f (Concrete.frontierTreePath parameter lay tree words frontier leaf) =
      evalWithAnswerFn g (Concrete.frontierTreePath parameter lay tree words frontier leaf) := by
  simp only [Concrete.frontierTreePath, evalWithAnswerFn_sequenceFin]
  funext level
  split_ifs
  · exact h.frontierTreeNode _ _ _ _ _ _
  · rfl
theorem ftsNode (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    evalWithAnswerFn f (Concrete.ftsNode parameter index tree secret level nodeIdx) =
      evalWithAnswerFn g (Concrete.ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [ftsNode_zero_eq, ftsLeafHash, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsLeaf index tree _) (by simp only [hashDomainFields, tweakFields]; decide) _)
  | succ level ih =>
      simp only [ftsNode_succ_eq, evalWithAnswerFn_bind, ih, eval_tweakableHash]
      exact congrArg truncateHash (h.domain (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx)) (by simp only [hashDomainFields, tweakFields]; decide) _)
theorem ftsOpen (index : Index) (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (Concrete.ftsOpen parameter index leaves secret) =
      evalWithAnswerFn g (Concrete.ftsOpen parameter index leaves secret) := by
  rw [eval_ftsOpen, eval_ftsOpen]
  exact congrArg (honestFts leaves (secret porsTree)) (funext fun level => funext fun nodeIdx =>
    h.ftsNode _ _ _ _ _)
theorem publicDigestLoop (root : Digest) (message : Message) (attempts : Nat) :
    fixedBoundaryRun parameter f (Concrete.publicDigestLoop parameter root message attempts) =
      fixedBoundaryRun parameter g (Concrete.publicDigestLoop parameter root message attempts) := by
  have hattempt (randomness : Randomness) :
      boundaryEval parameter f (publicSignAttempt parameter root message randomness) =
        boundaryEval parameter g (publicSignAttempt parameter root message randomness) := by
    have hinput := h.domain .message (by simp only [hashDomainFields, tweakFields]; decide) (messageDigestPayload root message randomness)
    simp [publicSignAttempt, messageDigest, oracleHash, boundaryEval, QueryImpl.withTrace_apply, hinput]
  induction attempts with
  | zero => simp only [Concrete.publicDigestLoop, fixedBoundaryRun_pure]
  | succ attempts ih =>
      rw [Concrete.publicDigestLoop]
      apply fixedBoundaryRun_bind_congr
      · exact fixedBoundaryRun_lift_prob_eq parameter f g sampleRandomness
      · intro randomness
        apply fixedBoundaryRun_bind_congr
        · rw [fixedBoundaryRun_lift_hash, fixedBoundaryRun_lift_hash, hattempt]
        · intro attempt
          cases attempt with
          | none => exact ih
          | some selected => rfl
theorem frontierSignLayer (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer)
    (hsearch : frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    Concrete.frontierSignLayer parameter f ftsSecret words frontier index lay =
      Concrete.frontierSignLayer parameter g ftsSecret words frontier index lay := by
  simp only [Concrete.frontierSignLayer, hsearch, h.frontierTreePath]
theorem frontierSignAfterDigest (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Concrete.frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves =
      Concrete.frontierSignAfterDigest parameter g ftsSecret words frontier randomness index leaves := by
  simp only [Concrete.frontierSignAfterDigest, h.frontierSignLayer ftsSecret words frontier _ _ (hsearch _ _),
    h.ftsOpen]
theorem frontierSigningRun (root : Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) (message : Message) :
    Concrete.frontierSigningRun parameter root f ftsSecret words frontier message =
      Concrete.frontierSigningRun parameter root g ftsSecret words frontier message := by
  simp only [Concrete.frontierSigningRun, frontierSigningRecord, h.publicDigestLoop,
    h.frontierSignAfterDigest ftsSecret words frontier hsearch]
theorem frontierRoot (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    Concrete.frontierRoot parameter f words frontier = Concrete.frontierRoot parameter g words frontier :=
  h.frontierTreeNode _ _ _ _ _ _
end AgreeOutsideEncoding
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs frontierSigningRun frontierRoot
theorem joinEncodingTable_agrees_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (left right : canonicalEncodingInputs parameter → HashOutput)
    (outside : NonencodingRows parameter inputs hencoding) :
    AgreeOutsideEncoding parameter
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding left outside))
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding right outside)) := by
  intro input hnot
  by_cases hin : input ∈ inputs
  · rw [finiteHashAnswer_none ∅ inputs _ _ hin (by simp), finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    let cell : UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) :=
      ⟨⟨input, hin⟩, UniformTableSplit.inclusion_not_range hencoding ⟨input, hin⟩ hnot⟩
    exact (UniformTableSplit.join_outside _ _ left outside cell).trans
      (UniformTableSplit.join_outside _ _ right outside cell).symm
  · simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]
theorem frontierLayerSearch_eq_referenceSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (selections : ReferenceFamily)
    (hselected : referenceTableSelection key f = selections) (index : Index) (lay : Layer) :
    frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay =
      referenceSelectionResult (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) := by
  rw [frontierLayerSearch, eval_frontierLayerMessage key f words frontier hfrontier,
    ← canonicalEncodingSearch_at,
    ← referenceSelectionResult_eq_search key f ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩, hselected]
namespace CausalFrontierProgram
theorem game_eq_of_encoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) (h : AgreeOutsideEncoding parameter f g)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    game parameter f ftsSecret words frontier adversary = game parameter g ftsSecret words frontier adversary := by
  have hsign (root : Digest) (message : Message) :
      frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message =
        frontierSigningRun parameter root (maskOtsPrefixes parameter words g) ftsSecret words frontier message := by
    rw [← frontierSigningRun_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
      ← frontierSigningRun_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g)]
    exact h.frontierSigningRun root ftsSecret words frontier hsearch message
  have himpl (root : Digest) : adversaryImpl parameter root f ftsSecret words frontier =
      adversaryImpl parameter root g ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message => simp only [adversaryImpl_signing, hsign]
  rw [game, game,
    ← frontierRoot_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
    ← frontierRoot_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g),
    h.frontierRoot words frontier]
  simp only [gameRest, adversaryRun, himpl]
end CausalFrontierProgram
theorem joinedEncoding_isSigningFrontier (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (words : OtsReferenceWords) :
    IsSigningFrontier key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      words (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
        (nonencodingAnswer key.parameter inputs hencoding outside)) words) := by
  have hfrontier := canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) words key.root key.top
  rw [canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph] at hfrontier
  rw [hfrontier]
  exact isSigningFrontier_canonical key _ words
theorem joinedEncoding_program_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (left right : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (hleft : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside)) = selections)
    (hright : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside))
        key.ftsSecret words frontier adversary =
      CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside))
        key.ftsSecret words frontier adversary := by
  dsimp only
  apply CausalFrontierProgram.game_eq_of_encoding
  · exact joinEncodingTable_agrees_outside _ _ _ _ _ _
  · intro index lay
    rw [frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph left outside _) selections hleft,
      frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph right outside _) selections hright]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
noncomputable def referenceRecordedRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain) :=
  let words := referenceFamilyWords selections dummy
  simulateQ (fixedHashWorld f) (QueryCap.recorded (CausalFrontierProgram.game key.parameter f key.ftsSecret words
    (canonicalGraphFrontier key.otsSecret labels words) adversary))
theorem referenceRecordedRest_erased (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.fst <$> referenceRecordedRest key f labels selections dummy adversary =
      referenceFamilyFrontierRest key f labels selections dummy adversary := by
  rw [referenceRecordedRest, ← simulateQ_map, QueryCap.recorded_forget, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]
abbrev ReferenceRecordedResult := PublicParameter × ReferenceFamily × ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
def ReferenceRecordedResult.erase (result : ReferenceRecordedResult) : ReferenceFamily × (Bool × SigningBoundaryTrace) :=
  (result.2.1, result.2.2.1)
noncomputable def referenceRecordedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF ReferenceRecordedResult := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceRecordedRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (parameter, reference.1, result)
theorem referenceRecordedGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.erase <$> referenceRecordedGame inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceRecordedGame referenceFamilyGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.erase]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceRecordedRest_erased, evalSPMF_map, bind_map_left]
theorem referenceRecordedGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) : result.2.2.1.2.hashCalls ≤ q := by
  apply referenceFamilyGame_hashCalls_le dummy adversary q hbound result.erase
  rw [← referenceRecordedGame_erased, support_map]
  exact ⟨result, hresult, rfl⟩
end SphincsSecurity.Concrete
end

section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs
abbrev FrontierObserver (Result : Type) := PublicParameter → OtsReferenceWords → OtsFrontierValues →
  OracleComp OracleWorld (Bool × SigningBoundaryTrace) → OracleComp OracleWorld Result
noncomputable def referenceInstrumentedRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  simulateQ (fixedHashWorld oracle) (observer key.parameter words frontier
    (CausalFrontierProgram.game key.parameter oracle key.ftsSecret words frontier adversary))
abbrev InstrumentedResult (Result : Type) := PublicParameter × ReferenceFamily × Result
noncomputable def referenceInstrumentedGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒮[sampleParameter]
  let otsSecret ← 𝒮[sampleOtsSecrets]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret, fun _ _ => 0⟩
  let reference ← 𝒮[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let oracle := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒮[referenceInstrumentedRest observer key oracle
    (canonicalGraphLabels parameter otsSecret ftsSecret oracle) reference.1 dummy adversary]
  pure (parameter, reference.1, result)
theorem referenceInstrumentedRest_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    erase <$> referenceInstrumentedRest observer key oracle labels selections dummy adversary =
      referenceFamilyFrontierRest key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, ← simulateQ_map, herase, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]
theorem referenceInstrumentedGame_erased {Result : Type} (observer : FrontierObserver Result)
    (erase : Result → Bool × SigningBoundaryTrace)
    (herase : ∀ parameter words frontier computation, erase <$> observer parameter words frontier computation = computation)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => (result.2.1, erase result.2.2)) <$> referenceInstrumentedGame observer inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceInstrumentedGame referenceFamilyGame
  simp only [map_bind, map_pure]
  apply congrArg (𝒮[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒮[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒮[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒮[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceInstrumentedRest_erased observer erase herase, evalSPMF_map, bind_map_left]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
noncomputable def referenceEncodingRepresentative (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily) :
    canonicalEncodingInputs key.parameter → HashOutput :=
  if h : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections
  then Classical.choose h else fun _ => 0
theorem referenceEncodingRepresentative_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections) :
    referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) = selections := by
  have hex : ∃ encoding, referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections :=
    ⟨encoding, hselected⟩
  rw [referenceEncodingRepresentative, dif_pos hex]
  exact Classical.choose_spec hex
noncomputable def referenceEncodingProgram (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  CausalFrontierProgram.game key.parameter
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (referenceEncodingRepresentative key inputs hencoding outside selections) outside)) key.ftsSecret words frontier adversary
theorem referenceEncodingProgram_selected (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
        key.ftsSecret words frontier adversary =
      referenceEncodingProgram key inputs hencoding outside selections dummy adversary :=
  joinedEncoding_program_eq key inputs hencoding hgraph encoding _ outside selections hselected
    (referenceEncodingRepresentative_selected key inputs hencoding outside selections encoding hselected) dummy adversary
noncomputable def referenceEncodingRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Result :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)))
    (observer key.parameter words frontier (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))
theorem referenceEncodingRest_selected {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (hselected : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let oracle := finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)
    referenceInstrumentedRest observer key oracle (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle)
        selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary := by
  dsimp only
  rw [referenceInstrumentedRest, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  rw [referenceEncodingProgram_selected key inputs hencoding hgraph outside selections encoding hselected]
  rfl
theorem referenceEncodingRest_table {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (selections : ReferenceFamily)
    (table : inputs → HashOutput) (hselected : referenceTableSelection key (finiteHashAnswer ∅ inputs table) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceInstrumentedRest observer key (finiteHashAnswer ∅ inputs table)
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs table)) selections dummy adversary =
      referenceEncodingRest observer key inputs hencoding (fun cell => table cell.val) selections
        (table ∘ encodingInputCell key.parameter inputs hencoding) dummy adversary := by
  have hjoin : joinEncodingTable key.parameter inputs hencoding (table ∘ encodingInputCell key.parameter inputs hencoding)
      (fun cell => table cell.val) = table := UniformTableSplit.join_split _ _ table
  have hs : referenceTableSelection key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding
      (table ∘ encodingInputCell key.parameter inputs hencoding) (fun cell => table cell.val))) = selections := by
    rw [hjoin]
    exact hselected
  have h := referenceEncodingRest_selected observer key inputs hencoding hgraph (fun cell => table cell.val) selections
    (table ∘ encodingInputCell key.parameter inputs hencoding) hs dummy adversary
  simpa only [hjoin] using h
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ
abbrev World (parameter : PublicParameter) :=
  OracleWorld + UniformTableObservation.TableSpec (canonicalEncodingInputs parameter) HashOutput
noncomputable def translate (parameter : PublicParameter) : QueryImpl OracleWorld (OracleComp (World parameter))
  | .inl input => liftM ((World parameter).query (.inl (.inl input)))
  | .inr input =>
      if h : input ∈ canonicalEncodingInputs parameter then liftM ((World parameter).query (.inr ⟨input, h⟩))
      else liftM ((World parameter).query (.inl (.inr input)))
noncomputable def auxiliary (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld SPMF := fun input => 𝒮[fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input]
theorem fixed_translate (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (input : OracleWorld.Domain) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding) (translate parameter input) =
      𝒮[fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside)) input] := by
  cases input with
  | inl input =>
      simp only [translate, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld]
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · have hrow : finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside) input = encoding ⟨input, hc⟩ := by
          rw [finiteHashAnswer_none ∅ inputs _ _ (hencoding hc) (by simp)]
          exact UniformTableSplit.join_embed (encodingInputCell parameter inputs hencoding)
            (encodingInputCell_injective parameter inputs hencoding) encoding outside ⟨input, hc⟩
        simp only [translate, dif_pos hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, fixedHashWorld,
          evalSPMF_pure, hrow]
      · have hrow := joinEncodingTable_agrees_outside parameter inputs hencoding encoding (fun _ => 0) outside input hc
        simp only [translate, dif_neg hc, simulateQ_spec_query, UniformTableObservation.fixedImpl, auxiliary, fixedHashWorld,
          evalSPMF_pure, hrow, nonencodingAnswer]
theorem fixed_run {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (computation : OracleComp OracleWorld Result) :
    simulateQ (UniformTableObservation.fixedImpl (auxiliary parameter inputs hencoding outside) encoding)
        (simulateQ (translate parameter) computation) =
      𝒮[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih, fixed_translate]
noncomputable def lazyRun {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    SPMF (Result × (canonicalEncodingInputs parameter → Finset HashOutput)) :=
  UniformTableObservation.lazyRun (auxiliary parameter inputs hencoding outside) (simulateQ (translate parameter) computation) allowed
theorem lazyRun_original {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ cell, (allowed cell).Nonempty) :
    (complete allowed >>= fun encoding =>
      𝒮[simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside))) computation]) =
        Prod.fst <$> lazyRun parameter inputs hencoding outside computation allowed := by
  have h := UniformTableObservation.run_marginal (auxiliary parameter inputs hencoding outside)
    (simulateQ (translate parameter) computation) allowed ha
  simpa only [fixed_run, lazyRun] using h
end SphincsSecurity.Concrete.EncodingObservation
end
