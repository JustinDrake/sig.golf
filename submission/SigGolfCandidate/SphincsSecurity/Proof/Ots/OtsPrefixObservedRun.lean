import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceFamilyConditioning
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixOracle
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixFrontier
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixSimulation
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainErasure

section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false
namespace UniformTableSplit
theorem uniform_outside {Index Cell Answer : Type} [Fintype Index] [Fintype Cell] [Fintype Answer]
    [Nonempty Answer] [DecidableEq Index] [DecidableEq Cell]
    (embed : Index → Cell) (hinj : Function.Injective embed) :
    (PMF.uniformOfFintype (Cell → Answer)).map (fun table => fun cell : Outside embed => table cell.val) =
      PMF.uniformOfFintype (Outside embed → Answer) := by
  rw [uniform_join embed hinj, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, join_outside, PMF.bind_const]
  exact PMF.map_id _
end UniformTableSplit
structure ReferenceFamilySeed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) where
  selections : ReferenceFamily
  nonencoding : NonencodingRows parameter inputs hencoding
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs parameter → HashOutput
noncomputable def referenceFamilySeedLawAt (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (PMF.uniformOfFintype (NonencodingRows parameter inputs hencoding)).bind (fun nonencoding =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
      (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs parameter → HashOutput)).map
        (fun encoding => ⟨selections, nonencoding, selectedRows, encoding⟩)))
noncomputable def referenceFamilySeedLaw (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) : PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
    (referenceFamilySeedLawAt parameter inputs hencoding)
noncomputable def referenceFamilySeedTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (seed : ReferenceFamilySeed key.parameter inputs hencoding) : inputs → HashOutput :=
  referenceFamilyOracleTable key inputs hencoding seed.nonencoding seed.selectedRows
    (fun cell => seed.encoding cell.val)
theorem referenceFamilyOracleSample_eq_seed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) :
    referenceFamilyOracleSample key inputs hencoding =
      (referenceFamilySeedLaw key.parameter inputs hencoding).map
        (fun seed => (seed.selections, referenceFamilySeedTable key inputs hencoding seed)) := by
  rw [referenceFamilyOracleSample, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [referenceFamilySeedLawAt, PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext nonencoding
  rw [PMF.map_bind]
  apply congrArg (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
  funext selectedRows
  rw [← UniformTableSplit.uniform_outside
    (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding nonencoding))
    (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding nonencoding))]
  simp only [PMF.map_comp, Function.comp_def, referenceFamilySeedTable]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalPayloadInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
theorem input_mem_graph (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∈ canonicalGraphInputs segment.parameter := by
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨[query.2].flatMap digestBytes, flatMap_mem_canonicalPayloadInputs _ (by change 1 ≤ numChains; decide), ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, input, Position.domain]
theorem input_not_encoding (segment : OtsPrefix) (query : segment.Query) :
    segment.input query ∉ canonicalEncodingInputs segment.parameter := by
  intro h
  rw [canonicalEncodingInputs] at h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at h
  obtain ⟨position, pair, heq⟩ := h
  have hencoding : AtEncodingPosition segment.parameter (segment.input query) position := ⟨_, heq.symm⟩
  exact hencoding.not_atPosition
    (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1)) ⟨digestBytes query.2, rfl⟩
noncomputable def nonencodingCell (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (query : segment.Query) :
    UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
  ⟨⟨segment.input query, hgraph (segment.input_mem_graph query)⟩,
    UniformTableSplit.inclusion_not_range hencoding _ (segment.input_not_encoding query)⟩
theorem nonencodingCell_injective (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    Function.Injective (segment.nonencodingCell inputs hencoding hgraph) := by
  intro left right heq
  exact segment.input_injective (congrArg (fun cell => cell.val.val) heq)
noncomputable def splitRows (segment : OtsPrefix) :
    (segment.Query → HashOutput) ≃ (Fin segment.digit.val → Digest → Digest) × (segment.Query → High) where
  toFun rows := (fun level input => truncateHash (rows (level, input)), fun query => (splitHashOutput digestBits (rows query)).2)
  invFun pair query := combine (pair.1 query.1 query.2) (pair.2 query)
  left_inv rows := funext fun query => combine_split (rows query)
  right_inv pair := Prod.ext
    (funext fun level => funext fun input => truncate_combine (pair.1 level input) (pair.2 (level, input)))
    (funext fun query => congrArg Prod.snd (split_combine (pair.1 query.1 query.2) (pair.2 query)))
theorem uniform_rows (segment : OtsPrefix) :
    PMF.uniformOfFintype (segment.Query → HashOutput) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).map (fun high => fun query => combine (tables query.1 query.2) (high query))) := by
  have h := PMF.uniformOfFintype_map_of_bijective segment.splitRows.symm segment.splitRows.symm.bijective
  rw [UniformTableSplit.uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, splitRows, Equiv.coe_fn_symm_mk] using h.symm
abbrev RemainingRows (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :=
  UniformTableSplit.Outside (segment.nonencodingCell inputs hencoding hgraph) → HashOutput
noncomputable def joinNonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : NonencodingRows segment.parameter inputs hencoding :=
  UniformTableSplit.join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph)
    (fun query => combine (tables query.1 query.2) (high query)) remaining
theorem joinNonencoding_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.joinNonencoding inputs hencoding hgraph tables high remaining
        (segment.nonencodingCell inputs hencoding hgraph query) = combine (tables query.1 query.2) (high query) :=
  UniformTableSplit.join_embed _ _ _ _ _
theorem uniform_nonencoding (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) :
    PMF.uniformOfFintype (NonencodingRows segment.parameter inputs hencoding) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
          (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).map
            (segment.joinNonencoding inputs hencoding hgraph tables high))) := by
  rw [UniformTableSplit.uniform_join (segment.nonencodingCell inputs hencoding hgraph)
    (segment.nonencodingCell_injective inputs hencoding hgraph), segment.uniform_rows]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl
end SphincsSecurity.Concrete.OtsPrefix
end

section

namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
noncomputable def rawAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  finiteHashAnswer ∅ inputs (joinEncodingTable segment.parameter inputs hencoding encoding
    (segment.joinNonencoding inputs hencoding hgraph tables high remaining))
noncomputable def auxiliaryAnswer (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (remaining : segment.RemainingRows inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.rawAnswer inputs hencoding hgraph encoding (fun _ _ => 0) (fun _ => 0) remaining
theorem rawAnswer_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (query : segment.Query) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining (segment.input query) =
      combine (tables query.1 query.2) (high query) := by
  rw [rawAnswer, finiteHashAnswer_none ∅ inputs _ _ (hgraph (segment.input_mem_graph query)) (by simp)]
  exact (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
    (encodingInputCell_injective segment.parameter inputs hencoding) encoding _
    (segment.nonencodingCell inputs hencoding hgraph query)).trans
    (segment.joinNonencoding_prefix inputs hencoding hgraph tables high remaining query)
theorem rawAnswer_other (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (first second : Fin segment.digit.val → Digest → Digest) (firstHigh secondHigh : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) (bytes : HashInput) (hparse : segment.parse bytes = none) :
    segment.rawAnswer inputs hencoding hgraph encoding first firstHigh remaining bytes =
      segment.rawAnswer inputs hencoding hgraph encoding second secondHigh remaining bytes := by
  by_cases hin : bytes ∈ inputs
  · rw [rawAnswer, rawAnswer, finiteHashAnswer_none ∅ inputs _ _ hin (by simp),
      finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    by_cases henc : bytes ∈ canonicalEncodingInputs segment.parameter
    · exact (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
        (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).trans
        (UniformTableSplit.join_embed (encodingInputCell segment.parameter inputs hencoding)
          (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ ⟨bytes, henc⟩).symm
    · let cell : UniformTableSplit.Outside (encodingInputCell segment.parameter inputs hencoding) :=
        ⟨⟨bytes, hin⟩, UniformTableSplit.inclusion_not_range hencoding _ henc⟩
      have hcell : cell ∉ Set.range (segment.nonencodingCell inputs hencoding hgraph) := by
        rintro ⟨query, heq⟩
        have hbytes : segment.input query = bytes := congrArg (fun value => value.val.val) heq
        have hsome := (segment.parse_some_iff bytes query).mpr hbytes.symm
        rw [hparse] at hsome
        cases hsome
      calc
        _ = segment.joinNonencoding inputs hencoding hgraph first firstHigh remaining cell :=
          UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell
        _ = remaining ⟨cell, hcell⟩ :=
          UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩
        _ = segment.joinNonencoding inputs hencoding hgraph second secondHigh remaining cell :=
          (UniformTableSplit.join_outside (segment.nonencodingCell inputs hencoding hgraph)
            (segment.nonencodingCell_injective inputs hencoding hgraph) _ remaining ⟨cell, hcell⟩).symm
        _ = _ :=
          (UniformTableSplit.join_outside (encodingInputCell segment.parameter inputs hencoding)
            (encodingInputCell_injective segment.parameter inputs hencoding) encoding _ cell).symm
  · simp only [rawAnswer, finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]
theorem rawAnswer_eq (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs segment.parameter → HashOutput)
    (tables : Fin segment.digit.val → Digest → Digest) (high : segment.Query → High)
    (remaining : segment.RemainingRows inputs hencoding hgraph) :
    segment.rawAnswer inputs hencoding hgraph encoding tables high remaining =
      segment.answer tables high (segment.auxiliaryAnswer inputs hencoding hgraph encoding remaining) := by
  funext bytes
  cases hparse : segment.parse bytes with
  | none =>
      rw [answer, hparse]
      exact segment.rawAnswer_other inputs hencoding hgraph encoding _ _ _ _ remaining bytes hparse
  | some query =>
      rw [(segment.parse_some_iff bytes query).mp hparse, rawAnswer_prefix, answer_input]
end SphincsSecurity.Concrete.OtsPrefix
end

section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false
namespace OtsPrefix
structure ReferenceAuxSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) where
  high : segment.Query → High
  remaining : segment.RemainingRows inputs hencoding hgraph
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs segment.parameter → HashOutput
noncomputable def referenceAuxSeedLaw (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (segment.ReferenceAuxSeed inputs hencoding hgraph) :=
  (PMF.uniformOfFintype (segment.Query → High)).bind (fun high =>
    (PMF.uniformOfFintype (segment.RemainingRows inputs hencoding hgraph)).bind (fun remaining =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
        (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs segment.parameter → HashOutput)).map
          (fun encoding => ⟨high, remaining, selectedRows, encoding⟩))))
noncomputable def referenceSeed (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily)
    (tables : Fin segment.digit.val → Digest → Digest) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) :
    ReferenceFamilySeed segment.parameter inputs hencoding :=
  ⟨selections, segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining,
    auxiliary.selectedRows, auxiliary.encoding⟩
theorem referenceFamilySeedLawAt_eq_prefix (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs) (selections : ReferenceFamily) :
    referenceFamilySeedLawAt segment.parameter inputs hencoding selections =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map
          (segment.referenceSeed inputs hencoding hgraph selections tables)) := by
  rw [referenceFamilySeedLawAt, segment.uniform_nonencoding inputs hencoding hgraph]
  simp only [PMF.bind_bind, PMF.bind_map, referenceAuxSeedLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl
end OtsPrefix
theorem referenceFamilyOracleSample_eq_prefixSeed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (digit : ReferenceFamily → Digit) :
    referenceFamilyOracleSample key inputs hencoding =
      (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
        let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩
        (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
          (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).map (fun auxiliary =>
            (selections, referenceFamilySeedTable key inputs hencoding
              (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))))) := by
  rw [referenceFamilyOracleSample_eq_seed, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [OtsPrefix.referenceFamilySeedLawAt_eq_prefix
    ⟨key.parameter, lay, tree, leaf, chainIdx, digit selections⟩ inputs hencoding hgraph selections]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, OtsPrefix.referenceSeed]
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
noncomputable def encodingFromMessages (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (seed : canonicalEncodingInputs parameter → HashOutput) : canonicalEncodingInputs parameter → HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (Function.uncurry rows) (fun cell => seed cell.val)
noncomputable def seedBaseOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph (fun _ => 0) auxiliary.remaining
noncomputable def seedFrontier (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint : Digest) : OtsFrontierValues :=
  segment.frontierFromEndpoint (segment.seedBaseOracle inputs hencoding hgraph auxiliary) secrets words endpoint
noncomputable def seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : EncodingPosition → Digest :=
  fun position => evalWithAnswerFn (segment.seedBaseOracle inputs hencoding hgraph auxiliary)
    (frontierLayerMessage segment.parameter ftsSecret words
      (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint)
      (referenceIndex position.lay position.tree position.leafIdx) position.lay)
noncomputable def seedEncoding (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : canonicalEncodingInputs segment.parameter → HashOutput :=
  encodingFromMessages segment.parameter (segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    auxiliary.selectedRows auxiliary.encoding
noncomputable def seedOracle (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) : QueryImpl HashSpec Id :=
  segment.auxiliaryAnswer inputs hencoding hgraph
    (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint) auxiliary.remaining
theorem seedFrontier_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedFrontier inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) words endpoint =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint :=
  segment.frontierFromEndpoint_replaceSecret _ secrets words endpoint replacement
theorem seedMessages_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedMessages inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  funext position
  simp only [seedMessages, seedFrontier_replaceSecret]
theorem seedOracle_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) :
    segment.seedOracle inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint =
      segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint := by
  simp only [seedOracle, seedEncoding, seedMessages_replaceSecret]
theorem outsideGraphMessage_eq_seedMessages (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) =
      segment.seedMessages inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  funext position
  change canonicalGraphMessage (canonicalGraphLabels segment.parameter secrets ftsSecret
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining)) position = _
  rw [rawAnswer_eq]
  exact segment.graphMessage_answer tables auxiliary.high _ root top secrets ftsSecret words hword position
theorem referenceSeedTable_eq_raw (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary) =
      joinEncodingTable segment.parameter inputs hencoding
        (segment.seedEncoding inputs hencoding hgraph auxiliary secrets ftsSecret words
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)))
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) := by
  change joinEncodingTable segment.parameter inputs hencoding
    (encodingFromMessages segment.parameter
      (outsideGraphMessage ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
        (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining))
      auxiliary.selectedRows auxiliary.encoding)
    (segment.joinNonencoding inputs hencoding hgraph tables auxiliary.high auxiliary.remaining) = _
  rw [segment.outsideGraphMessage_eq_seedMessages inputs hencoding hgraph auxiliary root top secrets ftsSecret words hword tables]
  rfl
theorem referenceSeedOracle_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)) =
      segment.answer tables auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx))) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root top secrets ftsSecret selections words hword tables]
  exact segment.rawAnswer_eq inputs hencoding hgraph _ tables auxiliary.high auxiliary.remaining
theorem referenceSeedFrontier_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (words : OtsReferenceWords)
    (hword : words segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) :
    canonicalGraphFrontier secrets (canonicalGraphLabels segment.parameter secrets ftsSecret
      (finiteHashAnswer ∅ inputs
        (referenceFamilySeedTable ⟨segment.parameter, root, secrets, ftsSecret, top⟩ inputs hencoding
          (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary)))) words =
      segment.seedFrontier inputs hencoding hgraph auxiliary secrets words
        (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) := by
  rw [segment.referenceSeedTable_eq_raw inputs hencoding hgraph auxiliary root top secrets ftsSecret selections words hword tables,
    canonicalGraphLabels_joinEncodingTable segment.parameter secrets ftsSecret inputs hencoding hgraph,
    canonicalGraphLabels_frontier segment.parameter secrets ftsSecret _ words root top]
  change canonicalFrontierValues ⟨segment.parameter, root, secrets, ftsSecret, top⟩
    (segment.rawAnswer inputs hencoding hgraph (fun _ => 0) tables auxiliary.high auxiliary.remaining) words = _
  rw [rawAnswer_eq, segment.canonicalFrontierValues_answer tables auxiliary.high _ root top secrets ftsSecret words hword]
  rfl
end SphincsSecurity.Concrete.OtsPrefix
end

section



namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
  (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
noncomputable def seedGame (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint : Digest) (adversary : Adversary) : OracleComp segment.World (Bool × SigningBoundaryTrace) :=
  segment.game auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary
theorem seedGame_replaceSecret (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (endpoint replacement : Digest) (adversary : Adversary) :
    segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets replacement) ftsSecret words endpoint adversary =
      segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [seedGame, seedGame, seedOracle_replaceSecret, seedFrontier_replaceSecret]
theorem referenceSeedGame_eq (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (top : Nat → Nat → Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (hword : referenceFamilyWords selections dummy segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) (adversary : Adversary) :
    let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret, top⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    referenceFamilyFrontierRest key oracle (canonicalGraphLabels segment.parameter secrets ftsSecret oracle) selections dummy adversary =
      simulateQ (segment.fixedImpl tables)
        (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets 0) ftsSecret
          (referenceFamilyWords selections dummy)
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) adversary) := by
  dsimp only
  rw [seedGame_replaceSecret, seedGame,
    segment.fixedImpl_game tables auxiliary.high _ ftsSecret (referenceFamilyWords selections dummy) (by rw [hword])]
  rw [referenceFamilyFrontierRest, causalFrontierGame_eq,
    segment.referenceSeedFrontier_eq inputs hencoding hgraph auxiliary root top secrets ftsSecret selections _ hword tables,
    segment.referenceSeedOracle_eq inputs hencoding hgraph auxiliary root top secrets ftsSecret selections _ hword tables]
end SphincsSecurity.Concrete.OtsPrefix
end

section


namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
noncomputable def uniformImpl : QueryImpl unifSpec PMF :=
  fun input => PMF.uniformOfFintype (Fin (input + 1))
theorem fixedImpl_evalDist (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Result : Type} (computation : OracleComp segment.World Result) :
    𝒮[simulateQ (PartialChainEndpoint.fixedImpl uniformImpl tables) computation] =
      𝒮[simulateQ (segment.fixedImpl tables) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalSPMF_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalSPMF_bind, ih]
      cases input with
      | inl input =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inl,
            uniformImpl]
          change (𝒮[PMF.uniformOfFintype (Fin (input + 1))] >>= fun answer =>
            𝒮[simulateQ (segment.fixedImpl tables) (next answer)]) =
            (𝒮[(liftM (unifSpec.query input) : ProbComp (Fin (input + 1)))] >>= fun answer =>
              𝒮[simulateQ (segment.fixedImpl tables) (next answer)])
          rw [evalSPMF_query]
      | inr query =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inr,
            ← PMF.monad_pure_eq_pure, evalSPMF_pure]
theorem realRun_empty_forget (segment : OtsPrefix) {Result : Type}
    (computation : Digest → OracleComp segment.World Result) :
    𝒮[(PartialChainEndpoint.realRun (fun _ => uniformImpl) computation (fun _ _ => none)).map
      (fun result => result.2.1)] = (do
        let tables ← 𝒮[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
        let secret ← 𝒮[PMF.uniformOfFintype Digest]
        𝒮[simulateQ (segment.fixedImpl tables) (computation (PartialChainEndpoint.evaluate tables secret))] : SPMF Result) := by
  rw [PartialChainEndpoint.realRun_empty_forget]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, segment.fixedImpl_evalDist]
noncomputable def seedObservedRun (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) :
    PMF (Digest × ((Bool × SigningBoundaryTrace) × (Fin segment.digit.val → Digest → Option Digest))) :=
  PartialChainEndpoint.realRun (fun _ => uniformImpl)
    (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
    (fun _ _ => none)
end SphincsSecurity.Concrete.OtsPrefix
end
