import SigGolfCandidate.SphincsSecurity.Proof.Ots.LayerVerifierWitness
import SigGolfCandidate.SphincsSecurity.Proof.Ots.PublicEncodingMatch
import SigGolfCandidate.SphincsSecurity.Proof.Ots.PaddedChain
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
  (messages : EncodingPosition → EncMessage) (selections : ReferenceFamily)

def EncodingOutputMatch (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, entry.1 ∈ canonicalEncodingInputs parameter ∧ PublicEncodingMatch.Match parameter messages words selections entry.1 entry.2

theorem equal_word_reference (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : EncMessage) (counter : Counter) (values : ChainIndex → Digest) (trace : Trace)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some (words lay tree leaf))
    (hrun : ContainsRun f trace (otsLeafAttempt parameter lay tree leaf message counter values)) :
    (∃ selected, selections ⟨lay, tree, leaf⟩ = some selected ∧ message = messages ⟨lay, tree, leaf⟩ ∧
      counter = BitVec.ofNat counterBits selected.1.val) ∨ EncodingOutputMatch parameter words messages selections trace := by
  let position : EncodingPosition := ⟨lay, tree, leaf⟩
  let input := tweakableHashInput message.1 position.domain (digestBytes message.2 ++ counterBytes counter)
  by_cases hreference : PublicEncodingMatch.referenceInput parameter messages selections position = some input
  · cases hselected : selections position with
    | none => simp only [PublicEncodingMatch.referenceInput, hselected, Option.map_none, reduceCtorEq] at hreference
    | some selected =>
        have hinput : encodingRetryInput parameter position (messages position) selected.1.val = input := by
          simpa only [PublicEncodingMatch.referenceInput, hselected, Option.map_some, Option.some.injEq] using hreference
        obtain ⟨_, hfirst, hpayload⟩ := tweakableHashInput_injective' (by trivial) (by trivial) hinput
        obtain ⟨hm, hc⟩ := List.append_inj hpayload (by simp [digestBytes_length])
        exact Or.inl ⟨selected, rfl, (Prod.ext hfirst (digestBytes_injective hm)).symm,
          (bytesLE_injective hc).symm⟩
  · refine Or.inr ⟨(input, f input), ?_, ?_, position, ⟨_, _, rfl⟩, hreference, ?_⟩
    · apply hrun.bind_left
      simp only [encodeAttempt, queriedInputs_bind, queriedInputs_oracleHash, queriedInputs_pure,
        List.append_nil, List.mem_singleton, input, position, EncodingPosition.domain]
    · have hcounter : counter.toNat < 2 ^ counterBits := counter.isLt
      have hin := encodingRetryInput_mem_canonicalEncodingInputs_wide parameter position message ⟨counter.toNat, hcounter⟩
      simpa only [encodingRetryInput, BitVec.ofNat_toNat, BitVec.setWidth_eq, input] using hin
    · exact decode_of_eval_encode_eq_some f parameter lay tree leaf message counter (words lay tree leaf) hencode

theorem layer_reference_classification (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (leaf : LeafIndex) (hleafIndex : leaf.val < 2 ^ layerHeight lay) (path : Nat → Digest)
    (message : EncMessage) (counter : Counter) (values : ChainIndex → Digest) (candidate : Encoding) (leafValue : Digest) (trace : Trace)
    (hvalid : OtsCode.Valid lay (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some candidate)
    (hots : evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values) = some leafValue)
    (hfold : foldPair f parameter lay tree leaf path leafValue =
      honestPair f parameter lay tree secret)
    (hotsRun : ContainsRun f trace (otsLeafAttempt parameter lay tree leaf message counter values))
    (hfoldRun : ContainsRun f trace (treeFold parameter lay tree leaf path (layerHeight lay - 1) leafValue)) :
    (∃ selected, selections ⟨lay, tree, leaf⟩ = some selected ∧ message = messages ⟨lay, tree, leaf⟩ ∧
      counter = BitVec.ofNat counterBits selected.1.val ∧ candidate = words lay tree leaf ∧
      (∀ index, values index = frontier f parameter words lay tree leaf (secret leaf) index) ∧
      ∀ level, level < layerHeight lay → path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) ∨
      TreeOutputMatch f parameter lay tree secret trace ∨ LeafOutputMatch f parameter lay tree leaf (secret leaf) trace ∨
        ChainException f parameter words lay tree leaf (secret leaf) trace ∨ EncodingOutputMatch parameter words messages selections trace := by
  rcases layer_classification f parameter words lay tree secret leaf hleafIndex path message counter values candidate leafValue trace
      hvalid hencode hots hfold hotsRun hfoldRun with ⟨hword, hvalues, hpath⟩ | ht | hl | hc
  · rw [hword] at hencode
    rcases equal_word_reference f parameter words messages selections lay tree leaf message counter values trace hencode hotsRun
      with ⟨selected, hs, hm, hc⟩ | he
    · exact Or.inl ⟨selected, hs, hm, hc, hword, hvalues, hpath⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr (Or.inl hl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))

attribute [local irreducible] canonicalPayloadInputs

/-- **The new primitive event.** At a leaf, a traced padded query at the last chain step
(`pad ≠ 0`, 48-byte payload) whose answer is the honest endpoint of its chain. It is the verifier's
only new way to reach an honest value; it is priced as a structural (OtherHash) match. -/
def PaddedChainMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (trace : Trace) : Prop :=
  ∃ (chainIdx : ChainIndex) (pad : Pad) (previous : Digest), pad ≠ 0 ∧
    (tweakableHashInput parameter (.chain lay tree leaf chainIdx Position.lastChainStep) (chainPayload pad previous),
      f (tweakableHashInput parameter (.chain lay tree leaf chainIdx Position.lastChainStep)
        (chainPayload pad previous))) ∈ trace.toList ∧
    truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx Position.lastChainStep)
        (chainPayload pad previous))) =
      honestChain f parameter lay tree leaf chainIdx (secret chainIdx) (Position.lastChainStep.val + 1)

theorem containsRun_otsLeafAttempt_of_inactive (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : EncMessage) (counter : Counter)
    (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding) (trace : Trace)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (hinactive : PadsInactive pads codeword)
    (hrun : ContainsRun f trace (otsLeafAttemptP parameter lay tree leaf message counter values pads)) :
    ContainsRun f trace (otsLeafAttempt parameter lay tree leaf message counter values) := by
  intro input hinput
  apply hrun
  rw [(otsLeafAttemptP_run_eq_of_inactive f parameter lay tree leaf message counter values pads codeword
    hencode hinactive).2]
  exact hinput

/-- **Per-layer classification, small route** (`layer_reference_classification` with pads). Inactive
pads reduce to the record lemma verbatim; an active padded chain gives a tree match, a leaf match, or
the new `PaddedChainMatch`. -/
theorem layer_reference_classificationP (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (words : OtsReferenceWords) (messages : EncodingPosition → EncMessage) (selections : ReferenceFamily)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (leaf : LeafIndex) (hleafIndex : leaf.val < 2 ^ layerHeight lay) (path : Nat → Digest)
    (message : EncMessage) (counter : Counter) (values : ChainIndex → Digest) (pads : ChainIndex → Pad)
    (candidate : Encoding) (leafValue : Digest) (trace : Trace)
    (hvalid : OtsCode.Valid lay (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some candidate)
    (hots : evalWithAnswerFn f (otsLeafAttemptP parameter lay tree leaf message counter values pads) =
      some leafValue)
    (hfold : foldPair f parameter lay tree leaf path leafValue =
      honestPair f parameter lay tree secret)
    (hotsRun : ContainsRun f trace (otsLeafAttemptP parameter lay tree leaf message counter values pads))
    (hfoldRun : ContainsRun f trace (treeFold parameter lay tree leaf path (layerHeight lay - 1) leafValue)) :
    (PadsInactive pads candidate ∧
      ∃ selected, selections ⟨lay, tree, leaf⟩ = some selected ∧ message = messages ⟨lay, tree, leaf⟩ ∧
        counter = BitVec.ofNat counterBits selected.1.val ∧ candidate = words lay tree leaf ∧
        (∀ index, values index = frontier f parameter words lay tree leaf (secret leaf) index) ∧
        ∀ level, level < layerHeight lay →
          path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) ∨
      TreeOutputMatch f parameter lay tree secret trace ∨
      LeafOutputMatch f parameter lay tree leaf (secret leaf) trace ∨
      ChainException f parameter words lay tree leaf (secret leaf) trace ∨
      EncodingOutputMatch parameter words messages selections trace ∨
      PaddedChainMatch f parameter lay tree leaf (secret leaf) trace := by
  by_cases hinactive : PadsInactive pads candidate
  · have heval := (otsLeafAttemptP_run_eq_of_inactive f parameter lay tree leaf message counter values pads
      candidate hencode hinactive).1
    have hrun := containsRun_otsLeafAttempt_of_inactive f parameter lay tree leaf message counter values pads
      candidate trace hencode hinactive hotsRun
    rcases layer_reference_classification f parameter words messages selections lay tree secret leaf hleafIndex
        path message counter values candidate leafValue trace hvalid hencode (heval ▸ hots) hfold hrun hfoldRun
      with h | h | h | h | h
    · exact Or.inl ⟨hinactive, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨chainIdx, hpad, hdigit⟩ := exists_active_of_not_inactive hinactive
    rcases foldPair_extract_all f parameter lay tree secret leaf path hleafIndex (layerHeight_pos lay)
        leafValue hfold with ⟨hleaf, _⟩ | ⟨level, hl, hh⟩
    · have heval := eval_otsLeafAttemptP f parameter lay tree leaf message counter values pads candidate hencode
      rw [hots, hleaf] at heval
      have hvalue := (Option.some.inj heval).symm
      by_cases hp : (leafPayload fun index => evalWithAnswerFn f (recoverChainP parameter lay tree leaf index
            (pads index) (candidate index) (values index))) =
          leafPayload (fun index => honestChain f parameter lay tree leaf index (secret leaf index) (chainLength - 1))
      · have hend := congrFun (leafPayload_injective hp) chainIdx
        obtain ⟨previous, hmem, -, hhit⟩ := recoverChainP_active_hit f parameter lay tree leaf chainIdx
          (pads chainIdx) (secret leaf chainIdx) (candidate chainIdx) (values chainIdx) hpad hdigit hend
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨chainIdx, pads chainIdx, previous, hpad,
          hotsRun _ (otsLeafP_chain_query_mem f parameter lay tree leaf message counter values pads candidate
            hencode chainIdx hmem), hhit⟩))))
      · refine Or.inr (Or.inr (Or.inl ⟨_, leafPayload_mem_canonicalPayloadInputs _, hp,
          hotsRun _ (otsLeafP_leaf_query_mem f parameter lay tree leaf message counter values pads candidate
            hencode), ?_⟩))
        rw [hvalue, canonicalLeaf_eq_honestNode]
    · have hl' : level < layerHeight lay := Nat.lt_of_lt_of_le hl (Nat.sub_le _ _)
      refine Or.inr (Or.inl ⟨level, leaf.val / 2 ^ (level + 1), _, orderedPayload_mem_canonicalPayloadInputs _ _ _,
        hl', ?_, ?_, ?_, hh⟩)
      · exact (Nat.div_le_self _ _).trans_lt leaf.isLt
      · exact fold_node_bound maxLayerHeight level leaf.val (hl'.trans_le (layerHeight_le lay)) leaf.isLt
      · exact hfoldRun _ (treeFold_query_mem f parameter lay tree leaf path leafValue (layerHeight lay - 1) level hl)

end SphincsSecurity.Concrete.OtsVerifierWitness
