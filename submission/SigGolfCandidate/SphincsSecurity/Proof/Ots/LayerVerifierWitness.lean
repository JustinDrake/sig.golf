import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsVerifierWitness
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.TreeFoldBound
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk canonicalPayloadInputs

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
  (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)

def TreeOutputMatch (trace : Trace) : Prop :=
  ∃ (level nodeIdx : Nat) (payload : HashInput), payload ∈ canonicalPayloadInputs ∧ level < layerHeight lay ∧ nodeIdx < 2 ^ maxLayerHeight ∧
    2 ^ (level + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight ∧
    (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload,
      f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload)) ∈ trace.toList ∧
    NodeHit f parameter lay tree secret level nodeIdx payload

theorem canonicalLeaf_eq_honestNode (leaf : LeafIndex) :
    canonicalLeaf f parameter lay tree leaf (secret leaf) = honestNode f parameter lay tree secret 0 leaf.val := by
  rw [honestNode_zero_eq_leafHash]
  simp only [canonicalLeaf, leafHash, eval_tweakableHash]
  rfl

theorem layer_classification (leaf : LeafIndex) (hleafIndex : leaf.val < 2 ^ layerHeight lay)
    (path : Nat → Digest) (message : EncMessage) (counter : Counter) (values : ChainIndex → Digest)
    (candidate : Encoding) (leafValue : Digest) (trace : Trace) (hvalid : OtsCode.Valid lay (words lay tree leaf))
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some candidate)
    (hots : evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values) = some leafValue)
    (hfold : foldPair f parameter lay tree leaf path leafValue =
      honestPair f parameter lay tree secret)
    (hotsRun : ContainsRun f trace (otsLeafAttempt parameter lay tree leaf message counter values))
    (hfoldRun : ContainsRun f trace (treeFold parameter lay tree leaf path (layerHeight lay - 1) leafValue)) :
    (candidate = words lay tree leaf ∧
      (∀ index, values index = frontier f parameter words lay tree leaf (secret leaf) index) ∧
      ∀ level, level < layerHeight lay → path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) ∨
      TreeOutputMatch f parameter lay tree secret trace ∨ LeafOutputMatch f parameter lay tree leaf (secret leaf) trace ∨
        ChainException f parameter words lay tree leaf (secret leaf) trace := by
  rcases foldPair_extract_all f parameter lay tree secret leaf path hleafIndex (layerHeight_pos lay) leafValue
      hfold with ⟨hleaf, hpath⟩ | ⟨level, hl, hh⟩
  · have hcanonical : evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values) =
        some (canonicalLeaf f parameter lay tree leaf (secret leaf)) := by
      rw [canonicalLeaf_eq_honestNode, hots, hleaf]
    rcases otsLeaf_classification f parameter words lay tree leaf (secret leaf) message counter values candidate trace hvalid hencode hotsRun hcanonical
      with ⟨hword, hvalues⟩ | hleafMatch | hchains
    · exact Or.inl ⟨hword, hvalues, hpath⟩
    · exact Or.inr (Or.inr (Or.inl hleafMatch))
    · exact Or.inr (Or.inr (Or.inr hchains))
  · have hl' : level < layerHeight lay := Nat.lt_of_lt_of_le hl (Nat.sub_le _ _)
    refine Or.inr (Or.inl ⟨level, leaf.val / 2 ^ (level + 1), _, orderedPayload_mem_canonicalPayloadInputs _ _ _, hl', ?_, ?_, ?_, hh⟩)
    · exact (Nat.div_le_self _ _).trans_lt leaf.isLt
    · exact fold_node_bound maxLayerHeight level leaf.val (hl'.trans_le (layerHeight_le lay)) leaf.isLt
    · exact hfoldRun _ (treeFold_query_mem f parameter lay tree leaf path leafValue (layerHeight lay - 1) level hl)

/-- The top tree's last hash on a trace: the verifier's pair is the honest pair, or the trace holds a tree
match at the root. -/
theorem topRoot_classification (index : Index) (top : EncMessage) (trace : Trace)
    (hroot : evalWithAnswerFn f (topRoot parameter index top) =
      honestNode f parameter topLayer rootTree secret (layerHeight topLayer) 0)
    (hrun : ContainsRun f trace (topRoot parameter index top)) :
    top = honestPair f parameter topLayer rootTree secret ∨
      TreeOutputMatch f parameter topLayer rootTree secret trace := by
  rcases topRoot_extract f parameter secret index top hroot with h | h
  · exact Or.inl h
  · refine Or.inr ⟨layerHeight topLayer - 1, 0, _, nodePayload_mem_canonicalPayloadInputs _ _, by decide,
      by decide, by decide, ?_, h⟩
    have hmem : tweakableHashInput parameter (.node topLayer rootTree (layerHeight topLayer - 1 + 1) 0)
        (nodePayload top.1 top.2) ∈ queriedInputs f (topRoot parameter index top) := by
      rw [topRoot, queriedInputs_tweakableHash,
        show treeIndexAt index topLayer = rootTree from Fin.ext (treeIndexAt_topLayer index)]
      exact List.mem_singleton_self _
    exact hrun _ hmem

end SphincsSecurity.Concrete.OtsVerifierWitness
