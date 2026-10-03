import SigGolfCandidate.T3.Secc.LargeResidualRouter

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def coordVal (s : Secrets) (L : Labels) : Coord → Digest
  | .inl M => (L M).extractLsb' 0 128
  | .inr x => s x
def cellValues : CanonGraph.Node → (Coord → Digest) → HashInput
  | .chain p, v => ChainGraph.row p (v (chainChild p))
  | .leaf L, v => pad64 (Extract.leafInput L.lay L.tree.val L.leaf.val
      ((List.range (chainCount L.lay)).map fun i => v (.inl (.chain (endPoint L i)))))
  | .node n, v => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .ftsLeaf f, v => pad64 (ftsLeafInputP f.index.val f.coord.val f.leaf.val 0 (v (.inr (.inr f))) 0)
  | .ftsNode n, v => pad64 (nodeInputP 10 n.1.coord.val n.1.index.val
      (2 ^ (11 - n.1.level.val - 1) + n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .forest index, v => pad64 (Extract.forestInput index.val
      ((List.range 7).map fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))))
theorem treeLabel_eq (s : Secrets) (L : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) :
    treeLabel L lay tree level c = ((treeChild lay tree level c).map (coordVal s L)).getD 0 := by
  unfold treeLabel treeChild
  by_cases h0 : level = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : c < 4096
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]; rfl
  · rw [if_neg h0, if_neg h0]
    cases treeNodeAt lay tree (level - 1) c <;> rfl
theorem ftsLabel_eq (s : Secrets) (L : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) :
    ftsLabel L index coord level c = ((ftsChild index coord level c).map (coordVal s L)).getD 0 := by
  unfold ftsLabel ftsChild
  by_cases h0 : level = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : c < 2048
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]; rfl
  · rw [if_neg h0, if_neg h0]
    cases ftsNodeAt index coord (level - 1) c <;> rfl
theorem width_ge (lay : Layer) (i : Nat) : 2 ≤ width lay i := by
  unfold width; split_ifs <;> norm_num
theorem cell_eq_cellValues (s : Secrets) (L : Labels) (N : CanonGraph.Node) :
    cell s N L = cellValues N (coordVal s L) := by
  cases N with
  | chain p =>
      change ChainGraph.row p (ChainGraph.prior (seedsOf s) p (chainLabels L)) = ChainGraph.row p _
      congr 1
      unfold ChainGraph.prior chainChild
      by_cases h0 : p.2.val = 0
      · rw [if_pos h0, if_pos h0]; rfl
      · rw [if_neg h0, if_neg h0]; rfl
  | leaf Lf =>
      change pad64 (Extract.leafInput _ _ _ ((List.range (chainCount Lf.lay)).map (endLabel s L Lf))) = _
      congr 3
      funext i
      unfold endLabel ChainGraph.value
      have hw := width_ge Lf.lay i
      have h1 : 1 ≤ maxDigit Lf.lay i := by
        unfold maxDigit
        split_ifs <;> decide
      rw [if_neg (by omega)]
      simp only [coordVal, endPoint, chainLabels, Nat.sub_sub]
  | node n =>
      change pad64 (nodeInputP 3 _ _ _ (treeLabel L _ _ _ _) 0 (treeLabel L _ _ _ _)) = _
      rw [treeLabel_eq s, treeLabel_eq s]
      rfl
  | ftsLeaf f => rfl
  | ftsNode n =>
      change pad64 (nodeInputP 10 _ _ _ (ftsLabel L _ _ _ _) 0 (ftsLabel L _ _ _ _)) = _
      rw [ftsLabel_eq s, ftsLabel_eq s]
      rfl
  | forest index =>
      change pad64 (Extract.forestInput _ ((List.range 7).map fun c => ftsLabel L index (fin7 c) 11 0)) = _
      congr 3
theorem coordVal_from (v : Coord → Digest) :
    coordVal (fun x => v (.inr x)) (joinLabels (fun M => v (.inl M)) fun _ => 0) = v := by
  funext c
  cases c with
  | inl M => exact joinLabels_low _ _ M
  | inr x => rfl
theorem cellFrom_eq (N : CanonGraph.Node) (v : Coord → Digest) : cellFrom N v = cellValues N v := by
  unfold cellFrom
  rw [cell_eq_cellValues, coordVal_from]
theorem cellValues_congr (N : CanonGraph.Node) (v v' : Coord → Digest)
    (h : ∀ cs ∈ childSlots N, v cs.1 = v' cs.1) : cellValues N v = cellValues N v' := by
  cases N with
  | chain p =>
      have := h (chainChild p, 3) (by simp [childSlots])
      simp only [cellValues, this]
  | leaf L =>
      simp only [cellValues]
      congr 2
      exact List.map_congr_left (fun i hi => h _ (by simp only [childSlots, List.mem_map]; exact ⟨i, hi, rfl⟩))
  | node n =>
      simp only [cellValues]
      have h1 : ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map v).getD 0 =
          ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)).map v').getD 0 := by
        cases hc : treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val) with
        | none => rfl
        | some c =>
            have := h (c, 0) (by simp [childSlots, hc])
            simp [this]
      have h2 : ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0 =
          ((treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)).map v').getD 0 := by
        cases hc : treeChild n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1) with
        | none => rfl
        | some c =>
            have := h (c, 3) (by simp [childSlots, hc])
            simp [this]
      rw [h1, h2]
  | ftsLeaf f =>
      have := h (.inr (.inr f), 2) (by simp [childSlots])
      simp only [cellValues, this]
  | ftsNode n =>
      simp only [cellValues]
      have h1 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val) with
        | none => rfl
        | some c =>
            have := h (c, 0) (by simp [childSlots, hc])
            simp [this]
      have h2 : ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0 =
          ((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v').getD 0 := by
        cases hc : ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1) with
        | none => rfl
        | some c =>
            have := h (c, 3) (by simp [childSlots, hc])
            simp [this]
      rw [h1, h2]
  | forest index =>
      simp only [cellValues]
      congr 2
      exact List.map_congr_left (fun c hc => h _ (by simp only [childSlots, List.mem_map]; exact ⟨c, hc, rfl⟩))
theorem slotValue_append_left (X Y : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (X ++ Y) k = slotValue X k := by
  unfold slotValue
  congr 1
  rw [List.drop_append_of_le_length (by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]
theorem slotValue_pad64 (X : HashInput) (k : Nat) (hk : 16 * (k + 1) ≤ X.length) :
    slotValue (pad64 X) k = slotValue X k := slotValue_append_left _ _ k hk
theorem slotValue_bytes_cons (x : Digest) (rest : HashInput) : slotValue (bytesLE 16 x ++ rest) 0 = x := by
  unfold slotValue
  simp only [Nat.mul_zero, List.drop_zero]
  rw [List.take_append_of_le_length (by rw [bytesLE_length])]
  rw [List.take_of_length_le (by rw [bytesLE_length])]
  exact Correctness.readDigest_bytesLE x
theorem slotValue_shift (X Y : HashInput) (k : Nat) (hX : X.length = 16) :
    slotValue (X ++ Y) (k + 1) = slotValue Y k := by
  unfold slotValue
  congr 1
  rw [show 16 * (k + 1) = X.length + 16 * k by omega, List.drop_append,
    List.drop_eq_nil_of_le (by omega), List.nil_append]
  simp
theorem slotValue_flatMap (values : List Digest) (rest : HashInput) (j : Nat) (hj : j < values.length) :
    slotValue (values.flatMap (bytesLE 16) ++ rest) j = values.getD j 0 := by
  induction values generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
      rw [List.flatMap_cons, List.append_assoc]
      cases j with
      | zero => exact slotValue_bytes_cons x _
      | succ j =>
          rw [slotValue_shift _ _ j (bytesLE_length _ _)]
          simp only [List.getD_cons_succ]
          exact ih j (by simpa using hj)
theorem slotValue_block4 (a b c d : Digest) :
    slotValue (block4 a b c d) 0 = a ∧ slotValue (block4 a b c d) 2 = c ∧ slotValue (block4 a b c d) 3 = d := by
  have hl : ∀ x : Digest, (bytesLE 16 x).length = 16 := fun x => bytesLE_length 16 x
  unfold block4
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc]; exact slotValue_bytes_cons a _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 1 (hl a), slotValue_shift _ _ 0 (hl b)]
    exact slotValue_bytes_cons c _
  · rw [List.append_assoc, List.append_assoc, slotValue_shift _ _ 2 (hl a), slotValue_shift _ _ 1 (hl b),
      slotValue_shift _ _ 0 (hl c)]
    have := slotValue_bytes_cons d []
    simpa using this
theorem slotValue_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) (i : Nat)
    (hi : i ≤ rest.length) : slotValue (pad64 (Extract.listInput first hdr rest)) (listBlock i) =
      (first :: rest).getD i 0 := by
  have hlen := Extract.listInput_length first hdr rest
  unfold listBlock
  by_cases h0 : i = 0
  · subst h0
    rw [if_pos rfl, slotValue_pad64 _ 0 (by omega)]
    unfold Extract.listInput
    rw [List.append_assoc]
    exact slotValue_bytes_cons first _
  · rw [if_neg h0, slotValue_pad64 _ _ (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    unfold Extract.listInput
    rw [List.append_assoc, show j + 1 + 1 = (j + 1) + 1 from rfl,
      slotValue_shift _ _ (j + 1) (bytesLE_length _ _), slotValue_shift _ _ j (bytesLE_length _ _)]
    simp only [List.getD_cons_succ]
    have := slotValue_flatMap rest [] j (by omega)
    simpa using this
theorem chainRow_block4 (p : ChainGraph.Point) (x : Digest) :
    ChainGraph.row p x = block4 0 (header 1 p.1.layer.val p.1.tree.val (p.2.val + 256 * p.1.chain.val) p.1.leaf.val) 0 x := by
  unfold ChainGraph.row
  rw [chainInput_eq_zero, chainInputP_eq_block4]
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem slot_cellValues (N : CanonGraph.Node) (v : Coord → Digest) :
    ∀ cs ∈ childSlots N, slotValue (cellValues N v) cs.2 = v cs.1 := by
  intro cs hcs
  cases N with
  | chain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      simp only [cellValues, chainRow_block4]
      exact (slotValue_block4 _ _ _ _).2.2
  | leaf L =>
      simp only [childSlots, List.mem_map, List.mem_range] at hcs
      obtain ⟨i, hi, rfl⟩ := hcs
      simp only [cellValues, Extract.leafInput]
      have hl : (List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay))).length =
          chainCount L.lay := by simp
      have hpos : 0 < chainCount L.lay := chainCount_pos L.lay
      rw [show listBlock i = listBlock i from rfl]
      have key := slotValue_listInput
        ((List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay))).getD 0 0)
        (header 2 L.lay.val L.tree.val 0 L.leaf.val)
        ((List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay))).drop 1) i
        (by simp; omega)
      rw [key]
      have hcons : ((List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay))).getD 0 0 ::
          (List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay))).drop 1) =
          List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay)) := by
        cases hm : List.map (fun i => v (.inl (.chain (endPoint L i)))) (List.range (chainCount L.lay)) with
        | nil => rw [hm] at hl; simp at hl; omega
        | cons x xs => rfl
      rw [hcons]
      simp [List.getD_eq_getElem, hi]
  | node n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      simp only [cellValues, pad64_nodeInputP, nodeInputP, pad64_block4]
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
  | ftsLeaf f =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      simp only [cellValues, pad64_ftsLeafInputP, ftsLeafInputP, pad64_block4]
      refine ((slotValue_block4 0 _ _ 0).2.1).trans ?_
      rfl
  | ftsNode n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      simp only [cellValues, pad64_nodeInputP, nodeInputP, pad64_block4]
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
  | forest index =>
      simp only [childSlots, List.mem_map, List.mem_range] at hcs
      obtain ⟨c, hc, rfl⟩ := hcs
      simp only [cellValues, Extract.forestInput]
      have key := slotValue_listInput
        ((List.map (fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))) (List.range 7)).getD 0 0)
        (header 11 0 index.val 0 0)
        ((List.map (fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))) (List.range 7)).drop 1) c
        (by simp; omega)
      rw [key]
      have hcons : ((List.map (fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))) (List.range 7)).getD 0 0 ::
          (List.map (fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))) (List.range 7)).drop 1) =
          List.map (fun c => v (.inl (.ftsNode (ftsRootNode index (fin7 c))))) (List.range 7) := rfl
      rw [hcons]
      simp [List.getD_eq_getElem, hc]
end SigGolfCandidate.T3.Security.LargeResidual
