import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeResidualRouter
import SigGolfCandidate.T3.Secc.LargeCouplingCell
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layers
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.Secc.LargeCouplingSign

section


namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue slotValue_pad64 slotValue_block4
  chainRow_block4 slotValue_listInput width_ge chainCount_pos)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
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
  | .wctChain p, v => WCT9.chainInput p.1.1.val p.1.2.1.val p.1.2.2.1.val p.1.2.2.2.val p.2.val
      (v (wctItem p.1 p.2.val))
  | .wctLeaf L, v => pad64 (Extract.wctLeafInput L.index.val L.coord.val L.child.val
      (List.ofFn fun t : Fin 7 => v (wctItem (L.index, L.coord, L.child, t) 3)))
  | .wctNode n, v => pad64 (nodeInputP 11 n.1.coord.val n.1.index.val
      (2 ^ (7 - n.1.level.val - 1) + n.1.idx.val)
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)).map v).getD 0) 0
      (((ftsChild n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)).map v).getD 0))
  | .forest index, v => pad64 (Extract.forestInput index.val
      ((List.range 9).map fun c => v (.inl (.wctNode (ftsRootNode index (fin9 c))))))
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
theorem ftsLabel_eq (s : Secrets) (L : Labels) (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) :
    ftsLabel L index coord level c = ((ftsChild index coord level c).map (coordVal s L)).getD 0 := by
  unfold ftsLabel ftsChild
  by_cases h0 : level = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hc : c < 128
    · rw [dif_pos hc, dif_pos hc]; rfl
    · rw [dif_neg hc, dif_neg hc]; rfl
  · rw [if_neg h0, if_neg h0]
    cases ftsNodeAt index coord (level - 1) c <;> rfl
theorem coordVal_wctItem (s : Secrets) (L : Labels) (a : WctAddr) (p : Nat) :
    coordVal s L (wctItem a p) = wctValueL s L a p := by
  unfold wctItem wctValueL
  by_cases h0 : p = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]; rfl
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
      simp only [coordVal, endPoint, chainLabels]
  | node n =>
      change pad64 (nodeInputP 3 _ _ _ (treeLabel L _ _ _ _) 0 (treeLabel L _ _ _ _)) = _
      rw [treeLabel_eq s, treeLabel_eq s]
      rfl
  | wctChain p =>
      change WCT9.chainInput _ _ _ _ _ (wctValueL s L p.1 p.2.val) = _
      rw [← coordVal_wctItem]
      rfl
  | wctLeaf Lf =>
      change pad64 (Extract.wctLeafInput _ _ _
        (List.ofFn fun t : Fin 7 => wctEndLabel L (Lf.index, Lf.coord, Lf.child, t))) = _
      simp only [cellValues, coordVal_wctItem, wctValueL_three]
  | wctNode n =>
      change pad64 (nodeInputP 11 _ _ _ (ftsLabel L _ _ _ _) 0 (ftsLabel L _ _ _ _)) = _
      rw [ftsLabel_eq s, ftsLabel_eq s]
      rfl
  | forest index =>
      change pad64 (Extract.forestInput _ ((List.range 9).map fun c => ftsLabel L index (fin9 c) 7 0)) =
        pad64 (Extract.forestInput _ ((List.range 9).map fun c =>
          coordVal s L (.inl (.wctNode (ftsRootNode index (fin9 c))))))
      congr 2
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
  | wctChain p =>
      have := h (wctItem p.1 p.2.val, 3) (by simp [childSlots])
      simp only [cellValues, this]
  | wctLeaf L =>
      have hfg : (fun t : Fin 7 => v (wctItem (L.index, L.coord, L.child, t) 3)) =
          fun t : Fin 7 => v' (wctItem (L.index, L.coord, L.child, t) 3) := by
        funext t
        exact h (wctItem (L.index, L.coord, L.child, t) 3, listBlock t.val) (by
          simp only [childSlots]
          exact List.mem_ofFn.mpr ⟨t, rfl⟩)
      simp only [cellValues]
      rw [hfg]
  | wctNode n =>
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
theorem slotValue_listOf (hdr : BitVec 128) (values : List Digest) (i : Nat) (hi : i < values.length) :
    slotValue (pad64 (Extract.listInput (values.getD 0 0) hdr (values.drop 1))) (listBlock i) =
      values.getD i 0 := by
  have key := slotValue_listInput (values.getD 0 0) hdr (values.drop 1) i (by simp; omega)
  have hcons : values.getD 0 0 :: values.drop 1 = values := by
    cases values with
    | nil => simp at hi
    | cons x xs => rfl
  rw [hcons] at key
  exact key
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
      rw [slotValue_listOf _ _ _ (by simpa using hi)]
      simp [hi]
  | node n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      simp only [cellValues, nodeInputP, pad64_block4]
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
  | wctChain p =>
      simp only [childSlots, List.mem_singleton] at hcs
      subst hcs
      simp only [cellValues, Extract.wctChainInput_block4]
      exact (slotValue_block4 _ _ _ _).2.2
  | wctLeaf L =>
      simp only [childSlots] at hcs
      obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hcs
      simp only [cellValues, Extract.wctLeafInput]
      rw [slotValue_listOf _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  | wctNode n =>
      simp only [childSlots, List.mem_append, Option.mem_toList, Option.map_eq_some_iff] at hcs
      simp only [cellValues, nodeInputP, pad64_block4]
      rcases hcs with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
      · refine ((slotValue_block4 _ _ _ _).1).trans ?_
        rw [hc]; rfl
      · refine ((slotValue_block4 _ _ _ _).2.2).trans ?_
        rw [hc]; rfl
  | forest index =>
      simp only [childSlots, List.mem_map, List.mem_range] at hcs
      obtain ⟨c, hc, rfl⟩ := hcs
      simp only [cellValues, Extract.forestInput]
      rw [slotValue_listOf _ _ _ (by simp; omega)]
      simp [hc]
end ClaudeWCT.W9.T3.Security.LargeResidual
end

section





namespace ClaudeWCT.W9.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafValue honestPieces)
open SigGolfCandidate.T3.Security.LargeResidual (listBlock slotValue digestIndex routeAddr filterMap_map_getD)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.keygen ClaudeWCT.WCT9.heapBuild
noncomputable local instance instDecidableEqCache_w9largeCouplingSign : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Honest
variable {T : Answers} {labels : Labels}
theorem honestValue_eq (h : Agrees T labels) : honestValue T = coordVal (secretsOf T) labels := by
  funext c
  cases c with
  | inl M =>
      change (T (.inl (.inr (Extract.honestInput T M.toPos)))).extractLsb' 0 128 = _
      rw [honest_answer h M]
      rfl
  | inr x => rfl
theorem ftsChild_isSome (index : Fin (2^31)) (coord : Fin 9) (level c : Nat) (hl : level ≤ 7)
    (hc : c < 2 ^ (7 - level)) : (ftsChild index coord level c).isSome := by
  unfold ftsChild
  by_cases h0 : level = 0
  · subst h0
    rw [if_pos rfl, dif_pos (by simpa using hc)]
    rfl
  · rw [if_neg h0]
    unfold ftsNodeAt
    rw [dif_pos ⟨by omega, by
      have : 7 - (level - 1) - 1 = 7 - level := by omega
      rw [this]; exact hc⟩]
    rfl
theorem treeChild_isSome (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hl : level ≤ height lay)
    (hc : c < 2 ^ (height lay - level)) (hlt : level < height lay ∨ c < 4096) :
    (treeChild lay tree level c).isSome := by
  unfold treeChild
  by_cases h0 : level = 0
  · subst h0
    have h4096 : c < 4096 := by
      have := Extract.height_le lay
      calc c < 2 ^ (height lay - 0) := hc
        _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 4096 := by norm_num
    rw [if_pos rfl, dif_pos h4096]
    rfl
  · rw [if_neg h0]
    unfold treeNodeAt
    rw [dif_pos ⟨by omega, by
      have : height lay - (level - 1) - 1 = height lay - level := by omega
      rw [this]; exact hc⟩]
    rfl
theorem path_bound (N : HashOutput) (k : Fin 9) (l : Nat) (hl : l < 7) :
    (WCT9.child N k).val / 2 ^ l ^^^ 1 < 2 ^ (7 - l) := by
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 7 - l + l = 7 by omega]
    exact (WCT9.child N k).isLt
  · exact Nat.one_lt_two_pow (by omega)
theorem wctPath_map (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) (v : Coord → Digest) :
    (wctPath index k N).map v = (List.range 7).map fun l =>
      ((ftsChild index k l ((WCT9.child N k).val / 2 ^ l ^^^ 1)).map v).getD 0 := by
  unfold wctPath
  exact filterMap_map_getD _ _ _ 0 (fun l hl => ftsChild_isSome _ _ _ _
    (by have := List.mem_range.mp hl; omega) (path_bound N k l (List.mem_range.mp hl)))
theorem openingValue_eq (h : Agrees T labels) (index : Fin (2^31)) (N : HashOutput) (k : Fin 9) (t : Fin 7) :
    (WCT9.expectedOpening T index.val N k).values t =
      honestValue T (wctItem (index, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)) := by
  rw [honestValue_eq h, coordVal_wctItem,
    ← wctValue_eq h (index, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t) (Nat.sub_le _ _)]
  simp only [WCT9.expectedOpening, WCT9.honestOpening]
  rw [WCT9.buildCoordinate_result]
  simp only
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact t.isLt), List.getElem_ofFn]
  rfl
theorem openingPath_eq (h : Agrees T labels) (index : Fin (2^31)) (N : HashOutput) (k : Fin 9) (l : Fin 7) :
    (WCT9.expectedOpening T index.val N k).path l = ((wctPath index k N).map (honestValue T)).getD l.val 0 := by
  have hb := path_bound N k l.val l.isLt
  rw [wctPath_map]
  simp only [WCT9.expectedOpening, WCT9.honestOpening]
  rw [WCT9.buildCoordinate_result]
  rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  have hx := ftsTree_eq h index k l.val ((WCT9.child N k).val / 2 ^ l.val ^^^ 1) (by omega) hb
  rw [ftsLabel_eq (secretsOf T), ← honestValue_eq h] at hx
  exact hx
theorem wctOpened_eq (h : Agrees T labels) (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) :
    List.ofFn (WCT9.expectedOpening T index.val N k).values = (wctOpened index k N).map (honestValue T) := by
  unfold wctOpened
  rw [List.map_ofFn]
  congr 1
  funext t
  exact openingValue_eq h index N k t
theorem wctPath_eq (h : Agrees T labels) (index : Fin (2^31)) (k : Fin 9) (N : HashOutput) :
    List.ofFn (WCT9.expectedOpening T index.val N k).path = (wctPath index k N).map (honestValue T) := by
  have hlen : ((wctPath index k N).map (honestValue T)).length = 7 := by
    rw [wctPath_map]; simp
  apply List.ext_getElem (by rw [hlen]; simp)
  intro l h1 h2
  rw [List.getElem_ofFn, openingPath_eq h index N k ⟨l, by simpa using h1⟩, List.getD_eq_getElem _ _ h2]
theorem expectedOpening_eq (h : Agrees T labels) (index : Fin (2^31)) (N : HashOutput) (k : Fin 9) :
    WCT9.expectedOpening T index.val N k =
      ⟨fun t => honestValue T (wctItem (index, k, WCT9.child N k, t) (3 - WCT9.digit (WCT9.rank N k) t)),
        fun l => ((wctPath index k N).map (honestValue T)).getD l.val 0⟩ := by
  have hv := funext (openingValue_eq h index N k)
  have hp := funext (openingPath_eq h index N k)
  rw [← hv, ← hp]
end Honest
section Layers
variable {T : Answers} {labels : Labels}
theorem chainItem_value (h : Agrees T labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hd : digits.getD i 0 ≤ 7) :
    leafValue T L.lay L.tree.val L.leaf.val digits i = honestValue T (chainItem L i (digits.getD i 0)) := by
  rw [leafValue_eq h L digits i hi hd, honestValue_eq h]
  unfold chainItem ChainGraph.value
  by_cases h0 : digits.getD i 0 = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]; rfl
theorem honestPieces_eq (h : Agrees T labels) (index : Fin (2^31)) (lay : Layer) :
    honestPieces T lay (route index.val lay).2 (route index.val lay).1 (Wots.referenceDigits T (routeAddr index.val lay)) =
      ((layerChains (Wots.referenceDigits T) index lay).map (honestValue T), (layerPath index lay).map (honestValue T)) := by
  have htree := route_tree_lt index.val index.isLt lay
  have ht31 : (route index.val lay).2 < 2 ^ 31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hleaf := route_leaf_bound index.val lay
  have hl4096 : (route index.val lay).1 < 4096 := lt_of_lt_of_le hleaf (by
    calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      _ = 4096 := by norm_num)
  unfold honestPieces layerChains layerPath
  rw [dif_pos ⟨ht31, hl4096⟩, dif_pos ht31]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
    have hd : (Wots.referenceDigits T (routeAddr index.val lay)).getD i 0 ≤ 7 := by
      have hle : (Wots.referenceDigits T (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
        WotsExtract.depth_le T ⟨routeAddr index.val lay, i⟩ hi
      have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
      omega
    exact chainItem_value h ⟨lay, ⟨_, ht31⟩, ⟨_, hl4096⟩⟩ _ i hi58 hd
  · have hc : ∀ j ∈ List.range (height lay),
        (route index.val lay).1 / 2 ^ j ^^^ 1 < 2 ^ (height lay - j) := by
      intro j hj
      rw [List.mem_range] at hj
      apply Nat.xor_lt_two_pow
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show height lay - j + j = height lay by omega]
        exact hleaf
      · exact Nat.one_lt_two_pow (by omega)
    rw [filterMap_map_getD _ _ _ 0 (fun j hj => treeChild_isSome _ _ _ _
      (by have := List.mem_range.mp hj; omega) (hc j hj) (Or.inl (List.mem_range.mp hj)))]
    apply List.map_congr_left
    intro j hj
    rw [builtTree_eq h lay ⟨_, ht31⟩ j _ (by have := List.mem_range.mp hj; omega) (hc j hj),
      treeLabel_eq (secretsOf T), honestValue_eq h]
noncomputable def layerPieces (T : Answers) (index : Nat) (lay : Layer) : Pieces :=
  honestPieces T lay (route index lay).2 (route index lay).1 (Wots.referenceDigits T (routeAddr index lay))
theorem referenceSearch_route (T : Answers) (index : Nat) (lay : Layer) :
    Wots.referenceSearch T (routeAddr index lay) =
      evalWithAnswerFn T (counterSearch lay (route index lay).2 (route index lay).1
        (Extract.honestMsg T index lay) 0 counterLimit) := by
  have hmsg : Wots.leafMsg T (routeAddr index lay) = Extract.honestMsg T index lay := by
    unfold Wots.leafMsg Extract.honestMsg
    simp only [routeAddr]
    by_cases h : lay.val < 3
    · rw [dif_pos h, dif_pos h, WotsExtract.route_tree_succ index lay h]
    · rw [dif_neg h, dif_neg h, WotsExtract.route_forest index lay h]
  unfold Wots.referenceSearch
  rw [hmsg]
  rfl
theorem referenceDigits_some (T : Answers) (L : Wots.LeafAddr) (c : BitVec 32) (digits : List Nat)
    (h : Wots.referenceSearch T L = some (c, digits)) : Wots.referenceDigits T L = digits := by
  unfold Wots.referenceDigits
  rw [h]
  rfl
theorem signLayers_eq (T : Answers) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = Correctness.cacheRegion (Correctness.maskedTop T))
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → evalWithAnswerFn T (signLayers cache index n (Extract.walkTarget T index n)) =
      if ∀ l, l < n → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome then
        some ((List.range n).map fun l => layerPieces T index (Fin.ofNat 4 l))
      else none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [signLayers]
  | succ n ih =>
      intro hn
      have hlay : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      have hmsg : Extract.walkTarget T index (n + 1) = Extract.honestMsg T index (Fin.ofNat 4 n) := by
        have hl : (⟨n, by omega⟩ : Layer) = Fin.ofNat 4 n := Fin.ext hlay.symm
        simp only [Extract.walkTarget, dif_pos (show n < 4 by omega), hl]
      rw [hmsg]
      simp only [signLayers, evalWithAnswerFn_bind]
      rw [← referenceSearch_route]
      cases hs : Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 n)) with
      | none =>
          simp only [evalWithAnswerFn_pure]
          rw [if_neg (fun hall => by have := hall n (by omega); rw [hs] at this; cases this)]
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hdig := referenceDigits_some T _ counter digits hs
          have hdec : decode (Fin.ofNat 4 n) _ = some digits := WotsExtract.referenceSearch_decode T _ hs
          have hvalid := Cost.validDigits_decode hdec
          simp only
          by_cases hn0 : n = 0
          · subst hn0
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
            have hl0 : (Fin.ofNat 4 0 : Layer) = 0 := rfl
            rw [hl0] at hvalid hdig hs ⊢
            have htop := route_top_tree index hindex
            rw [Correctness.eval_signTop_honest T cache _ digits hcache (by
              have := route_leaf_bound index 0
              calc (route index 0).1 < 2 ^ height 0 := this
                _ = 4096 := by decide) hvalid]
            rw [if_pos (fun l hl => by
              have : l = 0 := by omega
              subst this; rw [hl0, hs]; rfl)]
            rw [Nat.zero_add, List.range_one, List.map_singleton]
            unfold layerPieces
            rw [hl0, hdig, htop]
          · simp only [hn0, if_false, evalWithAnswerFn_bind]
            rw [Correctness.eval_buildTree_result T _ _ _ digits hvalid (route_leaf_bound index _)]
            simp only
            have hroot : ((builtTree T (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                (height (Fin.ofNat 4 n)) []).getD 0 0 = Extract.walkTarget T index n := by
              rw [Extract.walkTarget_root T index n (by omega)]
              rfl
            rw [hroot, ih (by omega)]
            by_cases hall : ∀ l, l < n → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome
            · rw [if_pos hall, if_pos (fun l hl => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
                · exact hall l hl
                · rw [hs]; rfl)]
              simp only [evalWithAnswerFn_pure, Option.some.injEq, List.range_succ, List.map_append,
                List.map_cons, List.map_nil]
              congr 2
              unfold layerPieces honestPieces
              rw [hdig]
              rfl
            · rw [if_neg hall, if_neg (fun h' => hall fun l hl => h' l (by omega))]
              simp only [evalWithAnswerFn_pure]
end Layers
section Payload
theorem walkTarget_four (T : Answers) (index : Nat) :
    Extract.walkTarget T index 4 = WCT9.honestForest T index := by
  have h4 : Extract.walkTarget T index 4 = Extract.honestForest T index := by
    simp only [Extract.walkTarget, dif_pos (show 3 < 4 by decide), Extract.honestMsg]
    rfl
  rw [h4, Extract.honestForest_eq_recover]
  rfl
theorem routeOk_iff (T : Answers) (index : Nat) :
    (∀ l, l < 4 → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome) ↔ RouteOk T index := by
  constructor
  · intro hall lay
    have := hall lay.val lay.isLt
    rwa [show (Fin.ofNat 4 lay.val : Layer) = lay from Fin.ext (by simp)] at this
  · intro hok l _
    exact hok _
theorem signPayload_disclosed {T : Answers} {labels : Labels} (h : Agrees T labels) (cache : SigGolfCandidate.T3.Cache)
    (hcache : cache.region = Correctness.cacheRegion (Correctness.maskedTop T)) (m : Message) :
    evalWithAnswerFn T (signPayload cache m) =
      match signDigest T m with
      | none => none
      | some (_, N) =>
          if RouteOk T (N.toNat % 2 ^ 31) then
            some (assembleSig (evalWithAnswerFn T (privateNonce m)) N (honestValue T) (Wots.referenceDigits T))
          else none := by
  rw [show signPayload cache m = WCT9.Rev3.signPayload cache m from rfl, WCT9.Rev3.signPayload_eq]
  simp only [evalWithAnswerFn_bind]
  unfold signDigest
  cases hd : evalWithAnswerFn T (WCT9.digestSearch (evalWithAnswerFn T (privateNonce m)) m 0
      WCT9.digestAttemptLimit) with
  | none => rfl
  | some found =>
      obtain ⟨counter, N⟩ := found
      simp only [evalWithAnswerFn_bind]
      rw [WCT9.eval_signForest]
      simp only
      rw [← walkTarget_four, signLayers_eq T cache hcache _ (Nat.mod_lt _ (by positivity)) 4 le_rfl]
      by_cases hok : RouteOk T (N.toNat % 2 ^ 31)
      · rw [if_pos ((routeOk_iff T _).mpr hok), if_pos hok]
        simp only [evalWithAnswerFn_pure]
        unfold WCT9.assembledSignature assembleSig
        simp only [digestIndex]
        congr 2
        · funext k
          rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact k.isLt), List.getElem_ofFn]
          exact expectedOpening_eq h ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩ N k
        · funext lay
          congr 1
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by have := lay.isLt; omega),
            Option.map_some, Option.getD_some,
            show (Fin.ofNat 4 lay.val : Layer) = lay from Fin.ext (by simp)]
          exact honestPieces_eq h ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩ lay
      · rw [if_neg (fun h' => hok ((routeOk_iff T _).mp h')), if_neg hok]
        rfl
theorem authenticatedSign_disclosed {T : Answers} {labels : Labels} (h : Agrees T labels)
    (published : SigGolfCandidate.T3.Cache)
    (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    (request : SigGolfCandidate.T3.Security.Request) :
    evalWithAnswerFn T (FullGame.authenticatedSign published request) =
      if request.cache = published then
        match signDigest T request.message with
        | none => none
        | some (_, N) =>
            if RouteOk T (N.toNat % 2 ^ 31) then
              some (assembleSig (evalWithAnswerFn T (privateNonce request.message)) N (honestValue T)
                (Wots.referenceDigits T))
            else none
      else none := by
  unfold FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  split_ifs with h1
  · rw [h1]
    exact signPayload_disclosed h published hpub request.message
  · rfl
end Payload
end ClaudeWCT.W9.T3.Security.LargeResidual
end
