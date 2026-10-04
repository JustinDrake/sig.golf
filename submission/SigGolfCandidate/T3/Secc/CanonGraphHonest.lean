import SigGolfCandidate.T3.Secc.CanonGraph

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot leafValue)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
  SigGolfCandidate.T3.buildLevels Correctness.builtTree Correctness.ftsRows
def ftsSecretNat (answers : Answers) (index coord leaf : Nat) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 coord index 0 (leaf / 2))
  if leaf % 2 = 0 then pair.1 else pair.2
theorem eval_ftsRows_secrets (answers : Answers) (index coord : Nat) :
    (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.length = 2048 ∧
      ∀ leaf, leaf < 2048 →
        (evalWithAnswerFn answers (Correctness.ftsRows index coord)).2.getD leaf 0 =
          ftsSecretNat answers index coord leaf := by
  unfold Correctness.ftsRows
  refine Correctness.eval_foldlM_range_inv answers 1024 _
    (fun pairs (rows : List Digest × List Digest) => rows.2.length = 2 * pairs ∧
      ∀ leaf, leaf < 2 * pairs → rows.2.getD leaf 0 = ftsSecretNat answers index coord leaf)
    ([], []) ⟨rfl, fun leaf h => by omega⟩ (fun pair _ rows hrows => ?_)
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  obtain ⟨hlen, hget⟩ := hrows
  refine ⟨by simp [hlen]; omega, ?_⟩
  intro leaf hleaf
  by_cases hold : leaf < 2 * pair
  · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hold)]
    exact hget leaf hold
  · rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen]
    have he : leaf = 2 * pair ∨ leaf = 2 * pair + 1 := by omega
    rcases he with rfl | rfl
    · simp only [Nat.sub_self, List.getD_cons_zero, ftsSecretNat]
      rw [show 2 * pair / 2 = pair by omega, if_pos (by omega)]
    · simp only [show 2 * pair + 1 - 2 * pair = 1 by omega, ftsSecretNat]
      rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega)]
      rfl
theorem ftsSecret_nat (answers : Answers) (index coord leaf : Nat) (hleaf : leaf < 2048) :
    Extract.ftsSecret answers index coord leaf = ftsSecretNat answers index coord leaf := by
  unfold Extract.ftsSecret
  rw [Correctness.buildFts_eq]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact (eval_ftsRows_secrets answers index coord).2 leaf hleaf
theorem ftsSecret_eq (answers : Answers) (f : FtsLeafPos) :
    Extract.ftsSecret answers f.index.val f.coord.val f.leaf.val = ftsOf (secretsOf answers) f :=
  ftsSecret_nat answers _ _ _ f.leaf.isLt
section Honest
variable {answers : Answers} {labels : Labels}
theorem seedsOf_secretsOf (answers : Answers) : seedsOf (secretsOf answers) = ChainGraph.sourceSeeds answers := rfl
theorem chainValue_eq (h : Agrees answers labels) (a : Address) (step : Nat) (hstep : step ≤ 7) :
    honestChainValue answers a.layer a.tree.val a.leaf.val a.chain.val
      (leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val) step =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a step :=
  ChainGraph.source_prefix answers (chainLabels labels) (agrees_chain h) a step hstep
theorem leafValue_eq (h : Agrees answers labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hdigit : digits.getD i 0 ≤ 7) :
    leafValue answers L.lay L.tree.val L.leaf.val digits i =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
        (digits.getD i 0) := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := chainValue_eq h ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (digits.getD i 0) hdigit
  simp only [hval] at hx
  exact hx
theorem leafEnd_eq (h : Agrees answers labels) (L : LeafPos) (i : Nat) (hi : i < 58) :
    leafEnd answers L.lay L.tree.val L.leaf.val i = endLabel (secretsOf answers) labels L i := by
  have hval : (fin58 i).val = i := Nat.mod_eq_of_lt hi
  have hx := ChainGraph.source_endpoint answers (chainLabels labels) (agrees_chain h) ⟨L.lay, L.tree, L.leaf, fin58 i⟩
  simp only [hval] at hx
  exact hx
theorem leafEnds_eq (h : Agrees answers labels) (L : LeafPos) :
    (List.range (chainCount L.lay)).map (leafEnd answers L.lay L.tree.val L.leaf.val) =
      (List.range (chainCount L.lay)).map (endLabel (secretsOf answers) labels L) := by
  apply List.map_congr_left
  intro i hi
  exact leafEnd_eq h L i (lt_of_lt_of_le (List.mem_range.mp hi) (chainCount_bound L.lay))
theorem leafRoot_eq (h : Agrees answers labels) (L : LeafPos) :
    leafRoot answers L.lay L.tree.val L.leaf.val = (labels (.leaf L)).extractLsb' 0 128 := by
  unfold leafRoot
  rw [Extract.leafHash_eq_shortHash, eval_shortHash, leafEnds_eq h L]
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.leaf L))
theorem treeNodeAt_some (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hlevel : level < height lay)
    (hc : c < 2 ^ (height lay - level - 1)) :
    ∃ n : TreeNode, treeNodeAt lay tree level c = some n ∧ n.1.lay = lay ∧ n.1.tree = tree ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold treeNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem builtTree_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (hlevel : level ≤ height lay) (hc : c < 2 ^ (height lay - level)) :
    treeValue (builtTree answers lay tree.val) level c = treeLabel labels lay tree level c := by
  have hcorrect := Correctness.builtTree_correct answers lay tree.val
  obtain ⟨-, -, hnodes⟩ := hcorrect
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2 ^ height lay := by simpa using hc
      have h4096 : c < 4096 := lt_of_lt_of_le hc' (by
        calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
          _ = 4096 := by norm_num)
      rw [Correctness.builtTree_leaf answers lay tree.val c hc']
      have hr := leafRoot_eq h ⟨lay, tree, ⟨c, h4096⟩⟩
      unfold treeLabel
      rw [if_pos rfl, dif_pos h4096]
      exact hr
  | succ level ih =>
      intro c hc
      have hlt : level < height lay := by omega
      have hsub : height lay - (level + 1) = height lay - level - 1 := by omega
      have hc1 : c < 2 ^ (height lay - level - 1) := by rw [← hsub]; exact hc
      have hrec := hnodes level hlt c (by rw [hsub]; exact hc1)
      have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hchild : ∀ j, j < 2 * c + 2 → treeValue (builtTree answers lay tree.val) level j =
          treeLabel labels lay tree level j := by
        intro j hj
        exact ih (by omega) j (by omega)
      obtain ⟨n, hn, hlay, htree, hlev, hidx⟩ := treeNodeAt_some lay tree level c hlt hc1
      change ((builtTree answers lay tree.val).getD (level + 1) []).getD c 0 = _
      rw [hrec, nodeHash_eq_shortHash, eval_shortHash]
      unfold treeLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      simp only
      have hinput : cell (secretsOf answers) (.node n) labels =
          pad64 (nodeInputP 3 lay.val tree.val (2 ^ (height lay - (level + 1)) + c)
            (((builtTree answers lay tree.val).getD level []).getD (2 * c) 0) 0
            (((builtTree answers lay tree.val).getD level []).getD (2 * c + 1) 0)) := by
        have h1 := hchild (2 * c) (by omega)
        have h2 := hchild (2 * c + 1) (by omega)
        unfold treeValue at h1 h2
        rw [h1, h2]
        obtain ⟨⟨nlay, ntree, nlevel, nidx⟩, hv⟩ := n
        simp only at hlay htree hlev hidx
        subst hlay htree
        simp only [cell]
        rw [hlev, hidx, show height nlay - level - 1 = height nlay - (level + 1) by omega]
      rw [← hinput]
      exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.node n))
theorem honestRoot_eq (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) :
    Extract.honestRoot answers lay tree.val = treeLabel labels lay tree (height lay) 0 :=
  builtTree_eq h lay tree (height lay) 0 le_rfl (by simp)
theorem honestRoot_label (h : Agrees answers labels) (lay : Layer) (tree : Fin (2^31)) :
    Extract.honestRoot answers lay tree.val = (labels (.node (rootNode lay tree))).extractLsb' 0 128 := by
  rw [honestRoot_eq h, treeLabel_root]
theorem ftsNodeAt_some (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) (hlevel : level < 11)
    (hc : c < 2 ^ (11 - level - 1)) :
    ∃ n : FtsNodePos, ftsNodeAt index coord level c = some n ∧ n.1.index = index ∧ n.1.coord = coord ∧
      n.1.level.val = level ∧ n.1.idx.val = c := by
  unfold ftsNodeAt
  rw [dif_pos ⟨hlevel, hc⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
theorem ftsTree_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat)
    (hlevel : level ≤ 11) (hc : c < 2 ^ (11 - level)) :
    treeValue (evalWithAnswerFn answers (buildFts index.val coord.val)).1 level c =
      ftsLabel labels index coord level c := by
  have hcorrect := Correctness.eval_buildFts_correct answers index.val coord.val
  obtain ⟨-, -, hleaves, hnodes⟩ := hcorrect
  have hsecrets : ∀ leaf, leaf < 2048 →
      (evalWithAnswerFn answers (buildFts index.val coord.val)).2.getD leaf 0 =
        ftsSecretNat answers index.val coord.val leaf := by
    intro leaf hleaf
    have hx := ftsSecret_nat answers index.val coord.val leaf hleaf
    unfold Extract.ftsSecret at hx
    exact hx
  generalize evalWithAnswerFn answers (buildFts index.val coord.val) = X at hleaves hnodes hsecrets ⊢
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2048 := by simpa using hc
      rw [hleaves c hc', ftsLeaf_eq_shortHash, eval_shortHash, hsecrets c hc']
      unfold ftsLabel
      rw [if_pos rfl, dif_pos hc']
      exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.ftsLeaf ⟨index, coord, ⟨c, hc'⟩⟩))
  | succ level ih =>
      intro c hc
      have hlt : level < 11 := by omega
      have hsub : 11 - (level + 1) = 11 - level - 1 := by omega
      have hc1 : c < 2 ^ (11 - level - 1) := by rw [← hsub]; exact hc
      have hrec := hnodes level hlt c (by rw [hsub]; exact hc1)
      have hpow : 2 ^ (11 - level) = 2 * 2 ^ (11 - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hchild : ∀ j, j < 2 * c + 2 → treeValue X.1 level j = ftsLabel labels index coord level j := by
        intro j hj
        exact ih (by omega) j (by omega)
      obtain ⟨n, hn, hindex, hcoord, hlev, hidx⟩ := ftsNodeAt_some index coord level c hlt hc1
      rw [hrec, nodeHash_eq_shortHash, eval_shortHash]
      unfold ftsLabel
      rw [if_neg (by omega), show level + 1 - 1 = level by omega, hn]
      simp only
      have hinput : cell (secretsOf answers) (.ftsNode n) labels =
          pad64 (nodeInputP 10 coord.val index.val (2 ^ (11 - (level + 1)) + c)
            (treeValue X.1 level (2 * c)) 0 (treeValue X.1 level (2 * c + 1))) := by
        rw [hchild (2 * c) (by omega), hchild (2 * c + 1) (by omega)]
        obtain ⟨⟨nindex, ncoord, nlevel, nidx⟩, hv⟩ := n
        simp only at hindex hcoord hlev hidx
        subst hindex hcoord
        simp only [cell]
        rw [hlev, hidx, show 11 - level - 1 = 11 - (level + 1) by omega]
      rw [← hinput]
      exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.ftsNode n))
theorem ftsLevels_built (answers : Answers) (index coord level j : Nat) (hl : level < 11)
    (hj : j < 2 ^ (11 - level)) :
    treeValue (Extract.ftsLevels answers index coord) level j =
      treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level j := by
  have hpow : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
    rw [← pow_succ']; congr 1; omega
  have hn : j / 2 < 2 ^ (11 - (level + 1)) := by omega
  have hpex := FtsExtract.honestInput_ftsNode answers index coord level (j / 2) hl hn
  rw [show FtsExtract.builtSecret answers index coord =
      fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0 from rfl,
    FtsExtract.honInputL_built answers index coord level (j / 2) hl hn] at hpex
  have hdef : Extract.honestInput answers (.ftsNode index coord level (j / 2)) =
      pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + j / 2)
        (treeValue (Extract.ftsLevels answers index coord) level (2 * (j / 2))) 0
        (treeValue (Extract.ftsLevels answers index coord) level (2 * (j / 2) + 1))) := rfl
  rw [hdef, pad64_nodeInputP, nodeInputP, nodeInputP] at hpex
  obtain ⟨hleft, -, -, hright⟩ := block4_injective hpex
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hj2 : 2 * (j / 2) = j := by omega
    rw [hj2] at hleft
    exact hleft
  · have hj2 : 2 * (j / 2) + 1 = j := by omega
    rw [hj2] at hright
    exact hright
theorem ftsRoots_built (answers : Answers) (index : Nat) :
    Extract.ftsRootsHonest answers index =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0 := by
  have hpex := FtsExtract.honestInput_forest answers index
  have hdef : Extract.honestInput answers (.forest index) =
      pad64 (Extract.forestInput index (Extract.ftsRootsHonest answers index)) := rfl
  rw [hdef] at hpex
  exact FtsExtract.forestInput_injective (by simp [Extract.ftsRootsHonest]) (by simp) hpex
theorem ftsRoot_built (answers : Answers) (index coord : Nat) (hcoord : coord < 7) :
    Extract.ftsRoot answers index coord = treeValue (evalWithAnswerFn answers (buildFts index coord)).1 11 0 := by
  have h := ftsRoots_built answers index
  unfold Extract.ftsRootsHonest at h
  exact (List.map_inj_left.mp h) coord (List.mem_range.mpr hcoord)
theorem ftsLevels_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat)
    (hlevel : level ≤ 11) (hc : c < 2 ^ (11 - level)) :
    treeValue (Extract.ftsLevels answers index.val coord.val) level c = ftsLabel labels index coord level c := by
  rcases Nat.lt_or_ge level 11 with hl | hl
  · rw [ftsLevels_built answers _ _ level c hl hc, ftsTree_eq h index coord level c hlevel hc]
  · have h11 : level = 11 := by omega
    subst h11
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    change Extract.ftsRoot answers index.val coord.val = _
    rw [ftsRoot_built answers _ _ coord.isLt, ftsTree_eq h index coord 11 0 le_rfl (by decide)]
theorem ftsRoot_eq (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 7) :
    Extract.ftsRoot answers index.val coord.val = ftsLabel labels index coord 11 0 := by
  rw [ftsRoot_built answers _ _ coord.isLt, ftsTree_eq h index coord 11 0 le_rfl (by decide)]
theorem ftsRoot_label (h : Agrees answers labels) (index : Fin (2^31)) (coord : Fin 7) :
    Extract.ftsRoot answers index.val coord.val =
      (labels (.ftsNode (ftsRootNode index coord))).extractLsb' 0 128 := by
  rw [ftsRoot_eq h, ftsLabel_root]
theorem ftsRoots_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.ftsRootsHonest answers index.val =
      (List.range 7).map fun coord => ftsLabel labels index (fin7 coord) 11 0 := by
  rw [ftsRoots_built]
  apply List.map_congr_left
  intro coord hcoord
  have hc : coord < 7 := List.mem_range.mp hcoord
  have hval : (fin7 coord).val = coord := Nat.mod_eq_of_lt hc
  have hx := ftsTree_eq h index (fin7 coord) 11 0 le_rfl (by decide)
  rw [hval] at hx
  exact hx
theorem honestForest_eq (h : Agrees answers labels) (index : Fin (2^31)) :
    Extract.honestForest answers index.val = (labels (.forest index)).extractLsb' 0 128 := by
  unfold Extract.honestForest
  rw [Extract.forestPk_eq_shortHash, eval_shortHash, ftsRoots_eq h index]
  exact congrArg (fun output : HashOutput => output.extractLsb' 0 128) (h (.forest index))
theorem honestInput_eq (h : Agrees answers labels) (node : Node) :
    Extract.honestInput answers node.toPos = cell (secretsOf answers) node labels := by
  cases node with
  | chain p =>
      simp only [Node.toPos, Extract.honestInput]
      rw [chainValue_eq h p.1 p.2.val (by have := p.2.isLt; omega)]
      change pad64 (ChainGraph.row p _) = ChainGraph.row p (ChainGraph.prior _ p _)
      rw [ChainGraph.row_pad64, ChainGraph.prior_eq_value]
  | leaf L =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [leafEnds_eq h L]
  | node n =>
      obtain ⟨⟨lay, tree, level, idx⟩, hv1, hv2⟩ := n
      change level.val < height lay at hv1
      change idx.val < 2 ^ (height lay - level.val - 1) at hv2
      simp only [Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (height lay - level.val) = 2 * 2 ^ (height lay - level.val - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [builtTree_eq h lay tree level.val (2 * idx.val) (by omega) (by omega),
        builtTree_eq h lay tree level.val (2 * idx.val + 1) (by omega) (by omega)]
  | ftsLeaf f =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [ftsSecret_eq answers f]
  | ftsNode n =>
      obtain ⟨⟨index, coord, level, idx⟩, hv⟩ := n
      have hv' : idx.val < 2 ^ (11 - level.val - 1) := hv
      simp only [Node.toPos, Extract.honestInput, cell]
      have hpow : 2 ^ (11 - level.val) = 2 * 2 ^ (11 - level.val - 1) := by
        have := level.isLt
        rw [← pow_succ']; congr 1; omega
      rw [ftsLevels_eq h index coord level.val (2 * idx.val) (by have := level.isLt; omega) (by omega),
        ftsLevels_eq h index coord level.val (2 * idx.val + 1) (by have := level.isLt; omega) (by omega)]
  | forest index =>
      simp only [Node.toPos, Extract.honestInput, cell]
      rw [ftsRoots_eq h index]
theorem honest_answer (h : Agrees answers labels) (node : Node) :
    answers (.inl (.inr (Extract.honestInput answers node.toPos))) = labels node := by
  rw [honestInput_eq h node]
  exact h node
theorem frontierValue_eq (h : Agrees answers labels) (a : Address)
    (hdepth : Wots.depth answers ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩ ≤ 7) :
    Wots.frontierValue answers ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩ =
      ChainGraph.value (seedsOf (secretsOf answers)) (chainLabels labels) a
        (Wots.depth answers ⟨⟨a.layer, a.tree.val, a.leaf.val⟩, a.chain.val⟩) :=
  chainValue_eq h a _ hdepth
end Honest
end SigGolfCandidate.T3.Security.CanonGraph
