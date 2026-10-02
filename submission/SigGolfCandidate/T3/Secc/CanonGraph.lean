import SigGolfCandidate.T3.BPORS
import SigGolfCandidate.T3.Secc.SeccLaw
import SigGolfCandidate.T3.Secc.WotsEvents

/-!
# Stream G: canonical labels for every source-sized honest T3 position

SEC's `ChainGraph` presamples the honest chain points only. This module extends it to **every** source-sized
honest public position — chain points (tag 1), leaf pks (2), Merkle nodes (3), FTS leaves (9), FTS nodes (10),
forest pks (11) — as an instance of the pinned `FiniteGraphSampling` (record template `Hypertree/CanonicalGraph*`):

* `Node` is a finite superset of the source positions, `Node.depth` a depth order;
* `cell secrets node labels` is the honest input of `node` (PEX `Extract.honestInput`) computed from the
  labels of strictly lower depth (`cell_congr`) and the private secrets (chain seeds, FTS secrets);
* cells of distinct nodes differ (`cell_separated`) because their header blocks are the PEX headers
  (`hdrBlock_cell`) and `Extract.Pos.hdr_injective`.

Laws (all exact identities, for every finite universe `U ⊇ canonInputs`):
`graph_bind_eq_uniform_programmed` (fixed secrets), `tables_bind` (private table split into secrets and the
other private halves, plus the public table), `recorded_canon_law` (SEC's recorded game). In all of them the
honest labels are uniform and independent, the residual public table is uniform and independent of them, and
the actual table is the residual with every canonical cell programmed by its label (`programmed_at`,
`programmed_other`). `Agrees` (any answers table whose public part is such a programmed table) is what the honest
objects need (module `CanonGraphHonest`).
-/

namespace SigGolfCandidate.T3.Security.CanonGraph
open OracleComp OracleSpec OracleComp.EvalDist OracleComp.DeferredSampling ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete FiniteGraphSampling
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafRoot)
open ChainGraph (Address Point Seeds)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## Source-sized positions -/

/-- A WOTS leaf (key pair) of the source-sized superset: every layer, tree < 2^31, leaf < 4096. -/
structure LeafPos where
  lay : Layer
  tree : Fin (2^31)
  leaf : Fin 4096
  deriving DecidableEq, Fintype

/-- Raw coordinates of a hypertree Merkle node, PEX `.node lay tree level idx`
(the node at level `level + 1`; its children are at `level`). -/
structure TreeNodeRaw where
  lay : Layer
  tree : Fin (2^31)
  level : Fin 12
  idx : Fin 2048
  deriving DecidableEq, Fintype

def TreeNodeRaw.Valid (n : TreeNodeRaw) : Prop :=
  n.level.val < height n.lay ∧ n.idx.val < 2 ^ (height n.lay - n.level.val - 1)

instance instDecidablePredTreeNodeRawValid : DecidablePred TreeNodeRaw.Valid := fun n => by unfold TreeNodeRaw.Valid; infer_instance

/-- A valid hypertree Merkle node. -/
abbrev TreeNode := {n : TreeNodeRaw // n.Valid}

/-- An FTS leaf: index < 2^31, coordinate < 7, leaf < 2048. -/
structure FtsLeafPos where
  index : Fin (2^31)
  coord : Fin 7
  leaf : Fin 2048
  deriving DecidableEq, Fintype

/-- Raw coordinates of an FTS node, PEX `.ftsNode index coord level idx`. -/
structure FtsNodeRaw where
  index : Fin (2^31)
  coord : Fin 7
  level : Fin 11
  idx : Fin 1024
  deriving DecidableEq, Fintype

def FtsNodeRaw.Valid (n : FtsNodeRaw) : Prop := n.idx.val < 2 ^ (11 - n.level.val - 1)

instance instDecidablePredFtsNodeRawValid : DecidablePred FtsNodeRaw.Valid := fun n => by unfold FtsNodeRaw.Valid; infer_instance

/-- A valid FTS node. -/
abbrev FtsNodePos := {n : FtsNodeRaw // n.Valid}

/-- Every source-sized honest public position: chain points (SEC's `ChainGraph.Point`, tag 1), leaf pks (2),
Merkle nodes (3), FTS leaves (9), FTS nodes (10), forest pks (11). -/
inductive Node where
  | chain (point : Point)
  | leaf (pos : LeafPos)
  | node (pos : TreeNode)
  | ftsLeaf (pos : FtsLeafPos)
  | ftsNode (pos : FtsNodePos)
  | forest (index : Fin (2^31))
  deriving DecidableEq, Fintype

attribute [local irreducible] ChainGraph.instFintypeAddress

/-- Graph depth: every cell reads only labels of strictly smaller depth (`cell_congr`). -/
def Node.depth : Node → Nat
  | .chain p => p.2.val
  | .leaf _ => 7
  | .node n => 8 + n.1.level.val
  | .ftsLeaf _ => 0
  | .ftsNode n => 1 + n.1.level.val
  | .forest _ => 12

/-! ## Secrets and labels -/

/-- Private secret halves read by honest public inputs: chain seeds and FTS secrets. -/
abbrev SecretIndex := Address ⊕ FtsLeafPos
abbrev Secrets := SecretIndex → Digest
/-- One full 256-bit oracle answer per position. -/
abbrev Labels := Node → HashOutput

def seedsOf (secrets : Secrets) : Seeds := fun address => secrets (.inl address)
def ftsOf (secrets : Secrets) : FtsLeafPos → Digest := fun leaf => secrets (.inr leaf)
def chainLabels (labels : Labels) : ChainGraph.Labels := fun point => labels (.chain point)

def fin58 (i : Nat) : Fin 58 := ⟨i % 58, Nat.mod_lt _ (by decide)⟩
def fin7 (i : Nat) : Fin 7 := ⟨i % 7, Nat.mod_lt _ (by decide)⟩

/-- The end value (step `2^w − 1`) of chain `i` of a leaf, read off the chain labels. -/
def endLabel (secrets : Secrets) (labels : Labels) (L : LeafPos) (i : Nat) : Digest :=
  ChainGraph.value (seedsOf secrets) (chainLabels labels) ⟨L.lay, L.tree, L.leaf, fin58 i⟩ (2 ^ width L.lay i - 1)

/-- The valid Merkle node `(lay, tree, level, c)`, if any. -/
def treeNodeAt (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Option TreeNode :=
  if h : level < height lay ∧ c < 2 ^ (height lay - level - 1) then
    some ⟨⟨lay, tree, ⟨level, lt_of_lt_of_le h.1 (Extract.height_le lay)⟩,
      ⟨c, lt_of_lt_of_le h.2 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := Extract.height_le lay; omega)
          _ = 2048 := by norm_num)⟩⟩, h⟩
  else none

/-- Tree values read off labels (PEX/`treeValue` convention): level 0 = leaf pk labels, level `l + 1` = labels
of the nodes `(l, c)`; 0 outside the tree. -/
def treeLabel (labels : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 4096 then (labels (.leaf ⟨lay, tree, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match treeNodeAt lay tree (level - 1) c with
    | some n => (labels (.node n)).extractLsb' 0 128
    | none => 0

/-- The valid FTS node `(index, coord, level, c)`, if any. -/
def ftsNodeAt (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Option FtsNodePos :=
  if h : level < 11 ∧ c < 2 ^ (11 - level - 1) then
    some ⟨⟨index, coord, ⟨level, h.1⟩, ⟨c, lt_of_lt_of_le h.2 (by
      calc 2 ^ (11 - level - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 1024 := by norm_num)⟩⟩, h.2⟩
  else none

/-- FTS tree values read off labels: level 0 = FTS leaf labels, level `l + 1` = FTS node labels. -/
def ftsLabel (labels : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) : Digest :=
  if level = 0 then
    (if h : c < 2048 then (labels (.ftsLeaf ⟨index, coord, ⟨c, h⟩⟩)).extractLsb' 0 128 else 0)
  else
    match ftsNodeAt index coord (level - 1) c with
    | some n => (labels (.ftsNode n)).extractLsb' 0 128
    | none => 0

/-- **The honest input of a position from earlier labels** (PEX `Extract.honestInput` with every honest value
replaced by the label it is the low half of; chain cells are SEC's `ChainGraph.input`). -/
def cell (secrets : Secrets) : Node → Labels → HashInput
  | .chain p, labels => ChainGraph.input (seedsOf secrets) p (chainLabels labels)
  | .leaf L, labels => pad64 (Extract.leafInput L.lay L.tree.val L.leaf.val
      ((List.range (chainCount L.lay)).map (endLabel secrets labels L)))
  | .node n, labels => pad64 (nodeInputP 3 n.1.lay.val n.1.tree.val
      (2 ^ (height n.1.lay - n.1.level.val - 1) + n.1.idx.val)
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)) 0
      (treeLabel labels n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)))
  | .ftsLeaf f, _ => pad64 (ftsLeafInputP f.index.val f.coord.val f.leaf.val 0 (ftsOf secrets f) 0)
  | .ftsNode n, labels => pad64 (nodeInputP 10 n.1.coord.val n.1.index.val
      (2 ^ (11 - n.1.level.val - 1) + n.1.idx.val)
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)) 0
      (ftsLabel labels n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)))
  | .forest index, labels => pad64 (Extract.forestInput index.val
      ((List.range 7).map fun coord => ftsLabel labels index (fin7 coord) 11 0))

/-- Number of trees of each layer in the source (`route index lay` with `index < 2^31`): 2^0, 2^12, 2^19, 2^25. -/
def treeBits (lay : Layer) : Nat := ![0, 12, 19, 25] lay

/-- A source leaf: `tree < 2^treeBits lay`, `leaf < 2^height lay`. -/
def LeafPos.Source (L : LeafPos) : Prop := L.tree.val < 2 ^ treeBits L.lay ∧ L.leaf.val < 2 ^ height L.lay

instance instDecidablePredLeafPosSource : DecidablePred LeafPos.Source := fun L => by unfold LeafPos.Source; infer_instance

/-- The PEX position of a node. -/
def Node.toPos : Node → Extract.Pos
  | .chain p => .chain p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val
  | .leaf L => .leaf L.lay L.tree.val L.leaf.val
  | .node n => .node n.1.lay n.1.tree.val n.1.level.val n.1.idx.val
  | .ftsLeaf f => .ftsLeaf f.index.val f.coord.val f.leaf.val
  | .ftsNode n => .ftsNode n.1.index.val n.1.coord.val n.1.level.val n.1.idx.val
  | .forest index => .forest index.val

/-- Source-sized PEX positions: exactly the images of `Node.toPos`. -/
def SourcePos : Extract.Pos → Prop
  | .chain _ tree leaf i step => tree < 2 ^ 31 ∧ leaf < 4096 ∧ i < 58 ∧ step < 7
  | .leaf _ tree leaf => tree < 2 ^ 31 ∧ leaf < 4096
  | .node lay tree level nd => tree < 2 ^ 31 ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 31
  | .ftsLeaf index coord leaf => index < 2 ^ 31 ∧ coord < 7 ∧ leaf < 2048
  | .ftsNode index coord level nd => index < 2 ^ 31 ∧ coord < 7 ∧ level < 11 ∧ nd < 2 ^ (11 - level - 1)

theorem toPos_bounded (node : Node) : node.toPos.Bounded := by
  cases node with
  | chain p =>
      have := p.1.tree.isLt; have := p.1.leaf.isLt; have := p.1.chain.isLt; have := p.2.isLt
      exact ⟨by omega, by omega, by omega, by omega⟩
  | leaf L => have := L.tree.isLt; have := L.leaf.isLt; exact ⟨by omega, by omega⟩
  | node n => have := n.1.tree.isLt; exact ⟨by omega, n.2.1, n.2.2⟩
  | ftsLeaf f =>
      have := f.index.isLt; have := f.coord.isLt; have := f.leaf.isLt
      exact ⟨by omega, by omega, by omega⟩
  | ftsNode n =>
      have := n.1.index.isLt; have := n.1.coord.isLt; have := n.1.level.isLt
      exact ⟨by omega, by omega, by omega, n.2⟩
  | forest index => have := index.isLt; change index.val < 2 ^ 40; omega

theorem toPos_source (node : Node) : SourcePos node.toPos := by
  cases node with
  | chain p => exact ⟨p.1.tree.isLt, p.1.leaf.isLt, p.1.chain.isLt, p.2.isLt⟩
  | leaf L => exact ⟨L.tree.isLt, L.leaf.isLt⟩
  | node n => exact ⟨n.1.tree.isLt, n.2.1, n.2.2⟩
  | ftsLeaf f => exact ⟨f.index.isLt, f.coord.isLt, f.leaf.isLt⟩
  | ftsNode n => exact ⟨n.1.index.isLt, n.1.coord.isLt, n.1.level.isLt, n.2⟩
  | forest index => exact index.isLt

theorem toPos_injective : Function.Injective Node.toPos := by
  intro left right h
  cases left with
  | chain p =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i q
      simp only [Extract.Pos.chain.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hp : p = q := Prod.ext (ChainGraph.Address.ext h1 (Fin.ext h2) (Fin.ext h3) (Fin.ext h4)) (Fin.ext h5)
      rw [hp]
  | leaf L =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i M
      simp only [Extract.Pos.leaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      cases L; cases M
      simp only at h1 h2 h3
      subst h1
      rw [Fin.ext h2, Fin.ext h3]
  | node n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.node.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨lay, tree, level, idx⟩, hn⟩ := n
      obtain ⟨⟨lay', tree', level', idx'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      subst h1
      have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e2 e3 e4
      rfl
  | ftsLeaf f =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i g
      simp only [Extract.Pos.ftsLeaf.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      cases f; cases g
      simp only at h1 h2 h3
      rw [Fin.ext h1, Fin.ext h2, Fin.ext h3]
  | ftsNode n =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i m
      simp only [Extract.Pos.ftsNode.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨⟨index, coord, level, idx⟩, hn⟩ := n
      obtain ⟨⟨index', coord', level', idx'⟩, hm⟩ := m
      simp only at h1 h2 h3 h4
      have e1 := Fin.ext h1; have e2 := Fin.ext h2; have e3 := Fin.ext h3; have e4 := Fin.ext h4
      subst e1 e2 e3 e4
      rfl
  | forest index =>
      cases right <;> simp only [Node.toPos, reduceCtorEq] at h
      rename_i index'
      simp only [Extract.Pos.forest.injEq] at h
      rw [Fin.ext h]

theorem exists_toPos {p : Extract.Pos} (hp : SourcePos p) : ∃ node : Node, node.toPos = p := by
  cases p with
  | chain lay tree leaf i step =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      exact ⟨.chain (⟨lay, ⟨tree, h1⟩, ⟨leaf, h2⟩, ⟨i, h3⟩⟩, ⟨step, h4⟩), rfl⟩
  | leaf lay tree leaf =>
      obtain ⟨h1, h2⟩ := hp
      exact ⟨.leaf ⟨lay, ⟨tree, h1⟩, ⟨leaf, h2⟩⟩, rfl⟩
  | node lay tree level nd =>
      obtain ⟨h1, h2, h3⟩ := hp
      have hl : level < 12 := lt_of_lt_of_le h2 (Extract.height_le lay)
      have hn : nd < 2048 := lt_of_lt_of_le h3 (by
        calc 2 ^ (height lay - level - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by
              have := Extract.height_le lay; omega)
          _ = 2048 := by norm_num)
      exact ⟨.node ⟨⟨lay, ⟨tree, h1⟩, ⟨level, hl⟩, ⟨nd, hn⟩⟩, h2, h3⟩, rfl⟩
  | forest index => exact ⟨.forest ⟨index, hp⟩, rfl⟩
  | ftsLeaf index coord leaf =>
      obtain ⟨h1, h2, h3⟩ := hp
      exact ⟨.ftsLeaf ⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨leaf, h3⟩⟩, rfl⟩
  | ftsNode index coord level nd =>
      obtain ⟨h1, h2, h3, h4⟩ := hp
      have hn : nd < 1024 := lt_of_lt_of_le h4 (by
        calc 2 ^ (11 - level - 1) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
          _ = 1024 := by norm_num)
      exact ⟨.ftsNode ⟨⟨⟨index, h1⟩, ⟨coord, h2⟩, ⟨level, h3⟩, ⟨nd, hn⟩⟩, h4⟩, rfl⟩

/-- Cells carry the header of their position, whatever the labels. -/
theorem hdrBlock_cell (secrets : Secrets) (node : Node) (labels : Labels) :
    Extract.hdrBlock (cell secrets node labels) = bytesLE 16 node.toPos.hdr := by
  cases node with
  | chain p =>
      change Extract.hdrBlock (chainInput p.1.layer p.1.tree.val p.1.leaf.val p.1.chain.val p.2.val _) = _
      rw [chainInput_eq_zero, ← pad64_chainInputP, Extract.hdrBlock_chainInputP]
      rfl
  | leaf L =>
      simp only [cell, Extract.leafInput]
      rw [Extract.hdrBlock_listInput]
      rfl
  | node n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, Extract.hdrBlock_block4]
      rfl
  | ftsLeaf f =>
      simp only [cell]
      rw [pad64_ftsLeafInputP, ftsLeafInputP, Extract.hdrBlock_block4]
      rfl
  | ftsNode n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, Extract.hdrBlock_block4]
      rfl
  | forest index =>
      simp only [cell, Extract.forestInput]
      rw [Extract.hdrBlock_listInput]
      rfl

theorem cell_separated (secrets : Secrets) : Separated (cell secrets) := by
  intro left right hne before after heq
  have h1 := hdrBlock_cell secrets left before
  have h2 := hdrBlock_cell secrets right after
  rw [heq] at h1
  exact hne (toPos_injective (Extract.Pos.hdr_injective (toPos_bounded left) (toPos_bounded right)
    (bytesLE_injective (h1.symm.trans h2))))

theorem treeNodeAt_level {lay : Layer} {tree : Fin (2^31)} {level c : Nat} {n : TreeNode}
    (h : treeNodeAt lay tree level c = some n) : n.1.level.val = level := by
  unfold treeNodeAt at h
  split_ifs at h with hv
  cases h
  rfl

theorem ftsNodeAt_level {index : Fin (2^31)} {coord : Fin 7} {level c : Nat} {n : FtsNodePos}
    (h : ftsNodeAt index coord level c = some n) : n.1.level.val = level := by
  unfold ftsNodeAt at h
  split_ifs at h with hv
  cases h
  rfl

theorem treeLabel_congr (left right : Labels) (lay : Layer) (tree : Fin (2^31)) (level c : Nat)
    (h : ∀ other : Node, other.depth < 8 + level → left other = right other) :
    treeLabel left lay tree level c = treeLabel right lay tree level c := by
  unfold treeLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth]; omega)]
  · rfl
  · cases hn : treeNodeAt lay tree (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        rw [h _ (by simp only [Node.depth]; rw [treeNodeAt_level hn]; omega)]

theorem ftsLabel_congr (left right : Labels) (index : Fin (2^31)) (coord : Fin 7) (level c : Nat)
    (h : ∀ other : Node, other.depth < 1 + level → left other = right other) :
    ftsLabel left index coord level c = ftsLabel right index coord level c := by
  unfold ftsLabel
  split_ifs with hzero hc
  · rw [h _ (by simp only [Node.depth]; omega)]
  · rfl
  · cases hn : ftsNodeAt index coord (level - 1) c with
    | none => rfl
    | some n =>
        simp only
        rw [h _ (by simp only [Node.depth]; rw [ftsNodeAt_level hn]; omega)]

/-- A cell reads only labels of strictly smaller depth. -/
theorem cell_congr (secrets : Secrets) (node : Node) (left right : Labels)
    (h : ∀ other : Node, other.depth < node.depth → left other = right other) :
    cell secrets node left = cell secrets node right := by
  cases node with
  | chain p =>
      change ChainGraph.input (seedsOf secrets) p (chainLabels left) =
        ChainGraph.input (seedsOf secrets) p (chainLabels right)
      unfold ChainGraph.input ChainGraph.prior
      split_ifs with hz
      · rfl
      · have hd := h (.chain (ChainGraph.predecessor p)) (by
          simp only [Node.depth, ChainGraph.predecessor]; omega)
        simp only [chainLabels, hd]
  | leaf L =>
      have hends : (List.range (chainCount L.lay)).map (endLabel secrets left L) =
          (List.range (chainCount L.lay)).map (endLabel secrets right L) := by
        apply List.map_congr_left
        intro i _
        unfold endLabel ChainGraph.value
        split_ifs
        · rfl
        · simp only [chainLabels]
          rw [h _ (by simp only [Node.depth]; exact Nat.mod_lt _ (by decide))]
      simp only [cell, hends]
  | node n =>
      have hl := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := treeLabel_congr left right n.1.lay n.1.tree n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      simp only [cell, hl, hr]
  | ftsLeaf f => rfl
  | ftsNode n =>
      have hl := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      have hr := ftsLabel_congr left right n.1.index n.1.coord n.1.level.val (2 * n.1.idx.val + 1)
        (fun other ho => h other (by simpa only [Node.depth] using ho))
      simp only [cell, hl, hr]
  | forest index =>
      have hroots : ((List.range 7).map fun coord => ftsLabel left index (fin7 coord) 11 0) =
          ((List.range 7).map fun coord => ftsLabel right index (fin7 coord) 11 0) := by
        apply List.map_congr_left
        intro coord _
        exact ftsLabel_congr left right index (fin7 coord) 11 0
          (fun other ho => h other (by simpa only [Node.depth] using ho))
      simp only [cell, hroots]

/-- The node of a source position (`none` off the source range). -/
noncomputable def posNode (p : Extract.Pos) : Option Node :=
  if h : SourcePos p then some (Classical.choose (exists_toPos h)) else none

theorem posNode_toPos (node : Node) : posNode node.toPos = some node := by
  unfold posNode
  rw [dif_pos (toPos_source node)]
  exact congrArg some (toPos_injective (Classical.choose_spec (exists_toPos (toPos_source node))))

theorem toPos_of_posNode {p : Extract.Pos} {node : Node} (h : posNode p = some node) : node.toPos = p := by
  unfold posNode at h
  split_ifs at h with hp
  cases h
  exact Classical.choose_spec (exists_toPos hp)

/-- A cell parses (PEX `posOf`) to its own position. -/
theorem posOf_cell (secrets : Secrets) (node : Node) (labels : Labels) :
    Extract.posOf (cell secrets node labels) = some node.toPos :=
  Extract.posOf_eq (toPos_bounded node) (hdrBlock_cell secrets node labels)

/-- An input parsed at `node` can only be the cell of `node`. -/
theorem cell_eq_of_posOf {input : HashInput} {node node' : Node} (secrets : Secrets) (labels : Labels)
    (hpos : Extract.posOf input = some node.toPos) (h : input = cell secrets node' labels) : node' = node := by
  subst h
  rw [posOf_cell] at hpos
  exact toPos_injective (Option.some.inj hpos)

theorem height_pos (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide

/-- The root node of a hypertree tree and of an FTS tree. -/
def rootNode (lay : Layer) (tree : Fin (2^31)) : TreeNode :=
  ⟨⟨lay, tree, ⟨height lay - 1, by have := Extract.height_le lay; omega⟩, ⟨0, by decide⟩⟩,
    ⟨Nat.sub_lt (height_pos lay) Nat.one_pos, pow_pos (by decide : 0 < 2) _⟩⟩

def ftsRootNode (index : Fin (2^31)) (coord : Fin 7) : FtsNodePos :=
  ⟨⟨index, coord, ⟨10, by decide⟩, ⟨0, by decide⟩⟩, show 0 < 2 ^ (11 - 10 - 1) by decide⟩

theorem treeLabel_root (labels : Labels) (lay : Layer) (tree : Fin (2^31)) :
    treeLabel labels lay tree (height lay) 0 = (labels (.node (rootNode lay tree))).extractLsb' 0 128 := by
  have hpos := height_pos lay
  unfold treeLabel
  rw [if_neg (by omega)]
  have hv : height lay - 1 < height lay ∧ 0 < 2 ^ (height lay - (height lay - 1) - 1) :=
    ⟨by omega, pow_pos (by decide) _⟩
  unfold treeNodeAt
  rw [dif_pos hv]
  rfl

theorem ftsLabel_root (labels : Labels) (index : Fin (2^31)) (coord : Fin 7) :
    ftsLabel labels index coord 11 0 = (labels (.ftsNode (ftsRootNode index coord))).extractLsb' 0 128 := by
  unfold ftsLabel
  rw [if_neg (by omega)]
  unfold ftsNodeAt
  rw [dif_pos (show 11 - 1 < 11 ∧ 0 < 2 ^ (11 - (11 - 1) - 1) by decide)]
  rfl

/-! ## Finite universes, depth order, programmed tables -/

/-- Every possible cell. -/
noncomputable def canonInputs : Finset HashInput :=
  (Finset.univ : Finset (Secrets × Labels × Node)).image fun x => cell x.1 x.2.2 x.2.1

attribute [irreducible] canonInputs

theorem cell_mem (secrets : Secrets) (node : Node) (labels : Labels) : cell secrets node labels ∈ canonInputs := by
  rw [canonInputs]
  exact Finset.mem_image.mpr ⟨(secrets, labels, node), Finset.mem_univ _, rfl⟩

theorem cell_length_le (secrets : Secrets) (node : Node) (labels : Labels) :
    (cell secrets node labels).length ≤ 4096 := by
  cases node with
  | chain p =>
      change (ChainGraph.row p _).length ≤ 4096
      rw [ChainGraph.row_length]; omega
  | leaf L =>
      simp only [cell, Extract.leafInput]
      rw [Cost.pad64_length, Extract.listInput_length]
      have hc : chainCount L.lay ≤ 58 := chainCount_bound L.lay
      have hl : ((List.map (endLabel secrets labels L) (List.range (chainCount L.lay))).drop 1).length ≤ 57 := by
        simp only [List.length_drop, List.length_map, List.length_range]; omega
      have hm := Nat.mod_lt (32 + 16 * ((List.map (endLabel secrets labels L)
        (List.range (chainCount L.lay))).drop 1).length) (by decide : 0 < 64)
      omega
  | node n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | ftsLeaf f =>
      simp only [cell]
      rw [pad64_ftsLeafInputP, ftsLeafInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | ftsNode n =>
      simp only [cell]
      rw [pad64_nodeInputP, nodeInputP, block4]
      simp only [List.length_append, bytesLE_length]; omega
  | forest index =>
      simp only [cell, Extract.forestInput]
      rw [Cost.pad64_length, Extract.listInput_length]
      simp only [List.length_drop, List.length_map, List.length_range]
      omega

/-- Every cell has length ≤ 960, so the shared completion's universe contains all of them. -/
theorem canonInputs_subset_publicUniverse : canonInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [canonInputs, Finset.mem_image] at hinput
  obtain ⟨x, -, rfl⟩ := hinput
  exact SeccLaw.mem_publicUniverse _ (cell_length_le _ _ _)

noncomputable def cellIn (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (node : Node) (labels : Labels) : U :=
  ⟨cell secrets node labels, hU (cell_mem secrets node labels)⟩

theorem cellIn_separated (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) :
    Separated (cellIn U hU secrets) := by
  intro left right hne before after heq
  exact cell_separated secrets left right hne before after (congrArg Subtype.val heq)

theorem cellIn_injective (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (labels : Labels) :
    Function.Injective (fun node => cellIn U hU secrets node labels) := by
  intro left right heq
  by_contra hne
  exact cellIn_separated U hU secrets left right hne labels labels heq

noncomputable def order : List Node :=
  (Finset.univ : Finset Node).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))

attribute [irreducible] order

theorem order_nodup : order.Nodup := by
  unfold order
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem mem_order (node : Node) : node ∈ order := by
  rw [order, List.mem_mergeSort]
  simp

theorem order_sorted : order.Pairwise (fun left right => left.depth ≤ right.depth) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Node => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    (Finset.univ : Finset Node).toList
  simpa only [order, decide_eq_true_eq] using h

def advance (node : Node) (output : HashOutput) (labels : Labels) : Labels := Function.update labels node output

/-- Labels read off a table, in depth order (the table's honest outputs). -/
noncomputable def graph (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (table : U → HashOutput) : Labels :=
  read (cellIn U hU secrets) advance table order (fun _ => 0)

/-- The residual table with every canonical cell overwritten by its label. -/
noncomputable def programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (labels : Labels) (residual : U → HashOutput) : U → HashOutput :=
  patch (fun node => cellIn U hU secrets node labels) labels residual order

section Laws
variable (U : Finset HashInput) (hU : canonInputs ⊆ U)
noncomputable local instance instSampleableTypeHashOutput_canonGraph : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem read_preserves (secrets : Secrets) (table : U → HashOutput) (nodes : List Node) (before : Labels)
    (node : Node) (hnode : node ∉ nodes) :
    read (cellIn U hU secrets) advance table nodes before node = before node := by
  induction nodes generalizing before with
  | nil => rfl
  | cons first rest ih =>
      have hne : node ≠ first := fun h => hnode (by simp [h])
      have hrest : node ∉ rest := fun h => hnode (List.mem_cons_of_mem _ h)
      change read (cellIn U hU secrets) advance table rest
        (Function.update before first (table (cellIn U hU secrets first before))) node = before node
      rw [ih _ hrest, Function.update_of_ne hne]

theorem read_consistent (secrets : Secrets) (table : U → HashOutput) (nodes : List Node)
    (hnodup : nodes.Nodup) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) : ∀ node ∈ nodes,
    read (cellIn U hU secrets) advance table nodes before node =
      table (cellIn U hU secrets node (read (cellIn U hU secrets) advance table nodes before)) := by
  induction nodes generalizing before with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      intro node hnode
      rcases List.mem_cons.mp hnode with hnode | hnode
      · subst node
        have hinput : cellIn U hU secrets first (read (cellIn U hU secrets) advance table (first :: rest) before) =
            cellIn U hU secrets first before := by
          apply Subtype.ext
          apply cell_congr
          intro other hother
          apply read_preserves
          intro hmem
          rcases List.mem_cons.mp hmem with heq | hmem
          · rw [heq] at hother; omega
          · have := hdepth _ hmem; omega
        rw [hinput]
        change read (cellIn U hU secrets) advance table rest
          (Function.update before first (table (cellIn U hU secrets first before))) first = _
        rw [read_preserves _ _ _ _ _ _ _ hfirst, Function.update_self]
      · exact ih hrest hsorted _ node hnode

theorem graph_consistent (secrets : Secrets) (table : U → HashOutput) (node : Node) :
    graph U hU secrets table node = table (cellIn U hU secrets node (graph U hU secrets table)) :=
  read_consistent U hU secrets table order order_nodup order_sorted _ node (mem_order node)

theorem programmed_at (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (node : Node) :
    programmed U hU secrets labels residual (cellIn U hU secrets node labels) = labels node :=
  patch_at _ (cellIn_injective U hU secrets labels) labels residual order node (mem_order node)

theorem programmed_other (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply patch_of_forall_ne
  intro node _ heq
  exact hquery node (congrArg Subtype.val heq)

/-- A row that is not the cell of the node it parses to (PEX `posOf`) is answered by the residual: e.g. every
non-honest query at a parsed position (structural hits), every unparsed or off-source query. -/
theorem programmed_residual (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (query : U)
    (hquery : ∀ node, Extract.posOf query.val = some node.toPos → query.val ≠ cell secrets node labels) :
    programmed U hU secrets labels residual query = residual query := by
  apply programmed_other
  intro node heq
  exact hquery node (heq ▸ posOf_cell secrets node labels) heq

theorem read_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) (nodes : List Node)
    (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    read (cellIn U hU secrets) advance (programmed U hU secrets labels residual) nodes before = labels := by
  induction nodes generalizing before with
  | nil => exact funext fun node => hagrees node (by simp)
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      change read (cellIn U hU secrets) advance (programmed U hU secrets labels residual) rest
        (Function.update before first (programmed U hU secrets labels residual (cellIn U hU secrets first before))) = _
      rw [hinput, programmed_at]
      apply ih hsorted
      intro node hnode
      by_cases heq : node = first
      · subst node; rw [Function.update_self]
      · rw [Function.update_of_ne heq]
        exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)

theorem graph_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) :
    graph U hU secrets (programmed U hU secrets labels residual) = labels :=
  read_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)

theorem read_eq_plant (secrets : Secrets) (nodes : List Node) (hnodup : nodes.Nodup) (before : Labels) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (read (cellIn U hU secrets) advance table nodes before, table)] =
      𝒮[plant (cellIn U hU secrets) advance nodes before] :=
  evalDist_read_eq_plant (cellIn U hU secrets) advance (cellIn_separated U hU secrets) nodes hnodup before

theorem replay_eq_programmed (secrets : Secrets) (labels : Labels) (residual : U → HashOutput)
    (nodes : List Node) (hsorted : nodes.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : Labels) (hagrees : ∀ node, node ∉ nodes → before node = labels node) :
    replay (cellIn U hU secrets) advance labels residual nodes before =
      (labels, patch (fun node => cellIn U hU secrets node labels) labels residual nodes) := by
  induction nodes generalizing before with
  | nil =>
      have hbefore : before = labels := funext fun node => hagrees node (by simp)
      rw [hbefore]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : cellIn U hU secrets first before = cellIn U hU secrets first labels := by
        apply Subtype.ext
        apply cell_congr
        intro other hother
        apply hagrees
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · rw [heq] at hother; omega
        · have := hdepth _ hmem; omega
      have hafter : ∀ node, node ∉ rest → advance first (labels first) before node = labels node := by
        intro node hnode
        unfold advance
        by_cases heq : node = first
        · subst node; rw [Function.update_self]
        · rw [Function.update_of_ne heq]
          exact hagrees node (fun hmem => (List.mem_cons.mp hmem).elim heq hnode)
      rw [replay, ih hsorted _ hafter, patch, hinput]

theorem plant_eq_uniform_programmed (secrets : Secrets) :
    𝒮[plant (cellIn U hU secrets) advance order (fun _ => 0)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] := by
  rw [evalDist_plant_eq_replay _ _ _ order_nodup]
  apply evalSPMF_bind_congr_left
  intro labels
  apply evalSPMF_bind_congr_left
  intro residual
  rw [replay_eq_programmed U hU secrets labels residual order order_sorted _
    (fun node hnode => (hnode (mem_order node)).elim)]
  rfl

theorem graph_eq_uniform_programmed (secrets : Secrets) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      pure (graph U hU secrets table, table)] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        pure (labels, programmed U hU secrets labels residual)] :=
  (read_eq_plant U hU secrets order order_nodup _).trans (plant_eq_uniform_programmed U hU secrets)

/-- **Graph law** (fixed secrets): the honest labels of a uniform table are uniform, and the table is the
independent uniform residual with the canonical cells programmed. -/
theorem graph_bind_eq_uniform_programmed {Result : Type} (secrets : Secrets)
    (next : Labels → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let table ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (graph U hU secrets table) table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next labels (programmed U hU secrets labels residual)] := by
  have h := congrArg (fun law : SPMF (Labels × (U → HashOutput)) =>
    law >>= fun result => 𝒮[next result.1 result.2]) (graph_eq_uniform_programmed U hU secrets)
  simpa only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind] using h

/-- A uniform public table is the programmed uniform residual (the labels may be ignored). -/
theorem uniform_bind_programmed {Result : Type} (secrets : Secrets) (next : (U → HashOutput) → ProbComp Result) :
    𝒮[do let table ← ($ᵗ (U → HashOutput) : ProbComp _); next table] =
      𝒮[do
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (programmed U hU secrets labels residual)] :=
  graph_bind_eq_uniform_programmed U hU secrets (fun _ table => next table)

end Laws

/-! ## Private split: secrets ⊕ other private halves -/

def ftsCoordinate (f : FtsLeafPos) : ChainGraph.HalfCoordinate :=
  (.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)), ⟨f.leaf.val % 2, Nat.mod_lt _ (by decide)⟩)

def secretCoordinate : SecretIndex → ChainGraph.HalfCoordinate := Sum.elim ChainGraph.seedCoordinate ftsCoordinate

theorem ftsCoordinate_injective : Function.Injective ftsCoordinate := by
  intro left right heq
  have hp := congrArg Prod.fst heq
  have hh := congrArg (fun coordinate : ChainGraph.HalfCoordinate => coordinate.2.val) heq
  change Sum.inl (header 8 left.coord.val left.index.val 0 (left.leaf.val / 2)) =
    (Sum.inl (header 8 right.coord.val right.index.val 0 (right.leaf.val / 2)) : Coordinate) at hp
  change left.leaf.val % 2 = right.leaf.val % 2 at hh
  have hl := left.coord.isLt
  have hr := right.coord.isLt
  have hlt := left.index.isLt
  have hrt := right.index.isLt
  have hli := left.leaf.isLt
  have hri := right.leaf.isLt
  have fields := header_injective (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega)
    (by decide : 8 < 256) (by omega) (by omega) (by omega) (by omega) (Sum.inl.inj hp)
  obtain ⟨index, coord, leaf⟩ := left
  obtain ⟨index', coord', leaf'⟩ := right
  simp only at fields hh
  have e1 : index = index' := Fin.ext fields.2.2.1
  have e2 : coord = coord' := Fin.ext fields.2.1
  have e3 : leaf = leaf' := Fin.ext (by have := fields.2.2.2.2; omega)
  rw [e1, e2, e3]

theorem secretCoordinate_injective : Function.Injective secretCoordinate := by
  intro left right heq
  cases left with
  | inl a =>
      cases right with
      | inl b => exact congrArg Sum.inl (ChainGraph.seedCoordinate_injective heq)
      | inr g =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 0 a.layer.val a.tree.val (a.chain.val / 2) a.leaf.val) =
            (Sum.inl (header 8 g.coord.val g.index.val 0 (g.leaf.val / 2)) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
  | inr f =>
      cases right with
      | inl b =>
          exfalso
          have hp := congrArg Prod.fst heq
          change Sum.inl (header 8 f.coord.val f.index.val 0 (f.leaf.val / 2)) =
            (Sum.inl (header 0 b.layer.val b.tree.val (b.chain.val / 2) b.leaf.val) : Coordinate) at hp
          exact QuerySpace.header_ne_of_tag (by decide) (Sum.inl.inj hp)
      | inr g => exact congrArg Sum.inr (ftsCoordinate_injective heq)

def privateSecrets (table : FullGame.FullTable) : Secrets := ChainGraph.halves table ∘ secretCoordinate

abbrev OtherHalf := {coordinate : ChainGraph.HalfCoordinate // coordinate ∉ Set.range secretCoordinate}
abbrev OtherHalves := OtherHalf → Digest

noncomputable def splitEquiv : ChainGraph.HalfTable ≃ Secrets × OtherHalves :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range secretCoordinate)).symm.trans
    ((Equiv.ofInjective secretCoordinate secretCoordinate_injective).symm.sumCongr (Equiv.refl OtherHalf)))
    (Equiv.refl Digest)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

theorem splitEquiv_fst (table : ChainGraph.HalfTable) : (splitEquiv table).1 = table ∘ secretCoordinate := by
  funext index
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]

/-- Exact split of the whole private table into the secrets and every other private half. -/
noncomputable def privateEquiv : FullGame.FullTable ≃ Secrets × OtherHalves :=
  ChainGraph.halvesEquiv.trans splitEquiv

theorem privateEquiv_fst (table : FullGame.FullTable) : (privateEquiv table).1 = privateSecrets table :=
  splitEquiv_fst (ChainGraph.halves table)

theorem privateSecrets_symm (secrets : Secrets) (other : OtherHalves) :
    privateSecrets (privateEquiv.symm (secrets, other)) = secrets := by
  rw [← privateEquiv_fst, Equiv.apply_symm_apply]

set_option warn.classDefReducibility false in
/-- A fixed (irreducible) enumeration of SEC's encoding keys; unifying the product instance directly
exhausts the recursion limit. -/
noncomputable def encodingKeyFintype : Fintype QuerySpace.EncodingKey := inferInstance

attribute [irreducible] encodingKeyFintype

/-- Every encoding search row of SEC's `Presampling` key space. -/
noncomputable def encInputs : Finset HashInput :=
  (@Finset.univ _ encodingKeyFintype).image QuerySpace.encodingQuery

attribute [irreducible] encInputs

theorem encodingQuery_mem (key : QuerySpace.EncodingKey) : QuerySpace.encodingQuery key ∈ encInputs := by
  rw [encInputs]
  exact Finset.mem_image_of_mem _ (@Finset.mem_univ _ encodingKeyFintype key)

theorem encInputs_subset_publicUniverse : encInputs ⊆ SeccLaw.publicUniverse := by
  intro input hinput
  rw [encInputs, Finset.mem_image] at hinput
  obtain ⟨key, -, rfl⟩ := hinput
  apply SeccLaw.mem_publicUniverse
  simp only [QuerySpace.encodingQuery, Sampling.encodingTrial_length, SeccLaw.maxInputLength]
  omega

/-- The finite public universe of the recorded game: canonical cells, encoding rows, and SEC's `recordedInputs`. -/
noncomputable def canonUniverse {α : Type} (program : M α) : Finset HashInput :=
  canonInputs ∪ encInputs ∪ ChainGraph.recordedInputs program

attribute [irreducible] canonUniverse

theorem canonInputs_subset_universe {α : Type} (program : M α) : canonInputs ⊆ canonUniverse program := by
  rw [canonUniverse]
  exact Finset.subset_union_left.trans Finset.subset_union_left

theorem encInputs_subset_universe {α : Type} (program : M α) : encInputs ⊆ canonUniverse program := by
  rw [canonUniverse]
  exact Finset.subset_union_right.trans Finset.subset_union_left

theorem recordedInputs_subset_universe {α : Type} (program : M α) :
    ChainGraph.recordedInputs program ⊆ canonUniverse program := by
  rw [canonUniverse]
  exact Finset.subset_union_right

section PrivateLaws
noncomputable local instance instFintypeCoordinate_canonGraph : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonGraph : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeHashOutput_canonGraph_1 : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeLabels_1 : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves : SampleableType OtherHalves := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdSecretsOtherHalves : SampleableType (Secrets × OtherHalves) := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _

theorem uniform_private_split :
    𝒮[privateEquiv <$> ($ᵗ FullGame.FullTable : ProbComp _)] =
      𝒮[do let secrets ← ($ᵗ Secrets : ProbComp _); let other ← ($ᵗ OtherHalves : ProbComp _); pure (secrets, other)] :=
  (evalSPMF_map_bijective_uniform_cross (α := FullGame.FullTable) (β := Secrets × OtherHalves)
    privateEquiv privateEquiv.bijective).trans (FullGame.uniform_product (A := Secrets) (B := OtherHalves)).symm

theorem private_bind {Result : Type} (next : FullGame.FullTable → ProbComp Result) :
    𝒮[do let table ← ($ᵗ FullGame.FullTable : ProbComp _); next table] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        next (privateEquiv.symm (secrets, other))] := by
  have h := congrArg (fun law : SPMF (Secrets × OtherHalves) =>
    law >>= fun result => 𝒮[next (privateEquiv.symm result)]) uniform_private_split
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply] using h

/-- **Joint law of the eager tables**: secrets, other private halves, labels and residual public rows are
independent and uniform; the public table is the residual with the canonical cells programmed. -/
theorem tables_bind {Result : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
        next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels residual)] := by
  rw [private_bind (fun privateTable => do
    let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
    next privateTable publicTable)]
  apply evalSPMF_bind_congr_left
  intro secrets
  apply evalSPMF_bind_congr_left
  intro other
  exact uniform_bind_programmed U hU secrets (fun table => next (privateEquiv.symm (secrets, other)) table)

/-- **Recorded-game law** (SEC's `recorded_finite_law` with canonical labels). -/
theorem recorded_canon_law {α : Type} (program : M α) :
    𝒮[FirstHit.record program (∅, ∅)] =
      𝒮[do
        let secrets ← ($ᵗ Secrets : ProbComp _)
        let other ← ($ᵗ OtherHalves : ProbComp _)
        let labels ← ($ᵗ Labels : ProbComp _)
        let residual ← ($ᵗ (canonUniverse program → HashOutput) : ProbComp _)
        ChainGraph.finiteRecorded (privateEquiv.symm (secrets, other)) (canonUniverse program)
          (programmed (canonUniverse program) (canonInputs_subset_universe program) secrets labels residual)
          program] := by
  rw [ChainGraph.recorded_finite_tables program (canonUniverse program) (fun privateTable =>
    (ChainGraph.program_subset_recordedInputs program privateTable).trans (recordedInputs_subset_universe program))]
  exact tables_bind (canonUniverse program) (canonInputs_subset_universe program)
    (fun privateTable publicTable => ChainGraph.finiteRecorded privateTable (canonUniverse program) publicTable program)

/-! ### Low/high halves of the labels (the hidden honest values are the low halves) -/

abbrev LowLabels := Node → Digest

noncomputable def labelPairEquiv : Labels ≃ LowLabels × LowLabels :=
  (Equiv.arrowCongr (Equiv.refl Node) ChainGraph.outputEquiv).trans
    (Equiv.arrowProdEquivProdArrow Node (fun _ => Digest) (fun _ => Digest))

/-- Labels from their low (honest value) and high halves. -/
noncomputable def joinLabels (low high : LowLabels) : Labels :=
  fun node => ChainGraph.joinOutput (low node) (high node)

theorem labelPairEquiv_symm (low high : LowLabels) : labelPairEquiv.symm (low, high) = joinLabels low high := rfl

theorem joinLabels_low (low high : LowLabels) (node : Node) :
    (joinLabels low high node).extractLsb' 0 128 = low node := ChainGraph.joinOutput_low _ _

theorem joinLabels_high (low high : LowLabels) (node : Node) :
    (joinLabels low high node).extractLsb' 128 128 = high node := ChainGraph.joinOutput_high _ _

noncomputable local instance instSampleableTypeLowLabels : SampleableType LowLabels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeProdLowLabels : SampleableType (LowLabels × LowLabels) := SampleableType.ofFintype _

/-- The honest values (low halves) and the high halves of the labels are independent uniform tables. -/
theorem labels_bind {Result : Type} (next : Labels → ProbComp Result) :
    𝒮[do let labels ← ($ᵗ Labels : ProbComp _); next labels] =
      𝒮[do
        let low ← ($ᵗ LowLabels : ProbComp _)
        let high ← ($ᵗ LowLabels : ProbComp _)
        next (joinLabels low high)] := by
  have hpair : 𝒮[labelPairEquiv <$> ($ᵗ Labels : ProbComp _)] =
      𝒮[do let low ← ($ᵗ LowLabels : ProbComp _); let high ← ($ᵗ LowLabels : ProbComp _); pure (low, high)] :=
    (evalSPMF_map_bijective_uniform_cross (α := Labels) (β := LowLabels × LowLabels)
      labelPairEquiv labelPairEquiv.bijective).trans (FullGame.uniform_product (A := LowLabels) (B := LowLabels)).symm
  have h := congrArg (fun law : SPMF (LowLabels × LowLabels) =>
    law >>= fun result => 𝒮[next (labelPairEquiv.symm result)]) hpair
  simpa only [evalSPMF_map, evalSPMF_bind, bind_map_left, evalSPMF_pure, bind_assoc, pure_bind,
    Equiv.symm_apply_apply, labelPairEquiv_symm] using h

end PrivateLaws

/-! ## Answers tables agreeing with the graph -/

/-- The eager answers of a private and a finite public table (coins answer 0, inputs outside `U` answer 0). -/
noncomputable def eagerAnswers (privateTable : FullGame.FullTable) (U : Finset HashInput)
    (publicTable : U → HashOutput) : Answers
  | .inl (.inl n) => (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inl (.inr input) => finiteHashAnswer ∅ U publicTable input
  | .inr coordinate => privateTable coordinate

/-- FTS secret half of a private answer (Core's `buildFts`: pair `leaf / 2`, half `leaf % 2`). -/
def ftsSecretOf (answers : Answers) (f : FtsLeafPos) : Digest :=
  let pair := evalWithAnswerFn answers (privatePair 8 f.coord.val f.index.val 0 (f.leaf.val / 2))
  if f.leaf.val % 2 = 0 then pair.1 else pair.2

/-- The secrets of an answers table (its private part only). -/
def secretsOf (answers : Answers) : Secrets
  | .inl a => leafSeed answers a.layer a.tree.val a.leaf.val a.chain.val
  | .inr f => ftsSecretOf answers f

/-- The answers table answers every canonical cell (built with its own secrets) with the label. -/
def Agrees (answers : Answers) (labels : Labels) : Prop :=
  ∀ node, answers (.inl (.inr (cell (secretsOf answers) node labels))) = labels node

theorem secretsOf_eager (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput) :
    secretsOf (eagerAnswers privateTable U publicTable) = privateSecrets privateTable := by
  funext index
  cases index with
  | inl a => rfl
  | inr f => rfl

theorem eagerAnswers_mem (privateTable : FullGame.FullTable) (U : Finset HashInput) (publicTable : U → HashOutput)
    (x : U) : eagerAnswers privateTable U publicTable (.inl (.inr x.val)) = publicTable x :=
  finiteHashAnswer_none ∅ U publicTable x.val x.property rfl

/-- Any answers table whose public part on `U` is a programmed table (built with its own secrets) agrees. -/
theorem agrees_of_programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (answers : Answers)
    (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x) :
    Agrees answers labels := by
  intro node
  have h := hpub (cellIn U hU (secretsOf answers) node labels)
  rw [programmed_at] at h
  exact h

theorem eager_programmed_agrees (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets)
    (other : OtherHalves) (labels : Labels) (residual : U → HashOutput) :
    Agrees (eagerAnswers (privateEquiv.symm (secrets, other)) U (programmed U hU secrets labels residual)) labels := by
  apply agrees_of_programmed U hU _ labels residual
  intro x
  rw [secretsOf_eager, privateSecrets_symm, eagerAnswers_mem]

theorem eager_graph_agrees (privateTable : FullGame.FullTable) (U : Finset HashInput) (hU : canonInputs ⊆ U)
    (table : U → HashOutput) :
    Agrees (eagerAnswers privateTable U table) (graph U hU (privateSecrets privateTable) table) := by
  intro node
  rw [secretsOf_eager]
  exact (eagerAnswers_mem privateTable U table _).trans (graph_consistent U hU _ table node).symm

/-- The public part of the eager programmed answers is the programmed table (the `hpub` hypothesis of the
bridges, for `eagerAnswers`). -/
theorem eager_hpub (U : Finset HashInput) (hU : canonInputs ⊆ U) (secrets : Secrets) (other : OtherHalves)
    (labels : Labels) (residual : U → HashOutput) (x : U) :
    eagerAnswers (privateEquiv.symm (secrets, other)) U (programmed U hU secrets labels residual) (.inl (.inr x.val)) =
      programmed U hU (secretsOf (eagerAnswers (privateEquiv.symm (secrets, other)) U
        (programmed U hU secrets labels residual))) labels residual x := by
  rw [secretsOf_eager, privateSecrets_symm, eagerAnswers_mem]

/-- The shared completion (`SeccLaw.completeWith`) of the empty cache is the eager answers table on
`SeccLaw.publicUniverse`. -/
theorem completeWith_empty (tables : SeccLaw.CompletionTables) :
    SeccLaw.completeWith (∅, ∅) tables = eagerAnswers tables.1 SeccLaw.publicUniverse tables.2 := by
  funext input
  rcases input with (n | input) | coordinate
  · rfl
  · rfl
  · rfl

/-- The chain part of `Agrees` is SEC's `ChainGraph.Agrees`. -/
theorem agrees_chain {answers : Answers} {labels : Labels} (h : Agrees answers labels) :
    ChainGraph.Agrees answers (ChainGraph.sourceSeeds answers) (chainLabels labels) :=
  fun point => h (.chain point)

end SigGolfCandidate.T3.Security.CanonGraph
