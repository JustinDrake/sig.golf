import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes

namespace SphincsSecurity
open OracleComp
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (heap : Fin (2 ^ ftsTreeHeight))
  deriving DecidableEq, Fintype
namespace Position
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .ftsLeaf index tree leafIdx => HashDomain.ftsLeaf index tree leafIdx.val
  | .ftsNode index tree heap => HashDomain.ftsNode index tree heap.val
theorem domain_inRange (p : Position) : p.domain.InRange := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | ftsNode index tree heap =>
      have hheap := heap.isLt
      simp only [ftsTreeHeight] at hheap
      show heap.val < 2 ^ 32
      omega
  | ftsLeaf index tree leafIdx =>
      have hleaf := leafIdx.isLt
      simp only [ftsTreeHeight] at hleaf
      show leafIdx.val < 2 ^ 32
      omega
  | chain => exact (trivial : True)
  | leaf => exact (trivial : True)
theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]
def lastChainStep : ChainStep := ⟨chainLength - 2, by have := OtsCode.two_le_chainLength; omega⟩
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsLeaf _ _ _ => []
  | .ftsNode index tree heap =>
      if hpos : 0 < heap.val then
        if hidx : 2 * heap.val + 1 < 2 ^ ftsTreeHeight then
          [.ftsNode index tree ⟨2 * heap.val, by omega⟩, .ftsNode index tree ⟨2 * heap.val + 1, hidx⟩]
        else
          [.ftsLeaf index tree ⟨2 * heap.val - 2 ^ ftsTreeHeight, by have := heap.isLt; omega⟩,
            .ftsLeaf index tree ⟨2 * heap.val + 1 - 2 ^ ftsTreeHeight, by have := heap.isLt; omega⟩]
      else []
theorem children_length_le (p : Position) : p.children.length ≤ numChains := by
  have htwo := OtsCode.two_le_numChains
  cases p <;> simp only [children] <;> (try split_ifs) <;>
    simp only [List.length_ofFn, List.length_cons, List.length_nil] <;> omega
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .ftsLeaf _ _ _ => 0
  | .ftsNode _ _ heap => ftsTreeHeight - Nat.log2 heap.val
theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      have := OtsCode.two_le_chainLength
      simp only [depth, lastChainStep]
      omega
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsLeaf => simp [children] at hmem
  | ftsNode index tree heap =>
      rw [children] at hmem
      have hheap := heap.isLt
      split at hmem
      · rename_i hpos
        have hlog : Nat.log2 heap.val < ftsTreeHeight := by
          rw [Nat.log2_lt (by omega)]; exact hheap
        split at hmem
        · rename_i hidx
          rcases List.mem_pair.mp hmem with h | h <;> subst h <;> simp only [depth]
          · have : Nat.log2 (2 * heap.val) = Nat.log2 heap.val + 1 := by
              exact Nat.log2_two_mul (by omega)
            omega
          · have : Nat.log2 (2 * heap.val + 1) = Nat.log2 heap.val + 1 := by
              rw [Nat.log2_def, if_pos (by omega), show (2 * heap.val + 1) / 2 = heap.val by omega]
            omega
        · rcases List.mem_pair.mp hmem with h | h <;> subst h <;> simp only [depth] <;> omega
      · simp at hmem
end Position
end SphincsSecurity
