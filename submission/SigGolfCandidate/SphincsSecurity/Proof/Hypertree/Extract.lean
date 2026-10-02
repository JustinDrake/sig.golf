import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Arith
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
/-!
# Extracting the first divergence

The deterministic half of the reduction, for one layer's tree. If a fold on values an adversary
supplies reaches the honest node above the leaf, then either every value it supplied was the honest
one, or at some level it hashed something other than the honest payload to the honest value. The
second is what the union bound charges; the first is what makes the adversary's signature the honest
one, and so no forgery.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest)

/-- The value the honest tree carries at a position. -/
def honestNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx)

/-- What the fold has reached after `levels` steps. -/
def foldValue (value : Digest) (levels : Nat) : Digest :=
  evalWithAnswerFn f (treeFold parameter lay tree leaf path levels value)

/-- Two children in the order the bit dictates. Written with `Bool.rec` rather than `if`, so that
both cases hold by `rfl` and rewriting the bit needs no reasoning about `Decidable` instances. -/
def orderedPayload (bit : Bool) (current sibling : Digest) : HashInput :=
  bit.rec (nodePayload current sibling) (nodePayload sibling current)

@[simp] theorem orderedPayload_false (current sibling : Digest) :
    orderedPayload false current sibling = nodePayload current sibling := rfl

@[simp] theorem orderedPayload_true (current sibling : Digest) :
    orderedPayload true current sibling = nodePayload sibling current := rfl

/-- The payload the fold hashes on its way from `level` to `level + 1`. -/
def treeFoldPayload (value : Digest) (level : Nat) : HashInput :=
  orderedPayload (leaf.val.testBit level)
    (foldValue f parameter lay tree leaf path value level) (path level)

theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn f (tweakableHash parameter domain payload)
      = truncateHash (f (tweakableHashInput parameter domain payload)) := by
  simp only [tweakableHash, oracleHash, evalWithAnswerFn_bind, evalWithAnswerFn_query,
    evalWithAnswerFn_pure]

theorem honestNode_succ (level nodeIdx : Nat) :
    honestNode f parameter lay tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx)
          (nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
            (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestNode, treeNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem foldValue_succ (value : Digest) (level : Nat) :
    foldValue f parameter lay tree leaf path value (level + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.node lay tree (level + 1) (leaf.val / 2 ^ (level + 1)))
          (treeFoldPayload f parameter lay tree leaf path value level))) := by
  simp only [foldValue, treeFoldPayload, treeFold_succ_eq, evalWithAnswerFn_bind, orderedPayload]
  cases leaf.val.testBit level <;> rfl

/-- A hit at a node position: something other than the honest payload hashing to the honest value
there. Domain separation makes the target a function of the position alone, which is what lets the
union bound charge it. -/
def NodeHit (level nodeIdx : Nat) (payload : HashInput) : Prop :=
  payload ≠ nodePayload (honestNode f parameter lay tree secret level (2 * nodeIdx))
      (honestNode f parameter lay tree secret level (2 * nodeIdx + 1))
    ∧ truncateHash (f (tweakableHashInput parameter (.node lay tree (level + 1) nodeIdx) payload))
      = honestNode f parameter lay tree secret (level + 1) nodeIdx

/-- **The first divergence.** A fold that reaches the honest node above the leaf either used the
honest leaf and the honest siblings throughout, or hit a node value somewhere along the way. -/
theorem treeFold_extract (value : Digest) (levels : Nat)
    (hfold : foldValue f parameter lay tree leaf path value levels
      = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)) :
    (value = honestNode f parameter lay tree secret 0 leaf.val
        ∧ ∀ level, level < levels → path level
            = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < levels
          ∧ NodeHit f parameter lay tree secret level (leaf.val / 2 ^ (level + 1))
              (treeFoldPayload f parameter lay tree leaf path value level) := by
  induction levels with
  | zero =>
      left
      refine ⟨?_, fun level hlevel => absurd hlevel (by omega)⟩
      simpa [foldValue] using hfold
  | succ levels ih =>
      obtain ⟨j, hcase⟩ := index_sibling_cases (leaf.val / 2 ^ levels)
      have hj : leaf.val / 2 ^ (levels + 1) = j := by
        rw [div_pow_succ]
        rcases hcase with ⟨hc, _, _⟩ | ⟨hc, _, _⟩ <;> omega
      have hhash : truncateHash (f (tweakableHashInput parameter
            (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
            (treeFoldPayload f parameter lay tree leaf path value levels)))
          = honestNode f parameter lay tree secret (levels + 1) (leaf.val / 2 ^ (levels + 1)) := by
        rw [← foldValue_succ]
        exact hfold
      by_cases hagree : treeFoldPayload f parameter lay tree leaf path value levels
          = nodePayload (honestNode f parameter lay tree secret levels (2 * j))
              (honestNode f parameter lay tree secret levels (2 * j + 1))
      · have hstep : foldValue f parameter lay tree leaf path value levels
              = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels)
            ∧ path levels = honestNode f parameter lay tree secret levels
              (Nat.xor (leaf.val / 2 ^ levels) 1) := by
          rw [treeFoldPayload] at hagree
          rcases hcase with ⟨hc, hsibling, hmod⟩ | ⟨hc, hsibling, hmod⟩
          · rw [show leaf.val.testBit levels = false by
              rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hcur, hsib⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
          · rw [show leaf.val.testBit levels = true by
              rw [testBit_iff_div_mod]; omega] at hagree
            obtain ⟨hsib, hcur⟩ := nodePayload_injective hagree
            exact ⟨by rw [hcur, hc], by rw [hsib, hsibling]⟩
        rcases ih hstep.1 with ⟨hvalue, hpaths⟩ | ⟨level, hlevel, hnode⟩
        · left
          refine ⟨hvalue, fun level hlevel => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · exact hpaths level hlt
          · subst heq; exact hstep.2
        · exact Or.inr ⟨level, by omega, hnode⟩
      · right
        exact ⟨levels, by omega, by rw [hj]; exact hagree, hhash⟩

/-! ### The root's two children

The fold stops below the root: what it hands the layer above is the node it reached and the path's top
sibling, in order. If that pair is the honest one, the fold reached the honest node below the root and
the top sibling is honest, and the extraction continues from there. -/

/-- The honest tree's two children of the root. -/
def honestPair : EncMessage :=
  (honestNode f parameter lay tree secret (layerHeight lay - 1) 0,
    honestNode f parameter lay tree secret (layerHeight lay - 1) 1)

theorem eval_treeTop :
    evalWithAnswerFn f (treeTop parameter lay tree secret) = honestPair f parameter lay tree secret := by
  simp only [treeTop, evalWithAnswerFn_bind, evalWithAnswerFn_pure, honestNode, honestPair]

/-- What the fold hands the layer above: the node after `h - 1` levels and the path's top sibling, in
order. -/
def foldPair (value : Digest) : EncMessage :=
  topPair (leaf.val.testBit (layerHeight lay - 1))
    (foldValue f parameter lay tree leaf path value (layerHeight lay - 1)) (path (layerHeight lay - 1))

/-- A fold that hands up the honest pair reached the honest node below the root, next to the honest top
sibling. -/
theorem foldPair_extract (hleaf : leaf.val < 2 ^ layerHeight lay) (hheight : 0 < layerHeight lay)
    (value : Digest)
    (htop : foldPair f parameter lay tree leaf path value = honestPair f parameter lay tree secret) :
    foldValue f parameter lay tree leaf path value (layerHeight lay - 1)
        = honestNode f parameter lay tree secret (layerHeight lay - 1)
            (leaf.val / 2 ^ (layerHeight lay - 1))
      ∧ path (layerHeight lay - 1)
        = honestNode f parameter lay tree secret (layerHeight lay - 1)
            (Nat.xor (leaf.val / 2 ^ (layerHeight lay - 1)) 1) := by
  have hpow : 2 * 2 ^ (layerHeight lay - 1) = 2 ^ layerHeight lay := by
    conv_rhs => rw [← Nat.sub_add_cancel hheight, Nat.pow_succ']
  have hlt : leaf.val / 2 ^ (layerHeight lay - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hpow]
    exact hleaf
  simp only [foldPair, honestPair, topPair] at htop
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
  · have hzero : leaf.val / 2 ^ (layerHeight lay - 1) = 0 := Nat.lt_one_iff.mp h0
    rw [show leaf.val.testBit (layerHeight lay - 1) = false by
      rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod, hzero]; decide] at htop
    rw [hzero]
    simp only [Bool.false_eq_true, if_false, Prod.mk.injEq] at htop
    exact ⟨htop.1, htop.2⟩
  · rw [show leaf.val.testBit (layerHeight lay - 1) = true by
      rw [testBit_iff_div_mod, h1]] at htop
    rw [h1]
    simp only [if_true, Prod.mk.injEq] at htop
    exact ⟨htop.2, htop.1⟩

/-- **The first divergence below the root.** A fold that hands up the honest pair either used the honest
leaf and the honest siblings at every level, the top sibling included, or hit a node value at some level
below the root. -/
theorem foldPair_extract_all (hleaf : leaf.val < 2 ^ layerHeight lay) (hheight : 0 < layerHeight lay)
    (value : Digest)
    (htop : foldPair f parameter lay tree leaf path value = honestPair f parameter lay tree secret) :
    (value = honestNode f parameter lay tree secret 0 leaf.val
        ∧ ∀ level, level < layerHeight lay → path level
            = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1))
      ∨ ∃ level, level < layerHeight lay - 1
          ∧ NodeHit f parameter lay tree secret level (leaf.val / 2 ^ (level + 1))
              (treeFoldPayload f parameter lay tree leaf path value level) := by
  obtain ⟨hnode, hsibling⟩ := foldPair_extract f parameter lay tree secret leaf path hleaf hheight value htop
  rcases treeFold_extract f parameter lay tree secret leaf path value (layerHeight lay - 1) hnode with
    ⟨hvalue, hpath⟩ | hhit
  · refine Or.inl ⟨hvalue, fun level hlevel => ?_⟩
    rcases Nat.lt_or_ge level (layerHeight lay - 1) with hlt | hge
    · exact hpath level hlt
    · have hlast : level = layerHeight lay - 1 := by omega
      rw [hlast]
      exact hsibling
  · exact Or.inr hhit

/-- **The top tree's last hash.** A pair that hashes to the honest root is the honest pair, or a hit at
the root. -/
theorem topRoot_extract (index : Index) (top : EncMessage)
    (hroot : evalWithAnswerFn f (topRoot parameter index top) =
      honestNode f parameter topLayer rootTree secret (layerHeight topLayer) 0) :
    top = honestPair f parameter topLayer rootTree secret
      ∨ NodeHit f parameter topLayer rootTree secret (layerHeight topLayer - 1) 0
          (nodePayload top.1 top.2) := by
  have htree : treeIndexAt index topLayer = rootTree := Fin.ext (treeIndexAt_topLayer index)
  rw [topRoot, eval_tweakableHash, htree] at hroot
  by_cases hagree : nodePayload top.1 top.2 =
      nodePayload (honestNode f parameter topLayer rootTree secret (layerHeight topLayer - 1) (2 * 0))
        (honestNode f parameter topLayer rootTree secret (layerHeight topLayer - 1) (2 * 0 + 1))
  · left
    obtain ⟨h1, h2⟩ := nodePayload_injective hagree
    exact Prod.ext h1 h2
  · right
    exact ⟨hagree, hroot⟩

/-- The converse: the honest node below the root and its honest sibling, in order, are the honest pair. -/
theorem topPair_honest (hleaf : leaf.val < 2 ^ layerHeight lay) (hheight : 0 < layerHeight lay) :
    topPair (leaf.val.testBit (layerHeight lay - 1))
        (honestNode f parameter lay tree secret (layerHeight lay - 1)
          (leaf.val / 2 ^ (layerHeight lay - 1)))
        (honestNode f parameter lay tree secret (layerHeight lay - 1)
          (Nat.xor (leaf.val / 2 ^ (layerHeight lay - 1)) 1))
      = honestPair f parameter lay tree secret := by
  have hpow : 2 * 2 ^ (layerHeight lay - 1) = 2 ^ layerHeight lay := by
    conv_rhs => rw [← Nat.sub_add_cancel hheight, Nat.pow_succ']
  have hlt : leaf.val / 2 ^ (layerHeight lay - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hpow]
    exact hleaf
  simp only [honestPair, topPair]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h0 | h1
  · have hzero : leaf.val / 2 ^ (layerHeight lay - 1) = 0 := Nat.lt_one_iff.mp h0
    rw [show leaf.val.testBit (layerHeight lay - 1) = false by
      rw [Bool.eq_false_iff, ne_eq, testBit_iff_div_mod, hzero]; decide, hzero]
    rfl
  · rw [show leaf.val.testBit (layerHeight lay - 1) = true by
      rw [testBit_iff_div_mod, h1], h1]
    rfl

end SphincsSecurity.Concrete
