import SigGolfCandidate.SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef
import SigGolfCandidate.SphincsSecurity.Proof.Ots.Code

section


namespace SphincsSecurity.Concrete
open ENNReal
irreducible_def ftsOpenHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1
irreducible_def ftsKeyHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1
theorem two_pow_ftsTreeHeight_le_ftsOpenHashCost : 2 ^ ftsTreeHeight ≤ ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  decide
theorem ftsOpenHashCost_le_digestAttemptLimit : ftsOpenHashCost ≤ digestAttemptLimit := by
  rw [ftsOpenHashCost_def]
  decide
irreducible_def fixedProposalLength : Nat := 6455164942
irreducible_def proposalPrefixSlack : Nat := 2 ^ 23
noncomputable irreducible_def fullCertificateExcessRate : ENNReal := 1 / 2 ^ 144
noncomputable irreducible_def nearCertificatePrice : ENNReal := ((1241 : ENNReal) / 15) / (2 ^ 128 : Nat)
noncomputable irreducible_def proposalPrefixExceptionBound : ENNReal := (2 ^ 700 : ENNReal)⁻¹
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
irreducible_def oneTimeKeyHashCost : Nat := numChains * (chainLength - 1)
irreducible_def treeNodeHashCost (level : Nat) : Nat := (oneTimeKeyHashCost + 2) * 2 ^ level - 1
irreducible_def keygenHashCost : Nat := treeNodeHashCost (layerHeight topLayer)
theorem treeNodeHashCost_zero : treeNodeHashCost 0 = oneTimeKeyHashCost + 1 := by
  rw [treeNodeHashCost_def, pow_zero, mul_one]
  omega
theorem treeNodeHashCost_succ (level : Nat) :
    treeNodeHashCost (level + 1) = treeNodeHashCost level + (treeNodeHashCost level + 1) := by
  simp only [treeNodeHashCost_def, pow_succ, ← mul_assoc]
  have hpos : 0 < (oneTimeKeyHashCost + 2) * 2 ^ level := by positivity
  generalize (oneTimeKeyHashCost + 2) * 2 ^ level = nodes at hpos ⊢
  omega
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open ENNReal
irreducible_def budgetSplit : Nat := 3 * 2 ^ 114
noncomputable irreducible_def primitiveCoefficient : ENNReal := 7 / 4
theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num
end SphincsSecurity.Concrete
end

section




namespace SphincsSecurity
theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> (try split) <;> omega
abbrev Signature.counter (signature : Signature) (lay : Layer) : Counter :=
  (signature.layers lay).counter
abbrev Signature.chainValue (signature : Signature) (lay : Layer) : ChainIndex → Digest :=
  (signature.layers lay).chainValues
abbrev PaddedLayer := Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)
abbrev LayerSignature.ofPadded (lay : Layer) (part : PaddedLayer) : LayerSignature lay :=
  ⟨part.1, part.2.1, fun level => part.2.2 (level.castLE (layerHeight_le lay))⟩
@[ext]
theorem LayerSignature.ext {lay : Layer} {left right : LayerSignature lay}
    (hcounter : left.counter = right.counter) (hvalues : left.chainValues = right.chainValues)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  simp_all
end SphincsSecurity
end
