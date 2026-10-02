import SigGolfCandidate.T3M.Witness.VerifyP

/-! # Basic facts about the padded formats (stream W): at zero pads they are Core's formats. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3

open SphincsSecurity (bytesLE) in
theorem bytesLE_zero16 : bytesLE 16 (0 : Digest) = zero16 := by decide

@[simp] theorem Pads.zero_leaf (s : Fin 22) : (0 : Pads).leaf s = 0 := rfl
@[simp] theorem Pads.zero_fold (k : Fin 117) : (0 : Pads).fold k = 0 := rfl
@[simp] theorem Pads.zero_chain (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl

@[simp] theorem ftsLeafP_zero (index coord leaf : Nat) (secret : Digest) :
    ftsLeafP index coord leaf 0 secret 0 = ftsLeaf index coord leaf secret := by
  simp only [ftsLeafP, ftsLeaf, bytesLE_zero16]

@[simp] theorem nodeHashP_zero (tag lay tree heap : Nat) (left right : Digest) :
    nodeHashP tag lay tree heap left 0 right = nodeHash tag lay tree heap left right := by
  simp only [nodeHashP, nodeHash, bytesLE_zero16]

@[simp] theorem chainP_zero (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    chainP lay tree leaf i start count 0 0 value = chain lay tree leaf i start count value := by
  simp only [chainP, chain, chainInputP, chainInput, bytesLE_zero16]

@[simp] theorem foldPad_zero (leaves : List Nat) (level node used next : Nat) :
    foldPad 0 leaves level node used next = 0 := by
  unfold foldPad; split <;> [rfl; split <;> rfl]

end SigGolfCandidate.T3M
