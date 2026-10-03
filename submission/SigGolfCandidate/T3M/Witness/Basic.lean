import SigGolfCandidate.T3M.Witness.VerifyP
import SigGolfCandidate.T3.PackedChain

/-! # Basic facts about the padded formats (stream W): at zero pads they are Core's formats. -/
namespace SigGolfCandidate.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
set_option maxRecDepth 10000

open SphincsSecurity (bytesLE) in
theorem bytesLE_zero16 : bytesLE 16 (0 : Digest) = zero16 := by decide

@[simp] theorem Pads.zero_leaf (s : Fin 22) : (0 : Pads).leaf s = 0 := rfl
@[simp] theorem Pads.zero_fold (k : Fin 115) : (0 : Pads).fold k = 0 := rfl
@[simp] theorem Pads.zero_chain (lay : Layer) (i : Fin (chainCount lay)) : (0 : Pads).chain lay i = (0, 0) := rfl
@[simp] theorem Pads.zero_merkle (lay : Layer) (j : Fin (height lay)) : (0 : Pads).merkle lay j = 0 := rfl
@[simp] theorem Pads.zero_chainHeader (lay : Layer) (i : Fin (chainCount lay)) :
    (0 : Pads).chainHeader lay i = 0 := rfl

@[simp] theorem ftsLeafP_zero (index coord leaf : Nat) (secret : Digest) :
    ftsLeafP index coord leaf 0 secret 0 = ftsLeaf index coord leaf secret := by
  simp only [ftsLeafP, ftsLeaf, bytesLE_zero16]

@[simp] theorem nodeHashP_zero (tag lay tree heap : Nat) (left right : Digest) :
    nodeHashP tag lay tree heap left 0 right = nodeHash tag lay tree heap left right := by
  simp only [nodeHashP, nodeHash, bytesLE_zero16]

/-- Reassemble the full source header without assumptions on coordinates. -/
theorem chainHeaderP_source (lay : Layer) (tree leaf i step : Nat) :
    chainHeaderP lay tree leaf i step ((chainHeader lay tree leaf i step).extractLsb' 64 64) =
      chainHeader lay tree leaf i step := BitVec.extractLsb'_append_extractLsb'

private theorem extract_high_zero (x : Digest) (h : x.toNat / 2^64 = 0) :
    x.extractLsb' 64 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  change (x.extractLsb' 64 64).toNat = (0 : Nat)
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, h]

theorem chainHeader_high_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 64 64 = 0 :=
  extract_high_zero _ (T3.chainHeader_high_zero lay tree leaf i step ht hl hi hs)

@[simp] theorem chainHeaderP_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    chainHeaderP lay tree leaf i step 0 = chainHeader lay tree leaf i step := by
  rw [← chainHeader_high_zero lay tree leaf i step ht hl hi hs]
  exact chainHeaderP_source _ _ _ _ _

private theorem fold_steps_eq {α β : Type} (f g : β → α → M β) (xs : List α)
    (h : ∀ s ∈ xs, ∀ v, f v s = g v s) (v : β) :
    xs.foldlM f v = xs.foldlM g v := by
  induction xs generalizing v with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.foldlM_cons]
      rw [h s (by simp)]
      apply congrArg (fun k : β → M β => g v s >>= k)
      funext next
      exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) next

theorem chainP_zero (lay : Layer) (tree leaf i start count : Nat) (value : Digest)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64)
    (hsteps : count = 0 ∨ start + count ≤ 8) :
    chainP lay tree leaf i start count 0 0 0 value = chain lay tree leaf i start count value := by
  apply fold_steps_eq
  intro s hs v
  have hs8 : s < 8 := by
    have := List.mem_range'_1.mp hs
    rcases hsteps with hzero | hbound <;> omega
  simp only [chainInputP, chainInput, bytesLE_zero16,
    chainHeaderP_zero _ _ _ _ _ ht hl hi hs8]

theorem route_packed_bound (index : Nat) (lay : Layer) (hindex : index < 2^31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2^32 := by
  fin_cases lay <;> simp [route, height] <;> omega

theorem chainP_zero_route (index : Nat) (lay : Layer) (i : Fin (chainCount lay))
    (digit : Nat) (value : Digest) (hindex : index < 2^31) :
    chainP lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) 0 0 0 value =
    chain lay (route index lay).2 (route index lay).1 i.val digit
      (maxDigit lay i.val - digit) value := by
  have hi := i.isLt
  apply chainP_zero
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [route, height] <;> omega
  · fin_cases lay <;> simp [chainCount] at hi <;> omega
  · have hm : maxDigit lay i.val ≤ 7 := by unfold maxDigit; split_ifs <;> decide
    omega


@[simp] theorem foldPad_zero (leaves : List Nat) (level node used next : Nat) :
    foldPad 0 leaves level node used next = 0 := by
  unfold foldPad; split <;> [rfl; split <;> rfl]

end SigGolfCandidate.T3M
