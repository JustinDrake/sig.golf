import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries

section


namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem flatMap_bytes_injective : ∀ {xs ys : List Digest}, xs.length = ys.length →
    xs.flatMap (bytesLE 16) = ys.flatMap (bytesLE 16) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp only [bytesLE_length])
      rw [bytesLE_injective hxy, flatMap_bytes_injective (by simpa using hlen) hrest]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem listInput_injective {first first' : Digest} {hdr hdr' : BitVec 128} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (h : listInput first hdr rest = listInput first' hdr' rest') :
    first = first' ∧ hdr = hdr' ∧ rest = rest' := by
  unfold listInput at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hf, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hf, bytesLE_injective hh, flatMap_bytes_injective hlen hr⟩
theorem list_head_drop : ∀ (xs : List Digest), 0 < xs.length → xs.getD 0 0 :: xs.drop 1 = xs
  | _ :: _, _ => rfl
theorem listInput_lists {xs ys : List Digest} {hdr hdr' : BitVec 128} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr' (ys.drop 1))) :
    xs = ys ∧ hdr = hdr' := by
  have hl : (listInput (xs.getD 0 0) hdr (xs.drop 1)).length = (listInput (ys.getD 0 0) hdr' (ys.drop 1)).length := by
    rw [listInput_length, listInput_length, List.length_drop, List.length_drop, hlen]
  obtain ⟨hf, hh, hr⟩ := listInput_injective (by rw [List.length_drop, List.length_drop, hlen])
    (Sampling.pad64_inj_of_length hl h)
  refine ⟨?_, hh⟩
  rw [← list_head_drop xs (by omega), ← list_head_drop ys hpos, hf, hr]
theorem hdrBlock_prefix (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64 (input : HashInput) (h : 32 ≤ input.length) : hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4 (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix a b _
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  rw [hdrBlock_pad64 _ (by rw [listInput_length]; omega)]
  exact hdrBlock_prefix first hdr _
theorem leafHash_eq_shortHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl
theorem forestPk_eq_shortHash (index : Nat) (roots : List Digest) :
    WCT9.forestPk index roots = shortHash (forestInput index roots) := rfl
theorem listHash_extract (answers : Answers) (hdr : BitVec 128) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (hpos : 0 < ys.length)
    (reaches : evalWithAnswerFn answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1))) =
      evalWithAnswerFn answers (shortHash (listInput (ys.getD 0 0) hdr (ys.drop 1)))) :
    xs = ys ∨
      (HashHit answers (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1)))
          (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1))) ∧
        SameHeader (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))
          (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))) ∧
        .inl (.inr (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))) ∈
          queried answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1)))) := by
  by_cases heq : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))
  · exact Or.inl (listInput_lists hlen hpos heq).1
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · unfold SameHeader
      rw [hdrBlock_listInput, hdrBlock_listInput]
    · rw [queried_shortHash]
      exact List.mem_singleton_self _
theorem leafHash_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (ends honest : List Digest)
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (leafHash lay tree leaf ends) =
      evalWithAnswerFn answers (leafHash lay tree leaf honest)) :
    ends = honest ∨
      (HashHit answers (pad64 (leafInput lay tree leaf honest)) (pad64 (leafInput lay tree leaf ends)) ∧
        SameHeader (pad64 (leafInput lay tree leaf ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (leafInput lay tree leaf ends))) ∈ queried answers (leafHash lay tree leaf ends)) :=
  listHash_extract answers _ ends honest hlen hpos reaches
theorem forestPk_extract (answers : Answers) (index : Nat) (roots honest : List Digest)
    (hlen : roots.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index roots) =
      evalWithAnswerFn answers (WCT9.forestPk index honest)) :
    roots = honest ∨
      (HashHit answers (pad64 (forestInput index honest)) (pad64 (forestInput index roots)) ∧
        SameHeader (pad64 (forestInput index roots)) (pad64 (forestInput index honest)) ∧
        .inl (.inr (pad64 (forestInput index roots))) ∈ queried answers (WCT9.forestPk index roots)) :=
  listHash_extract answers _ roots honest hlen hpos reaches
theorem forestPk_honest_extract (answers : Answers) (index : Nat) (hidx : index < 2 ^ 40) (roots : List Digest)
    (hlen : roots.length = 9)
    (reaches : evalWithAnswerFn answers (WCT9.forestPk index roots) = honestForest answers index) :
    roots = ftsRootsHonest answers index ∨ HitIn answers (queried answers (WCT9.forestPk index roots)) := by
  rcases forestPk_extract answers index roots (ftsRootsHonest answers index)
      (by rw [hlen, ftsRootsHonest_length]) (by rw [ftsRootsHonest_length]; omega) reaches with h | ⟨hh, hs, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨.forest index, _, hidx, hq, hh, hs⟩
theorem queried_mapM_mem {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ (l : List α), ∀ a ∈ l, ∀ q ∈ queried answers (f a), q ∈ queried answers (l.mapM f)
  | [], _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, a, ha, q, hq => by
      rw [List.mapM_cons, queried_bind, queried_bind]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_append_left _ (queried_mapM_mem answers f xs a ha q hq))
end ClaudeWCT.W9.T3M.Extract
end

section

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  (∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      wmerklePad w lay j = 0) ∧
  (∀ i, i < chainCount lay →
    wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i → wchainPads w lay i = (0, 0)))
def layerChains (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wvalue w lay i.val)
theorem layerLeafP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerLeafP w index lay digits =
      (layerChains w index lay digits >>= leafHash lay (route index lay).2 (route index lay).1) := rfl
theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide
theorem merkle_honestInput (answers : Answers) (lay : Layer) (tree leaf step : Nat) :
    honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))) =
      pad64 (merkleInput 3 lay.val tree (height lay) leaf
        (fun j => treeValue (builtTree answers lay tree) j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0) step
        (treeValue (builtTree answers lay tree) step (leaf / 2 ^ step))) := by
  unfold merkleInput honestInput
  dsimp only
  rw [Correctness.sibling_pair (fun n => treeValue (builtTree answers lay tree) step n) (leaf / 2 ^ step),
    Correctness.div_pow_succ]
theorem hdrBlock_merkleInput (tag lay tree h leaf : Nat) (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    hdrBlock (pad64 (merkleInput tag lay tree h leaf path pads step value)) =
      bytesLE 16 (header tag lay tree 0 (2 ^ (h - step - 1) + leaf / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [pad64_nodeInputP, nodeInputP, hdrBlock_block4]
theorem hdrBlock_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) :
    hdrBlock (pad64 (chainInputP lay tree leaf i step pad0 pad1 value)) =
      bytesLE 16 (header 1 lay.val tree (step + 256 * i) leaf) := by
  rw [pad64_chainInputP, chainInputP_eq_block4, hdrBlock_block4]
theorem layerChains_queried (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (leaf tree : Nat) (hleaf : (route index lay).1 = leaf) (htree : (route index lay).2 = tree)
    (i : Nat) (hi : i < chainCount lay) :
    ∀ q ∈ queried answers (chainP lay tree leaf i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i)),
      q ∈ queried answers (layerChains w index lay digits) := by
  subst hleaf htree
  unfold layerChains
  exact queried_mapM_mem answers (fun i : Fin (chainCount lay) =>
    chainP lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wvalue w lay i.val)) (List.finRange (chainCount lay)) ⟨i, hi⟩ (List.mem_finRange _)
theorem map_finRange_val {β : Type} (n : Nat) (g : Nat → β) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [show (fun i : Fin n => g i.val) = g ∘ Fin.val from rfl, ← List.map_map, map_val_finRange]
theorem route_tree_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) : (route index lay).2 < 2 ^ 40 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; split_ifs <;> omega
theorem layerP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = honestRoot answers lay (route index lay).2) :
    HitIn answers (queried answers (layerP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerP w index lay digits))
  · exact Or.inl hH
  right
  have hleafB := route_leaf_bound index lay
  generalize hleaf : (route index lay).1 = leaf at hleafB
  have htreeB := route_tree_bound index lay hidx
  generalize htree : (route index lay).2 = tree at htreeB
  have hleaf32 : leaf < 2 ^ 32 :=
    lt_of_lt_of_le hleafB (le_trans (Nat.pow_le_pow_right (by decide) (height_le lay)) (by norm_num))
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPath, queried_bind]
    exact List.mem_append_left _ hq
  have hqC : ∀ q ∈ queried answers (layerChains w index lay digits), q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    apply hqL
    rw [layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  have hM := merklePath_extract answers 3 lay.val tree (height lay) leaf (height lay)
    (wpath w lay leaf) (wmerklePad w lay)
    (fun j => treeValue (builtTree answers lay tree) j (leaf / 2 ^ j ^^^ 1))
    (fun step => treeValue (builtTree answers lay tree) step (leaf / 2 ^ step))
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (merkleInput_tree_reference answers 3 lay.val tree (height lay) leaf _ _
      (Correctness.builtTree_correct answers lay tree) hleafB)
    (by
      have h := reaches
      rw [layerP_eq_hashPath, evalWithAnswerFn_bind, hleaf, htree] at h
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hH
    refine ⟨.node lay tree step (leaf / 2 ^ (step + 1)), pad64 (pathInput answers
      (merkleInput 3 lay.val tree (height lay) leaf (wpath w lay leaf) (wmerklePad w lay))
      (evalWithAnswerFn answers (layerLeafP w index lay digits)) step), ⟨htreeB, hstep, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := leaf) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [layerP_eq_hashPath, queried_bind, hleaf, htree]
      exact List.mem_append_right _ hq
    · rw [merkle_honestInput]; exact hhit
    · unfold SameHeader
      rw [merkle_honestInput, pathInput, hdrBlock_merkleInput, hdrBlock_merkleInput]
  refine ⟨fun j hj => by rw [hleaf, htree]; exact hpath j hj, ?_⟩
  rw [pow_zero, Nat.div_one, Correctness.builtTree_leaf answers lay tree leaf hleafB, layerLeafP_eq,
    evalWithAnswerFn_bind, hleaf, htree] at hv0
  have hends : evalWithAnswerFn answers (layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainP lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i))) := by
    rw [layerChains, Correctness.eval_mapM, hleaf, htree]
    exact map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainP lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i)))
  rcases leafHash_extract answers lay tree leaf (evalWithAnswerFn answers (layerChains w index lay digits))
      ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf))
      (by rw [hends]; simp) (by simpa using chainCount_pos lay) hv0 with hE | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hH
    refine ⟨.leaf lay tree leaf, _, ⟨htreeB, hleaf32⟩, ?_, hhit, hsame⟩
    apply hqL
    rw [layerLeafP_eq, queried_bind, hleaf, htree]
    exact List.mem_append_right _ hq
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hreach : evalWithAnswerFn answers
      (chainP lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
        (wchainPads w lay i).1 (wchainPads w lay i).2 (wvalue w lay i)) =
      honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  rcases chainP_extract answers lay tree leaf i _ _ _ _ _ _ hreach with ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
  · rw [hleaf, htree]
    refine ⟨hval, fun hlt => ?_⟩
    obtain ⟨h0, h1⟩ := hpads (by omega)
    exact Prod.ext h0 h1
  · exfalso
    apply hH
    have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> omega
    have hc := chainCount_le lay
    refine ⟨.chain lay tree leaf i (digits.getD i 0 + step), _, ⟨htreeB, hleaf32, by omega, by omega⟩, ?_, hhit, ?_⟩
    · apply hqC
      exact layerChains_queried answers w index lay digits leaf tree hleaf htree i hi _ hq
    · simp only [SameHeader, honestInput]
      rw [pathInput, chainPathInput, hdrBlock_chainInputP, chainInput_eq_zero, hdrBlock_chainInputP]
end ClaudeWCT.W9.T3M.Extract
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layerP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (hs : LayerShaped answers w (N.toNat % 2 ^ 31) lay digits) :
    layerP w (N.toNat % 2 ^ 31) lay digits =
      recoverLayer (WCT9.toT3Signature (witDecP N w).signature) (N.toNat % 2 ^ 31) lay digits := by
  have hpath : ∀ j : Fin (height lay), ((WCT9.toT3Signature (witDecP N w).signature).layers lay).path j =
      wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount lay),
      ((WCT9.toT3Signature (witDecP N w).signature).layers lay).values i = wvalue w lay i.val :=
    fun _ => rfl
  unfold layerP recoverLayer
  simp only [hpath, hvals]
  generalize hr : route (N.toNat % 2 ^ 31) lay = r at hs ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs ⊢
  have hchains : ((List.finRange (chainCount lay)).mapM fun i =>
      chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wchainPads w lay i.val).1 (wchainPads w lay i.val).2 (wvalue w lay i.val)) =
      ((List.finRange (chainCount lay)).mapM fun i =>
      chain lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wvalue w lay i.val)) := by
    congr 1
    funext i
    by_cases hd : digits.getD i.val 0 < maxDigit lay i.val
    · rw [(hs.2 i.val i.isLt).2 hd]
      exact chainP_zero _ _ _ _ _ _ _
    · have h0 : maxDigit lay i.val - digits.getD i.val 0 = 0 := by omega
      rw [h0]
      rfl
  rw [hchains]
  congr 1
  funext ends
  congr 1
  funext value
  congr 1
  funext v j
  rw [(hs.1 j.val j.isLt).2, nodeHashP_zero]
end ClaudeWCT.W9.T3M.Extract
end
