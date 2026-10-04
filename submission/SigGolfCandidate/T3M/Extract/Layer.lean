import SigGolfCandidate.T3M.Extract.Leaf
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def MerkleShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      (if lay ≠ 0 ∧ j = height lay - 1 then (wmerklePad w lay j).extractLsb' 32 96 = 0
        else wmerklePad w lay j = 0)
def ChainShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  ∀ i, i < chainCount lay →
    wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i →
        wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  MerkleShaped answers w index lay ∧ ChainShaped answers w index lay digits
def layerChains (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalue w lay i.val)
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
theorem hdrBlock_chainInputP (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 : Digest)
    (headerPad : BitVec 64) (value : Digest) :
    hdrBlock (pad64 (chainInputP lay tree leaf i step pad0 pad1 headerPad value)) =
      bytesLE 16 (chainHeaderP lay tree leaf i step headerPad) := by
  rw [pad64_chainInputP, chainInputP_eq_block4, hdrBlock_block4]
private theorem canonicalHeader_replace_high (x : Digest) (pad : BitVec 64)
    (hb : 128 ≤ x.toNat % 256) :
    canonicalHeader (bytesLE 16 (pad ++ x.extractLsb' 0 64)) =
      canonicalHeader (bytesLE 16 x) := by
  have hl : 128 ≤ (x.extractLsb' 0 64).toNat % 256 := by
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    omega
  have hx : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
    BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := x)
  exact (canonicalHeader_high_irrelevant _ _ _ hl).trans
    (congrArg (fun y => canonicalHeader (bytesLE 16 y)) hx)
theorem canonicalHeader_chainHeaderP (lay : Layer) (tree leaf i step : Nat)
    (headerPad : BitVec 64) :
    canonicalHeader (bytesLE 16 (chainHeaderP lay tree leaf i step headerPad)) =
      canonicalHeader (bytesLE 16 (chainHeader lay tree leaf i step)) := by
  exact canonicalHeader_replace_high _ headerPad (T3.chainHeader_firstByte lay tree leaf i step)
theorem layerChains_queried (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (leaf tree : Nat) (hleaf : (route index lay).1 = leaf) (htree : (route index lay).2 = tree)
    (i : Nat) (hi : i < chainCount lay) :
    ∀ q ∈ queried answers (chainP lay tree leaf i (digits.getD i 0)
        (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i)),
      q ∈ queried answers (layerChains w index lay digits) := by
  subst hleaf htree
  unfold layerChains
  exact queried_mapM_mem answers (fun i : Fin (chainCount lay) =>
    chainP lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wchainHeaderPad w lay i.val) (wvalue w lay i.val))
        (List.finRange (chainCount lay)) ⟨i, hi⟩ (List.mem_finRange _)
theorem map_finRange_val {β : Type} (n : Nat) (g : Nat → β) :
    (List.finRange n).map (fun i => g i.val) = (List.range n).map g := by
  rw [show (fun i : Fin n => g i.val) = g ∘ Fin.val from rfl, ← List.map_map, map_val_finRange]
theorem route_tree_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) : (route index lay).2 < 2 ^ 40 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))
theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide
theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide
theorem width_le (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; split_ifs <;> omega
def NodeHitIn (answers : Answers) (qs : List Spec.Domain) (lay : Layer) (tree leaf : Nat) : Prop :=
  ∃ step input, step < height lay ∧ .inl (.inr input) ∈ qs ∧
    HashHit answers (honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1)))) input ∧
    SameHeader input (honestInput answers (.node lay tree step (leaf / 2 ^ (step + 1))))
theorem NodeHitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} {lay : Layer} {tree leaf : Nat}
    (h : NodeHitIn answers qs lay tree leaf) (hsub : ∀ q ∈ qs, q ∈ qs') : NodeHitIn answers qs' lay tree leaf := by
  obtain ⟨step, input, hs, hq, hh, hsame⟩ := h
  exact ⟨step, input, hs, hsub _ hq, hh, hsame⟩
theorem node_bound (lay : Layer) (leaf step : Nat) (hleaf : leaf < 2 ^ height lay) (hs : step < height lay) :
    leaf / 2 ^ (step + 1) < 2 ^ (height lay - step - 1) := by
  simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
    (node := leaf) (height := height lay) (by omega) (by simpa using hleaf)
theorem NodeHitIn.hitIn {answers : Answers} {qs : List Spec.Domain} {lay : Layer} {tree leaf : Nat}
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ height lay) (h : NodeHitIn answers qs lay tree leaf) :
    HitIn answers qs := by
  obtain ⟨step, input, hs, hq, hh, hsame⟩ := h
  exact ⟨.node lay tree step (leaf / 2 ^ (step + 1)), input, ⟨htree, hs, node_bound lay leaf step hleaf hs⟩,
    hq, hh, hsame⟩
theorem merklePrefix_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (c : Nat) (hc : c ≤ height lay)
    (reaches : pathValue answers (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerklePad w lay)) (evalWithAnswerFn answers (layerLeafP w index lay digits)) c =
      treeValue (builtTree answers lay (route index lay).2) c ((route index lay).1 / 2 ^ c)) :
    NodeHitIn answers (queried answers (hashPath (merkleInput 3 lay.val (route index lay).2 (height lay)
        (route index lay).1 (wpath w lay (route index lay).1) (wmerklePad w lay)) c
        (evalWithAnswerFn answers (layerLeafP w index lay digits)))) lay (route index lay).2 (route index lay).1 ∨
      ((∀ j, j < c → wpath w lay (route index lay).1 j =
          treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
          wmerklePad w lay j = 0) ∧
        evalWithAnswerFn answers (layerLeafP w index lay digits) =
          treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) := by
  have hleafB := route_leaf_bound index lay
  rcases merklePath_extract answers 3 lay.val (route index lay).2 (height lay) (route index lay).1 c
      (wpath w lay (route index lay).1) (wmerklePad w lay)
      (fun j => treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
      (fun step => treeValue (builtTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
      (evalWithAnswerFn answers (layerLeafP w index lay digits))
      (merkleInput_tree_reference_prefix answers 3 lay.val (route index lay).2 (height lay) (route index lay).1 c _ _
        (Correctness.builtTree_correct answers lay (route index lay).2) hleafB hc)
      reaches with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  · right
    refine ⟨hpath, ?_⟩
    rw [hv0, pow_zero, Nat.div_one]
  · left
    refine ⟨step, _, by omega, hq, ?_, ?_⟩
    · rw [merkle_honestInput]; exact hhit
    · unfold SameHeader
      rw [merkle_honestInput, pathInput, hdrBlock_merkleInput, hdrBlock_merkleInput]
theorem leafChains_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) :
    HitIn answers (queried answers (layerLeafP w index lay digits)) ∨ ChainShaped answers w index lay digits := by
  classical
  by_cases hH : HitIn answers (queried answers (layerLeafP w index lay digits))
  · exact Or.inl hH
  right
  have hleafB := route_leaf_bound index lay
  generalize hleaf : (route index lay).1 = leaf at hleafB hv0
  have htreeB := route_tree_bound index lay hidx
  generalize htree : (route index lay).2 = tree at htreeB hv0
  have htree31 : tree < 2 ^ 31 := by
    rw [← htree]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hleaf12 : leaf < 4096 :=
    lt_of_lt_of_le hleafB (Nat.pow_le_pow_right (by decide) (height_le lay))
  have hleaf32 : leaf < 2 ^ 32 :=
    lt_of_lt_of_le hleafB (le_trans (Nat.pow_le_pow_right (by decide) (height_le lay)) (by norm_num))
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerLeafP w index lay digits) := fun q hq => hq
  have hqC : ∀ q ∈ queried answers (layerChains w index lay digits),
      q ∈ queried answers (layerLeafP w index lay digits) := by
    intro q hq
    rw [layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  rw [Correctness.builtTree_leaf answers lay tree leaf hleafB, layerLeafP_eq,
    evalWithAnswerFn_bind, hleaf, htree] at hv0
  have hends : evalWithAnswerFn answers (layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainP lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i))) := by
    rw [layerChains, Correctness.eval_mapM, hleaf, htree]
    exact map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainP lay tree leaf i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
          (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i)))
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
        (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i)) =
      honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> omega
  have hc := chainCount_le lay
  rcases chainP_extract answers lay tree leaf i _ _ _ _ _ _ _
      htree31 hleaf12 (by omega) (Or.inr (by omega)) hreach with
      ⟨hval, hpads⟩ | ⟨step, hstep, hq, hhit⟩
  · rw [hleaf, htree]
    refine ⟨hval, fun hlt => ?_⟩
    obtain ⟨h0, h1, hh⟩ := hpads (by omega)
    exact ⟨Prod.ext h0 h1, hh⟩
  · exfalso
    apply hH
    refine ⟨.chain lay tree leaf i (digits.getD i 0 + step), _,
      ⟨htree31, hleaf12, by omega, by omega⟩, ?_, hhit, ?_⟩
    · apply hqC
      exact layerChains_queried answers w index lay digits leaf tree hleaf htree i hi _ hq
    · simp only [SameHeader, honestInput]
      rw [pathInput, chainPathInput, hdrBlock_chainInputP, chainInput_padded]
      change canonicalHeader (bytesLE 16 (chainHeaderP _ _ _ _ _ _)) =
        canonicalHeader (((chainInput _ _ _ _ _ _).drop 16).take 16)
      rw [chainInput_header]
      exact canonicalHeader_chainHeaderP _ _ _ _ _ _
theorem pairOf_eq_honest (leaf h : Nat) (hh : 0 < h) (hleaf : leaf < 2 ^ h) (f : Nat → Digest)
    (other node : Digest) (pad : BitVec 96) (he : pairOf leaf h other pad node = (f 0, 0, f 1)) :
    node = f (leaf / 2 ^ (h - 1)) ∧ other = f (leaf / 2 ^ (h - 1) ^^^ 1) ∧ pad = 0 := by
  have hb : leaf / 2 ^ (h - 1) < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc leaf < 2 ^ h := hleaf
      _ = 2 * 2 ^ (h - 1) := by rw [← pow_succ']; congr 1; omega
  unfold pairOf at he
  generalize hq : leaf / 2 ^ (h - 1) = q at hb he ⊢
  interval_cases q <;> simp_all [Prod.ext_iff]
theorem merkleShaped_of_zero (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer)
    (h : ∀ j, j < height lay → wpath w lay (route index lay).1 j =
      treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      wmerklePad w lay j = 0) :
    MerkleShaped answers w index lay := by
  intro j hj
  refine ⟨(h j hj).1, ?_⟩
  split
  · rw [(h j hj).2]; rfl
  · exact (h j hj).2
theorem layerP_merkle (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = honestRoot answers lay (route index lay).2) :
    NodeHitIn answers (queried answers (layerP w index lay digits)) lay (route index lay).2 (route index lay).1 ∨
      (MerkleShaped answers w index lay ∧
        evalWithAnswerFn answers (layerLeafP w index lay digits) =
          treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) := by
  have hleafB := route_leaf_bound index lay
  have hr : pathValue answers (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1
        (wpath w lay (route index lay).1) (wmerklePad w lay)) (evalWithAnswerFn answers (layerLeafP w index lay digits))
        (height lay) =
      treeValue (builtTree answers lay (route index lay).2) (height lay) ((route index lay).1 / 2 ^ height lay) := by
    have h := reaches
    rw [layerP_eq_hashPath, evalWithAnswerFn_bind] at h
    rw [Nat.div_eq_of_lt hleafB]
    exact h
  rcases merklePrefix_extract answers w index lay digits (height lay) le_rfl hr with hn | ⟨hpath, hv0⟩
  · left
    refine hn.mono fun q hq => ?_
    rw [layerP_eq_hashPath, queried_bind]
    exact List.mem_append_right _ hq
  · exact Or.inr ⟨merkleShaped_of_zero answers w index lay hpath, hv0⟩
theorem layerPairP_merkle (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0)
    (digits : List Nat)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) = honestPair answers lay (route index lay).2) :
    NodeHitIn answers (queried answers (layerPairP w index lay digits)) lay (route index lay).2 (route index lay).1 ∨
      (MerkleShaped answers w index lay ∧
        evalWithAnswerFn answers (layerLeafP w index lay digits) =
          treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) := by
  have hleafB := route_leaf_bound index lay
  have hh := height_pos lay
  have hpair := reaches
  rw [layerPairP_eq_hashPath, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hpair
  unfold honestPair at hpair
  obtain ⟨hnode, hsib, hpad⟩ := pairOf_eq_honest _ (height lay) hh hleafB
    (fun k => treeValue (builtTree answers lay (route index lay).2) (height lay - 1) k) _ _ _ hpair
  rcases merklePrefix_extract answers w index lay digits (height lay - 1) (by omega) hnode with hn | ⟨hpath, hv0⟩
  · left
    refine hn.mono fun q hq => ?_
    rw [layerPairP_eq_hashPath, queried_bind]
    apply List.mem_append_right
    rw [queried_bind]
    exact List.mem_append_left _ hq
  · right
    refine ⟨fun j hj => ?_, hv0⟩
    by_cases hj' : j = height lay - 1
    · subst hj'
      exact ⟨hsib, by rw [if_pos ⟨hlay, rfl⟩]; exact hpad⟩
    · exact ⟨(hpath j (by omega)).1, by rw [if_neg (fun h => hj' h.2)]; exact (hpath j (by omega)).2⟩
theorem layerP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) = honestRoot answers lay (route index lay).2) :
    HitIn answers (queried answers (layerP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  rcases layerP_merkle answers w index lay digits reaches with hn | ⟨hm, hv0⟩
  · exact Or.inl (hn.hitIn (route_tree_bound index lay hidx) (route_leaf_bound index lay))
  rcases leafChains_extract answers w index lay digits hidx hvalid hv0 with hh | hc
  · left
    refine hh.mono fun q hq => ?_
    rw [layerP_eq_hashPath, queried_bind]
    exact List.mem_append_left _ hq
  · exact Or.inr ⟨hm, hc⟩
theorem layerPairP_extract (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (hlay : lay ≠ 0)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) = honestPair answers lay (route index lay).2) :
    HitIn answers (queried answers (layerPairP w index lay digits)) ∨ LayerShaped answers w index lay digits := by
  rcases layerPairP_merkle answers w index lay hlay digits reaches with hn | ⟨hm, hv0⟩
  · exact Or.inl (hn.hitIn (route_tree_bound index lay hidx) (route_leaf_bound index lay))
  rcases leafChains_extract answers w index lay digits hidx hvalid hv0 with hh | hc
  · left
    refine hh.mono fun q hq => ?_
    rw [layerPairP_eq_hashPath, queried_bind]
    exact List.mem_append_left _ hq
  · exact Or.inr ⟨hm, hc⟩
end SigGolfCandidate.T3M.Extract
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layerP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (h0 : lay = 0) (hs : LayerShaped answers w (N.toNat % 2 ^ 31) lay digits) :
    layerP w (N.toNat % 2 ^ 31) lay digits = recoverLayer (witDecP N w).signature (N.toNat % 2 ^ 31) lay digits := by
  have hpath : ∀ j : Fin (height lay), ((witDecP N w).signature.layers lay).path j =
      wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount lay), ((witDecP N w).signature.layers lay).values i = wvalue w lay i.val :=
    fun _ => rfl
  have hzero := chainP_zero_route (N.toNat % 2 ^ 31) lay
  have hindex : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  unfold layerP recoverLayer
  simp only [hpath, hvals]
  generalize hr : route (N.toNat % 2 ^ 31) lay = r at hs hzero ⊢
  obtain ⟨leaf, tree⟩ := r
  dsimp only at hs hzero ⊢
  have hchains : ((List.finRange (chainCount lay)).mapM fun i =>
      chainP lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
        (wchainHeaderPad w lay i.val) (wvalue w lay i.val)) =
      ((List.finRange (chainCount lay)).mapM fun i =>
      chain lay tree leaf i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
        (wvalue w lay i.val)) := by
    congr 1
    funext i
    by_cases hd : digits.getD i.val 0 < maxDigit lay i.val
    · rw [((hs.2 i.val i.isLt).2 hd).1, ((hs.2 i.val i.isLt).2 hd).2]
      exact hzero i _ _ hindex
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
  have hp := (hs.1 j.val j.isLt).2
  rw [if_neg (fun h => h.1 h0)] at hp
  rw [hp, nodeHashP_zero]
end SigGolfCandidate.T3M.Extract
