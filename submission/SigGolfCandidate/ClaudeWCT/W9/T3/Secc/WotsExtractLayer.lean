import SigGolfCandidate.T3.Secc.WotsExtractLayer
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractWord
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layers
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low entriesOf word_cases)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (chainP layerP wchainPads wchainHeaderPad wmerklePad wpath wvalue)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain seenRow_mono entriesOf_mono mem_entriesOf routeLeaf
  routeLeaf_source)
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def WotsPrimitiveSrc (answers : Answers) (trace : List Entry) : Prop :=
  (∃ L, SourceLeaf L ∧ EncodingMatchAt answers trace L) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)
theorem WotsPrimitiveSrc.toPrimitive {answers : Answers} {trace : List Entry} (h : WotsPrimitiveSrc answers trace) :
    WotsPrimitive answers trace := by
  rcases h with ⟨L, -, h⟩ | h | ⟨a, -, h⟩ | ⟨a, b, -, -, hab, ha, hb⟩ | ⟨a, -, hm, hc⟩
  · exact Or.inl ⟨L, h⟩
  · exact Or.inr (Or.inl h.toStructuralHit)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, ha, hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, hm, hc⟩)))
section mono
variable {answers : Answers} {trace trace' : List Entry}
theorem WotsPrimitiveSrc.mono (h : WotsPrimitiveSrc answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveSrc answers trace' := by
  rcases h with ⟨L, hL, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨L, hL, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
end mono
theorem leaf_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits) (qs : List Spec.Domain)
    (hsubL : ∀ q ∈ queried answers (layerLeafP w index lay digits), q ∈ qs)
    (hv0 : evalWithAnswerFn answers (layerLeafP w index lay digits) =
      treeValue (builtTree answers lay (route index lay).2) 0 (route index lay).1) :
    StructuralHitSrc answers (entriesOf answers qs) ∨
    ∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩)) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers qs)
  · exact Or.inl hS
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have htree31 : (route index lay).2 < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hleaf32 : (route index lay).1 < 2 ^ 32 :=
    lt_of_lt_of_le hleafB (le_trans (Nat.pow_le_pow_right (by decide) (Extract.height_le lay)) (by norm_num))
  have hqC : ∀ q ∈ queried answers (Extract.layerChains w index lay digits), q ∈ qs := by
    intro q hq
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_left _ hq
  rw [Correctness.builtTree_leaf answers lay _ _ hleafB, Extract.layerLeafP_eq, evalWithAnswerFn_bind] at hv0
  have hends : evalWithAnswerFn answers (Extract.layerChains w index lay digits) =
      (List.range (chainCount lay)).map (fun i => evalWithAnswerFn answers
        (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i))) := by
    rw [Extract.layerChains, Correctness.eval_mapM]
    exact Extract.map_finRange_val _ (fun i => evalWithAnswerFn answers
        (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0)
          (maxDigit lay i - digits.getD i 0) (wchainPads w lay i).1 (wchainPads w lay i).2
          (wchainHeaderPad w lay i) (wvalue w lay i)))
  rcases Extract.leafHash_extract answers lay (route index lay).2 (route index lay).1
      (evalWithAnswerFn answers (Extract.layerChains w index lay digits))
      ((List.range (chainCount lay)).map (leafEnd answers lay (route index lay).2 (route index lay).1))
      (by rw [hends]; simp) (by simpa using Extract.chainCount_pos lay) hv0 with hE | ⟨hhit, hsame, hq⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.leaf lay (route index lay).2 (route index lay).1) _ ⟨htreeB, hleaf32⟩
      ⟨htree31, hleafB⟩ ?_ hhit hsame trivial
    apply hsubL
    rw [Extract.layerLeafP_eq, queried_bind]
    exact List.mem_append_right _ hq
  rw [hends] at hE
  have hE' := (List.map_inj_left).mp hE
  intro i hi
  have hd := hvalid i hi
  have hci := hE' i (List.mem_range.mpr hi)
  have hw : 2 ^ width lay i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (Extract.width_le lay i)
  have hc := Extract.chainCount_le lay
  have hreach : evalWithAnswerFn answers
      (chainP lay (route index lay).2 (route index lay).1 i (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
        (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalue w lay i)) =
      honestChainValue answers lay (route index lay).2 (route index lay).1 i
        (leafSeed answers lay (route index lay).2 (route index lay).1 i)
        (digits.getD i 0 + (maxDigit lay i - digits.getD i 0)) := by
    rw [hci, Nat.add_sub_cancel' hd]; rfl
  have hdepth : depth answers ⟨routeLeaf index lay, i⟩ ≤ maxDigit lay i := depth_le answers ⟨routeLeaf index lay, i⟩ hi
  have hsrcC : SourceChain ⟨routeLeaf index lay, i⟩ := ⟨routeLeaf_source index lay hidx, hi⟩
  have hcount : digits.getD i 0 + (maxDigit lay i - digits.getD i 0) < 2 ^ width lay i := by
    have hm := Nonbinary.maxDigit_lt_pow_width lay i
    omega
  rcases chain_cases answers ⟨routeLeaf index lay, i⟩ (digits.getD i 0) (maxDigit lay i - digits.getD i 0)
      (wchainPads w lay i).1 (wchainPads w lay i).2 (wchainHeaderPad w lay i) (wvalue w lay i) qs
      (fun q hq => hqC q (Extract.layerChains_queried answers w index lay digits (route index lay).1
        (route index lay).2 rfl rfl i hi q hq))
      hsrcC hcount (by omega) hreach with
    hS' | ⟨hhon, hlow⟩
  · exact (hS hS').elim
  refine ⟨fun hle => ?_, hlow⟩
  obtain ⟨hval, hpads⟩ := hhon hle
  refine ⟨hval, fun hlt => ?_⟩
  obtain ⟨h0, h1, hh⟩ := hpads (by omega)
  exact ⟨Prod.ext h0 h1, hh⟩
theorem layerP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    StructuralHitSrc answers (entriesOf answers (queried answers (layerP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        wmerklePad w lay j = 0) ∧
      ∀ i, i < chainCount lay →
        (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
          ContactAt answers (entriesOf answers (queried answers (layerP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
              TwoEdgeAt answers (entriesOf answers (queried answers (layerP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers (queried answers (layerP w index lay digits)))
  · exact Or.inl hS
  right
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have htree31 : (route index lay).2 < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerP w index lay digits) := by
    intro q hq
    rw [layerP_eq_hashPath, queried_bind]
    exact List.mem_append_left _ hq
  have hM := merklePath_extract answers 3 lay.val (route index lay).2 (height lay) (route index lay).1 (height lay)
    (wpath w lay (route index lay).1) (wmerklePad w lay)
    (fun j => treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (builtTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (merkleInput_tree_reference answers 3 lay.val (route index lay).2 (height lay) (route index lay).1 _ _
      (Correctness.builtTree_correct answers lay (route index lay).2) hleafB)
    (by
      have h := reaches
      rw [layerP_eq_hashPath, evalWithAnswerFn_bind] at h
      rw [Nat.div_eq_of_lt hleafB]
      exact h)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (pathInput answers
        (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
          (wmerklePad w lay)) (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, hstep, ?_⟩ ⟨htree31, hstep, ?_⟩ ?_ ?_ ?_ trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [layerP_eq_hashPath, queried_bind]
      exact List.mem_append_right _ hq
    · rw [Extract.merkle_honestInput]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.merkle_honestInput, pathInput, Extract.hdrBlock_merkleInput, Extract.hdrBlock_merkleInput]
  refine ⟨hpath, ?_⟩
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | hchains
  · exact (hS hS').elim
  · exact hchains
theorem layerPairP_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat)
    (hidx : index < 2 ^ 31) (hvalid : Cost.ValidDigits lay digits)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    StructuralHitSrc answers (entriesOf answers (queried answers (layerPairP w index lay digits))) ∨
    ((∀ j, j < height lay →
        wpath w lay (route index lay).1 j =
          treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay → wmerklePad w lay j = 0)) ∧
      ∀ i, i < chainCount lay →
        (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
          wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
            (digits.getD i 0 < maxDigit lay i →
              wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
        (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
          ContactAt answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
              ⟨routeLeaf index lay, i⟩ ∧
            (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
              TwoEdgeAt answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
                ⟨routeLeaf index lay, i⟩))) := by
  classical
  by_cases hS : StructuralHitSrc answers (entriesOf answers (queried answers (layerPairP w index lay digits)))
  · exact Or.inl hS
  right
  have hh := Extract.height_pos lay
  have hleafB := route_leaf_bound index lay
  have htreeB := Extract.route_tree_bound index lay hidx
  have htree31 : (route index lay).2 < 2 ^ 31 := lt_of_le_of_lt (Nat.div_le_self _ _) hidx
  have hqL : ∀ q ∈ queried answers (layerLeafP w index lay digits),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPath, queried_bind]
    exact List.mem_append_left _ hq
  have hqM : ∀ q ∈ queried answers (hashPath (merkleInput 3 lay.val (route index lay).2 (height lay)
      (route index lay).1 (wpath w lay (route index lay).1) (wmerklePad w lay)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))),
      q ∈ queried answers (layerPairP w index lay digits) := by
    intro q hq
    rw [Extract.layerPairP_eq_hashPath, queried_bind, queried_bind]
    exact List.mem_append_right _ (List.mem_append_left _ hq)
  have hq2 : (route index lay).1 / 2 ^ (height lay - 1) = 0 ∨ (route index lay).1 / 2 ^ (height lay - 1) = 1 := by
    have hq : (route index lay).1 / 2 ^ (height lay - 1) < 2 := by
      apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
      have he : 2 ^ (height lay - 1) * 2 = 2 ^ height lay := by rw [← pow_succ, Nat.sub_add_cancel hh]
      rw [Nat.mul_comm, he]
      exact hleafB
    generalize (route index lay).1 / 2 ^ (height lay - 1) = q at hq ⊢
    omega
  have reaches' := reaches
  rw [Extract.layerPairP_eq_hashPath, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches'
  generalize htop : evalWithAnswerFn answers (hashPath (merkleInput 3 lay.val (route index lay).2 (height lay)
      (route index lay).1 (wpath w lay (route index lay).1) (wmerklePad w lay)) (height lay - 1)
      (evalWithAnswerFn answers (layerLeafP w index lay digits))) = top at reaches'
  have hpair : top = treeValue (builtTree answers lay (route index lay).2) (height lay - 1)
        ((route index lay).1 / 2 ^ (height lay - 1)) ∧
      wpath w lay (route index lay).1 (height lay - 1) =
        treeValue (builtTree answers lay (route index lay).2) (height lay - 1)
          ((route index lay).1 / 2 ^ (height lay - 1) ^^^ 1) := by
    unfold Extract.honestPair at reaches'
    rcases hq2 with h | h <;> simp only [h] at reaches' ⊢ <;>
      simp only [Nat.one_mod, if_true, if_false, Prod.mk.injEq, one_ne_zero] at reaches' <;>
      exact ⟨by first | exact reaches'.1 | exact reaches'.2, by first | exact reaches'.2 | exact reaches'.1⟩
  have hM := merklePath_extract answers 3 lay.val (route index lay).2 (height lay) (route index lay).1
    (height lay - 1) (wpath w lay (route index lay).1) (wmerklePad w lay)
    (fun j => treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1))
    (fun step => treeValue (builtTree answers lay (route index lay).2) step ((route index lay).1 / 2 ^ step))
    (evalWithAnswerFn answers (layerLeafP w index lay digits))
    (fun step hstep => merkleInput_tree_reference answers 3 lay.val (route index lay).2 (height lay)
      (route index lay).1 _ _ (Correctness.builtTree_correct answers lay (route index lay).2) hleafB step
      (by omega))
    (by unfold pathValue; rw [htop]; exact hpair.1)
  rcases hM with ⟨hv0, hpath⟩ | ⟨step, hstep, hq, hhit⟩
  swap
  · exfalso
    apply hS
    refine structuralHit_intro (.node lay (route index lay).2 step ((route index lay).1 / 2 ^ (step + 1)))
      (pad64 (pathInput answers
        (merkleInput 3 lay.val (route index lay).2 (height lay) (route index lay).1 (wpath w lay (route index lay).1)
          (wmerklePad w lay)) (evalWithAnswerFn answers (layerLeafP w index lay digits)) step))
      ⟨htreeB, by omega, ?_⟩ ⟨htree31, by omega, ?_⟩ (hqM _ hq) ?_ ?_ trivial
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · simpa only [Nat.sub_sub, Nat.zero_add] using Correctness.div_pow_bound (start := 0) (level := step + 1)
        (node := (route index lay).1) (height := height lay) (by omega) (by simpa using hleafB)
    · rw [Extract.merkle_honestInput]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.merkle_honestInput, pathInput, Extract.hdrBlock_merkleInput, Extract.hdrBlock_merkleInput]
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases hjt : j < height lay - 1
    · exact ⟨(hpath j hjt).1, fun _ => (hpath j hjt).2⟩
    · have hj1 : j = height lay - 1 := by omega
      subst hj1
      exact ⟨hpair.2, fun h => by omega⟩
  rw [pow_zero, Nat.div_one] at hv0
  rcases leaf_wots answers w index lay digits hidx hvalid _ hqL hv0 with hS' | hchains
  · exact (hS hS').elim
  · exact hchains
theorem frame_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hmerkle : ∀ j, j < height lay →
      wpath w lay (route index lay).1 j =
          treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
        (j + 1 < height lay ∨ lay.val = 0 → wmerklePad w lay j = 0))
    (hchains : ∀ i, i < chainCount lay →
      (depth answers ⟨routeLeaf index lay, i⟩ ≤ digits.getD i 0 →
        wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
          (digits.getD i 0 < maxDigit lay i →
            wchainPads w lay i = (0, 0) ∧ wchainHeaderPad w lay i = 0)) ∧
      (digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
        ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ ∧
          (digits.getD i 0 + 2 ≤ depth answers ⟨routeLeaf index lay, i⟩ →
            TwoEdgeAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩))) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (low (answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay)))))) = some digits :=
    hframe.2
  have hfit' : Extract.msgFits (routeLeaf index lay).lay msg := hfit
  have hencE : (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay),
      answers (.inl (.inr (encRow (routeLeaf index lay) msg (wbcCtr w lay) (wbcPad w lay))))) ∈
        entriesOf answers qs :=
    mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    ((hchains i hi).2 hlt).1
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  ·
    have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · by_cases hp : lay.val < 3 → wbcPad w lay = 0
      · exact Or.inr ⟨hm, ⟨digits, hm ▸ hframe, hshape⟩, hp⟩
      ·
        have hlay : lay.val < 3 := by by_contra h3; exact hp (fun h => absurd h h3)
        have hpad : wbcPad w lay ≠ 0 := fun h0 => hp (fun _ => h0)
        obtain ⟨l, r, hlr⟩ : ∃ l r, msg = .pair l r := by
          cases msg with
          | forest root => exact absurd hfit (by change ¬(lay.val = 3); omega)
          | pair l r => exact ⟨l, r, rfl⟩
        subst hlr
        refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, _, wbcCtr w lay, wbcPad w lay, _, hfit', hencE, ?_, ?_⟩)
        · exact referenceInput_ne_pad answers _ l r _ _ hfit' hpad
        · rw [← heq]; exact hdec
    · refine Or.inl (Or.inl ⟨routeLeaf index lay, hsrc, msg, wbcCtr w lay, wbcPad w lay, _, hfit', hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inl (by rw [leafMsg_route _ _ _ hidx]; exact hm))
      · rw [← heq]; exact hdec
  ·
    have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wbcCtr w lay, wbcPad w lay, _, digits, hfit', hencE,
        referenceInput_ne answers _ msg _ _ hfit' hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  ·
    refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact ((hchains i.val i.isLt).2 hlt).2 h2
  ·
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)
theorem layer_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun _ => (hmerkle j hj).2⟩)
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
theorem layerPair_wots (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : WCT9.LayerMsg)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hlay : lay.val ≠ 0) (hfit : Extract.msgFits lay msg)
    (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerPairP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerPairP w index lay digits) =
      Extract.honestPair answers lay (route index lay).2) :
    WotsPrimitiveSrc answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ BC.GoodZ answers w index lay) := by
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  rcases layerPairP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  exact frame_wots answers w index lay msg digits hidx hfit hframe qs henc
    (fun j hj => ⟨(hmerkle j hj).1, fun h => (hmerkle j hj).2 (h.resolve_right hlay)⟩)
    (fun i hi => ⟨(hchains i hi).1, fun hlt => ⟨contactAt_mono ((hchains i hi).2 hlt).1 hmono,
      fun h2 => twoEdgeAt_mono (((hchains i hi).2 hlt).2 h2) hmono⟩⟩)
end ClaudeWCT.W9.T3.Security.WotsExtract
