import SigGolfCandidate.T3M.Extract.Leaf

/-! # One padded hypertree layer (stream PEX-L)

`layerP_extract`: `layerP w index lay digits` (valid digits) reaching the honest root of its tree gives a
header-preserving hit among the layer's actual queries (`HitIn`, at a `.node`, `.leaf` or `.chain` position), or
`LayerShaped`: honest Merkle siblings with zero Merkle pads, chain values equal to Core's honest `leafValue` at the
digits, and zero chain pads on every chain that hashes at least one step. -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The honest shape of layer `lay`'s Merkle bytes: honest siblings and zero pads, except that below the top the
last pad only needs its 12 hashed bytes zero (E8: its first 4 bytes hold the counter of the layer above). -/
def MerkleShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) : Prop :=
  ∀ j, j < height lay →
    wpath w lay (route index lay).1 j =
        treeValue (builtTree answers lay (route index lay).2) j ((route index lay).1 / 2 ^ j ^^^ 1) ∧
      (if lay ≠ 0 ∧ j = height lay - 1 then (wmerklePad w lay j).extractLsb' 32 96 = 0
        else wmerklePad w lay j = 0)

/-- The honest shape of layer `lay`'s chain bytes for the digits `digits`. -/
def ChainShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  ∀ i, i < chainCount lay →
    wvalue w lay i = leafValue answers lay (route index lay).2 (route index lay).1 digits i ∧
      (digits.getD i 0 < maxDigit lay i → wchainPads w lay i = (0, 0))

/-- The honest shape of layer `lay`'s witness bytes for the digits `digits`. -/
def LayerShaped (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : Prop :=
  MerkleShaped answers w index lay ∧ ChainShaped answers w index lay digits

/-- The padded chains of layer `lay` (the first part of `layerLeafP`). -/
def layerChains (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) : M (List Digest) :=
  (List.finRange (chainCount lay)).mapM fun i =>
    chainP lay (route index lay).2 (route index lay).1 i.val (digits.getD i.val 0)
      (maxDigit lay i.val - digits.getD i.val 0) (wchainPads w lay i.val).1 (wchainPads w lay i.val).2
      (wvalue w lay i.val)

theorem layerLeafP_eq (w : WBytes) (index : Nat) (lay : Layer) (digits : List Nat) :
    layerLeafP w index lay digits =
      (layerChains w index lay digits >>= leafHash lay (route index lay).2 (route index lay).1) := rfl

theorem chainCount_pos (lay : Layer) : 0 < chainCount lay := by fin_cases lay <;> decide

/-! ## Honest inputs and headers of the three formats -/

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

/-! ## The extraction -/

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

/-- **One layer.** -/
theorem route_tree_bound (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) : (route index lay).2 < 2 ^ 40 :=
  lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hidx (by norm_num))

theorem height_le (lay : Layer) : height lay ≤ 12 := by fin_cases lay <;> decide

theorem chainCount_le (lay : Layer) : chainCount lay ≤ 58 := by fin_cases lay <;> decide

theorem width_le (lay : Layer) (i : Nat) : width lay i ≤ 3 := by unfold width; split_ifs <;> omega

/-- A header-preserving hit at a Merkle node of the layer-`lay` tree `tree` (leaf `leaf`) among `qs`. -/
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

/-- The extraction of `c ≤ h` folds of a layer's Merkle path from the target node at level `c`: a node hit among
the path's queries, or honest siblings / zero pads below `c` and the honest leaf pk. -/
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

/-- The leaf pk and the chains of a layer from the honest leaf pk: a hit among `layerLeafP`'s queries, or honest
chain bytes. -/
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
  -- chains
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

/-- **The top layer** (all `h` folds to the root). -/
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

/-- **A layer below the top** (E8): the handed-over pair equal to the honest pair of its tree. The pair binds the
level-`h-1` node and its sibling; the 12 hashed pad bytes are zero; the `h-1` folds below are extracted. -/
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

/-- **One layer** (kept interface: the whole layer reaching the honest root). -/
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

/-- **One layer below the top** (E8). -/
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

/-! ## Shaped layers are Core layers -/

/-- **Core bridge.** On honest-shaped bytes the byte verifier's layer *is* Core's `recoverLayer` (zero pads) on
the decoded witness `witDecP N w` — the same program, so the same queries in the same order. -/
theorem layerP_shaped_core (answers : Answers) (N : HashOutput) (w : WBytes) (lay : Layer) (digits : List Nat)
    (h0 : lay = 0) (hs : LayerShaped answers w (N.toNat % 2 ^ 31) lay digits) :
    layerP w (N.toNat % 2 ^ 31) lay digits = recoverLayer (witDecP N w).signature (N.toNat % 2 ^ 31) lay digits := by
  have hpath : ∀ j : Fin (height lay), ((witDecP N w).signature.layers lay).path j =
      wpath w lay (route (N.toNat % 2 ^ 31) lay).1 j.val := fun _ => rfl
  have hvals : ∀ i : Fin (chainCount lay), ((witDecP N w).signature.layers lay).values i = wvalue w lay i.val :=
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
  have hp := (hs.1 j.val j.isLt).2
  rw [if_neg (fun h => h.1 h0)] at hp
  rw [hp, nodeHashP_zero]

end SigGolfCandidate.T3M.Extract
