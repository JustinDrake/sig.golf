import SigGolfCandidate.T3.Secc.WotsMaskBase

/-!
# F1 (chains): chain values, leaves, trees and reference words under `maskAt`

* `chain_maskAt`: Core's chain fold of `a` from its (masked) seed re-converges at the frontier
  (`count ≥ depth`, `count ≤ 256`).
* `eval_honestChain_maskAt`: every honest chain `(lay, tree, leaf, i)` from its own seed evaluates identically under
  the mask, provided that an alias of `a` (same headers, `Mask.LeafAlias`) runs at least to `a`'s frontier.
* `leafEnd_maskAt`, `leafRoot_maskAt`, `builtTree_maskAt`, `honestRoot_maskAt`, `honestForest_maskAt`,
  `leafMsg_maskAt`, `referenceSearch_maskAt`, `referenceDigits_maskAt`, `depth_maskAt_all`: unconditional.
* `depth_maskAt`, `frontierValue_maskAt` (prototype statements), `frontierValue_maskAt_other`.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Mask

theorem eval_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    evalWithAnswerFn T (chain lay tree leaf i s 1 v) =
      (T (.inl (.inr (chainInput lay tree leaf i s v)))).extractLsb' 0 128 := by
  rw [← pad64_chainInput]
  rfl

variable (answers : Answers) (a : ChainAddr)

/-- One masked prefix step answers `0`, or the frontier value at the last prefix step, whatever its input. -/
theorem eval_chain_one_maskAt {s : Nat} (hs : s < depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain s 1 v) =
      if s + 1 = depth answers a then frontierValue answers a else 0 := by
  rw [eval_chain_one, ← chainRow_eq, maskAt_prefix answers a v hs]
  split
  · exact ChainGraph.joinOutput_low _ _
  · rfl

/-- The masked prefix of `a` reaches the frontier value from any start value. -/
theorem eval_chain_prefix_maskAt (hd : 1 ≤ depth answers a) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 (depth answers a) v) =
      frontierValue answers a := by
  have h1 := Correctness.eval_chain_add (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain 0
    (depth answers a - 1) 1 v
  rw [Nat.zero_add, eval_chain_one_maskAt answers a (by omega), if_pos (Nat.sub_add_cancel hd),
    Nat.sub_add_cancel hd] at h1
  exact h1

/-- **Re-convergence at the frontier** (any start value, `depth ≥ 1`). -/
theorem eval_chain_maskAt (hd : 1 ≤ depth answers a) {count : Nat} (hc : depth answers a ≤ count)
    (hc' : count ≤ 256) (v : Digest) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count v) =
      evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
        (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  obtain ⟨e, rfl⟩ : ∃ e, count = depth answers a + e := ⟨count - depth answers a, by omega⟩
  rw [Correctness.eval_chain_add, Correctness.eval_chain_add answers, Nat.zero_add,
    eval_chain_prefix_maskAt answers a hd]
  change _ = evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain (depth answers a) e
    (frontierValue answers a))
  refine Respects.eval_eq (S := fun q => maskAt answers a q = answers q) ?_ (fun q hq => hq)
  unfold chain
  refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
  rw [pad64_chainInput, ← chainRow_eq]
  obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hstep
  exact maskAt_row_ge answers a value hlo (by omega)

/-- A seed outside `a`'s half is unchanged (`i < 2^24`; the alias `(L, a.chain)` of `a` is excluded). -/
theorem leafSeed_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < 2 ^ 24)
    (hna : ¬(LeafAlias lay tree leaf a.key ∧ i = a.chain)) :
    leafSeed (maskAt answers a) lay tree leaf i = leafSeed answers lay tree leaf i := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hc : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  rw [leafSeed_eq, leafSeed_eq]
  by_cases heq : header 0 lay.val tree (i / 2) leaf = seedTweak a
  · obtain ⟨hal, hpair⟩ := seedTweak_alias hi hc heq
    have hpar : i % 2 ≠ a.chain % 2 := fun hp => hna ⟨hal, by omega⟩
    rw [maskAt_tweak, heq, if_pos (⟨rfl, by omega⟩ : seedTweak a = seedTweak a ∧ 1 ≤ depth answers a)]
    by_cases h0 : a.chain % 2 = 0
    · have hi1 : ¬i % 2 = 0 := by omega
      rw [if_neg hi1, if_neg hi1, if_pos h0, ChainGraph.joinOutput_high]
    · have hi0 : i % 2 = 0 := by omega
      rw [if_pos hi0, if_pos hi0, if_neg h0, ChainGraph.joinOutput_low]
  · rw [maskAt_untouched answers a (q := .inr (.inl _)) heq]

end Mask

/-- **`chain_maskAt`** (prototype statement plus the step bound `count ≤ 256`): Core's chain fold of `a` from its
(masked) seed agrees with the unmasked fold for every `count ≥ depth a`, in particular at the reference digit. -/
theorem chain_maskAt (answers : Answers) (a : ChainAddr) (count : Nat) (hcount : depth answers a ≤ count)
    (hsmall : count ≤ 256) :
    evalWithAnswerFn (maskAt answers a) (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
      (leafSeed (maskAt answers a) a.key.lay a.key.tree a.key.leaf a.chain)) =
    evalWithAnswerFn answers (chain a.key.lay a.key.tree a.key.leaf a.chain 0 count
      (leafSeed answers a.key.lay a.key.tree a.key.leaf a.chain)) := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  · exact eval_chain_maskAt answers a (by omega) hcount hsmall _

namespace Mask
variable (answers : Answers) (a : ChainAddr)

/-- **Honest chains under the mask.** The chain `(lay, tree, leaf, i)` run from its own seed for `count ≤ 256`
steps evaluates identically under `maskAt answers a`, provided that, if it is an alias of `a` (same headers), it
runs at least to `a`'s frontier. -/
theorem eval_honestChain_maskAt (lay : Layer) (tree leaf i count : Nat) (hi : i < chainCount lay)
    (hc : count ≤ 256) (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ count) :
    evalWithAnswerFn (maskAt answers a) (chain lay tree leaf i 0 count (leafSeed (maskAt answers a) lay tree leaf i)) =
      evalWithAnswerFn answers (chain lay tree leaf i 0 count (leafSeed answers lay tree leaf i)) := by
  by_cases hd : depth answers a = 0
  · rw [maskAt_of_depth_zero answers a hd]
  have hi' : i < 2 ^ 24 := by
    have := chainCount_le lay
    simp only [Nat.reducePow]; omega
  have hc' : a.chain < 2 ^ 24 := by
    have := chain_lt_of_depth answers a (by omega)
    have := chainCount_le a.key.lay
    simp only [Nat.reducePow]; omega
  by_cases hal : LeafAlias lay tree leaf a.key ∧ i = a.chain
  · obtain ⟨hal, rfl⟩ := hal
    rw [chain_alias hal, leafSeed_alias _ hal, leafSeed_alias _ hal]
    exact eval_chain_maskAt answers a (by omega) (halias hal rfl) hc _
  · rw [leafSeed_maskAt answers a lay tree leaf i hi' hal]
    apply eval_maskAt_of_respects
    unfold chain
    refine Respects.foldlM _ _ (fun step hstep value => Respects.shortHash _ ?_) _
    rw [pad64_chainInput]
    intro s' v' hs' heq
    have hstep' : step < 256 := by
      have := (List.mem_range'_1.mp hstep).2
      omega
    have h := chainInput_eq_chainRow hi' hc' hstep' hs' heq
    exact hal ⟨h.1, h.2.1⟩

theorem leafEnd_maskAt (lay : Layer) (tree leaf i : Nat) (hi : i < chainCount lay) :
    leafEnd (maskAt answers a) lay tree leaf i = leafEnd answers lay tree leaf i := by
  unfold leafEnd
  apply eval_honestChain_maskAt answers a lay tree leaf i _ hi (by have := width_le lay i; omega)
  intro hal hia
  obtain ⟨hl, -, -⟩ := hal
  subst hl hia
  exact depth_le_width answers a hi

/-- Leaf values (chain values at a word `digits`) are unchanged if an alias of `a` is read at or above `a`'s frontier. -/
theorem leafValue_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (i : Nat) (hi : i < chainCount lay)
    (hdig : digits.getD i 0 ≤ 256)
    (halias : LeafAlias lay tree leaf a.key → i = a.chain → depth answers a ≤ digits.getD i 0) :
    leafValue (maskAt answers a) lay tree leaf digits i = leafValue answers lay tree leaf digits i :=
  eval_honestChain_maskAt answers a lay tree leaf i _ hi hdig halias

theorem leafRoot_maskAt (lay : Layer) (tree leaf : Nat) :
    Correctness.leafRoot (maskAt answers a) lay tree leaf = Correctness.leafRoot answers lay tree leaf := by
  unfold Correctness.leafRoot
  rw [List.map_congr_left (fun i hi => leafEnd_maskAt answers a lay tree leaf i (List.mem_range.mp hi))]
  exact eval_maskAt_of_respects answers a (respects_leafHash a _ _ _ _)

theorem builtTree_maskAt (lay : Layer) (tree : Nat) :
    builtTree (maskAt answers a) lay tree = builtTree answers lay tree := by
  unfold builtTree
  have hr : Correctness.leafRoot (maskAt answers a) lay tree = Correctness.leafRoot answers lay tree :=
    funext (leafRoot_maskAt answers a lay tree)
  rw [hr]
  exact eval_maskAt_of_respects answers a (respects_buildLevels a 3 _ _ _ _ (by decide))

theorem honestRoot_maskAt (lay : Layer) (tree : Nat) :
    Extract.honestRoot (maskAt answers a) lay tree = Extract.honestRoot answers lay tree := by
  unfold Extract.honestRoot
  rw [builtTree_maskAt]

theorem honestPair_maskAt (lay : Layer) (tree : Nat) :
    Extract.honestPair (maskAt answers a) lay tree = Extract.honestPair answers lay tree := by
  unfold Extract.honestPair
  rw [builtTree_maskAt]

theorem eval_buildFts_maskAt (index coord : Nat) :
    evalWithAnswerFn (maskAt answers a) (buildFts index coord) = evalWithAnswerFn answers (buildFts index coord) :=
  eval_maskAt_of_respects answers a (respects_buildFts a index coord)

/-- Closed form of the honest forest pk through PEX-F's (already checked) `honestInput_forest`; stating it by
unfolding `Extract.ftsLevels` instead makes the kernel evaluate `buildFts` (≈ 40 s per occurrence). -/
theorem honestForest_eq (T : Answers) (index : Nat) :
    Extract.honestForest T index = evalWithAnswerFn T (forestPk index
      ((List.range 7).map fun c => treeValue (evalWithAnswerFn T (buildFts index c)).1 11 0)) := by
  have h : Extract.honestForest T index =
      (T (.inl (.inr (Extract.honestInput T (.forest index))))).extractLsb' 0 128 := rfl
  rw [h, FtsExtract.honestInput_forest]
  rfl

theorem honestForest_maskAt (index : Nat) :
    Extract.honestForest (maskAt answers a) index = Extract.honestForest answers index := by
  rw [honestForest_eq, honestForest_eq]
  have hl : ((List.range 7).map fun c => treeValue (evalWithAnswerFn (maskAt answers a) (buildFts index c)).1 11 0) =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0 :=
    List.map_congr_left fun c _ => congrArg (fun x : List (List Digest) × List Digest => treeValue x.1 11 0)
      (eval_buildFts_maskAt answers a index c)
  rw [hl]
  exact eval_maskAt_of_respects answers a (respects_forestPk a _ _)

end Mask

open Mask in
/-- The honest message of every leaf is unchanged. -/
theorem leafMsg_maskAt (answers : Answers) (a : ChainAddr) (L : LeafAddr) :
    leafMsg (maskAt answers a) L = leafMsg answers L := by
  unfold leafMsg
  split
  · exact honestPair_maskAt answers a _ _
  · rw [honestForest_maskAt answers a _]

open Mask in
/-- The honest signer's search at every leaf is unchanged. -/
theorem referenceSearch_maskAt (answers : Answers) (a : ChainAddr) (L : LeafAddr) :
    referenceSearch (maskAt answers a) L = referenceSearch answers L := by
  unfold referenceSearch
  rw [leafMsg_maskAt]
  exact eval_maskAt_of_respects answers a (respects_counterSearch a _ _ _ _ _ _)

theorem referenceDigits_maskAt (answers : Answers) (a : ChainAddr) (L : LeafAddr) :
    referenceDigits (maskAt answers a) L = referenceDigits answers L := by
  unfold referenceDigits
  rw [referenceSearch_maskAt]

theorem referenceInput_maskAt (answers : Answers) (a : ChainAddr) (L : LeafAddr) :
    referenceInput (maskAt answers a) L = referenceInput answers L := by
  unfold referenceInput
  rw [referenceSearch_maskAt, leafMsg_maskAt]

/-- Every chain's frontier position is unchanged. -/
theorem depth_maskAt_all (answers : Answers) (a b : ChainAddr) :
    depth (maskAt answers a) b = depth answers b := by
  unfold depth
  rw [referenceDigits_maskAt]

/-- **`depth_maskAt`**: the reference data of `a` does not read `a`'s own rows. -/
theorem depth_maskAt (answers : Answers) (a : ChainAddr) : depth (maskAt answers a) a = depth answers a :=
  depth_maskAt_all answers a a

/-- **`frontierValue_maskAt`**. -/
theorem frontierValue_maskAt (answers : Answers) (a : ChainAddr) :
    frontierValue (maskAt answers a) a = frontierValue answers a := by
  unfold frontierValue honestChainValue
  rw [depth_maskAt]
  exact chain_maskAt answers a _ le_rfl (by have := depth_le_seven answers a; omega)

open Mask in
/-- Frontier values of other chains are unchanged unless `b` is an alias of `a` revealed below `a`'s frontier. -/
theorem frontierValue_maskAt_other (answers : Answers) (a b : ChainAddr) (hb : b.chain < chainCount b.key.lay)
    (halias : LeafAlias b.key.lay b.key.tree b.key.leaf a.key → b.chain = a.chain → depth answers a ≤ depth answers b) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  unfold frontierValue honestChainValue
  rw [depth_maskAt_all]
  exact eval_honestChain_maskAt answers a _ _ _ _ _ hb (by have := depth_le_seven answers b; omega) halias

open Mask in
/-- Frontier values of every source-sized chain are unchanged. -/
theorem frontierValue_maskAt_bounded (answers : Answers) (a b : ChainAddr)
    (ha : a.key.tree < 2 ^ 40 ∧ a.key.leaf < 2 ^ 32) (hb : b.key.tree < 2 ^ 40 ∧ b.key.leaf < 2 ^ 32)
    (hc : b.chain < chainCount b.key.lay) :
    frontierValue (maskAt answers a) b = frontierValue answers b := by
  apply frontierValue_maskAt_other answers a b hc
  intro hal hch
  have hk : b.key = a.key := by
    have := hal.eq_of_lt hb.1 hb.2 ha.1 ha.2
    cases hbk : b.key
    rw [hbk] at this
    exact this
  have : b = a := by
    cases b; cases a
    simp only at hk hch
    rw [hk, hch]
  rw [this]

end SigGolfCandidate.T3.Security.Wots
