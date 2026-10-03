import SigGolfCandidate.T3.Secc.LargeCouplingCell
import SigGolfCandidate.T3.Secc.WotsExtractVerify

/-!
# LR-34 (coupling, signing): an honest signature is exactly its disclosures

Under answers `T` agreeing with canonical labels (G's `Agrees`) and the honest published cache, the honest signer's
answer is the router's disclosure-built signature with the honest values:

    evalWithAnswerFn T (signPayload cache m) =
      match signDigest T m with
      | none => none
      | some (_, N) => if RouteOk T index then some (assembleSig ρ N (honestValue T) (referenceDigits T)) else none

(`signPayload_disclosed`, then `authenticatedSign_disclosed`). Route: SEC's closed forms (`signPayload_eq`,
`eval_signForest`, `eval_signTop_honest`, `eval_buildTree_result`) and G's honest objects (`ftsSecret_eq`,
`ftsTree_eq`, `builtTree_eq`, `leafValue_eq`).
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafValue honestPieces forestOpenPrefix
  forestProofPrefix forestRoots forestOpened forestInner forestOuter)
open CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingSign : DecidableEq T3.Cache := Classical.decEq _

section Honest
variable {T : Answers} {labels : Labels}

/-- Under `Agrees`, honest values are the coordinate values of the labels. -/
theorem honestValue_eq (h : Agrees T labels) : honestValue T = coordVal (secretsOf T) labels := by
  funext c
  cases c with
  | inl M =>
      change (T (.inl (.inr (Extract.honestInput T M.toPos)))).extractLsb' 0 128 = _
      rw [honest_answer h M]
      rfl
  | inr x => rfl

theorem filterMap_map_getD {α β γ : Type} (l : List α) (f : α → Option β) (v : β → γ) (d : γ)
    (h : ∀ a ∈ l, (f a).isSome) : (l.filterMap f).map v = l.map fun a => ((f a).map v).getD d := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      have ha := h a List.mem_cons_self
      cases hf : f a with
      | none => rw [hf] at ha; cases ha
      | some b =>
          rw [List.filterMap_cons, hf]
          simp only [List.map_cons]
          rw [ih fun x hx => h x (List.mem_cons_of_mem _ hx), hf]
          rfl

theorem ftsChild_isSome (index : Fin (2^31)) (coord : Fin 7) (level c : Nat) (hl : level ≤ 11)
    (hc : c < 2 ^ (11 - level)) : (ftsChild index coord level c).isSome := by
  unfold ftsChild
  by_cases h0 : level = 0
  · subst h0
    rw [if_pos rfl, dif_pos (by simpa using hc)]
    rfl
  · rw [if_neg h0]
    unfold ftsNodeAt
    rw [dif_pos ⟨by omega, by
      have : 11 - (level - 1) - 1 = 11 - level := by omega
      rw [this]; exact hc⟩]
    rfl

theorem treeChild_isSome (lay : Layer) (tree : Fin (2^31)) (level c : Nat) (hl : level ≤ height lay)
    (hc : c < 2 ^ (height lay - level)) (hlt : level < height lay ∨ c < 4096) :
    (treeChild lay tree level c).isSome := by
  unfold treeChild
  by_cases h0 : level = 0
  · subst h0
    have h4096 : c < 4096 := by
      have := Extract.height_le lay
      calc c < 2 ^ (height lay - 0) := hc
        _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 4096 := by norm_num
    rw [if_pos rfl, dif_pos h4096]
    rfl
  · rw [if_neg h0]
    unfold treeNodeAt
    rw [dif_pos ⟨by omega, by
      have : height lay - (level - 1) - 1 = height lay - level := by omega
      rw [this]; exact hc⟩]
    rfl

/-- Frontier positions of a bucket: levels at most `level`, indices inside the bucket's block. -/
theorem frontier_bound (leaves : List Nat) : ∀ (level node : Nat), ∀ p ∈ frontier leaves level node,
    p.1 ≤ level ∧ p.2 < (node + 1) * 2 ^ (level - p.1) := by
  intro level
  induction level with
  | zero =>
      intro node p hp
      unfold frontier at hp
      split_ifs at hp
      · cases hp
      · simp only [List.mem_singleton] at hp
        subst hp
        simp
  | succ l ih =>
      intro node p hp
      unfold frontier at hp
      split_ifs at hp
      · rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨h1, h2⟩ := ih (2 * node) p hp
          refine ⟨by omega, ?_⟩
          have hpow : 2 ^ (l + 1 - p.1) = 2 * 2 ^ (l - p.1) := by
            rw [show l + 1 - p.1 = (l - p.1) + 1 by omega, pow_succ]; ring
          rw [hpow]
          nlinarith
        · obtain ⟨h1, h2⟩ := ih (2 * node + 1) p hp
          refine ⟨by omega, ?_⟩
          have hpow : 2 ^ (l + 1 - p.1) = 2 * 2 ^ (l - p.1) := by
            rw [show l + 1 - p.1 = (l - p.1) + 1 by omega, pow_succ]; ring
          rw [hpow]
          nlinarith
      · simp only [List.mem_singleton] at hp
        subst hp
        simp

theorem fin7_val (c : Nat) (hc : c < 7) : (fin7 c).val = c := Nat.mod_eq_of_lt hc

/-- The opened secrets of a coordinate are the disclosed secret values. -/
theorem forestOpened_eq (T : Answers) (index : Fin (2^31)) (coord : Nat) (hc : coord < 7) (sel : Selection)
    (hb : sel.bucket < 16) (hl : ∀ leaf ∈ sel.leaves, leaf < 128) :
    forestOpened T index.val coord sel = (ftsOpened index coord sel).map (honestValue T) := by
  unfold forestOpened ftsOpened
  rw [filterMap_map_getD _ _ _ 0 (fun a ha => by
    obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp ha
    have := hl leaf hleaf
    rw [dif_pos (by omega)]; rfl)]
  apply List.map_congr_left
  intro a ha
  obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp ha
  have hlt : sel.bucket * 128 + leaf < 2048 := by have := hl leaf hleaf; omega
  rw [dif_pos hlt]
  change Extract.ftsSecret T index.val coord (sel.bucket * 128 + leaf) = _
  have hs := ftsSecret_eq T ⟨index, fin7 coord, ⟨sel.bucket * 128 + leaf, hlt⟩⟩
  simp only [fin7_val coord hc] at hs
  exact hs

/-- The proof nodes of a coordinate are the disclosed node values. -/
theorem forestProof_eq (h : Agrees T labels) (index : Fin (2^31)) (coord : Nat) (hc : coord < 7) (sel : Selection)
    (hb : sel.bucket < 16) :
    forestInner T index.val coord sel ++ forestOuter T index.val coord sel =
      (ftsProof index coord sel).map (honestValue T) := by
  have hcoord : (fin7 coord).val = coord := fin7_val coord hc
  have hval : ∀ level c, level ≤ 11 → c < 2 ^ (11 - level) →
      treeValue (evalWithAnswerFn T (buildFts index.val coord)).1 level c =
        ((ftsChild index (fin7 coord) level c).map (honestValue T)).getD 0 := by
    intro level c hl hcl
    have := ftsTree_eq h index (fin7 coord) level c hl hcl
    rw [hcoord] at this
    rw [this, ftsLabel_eq (secretsOf T), honestValue_eq h]
  unfold forestInner forestOuter ftsProof
  rw [List.map_append]
  congr 1
  · rw [filterMap_map_getD _ _ _ 0 (fun p hp => by
      obtain ⟨h1, h2⟩ := frontier_bound _ 7 sel.bucket p hp
      exact ftsChild_isSome _ _ _ _ (by omega) (by
        calc p.2 < (sel.bucket + 1) * 2 ^ (7 - p.1) := h2
          _ ≤ 16 * 2 ^ (7 - p.1) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ (11 - p.1) := by
            rw [show 11 - p.1 = 4 + (7 - p.1) by omega, pow_add]; norm_num))]
    apply List.map_congr_left
    intro p hp
    obtain ⟨h1, h2⟩ := frontier_bound _ 7 sel.bucket p hp
    exact hval _ _ (by omega) (by
      calc p.2 < (sel.bucket + 1) * 2 ^ (7 - p.1) := h2
        _ ≤ 16 * 2 ^ (7 - p.1) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ (11 - p.1) := by
          rw [show 11 - p.1 = 4 + (7 - p.1) by omega, pow_add]; norm_num)
  · have hbound : ∀ j ∈ List.range 4, sel.bucket / 2 ^ j ^^^ 1 < 2 ^ (11 - (7 + j)) := by
      intro j hj
      rw [List.mem_range] at hj
      apply Nat.xor_lt_two_pow
      · interval_cases j <;> norm_num <;> omega
      · interval_cases j <;> norm_num
    rw [filterMap_map_getD _ _ _ 0 (fun j hj => ftsChild_isSome _ _ _ _ (by
      have := List.mem_range.mp hj; omega) (hbound j hj))]
    apply List.map_congr_left
    intro j hj
    exact hval _ _ (by have := List.mem_range.mp hj; omega) (hbound j hj)

end Honest

/-! ## Layer pieces -/

section Layers
variable {T : Answers} {labels : Labels}

theorem chainItem_value (h : Agrees T labels) (L : LeafPos) (digits : List Nat) (i : Nat) (hi : i < 58)
    (hd : digits.getD i 0 ≤ 7) :
    leafValue T L.lay L.tree.val L.leaf.val digits i = honestValue T (chainItem L i (digits.getD i 0)) := by
  rw [leafValue_eq h L digits i hi hd, honestValue_eq h]
  unfold chainItem ChainGraph.value
  by_cases h0 : digits.getD i 0 = 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]; rfl

/-- The honest pieces of a route layer are its disclosed chain and path values. -/
theorem honestPieces_eq (h : Agrees T labels) (index : Fin (2^31)) (lay : Layer) :
    honestPieces T lay (route index.val lay).2 (route index.val lay).1 (Wots.referenceDigits T (routeAddr index.val lay)) =
      ((layerChains (Wots.referenceDigits T) index lay).map (honestValue T), (layerPath index lay).map (honestValue T)) := by
  have htree := route_tree_lt index.val index.isLt lay
  have ht31 : (route index.val lay).2 < 2 ^ 31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hleaf := route_leaf_bound index.val lay
  have hl4096 : (route index.val lay).1 < 4096 := lt_of_lt_of_le hleaf (by
    calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      _ = 4096 := by norm_num)
  unfold honestPieces layerChains layerPath
  rw [dif_pos ⟨ht31, hl4096⟩, dif_pos ht31]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hi58 : i < 58 := lt_of_lt_of_le hi (by fin_cases lay <;> decide)
    have hd : (Wots.referenceDigits T (routeAddr index.val lay)).getD i 0 ≤ 7 := by
      have hle : (Wots.referenceDigits T (routeAddr index.val lay)).getD i 0 ≤ maxDigit lay i :=
        WotsExtract.depth_le T ⟨routeAddr index.val lay, i⟩ hi
      have hw : maxDigit lay i ≤ 7 := by unfold maxDigit; split_ifs <;> norm_num
      omega
    exact chainItem_value h ⟨lay, ⟨_, ht31⟩, ⟨_, hl4096⟩⟩ _ i hi58 hd
  · have hc : ∀ j ∈ List.range (height lay),
        (route index.val lay).1 / 2 ^ j ^^^ 1 < 2 ^ (height lay - j) := by
      intro j hj
      rw [List.mem_range] at hj
      apply Nat.xor_lt_two_pow
      · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show height lay - j + j = height lay by omega]
        exact hleaf
      · exact Nat.one_lt_two_pow (by omega)
    rw [filterMap_map_getD _ _ _ 0 (fun j hj => treeChild_isSome _ _ _ _
      (by have := List.mem_range.mp hj; omega) (hc j hj) (Or.inl (List.mem_range.mp hj)))]
    apply List.map_congr_left
    intro j hj
    rw [builtTree_eq h lay ⟨_, ht31⟩ j _ (by have := List.mem_range.mp hj; omega) (hc j hj),
      treeLabel_eq (secretsOf T), honestValue_eq h]

/-- The honest pieces of a route layer. -/
noncomputable def layerPieces (T : Answers) (index : Nat) (lay : Layer) : Pieces :=
  honestPieces T lay (route index lay).2 (route index lay).1 (Wots.referenceDigits T (routeAddr index lay))

theorem referenceSearch_route (T : Answers) (index : Nat) (lay : Layer) :
    Wots.referenceSearch T (routeAddr index lay) =
      evalWithAnswerFn T (counterSearch lay (route index lay).2 (route index lay).1
        (Extract.honestMsg T index lay) 0 counterLimit) := by
  unfold Wots.referenceSearch
  rw [show routeAddr index lay = WotsExtract.routeLeaf index lay from rfl, WotsExtract.leafMsg_route]
  rfl

theorem referenceDigits_some (T : Answers) (L : Wots.LeafAddr) (c : BitVec 32) (digits : List Nat)
    (h : Wots.referenceSearch T L = some (c, digits)) : Wots.referenceDigits T L = digits := by
  unfold Wots.referenceDigits
  rw [h]
  rfl

/-- **Closed form of the layer signer** on the honest message chain. -/
theorem signLayers_eq (T : Answers) (cache : T3.Cache) (hcache : cache.region = Correctness.cacheRegion (Correctness.maskedTop T))
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → evalWithAnswerFn T (signLayers cache index n (Extract.walkTarget T index n)) =
      if ∀ l, l < n → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome then
        some ((List.range n).map fun l => layerPieces T index (Fin.ofNat 4 l))
      else none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [signLayers]
  | succ n ih =>
      intro hn
      have hlay : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      have hmsg : Extract.walkTarget T index (n + 1) = Extract.honestMsg T index (Fin.ofNat 4 n) := by
        have hl : (⟨n, by omega⟩ : Layer) = Fin.ofNat 4 n := Fin.ext hlay.symm
        simp only [Extract.walkTarget, dif_pos (show n < 4 by omega), hl]
      rw [hmsg]
      simp only [signLayers, evalWithAnswerFn_bind]
      rw [← referenceSearch_route]
      cases hs : Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 n)) with
      | none =>
          simp only [evalWithAnswerFn_pure]
          rw [if_neg (fun hall => by have := hall n (by omega); rw [hs] at this; cases this)]
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hdig := referenceDigits_some T _ counter digits hs
          have hdec : decode (Fin.ofNat 4 n) _ = some digits := WotsExtract.referenceSearch_decode T _ hs
          have hvalid := Cost.validDigits_decode hdec
          simp only
          by_cases hn0 : n = 0
          · subst hn0
            simp only [if_true, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
            have hl0 : (Fin.ofNat 4 0 : Layer) = 0 := rfl
            rw [hl0] at hvalid hdig hs ⊢
            have htop := route_top_tree index hindex
            rw [Correctness.eval_signTop_honest T cache _ digits hcache (by
              have := route_leaf_bound index 0
              calc (route index 0).1 < 2 ^ height 0 := this
                _ = 4096 := by decide) hvalid]
            rw [if_pos (fun l hl => by
              have : l = 0 := by omega
              subst this; rw [hl0, hs]; rfl)]
            rw [Nat.zero_add, List.range_one, List.map_singleton]
            unfold layerPieces
            rw [hl0, hdig, htop]
          · simp only [hn0, if_false, evalWithAnswerFn_bind]
            rw [Correctness.eval_buildTree_result T _ _ _ digits hvalid (route_leaf_bound index _)]
            simp only
            have hroot : ((builtTree T (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).getD
                (height (Fin.ofNat 4 n)) []).getD 0 0 = Extract.walkTarget T index n := by
              rw [Extract.walkTarget_root T index n (by omega)]
              rfl
            rw [hroot, ih (by omega)]
            by_cases hall : ∀ l, l < n → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome
            · rw [if_pos hall, if_pos (fun l hl => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
                · exact hall l hl
                · rw [hs]; rfl)]
              simp only [evalWithAnswerFn_pure, Option.some.injEq, List.range_succ, List.map_append,
                List.map_cons, List.map_nil]
              congr 2
              unfold layerPieces honestPieces
              rw [hdig]
              rfl
            · rw [if_neg hall, if_neg (fun h' => hall fun l hl => h' l (by omega))]
              simp only [evalWithAnswerFn_pure]

end Layers

/-! ## The whole payload -/

section Payload

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.flatMap_cons]
      rw [h a (List.mem_cons_self), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem selection_bounds (N : HashOutput) (c : Nat) (hc : c < 7) :
    ((selections N).getD c ⟨0, []⟩).bucket < 16 ∧ ∀ leaf ∈ ((selections N).getD c ⟨0, []⟩).leaves, leaf < 128 := by
  simp only [selections, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some]
  refine ⟨Nat.mod_lt _ (by decide), fun leaf hleaf => ?_⟩
  rw [List.mem_mergeSort] at hleaf
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hleaf
  exact Nat.mod_lt _ (by decide)

theorem forestOpenPrefix_eq (T : Answers) (N : HashOutput) :
    forestOpenPrefix T (digestIndex N).val (selections N) 7 =
      ((List.range 7).flatMap fun c => ftsOpened (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map
        (honestValue T) := by
  unfold forestOpenPrefix
  rw [List.map_flatMap]
  apply flatMap_congr_mem
  intro c hc
  have hc7 := List.mem_range.mp hc
  exact forestOpened_eq T _ c hc7 _ (selection_bounds N c hc7).1 (selection_bounds N c hc7).2

theorem forestProofPrefix_eq {T : Answers} {labels : Labels} (h : Agrees T labels) (N : HashOutput) :
    forestProofPrefix T (digestIndex N).val (selections N) 7 =
      ((List.range 7).flatMap fun c => ftsProof (digestIndex N) c ((selections N).getD c ⟨0, []⟩)).map
        (honestValue T) := by
  unfold forestProofPrefix
  rw [List.map_flatMap]
  apply flatMap_congr_mem
  intro c hc
  have hc7 := List.mem_range.mp hc
  exact forestProof_eq h _ c hc7 _ (selection_bounds N c hc7).1

theorem walkTarget_four (T : Answers) (index : Nat) :
    Extract.walkTarget T index 4 = evalWithAnswerFn T (forestPk index (forestRoots T index 7)) := by
  have h4 : Extract.walkTarget T index 4 = Extract.honestForest T index := by
    simp only [Extract.walkTarget, dif_pos (show 3 < 4 by decide), Extract.honestMsg]
    rfl
  rw [h4, WotsExtract.honestForest_eq_built]
  rfl

theorem routeOk_iff (T : Answers) (index : Nat) :
    (∀ l, l < 4 → (Wots.referenceSearch T (routeAddr index (Fin.ofNat 4 l))).isSome) ↔ RouteOk T index := by
  constructor
  · intro hall lay
    have := hall lay.val lay.isLt
    rwa [show (Fin.ofNat 4 lay.val : Layer) = lay from Fin.ext (by simp)] at this
  · intro hok l _
    exact hok _

/-- **The honest payload signer, closed form**: under `Agrees` and the honest published cache, it returns the
router's disclosure-built signature with the honest values (or `none` exactly when the digest search or a route
encoding search fails). -/
theorem signPayload_disclosed {T : Answers} {labels : Labels} (h : Agrees T labels) (cache : T3.Cache)
    (hcache : cache.region = Correctness.cacheRegion (Correctness.maskedTop T)) (m : Message) :
    evalWithAnswerFn T (signPayload cache m) =
      match signDigest T m with
      | none => none
      | some (_, N) =>
          if RouteOk T (N.toNat % 2 ^ 31) then
            some (assembleSig (evalWithAnswerFn T (privateNonce m)) N (honestValue T) (Wots.referenceDigits T))
          else none := by
  rw [Correctness.signPayload_eq]
  simp only [evalWithAnswerFn_bind]
  unfold signDigest
  cases hd : evalWithAnswerFn T (digestSearch (evalWithAnswerFn T (privateNonce m)) m 0 attemptLimit) with
  | none => rfl
  | some found =>
      obtain ⟨counter, N⟩ := found
      simp only [evalWithAnswerFn_bind]
      rw [Correctness.eval_signForest]
      simp only
      rw [← walkTarget_four, signLayers_eq T cache hcache _ (Nat.mod_lt _ (by positivity)) 4 le_rfl]
      by_cases hok : RouteOk T (N.toNat % 2 ^ 31)
      · rw [if_pos ((routeOk_iff T _).mpr hok), if_pos hok]
        simp only [evalWithAnswerFn_pure]
        unfold Correctness.assembledSignature assembleSig
        have ho := forestOpenPrefix_eq T N
        have hp := forestProofPrefix_eq h N
        simp only [digestIndex] at ho hp
        simp only [digestIndex]
        rw [ho, hp]
        congr 2
        funext lay
        congr 1
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by have := lay.isLt; omega),
          Option.map_some, Option.getD_some,
          show (Fin.ofNat 4 lay.val : Layer) = lay from Fin.ext (by simp)]
        exact honestPieces_eq h ⟨N.toNat % 2 ^ 31, Nat.mod_lt _ (by positivity)⟩ lay
      · rw [if_neg (fun h' => hok ((routeOk_iff T _).mp h')), if_neg hok]
        rfl

end Payload

end SigGolfCandidate.T3.Security.LargeResidual
