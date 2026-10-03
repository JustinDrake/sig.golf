import SigGolfCandidate.T3.Secc.WotsMaskChain

/-!
# F1: frontier factorisation of honest outputs (`eval_maskAt_keygen`, `eval_maskAt_sign`, `maskAt_congr`)

For one chain address `a`, T3's honest programs read `a`'s canonical prefix rows and `a`'s seed half only through
`frontierValue answers a`:
* `eval_maskAt_keygen`: honest key generation evaluates identically under `maskAt answers a` (every address).
* `eval_maskAt_signPayload`, `eval_maskAt_coreSign`, `eval_maskAt_sign` (SEC's `FullGame.authenticatedSign`): the
  signer, on any cache and message, evaluates identically (source-sized `a`: `a.key.tree < 2^40`, `a.key.leaf < 2^32`).
  The signer reveals chain `a` exactly at the reference digit `depth answers a` (its counter search *is*
  `referenceSearch`), never below it.
* `maskAt_congr`: two tables agreeing outside `a`'s prefix rows and `a`'s seed half, with the same depth and frontier
  value, have the same mask; hence (`eval_keygen_of_maskAt_eq`, `eval_sign_of_maskAt_eq`) the same honest outputs.
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
variable (answers : Answers) (a : ChainAddr)

theorem eval_mask_maskAt (level index : Nat) :
    evalWithAnswerFn (maskAt answers a) (mask level index) = evalWithAnswerFn answers (mask level index) :=
  eval_maskAt_of_respects answers a (respects_mask a level index)

theorem eval_nodeHash3_maskAt (lay tree heap : Nat) (left right : Digest) :
    evalWithAnswerFn (maskAt answers a) (nodeHash 3 lay tree heap left right) =
      evalWithAnswerFn answers (nodeHash 3 lay tree heap left right) :=
  eval_maskAt_of_respects answers a (respects_nodeHash a 3 lay tree heap left right (by decide))

theorem eval_keygenPayload_maskAt :
    evalWithAnswerFn (maskAt answers a) keygenPayload = evalWithAnswerFn answers keygenPayload := by
  rw [Correctness.keygenPayload_eq, Correctness.eval_cachePayloadProgram, Correctness.eval_cachePayloadProgram,
    Correctness.eval_buildTree_levels (maskAt answers a) 0 0 0 [] (Cost.validDigits_nil 0),
    Correctness.eval_buildTree_levels answers 0 0 0 [] (Cost.validDigits_nil 0), builtTree_maskAt]
  simp only [eval_mask_maskAt]

end Mask

/-- **`eval_maskAt_keygen`**: honest key generation (public key and cache) is unchanged by the mask, for every
address `a`. -/
theorem eval_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    evalWithAnswerFn (maskAt answers a) keygen = evalWithAnswerFn answers keygen := by
  unfold keygen
  refine eval_bind_of (eval_keygenPayload_maskAt answers a) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact eval_maskAt_of_respects answers a (Respects.bind (respects_privateMac a region) fun _ => Respects.pure' _)

namespace Mask
variable (answers : Answers) (a : ChainAddr)

/-- The signature-only leaf builder in closed form (root slot `0`). -/
theorem eval_buildLeaf_sig (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    evalWithAnswerFn T (buildLeaf lay tree leaf digits true) =
      (0, (List.range (chainCount lay)).map (leafValue T lay tree leaf digits)) := by
  have h2 := Correctness.eval_buildLeaf_values T lay tree leaf digits hvalid true
  have h1 : (evalWithAnswerFn T (buildLeaf lay tree leaf digits true)).1 = 0 := by
    rw [Correctness.buildLeaf_eq]
    simp only [evalWithAnswerFn_bind, ↓reduceIte, evalWithAnswerFn_pure]
  exact Prod.ext h1 h2

/-- The leaf values of a word reading every alias of `a` at or above `a`'s frontier are unchanged. -/
theorem leafValues_maskAt (lay : Layer) (tree leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits lay digits)
    (halias : LeafAlias lay tree leaf a.key → a.chain < chainCount lay → depth answers a ≤ digits.getD a.chain 0) :
    (List.range (chainCount lay)).map (leafValue (maskAt answers a) lay tree leaf digits) =
      (List.range (chainCount lay)).map (leafValue answers lay tree leaf digits) := by
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  apply leafValue_maskAt answers a lay tree leaf digits i hi'
  · have := hvalid i hi'
    have := width_le lay i
    omega
  · intro hal hia
    subst hia
    exact halias hal hi'

/-- The top-layer authentication path (two recomputed siblings, ten cached and unmasked ones) is unchanged, for
every cache. -/
theorem eval_topPath_maskAt (cache : Cache) (leaf : Nat) :
    evalWithAnswerFn (maskAt answers a) (topPath cache leaf) = evalWithAnswerFn answers (topPath cache leaf) := by
  simp only [topPath, evalWithAnswerFn_bind, Correctness.eval_mapM, evalWithAnswerFn_pure,
    Correctness.eval_buildLeaf_root _ 0 0 _ [] (Cost.validDigits_nil 0), leafRoot_maskAt, eval_nodeHash3_maskAt,
    eval_mask_maskAt]

theorem eval_signTop_maskAt (cache : Cache) (leaf : Nat) (digits : List Nat) (hvalid : Cost.ValidDigits 0 digits)
    (halias : LeafAlias 0 0 leaf a.key → a.chain < chainCount 0 → depth answers a ≤ digits.getD a.chain 0) :
    evalWithAnswerFn (maskAt answers a) (signTop cache leaf digits) =
      evalWithAnswerFn answers (signTop cache leaf digits) := by
  simp only [signTop, evalWithAnswerFn_bind, eval_buildLeaf_sig _ 0 0 leaf digits hvalid, evalWithAnswerFn_pure,
    eval_topPath_maskAt answers a, leafValues_maskAt answers a 0 0 leaf digits hvalid halias]

theorem eval_buildTree_maskAt (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (hsel : selected < 2 ^ height lay)
    (halias : LeafAlias lay tree selected a.key → a.chain < chainCount lay → depth answers a ≤ digits.getD a.chain 0) :
    evalWithAnswerFn (maskAt answers a) (buildTree lay tree selected digits) =
      evalWithAnswerFn answers (buildTree lay tree selected digits) := by
  rw [Correctness.eval_buildTree_result _ lay tree selected digits hvalid hsel,
    Correctness.eval_buildTree_result _ lay tree selected digits hvalid hsel, builtTree_maskAt,
    leafValues_maskAt answers a lay tree selected digits hvalid halias]

/-! ## The layer signer -/

/-- The leaf the signer uses at layer `lay` for a message index (`route`). -/
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩

theorem route_tree_succ (index m : Nat) (hm : m < 3) :
    (route index (Fin.ofNat 4 (m + 1))).2 =
      (route index (Fin.ofNat 4 m)).2 * 2 ^ height (Fin.ofNat 4 m) + (route index (Fin.ofNat 4 m)).1 := by
  interval_cases m
  · change index / 2 ^ (12 + 7) = index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (6 + 6) = index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7
    simp only [Nat.reducePow, Nat.reduceAdd]; omega
  · change index / 2 ^ (0 + 6) = index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6
    simp only [Nat.reducePow, Nat.reduceAdd]; omega

theorem route_top_index (index : Nat) : (route index 3).2 * 2 ^ height 3 + (route index 3).1 = index := by
  change index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
  simp only [Nat.reducePow, Nat.reduceAdd]; omega

theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) : (route index lay).2 < 2 ^ 40 := by
  have : (route index lay).2 ≤ index := Nat.div_le_self _ _
  have : (2 : Nat) ^ 31 < 2 ^ 40 := by decide
  omega

theorem route_leaf_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ 32 := by
  have h := route_leaf_bound index lay
  have : 2 ^ height lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide)
  omega

/-- The signer's message one layer down is the honest message of that layer's route leaf. -/
theorem signedMsg_succ (T : Answers) (index m : Nat) (hm : m < 3) :
    (((builtTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2).getD
      (height (Fin.ofNat 4 (m + 1)) - 1) []).getD 0 0, 0, ((builtTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2).getD
      (height (Fin.ofNat 4 (m + 1)) - 1) []).getD 1 0) = leafMsg T (routeLeaf index (Fin.ofNat 4 m)) := by
  have hl : (Fin.ofNat 4 m : Layer).val < 3 := by
    change m % 4 < 3
    omega
  have hlay : (⟨(Fin.ofNat 4 m : Layer).val + 1, by omega⟩ : Layer) = Fin.ofNat 4 (m + 1) := by
    apply Fin.ext
    change m % 4 + 1 = (m + 1) % 4
    omega
  unfold leafMsg routeLeaf
  simp only [dif_pos hl]
  rw [hlay, ← route_tree_succ index m hm]
  rfl

/-- The signer's top message (the forest pk) is the honest message of the layer-3 route leaf. -/
theorem signedMsg_top (T : Answers) (index : Nat) :
    ((evalWithAnswerFn T (forestPk index (Correctness.forestRoots T index 7)), 0, 0) : Digest × BitVec 96 × Digest) =
      leafMsg T (routeLeaf index 3) := by
  unfold leafMsg routeLeaf
  simp only [show ¬((3 : Layer).val < 3) by decide, dite_false]
  rw [route_top_index, honestForest_eq]
  rfl

/-- At a route leaf, an alias of a source-sized `a` is `a`'s leaf itself, whose signed word is the reference word. -/
theorem routeLeaf_alias {index : Nat} (hindex : index < 2 ^ 31) {lay : Layer} {T : Answers} {counter : BitVec 32}
    {digits : List Nat} (hsearch : referenceSearch T (routeLeaf index lay) = some (counter, digits))
    (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (hal : LeafAlias lay (route index lay).2 (route index lay).1 a.key) :
    depth T a ≤ digits.getD a.chain 0 := by
  have hk : routeLeaf index lay = a.key :=
    hal.eq_of_lt (route_tree_lt index hindex lay) (route_leaf_lt index lay) htree hleaf
  unfold depth
  rw [← hk, referenceDigits_of_search hsearch]

/-- **The layer signer under the mask.** With honest messages at every layer (the forest pk on top, then the
roots), `signLayers` evaluates identically for a source-sized `a`. -/
theorem eval_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      evalWithAnswerFn (maskAt answers a) (signLayers cache index n msg) =
        evalWithAnswerFn answers (signLayers cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [signLayers, evalWithAnswerFn_bind]
      rw [eval_maskAt_of_respects answers a (respects_counterSearch a _ _ _ _ _ _)]
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (Correctness.counterSearch_some answers _ _ _ msg counterLimit 0 counter digits
            (by decide) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch answers (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          dsimp only
          split_ifs with hn0
          · subst hn0
            simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
            rw [eval_signTop_maskAt answers a cache _ digits hvalid]
            intro hal _
            apply routeLeaf_alias a hindex hsearch htree hleaf
            have ht : (route index (Fin.ofNat 4 0)).2 = 0 := route_top_tree index hindex
            rw [ht]
            exact hal
          · simp only [evalWithAnswerFn_bind]
            rw [eval_buildTree_maskAt answers a _ _ _ digits hvalid (route_leaf_bound index _)
                (fun hal _ => routeLeaf_alias a hindex hsearch htree hleaf hal),
              Correctness.eval_buildTree_result answers _ _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            rw [ih (by omega) _ (fun m' hm' => by
              obtain rfl : m = m' := by omega
              exact signedMsg_succ answers index m (by omega))]
            cases evalWithAnswerFn answers (signLayers cache index (m + 1) _) <;> rfl

end Mask

/-- **The payload signer under the mask** (any cache, any message; source-sized `a`). -/
theorem eval_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    evalWithAnswerFn (maskAt answers a) (signPayload cache message) =
      evalWithAnswerFn answers (signPayload cache message) := by
  rw [Correctness.signPayload_eq]
  refine eval_bind_of (eval_maskAt_of_respects answers a (respects_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine eval_bind_of (eval_maskAt_of_respects answers a (respects_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine eval_bind_of (eval_maskAt_of_respects answers a (respects_signForest a _ _)) ?_
    rw [Correctness.eval_signForest]
    dsimp only
    refine eval_bind_of (eval_maskAt_of_respects answers a (respects_forestPk a _ _)) ?_
    refine eval_bind_of (eval_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide)) 4
      le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      exact signedMsg_top answers _
    · generalize evalWithAnswerFn answers (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
      rcases pieces with _ | pieces <;> rfl

/-- **Core's signer** (`T3.sign`: MAC check, then the payload) under the mask. -/
theorem eval_maskAt_coreSign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    evalWithAnswerFn (maskAt answers a) (T3.sign cache message) = evalWithAnswerFn answers (T3.sign cache message) := by
  unfold T3.sign
  refine eval_bind_of (eval_maskAt_of_respects answers a (respects_privateMac a _)) ?_
  split
  · rfl
  · exact eval_maskAt_signPayload answers a htree hleaf cache message

/-- **`eval_maskAt_sign`**: SEC's logged signer `FullGame.authenticatedSign` on any published cache and request
evaluates identically under the mask (source-sized `a`). -/
theorem eval_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn (maskAt answers a) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn answers (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine eval_bind_of (eval_maskAt_of_respects answers a (respects_privateMac a _)) ?_
  split
  · exact eval_maskAt_signPayload answers a htree hleaf _ _
  · rfl

/-! ## The mask depends on the hidden part of `a` only through the frontier value -/

/-- **`maskAt_congr`.** Two tables that agree outside `a`'s prefix rows and outside `a`'s seed half (the sibling
half of `seedTweak a` agrees, `hsibling`), with the same depth and frontier value, have the same mask.
(The prototype omitted `hsibling`; without it the statement is false, since the mask keeps the sibling half.) -/
theorem maskAt_congr (answers answers' : Answers) (a : ChainAddr)
    (hrows : ∀ input, prefixStep answers a input = none →
      answers (.inl (.inr input)) = answers' (.inl (.inr input)))
    (hcoins : ∀ coin, answers (.inl (.inl coin)) = answers' (.inl (.inl coin)))
    (hprivate : ∀ coordinate, coordinate ≠ .inl (seedTweak a) →
      answers (.inr coordinate) = answers' (.inr coordinate))
    (hsibling : siblingHalf a (answers (.inr (.inl (seedTweak a)))) =
      siblingHalf a (answers' (.inr (.inl (seedTweak a)))))
    (hdepth : depth answers a = depth answers' a)
    (hfrontier : frontierValue answers a = frontierValue answers' a) :
    maskAt answers a = maskAt answers' a := by
  have hstep : prefixStep answers a = prefixStep answers' a := by
    funext input
    unfold prefixStep
    simp only [hdepth]
  funext q
  rcases q with (coin | input) | (tweak | other)
  · exact hcoins coin
  · rw [maskAt_public, maskAt_public, ← hstep, hdepth, hfrontier]
    cases hp : prefixStep answers a input with
    | none => exact hrows input hp
    | some step => rfl
  · rw [maskAt_tweak, maskAt_tweak, hdepth]
    by_cases ht : tweak = seedTweak a
    · subst ht
      by_cases hd : 1 ≤ depth answers' a
      · have hc : seedTweak a = seedTweak a ∧ 1 ≤ depth answers' a := ⟨rfl, hd⟩
        rw [if_pos hc, if_pos hc]
        by_cases h0 : a.chain % 2 = 0
        · have e : (answers (.inr (.inl (seedTweak a)))).extractLsb' 128 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 128 128 := by
            simpa only [siblingHalf, if_pos h0] using hsibling
          rw [if_pos h0, if_pos h0, e]
        · have e : (answers (.inr (.inl (seedTweak a)))).extractLsb' 0 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 0 128 := by
            simpa only [siblingHalf, if_neg h0] using hsibling
          rw [if_neg h0, if_neg h0, e]
      · have hc : ¬(seedTweak a = seedTweak a ∧ 1 ≤ depth answers' a) := fun h => hd h.2
        rw [if_neg hc, if_neg hc]
        have h0 : depth answers a = 0 := by omega
        have h0' : depth answers' a = 0 := by omega
        have hseed : ∀ T : Answers, depth T a = 0 → frontierValue T a =
            (if a.chain % 2 = 0 then (T (.inr (.inl (seedTweak a)))).extractLsb' 0 128
             else (T (.inr (.inl (seedTweak a)))).extractLsb' 128 128) := by
          intro T hT
          unfold frontierValue honestChainValue
          rw [hT]
          exact leafSeed_eq T _ _ _ _
        rw [hseed answers h0, hseed answers' h0'] at hfrontier
        rw [← ChainGraph.joinOutput_parts (answers (.inr (.inl (seedTweak a)))),
          ← ChainGraph.joinOutput_parts (answers' (.inr (.inl (seedTweak a))))]
        by_cases h2 : a.chain % 2 = 0
        · have e1 : (answers (.inr (.inl (seedTweak a)))).extractLsb' 0 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 0 128 := by
            simpa only [if_pos h2] using hfrontier
          have e2 : (answers (.inr (.inl (seedTweak a)))).extractLsb' 128 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 128 128 := by
            simpa only [siblingHalf, if_pos h2] using hsibling
          rw [e1, e2]
        · have e1 : (answers (.inr (.inl (seedTweak a)))).extractLsb' 128 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 128 128 := by
            simpa only [if_neg h2] using hfrontier
          have e2 : (answers (.inr (.inl (seedTweak a)))).extractLsb' 0 128 =
              (answers' (.inr (.inl (seedTweak a)))).extractLsb' 0 128 := by
            simpa only [siblingHalf, if_neg h2] using hsibling
          rw [e1, e2]
    · rw [if_neg (fun h => ht h.1), if_neg (fun h => ht h.1)]
      exact hprivate (.inl tweak) (fun h => ht (Sum.inl.inj h))
  · exact hprivate (.inr other) (fun h => by cases h)

/-- The mask is idempotent. -/
theorem maskAt_idem (answers : Answers) (a : ChainAddr) : maskAt (maskAt answers a) a = maskAt answers a := by
  have hstep : prefixStep (maskAt answers a) a = prefixStep answers a := by
    funext input
    unfold prefixStep
    simp only [depth_maskAt]
  apply maskAt_congr
  · intro input hp
    rw [hstep] at hp
    rw [maskAt_public, hp]
  · intro coin
    rfl
  · intro coordinate hc
    rcases coordinate with tweak | other
    · exact maskAt_untouched answers a (q := .inr (.inl tweak)) (fun h => hc (congrArg Sum.inl h))
    · rfl
  · rw [maskAt_tweak]
    by_cases hd : 1 ≤ depth answers a
    · rw [if_pos (⟨rfl, hd⟩ : seedTweak a = seedTweak a ∧ 1 ≤ depth answers a)]
      unfold siblingHalf
      by_cases h0 : a.chain % 2 = 0
      · rw [if_pos h0, if_pos h0, if_pos h0, ChainGraph.joinOutput_high]
      · rw [if_neg h0, if_neg h0, if_neg h0, ChainGraph.joinOutput_low]
    · rw [if_neg (fun h => hd h.2)]
  · exact depth_maskAt answers a
  · exact frontierValue_maskAt answers a

/-- Honest key generation is a function of the mask (hence of the rest and the frontier value of `a`). -/
theorem eval_keygen_of_maskAt_eq (answers answers' : Answers) (a : ChainAddr)
    (h : maskAt answers a = maskAt answers' a) :
    evalWithAnswerFn answers keygen = evalWithAnswerFn answers' keygen := by
  rw [← eval_maskAt_keygen answers a, h, eval_maskAt_keygen]

/-- The logged signer is a function of the mask (source-sized `a`). -/
theorem eval_sign_of_maskAt_eq (answers answers' : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (h : maskAt answers a = maskAt answers' a) (published : T3.Cache)
    (request : Request) :
    evalWithAnswerFn answers (FullGame.authenticatedSign published request) =
      evalWithAnswerFn answers' (FullGame.authenticatedSign published request) := by
  rw [← eval_maskAt_sign answers a htree hleaf, h, eval_maskAt_sign answers' a htree hleaf]

end SigGolfCandidate.T3.Security.Wots
