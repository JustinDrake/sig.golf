import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.New.BC.Respects
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.Secc.WotsMask

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
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
theorem eval_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    evalWithAnswerFn (maskAt answers a) keygen = evalWithAnswerFn answers keygen := by
  unfold keygen
  refine Mask.eval_bind_of (Mask.eval_keygenPayload_maskAt answers a) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact Mask.eval_maskAt_of_respects answers a (Mask.Respects.bind (Mask.respects_privateMac a region) fun _ => Mask.Respects.pure' _)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
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
theorem signedMsg_succ (T : Answers) (index m : Nat) (hm : m < 3) :
    WCT9.LayerMsg.pair
      (WCT9.topPair (Fin.ofNat 4 (m + 1)) (builtTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2)).1
      (WCT9.topPair (Fin.ofNat 4 (m + 1)) (builtTree T (Fin.ofNat 4 (m + 1)) (route index (Fin.ofNat 4 (m + 1))).2)).2 =
      leafMsg T (routeLeaf index (Fin.ofNat 4 m)) := by
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
theorem signedMsg_top (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.LayerMsg.forest (Extract.honestForest T index) = leafMsg T (routeLeaf index 3) := by
  unfold leafMsg routeLeaf
  simp only [show ¬((3 : Layer).val < 3) by decide, dite_false]
  rw [route_top_index, Nat.mod_eq_of_lt hindex]
theorem routeLeaf_alias {index : Nat} (hindex : index < 2 ^ 31) {lay : Layer} {T : Answers} {counter : BitVec 32}
    {digits : List Nat} (hsearch : referenceSearch T (routeLeaf index lay) = some (counter, digits))
    (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (hal : LeafAlias lay (route index lay).2 (route index lay).1 a.key) :
    depth T a ≤ digits.getD a.chain 0 := by
  have hk : routeLeaf index lay = a.key :=
    hal.eq_of_lt (route_tree_lt index hindex lay) (route_leaf_lt index lay) htree hleaf
  unfold depth
  rw [← hk, referenceDigits_of_search hsearch]
theorem eval_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      evalWithAnswerFn (maskAt answers a) (WCT9.signLayersBC cache index n msg) =
        evalWithAnswerFn answers (WCT9.signLayersBC cache index n msg) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC, evalWithAnswerFn_bind]
      rw [eval_maskAt_of_respects answers a (respects_layerCounterSearch a _ _ _ _ _ _)]
      cases hs : evalWithAnswerFn answers (WCT9.layerCounterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (WCT9.layerCounterSearch_some answers _ _ _ msg counterLimit 0 counter digits
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
            cases evalWithAnswerFn answers (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
end Mask
theorem eval_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    evalWithAnswerFn (maskAt answers a) (signPayload cache message) =
      evalWithAnswerFn answers (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_signForest a _ _)) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    refine Mask.eval_bind_of (Mask.eval_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide)) 4
      le_rfl _ (fun m hm => ?_)) ?_
    · obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact Mask.signedMsg_top answers _ (Nat.mod_lt _ (by decide))
    · generalize evalWithAnswerFn answers (WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4 _) = pieces
      rcases pieces with _ | pieces <;> rfl
theorem eval_maskAt_coreSign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    evalWithAnswerFn (maskAt answers a) (sign cache message) = evalWithAnswerFn answers (sign cache message) := by
  rw [ClaudeWCT.W9.T3.Security.sign_eq]
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateMac a _)) ?_
  split
  · rfl
  · exact eval_maskAt_signPayload answers a htree hleaf cache message
theorem eval_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn (maskAt answers a) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn answers (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine Mask.eval_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateMac a _)) ?_
  split
  · exact eval_maskAt_signPayload answers a htree hleaf _ _
  · rfl
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
  · rw [Mask.maskAt_public, Mask.maskAt_public, ← hstep, hdepth, hfrontier]
    cases hp : prefixStep answers a input with
    | none => exact hrows input hp
    | some step => rfl
  · rw [Mask.maskAt_tweak, Mask.maskAt_tweak, hdepth]
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
          exact Mask.leafSeed_eq T _ _ _ _
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
theorem maskAt_idem (answers : Answers) (a : ChainAddr) : maskAt (maskAt answers a) a = maskAt answers a := by
  have hstep : prefixStep (maskAt answers a) a = prefixStep answers a := by
    funext input
    unfold prefixStep
    simp only [depth_maskAt]
  apply maskAt_congr
  · intro input hp
    rw [hstep] at hp
    rw [Mask.maskAt_public, hp]
  · intro coin
    rfl
  · intro coordinate hc
    rcases coordinate with tweak | other
    · exact Mask.maskAt_untouched answers a (q := .inr (.inl tweak)) (fun h => hc (congrArg Sum.inl h))
    · rfl
  · rw [Mask.maskAt_tweak]
    by_cases hd : 1 ≤ depth answers a
    · rw [if_pos (⟨rfl, hd⟩ : seedTweak a = seedTweak a ∧ 1 ≤ depth answers a)]
      unfold siblingHalf
      by_cases h0 : a.chain % 2 = 0
      · rw [if_pos h0, if_pos h0, if_pos h0, ChainGraph.joinOutput_high]
      · rw [if_neg h0, if_neg h0, if_neg h0, ChainGraph.joinOutput_low]
    · rw [if_neg (fun h => hd h.2)]
  · exact depth_maskAt answers a
  · exact frontierValue_maskAt answers a
theorem eval_keygen_of_maskAt_eq (answers answers' : Answers) (a : ChainAddr)
    (h : maskAt answers a = maskAt answers' a) :
    evalWithAnswerFn answers keygen = evalWithAnswerFn answers' keygen := by
  rw [← eval_maskAt_keygen answers a, h, eval_maskAt_keygen]
theorem eval_sign_of_maskAt_eq (answers answers' : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (h : maskAt answers a = maskAt answers' a) (published : SigGolfCandidate.T3.Cache)
    (request : Request) :
    evalWithAnswerFn answers (FullGame.authenticatedSign published request) =
      evalWithAnswerFn answers' (FullGame.authenticatedSign published request) := by
  rw [← eval_maskAt_sign answers a htree hleaf, h, eval_maskAt_sign answers' a htree hleaf]
end ClaudeWCT.W9.T3.Security.Wots
