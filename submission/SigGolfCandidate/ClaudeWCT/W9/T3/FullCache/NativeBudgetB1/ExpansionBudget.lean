import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.T3.FullCache.ExpansionCost
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.PairRows
import SigGolfCandidate.ClaudeWCT.WCT9.Cost

section


namespace ClaudeWCT.W9.T3.FullCacheExpansionCost
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query)
open SigGolfCandidate.T3.FullCacheExpansionCost (foldlM_cost_ge privatePair_cost)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem buildChild_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index coord selected : Nat)
    (word : ClaudeWCT.WCT9.Rank) :
    4 ≤ cost answers (ClaudeWCT.WCT9.buildChild index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildChild
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) (pair : Fin 4) => do
      let seeds ← privatePair 8 coord index 0 (4 * selected + pair.val)
      (List.finRange 2).foldlM
        (fun (state : List Digest × List Digest) half => do
          if h : 2 * pair.val + half.val < 7 then
            let i : Fin 7 := ⟨2 * pair.val + half.val, h⟩
            let secret := if half.val = 0 then seeds.1 else seeds.2
            let deficit := ClaudeWCT.WCT9.digit word i
            let value ← ClaudeWCT.WCT9.chain index coord selected i.val 0 (3 - deficit) secret
            let last ← ClaudeWCT.WCT9.chain index coord selected i.val (3 - deficit) deficit value
            pure (state.1 ++ [last], state.2 ++ [value])
          else pure state) state) 1
    (fun state pair => by
      simp only [cost_bind, privatePair_cost]
      omega) (List.finRange 4) ([], [])
  simpa only [List.length_finRange, Nat.mul_one] using h
theorem buildCoordinate_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (coord : ClaudeWCT.WCT9.Coord) (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    512 ≤ cost answers (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  rw [cost_bind]
  apply Nat.le_trans _ (Nat.le_add_right _ _)
  have h := foldlM_cost_ge answers
    (fun (state : List Digest × List Digest) (j : Nat) => do
      let (root, values) ← ClaudeWCT.WCT9.buildChild index coord.val j word
      pure (state.1 ++ [root], if j = selected.val then values else state.2)) 4
    (fun state j => by
      simp only [cost_bind, cost_pure, Nat.add_zero]
      exact buildChild_cost_ge answers index coord.val j word) (List.range 128) ([], [])
  simpa only [List.length_range] using h
theorem forestRows_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    4608 ≤ cost answers (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows
  apply (show 4608 = (List.finRange 9).length * 512 by decide).le.trans
  apply foldlM_cost_ge
  intro state coord
  unfold ClaudeWCT.WCT9.openingStep
  simp only [cost_bind, cost_pure, Nat.add_zero]
  exact buildCoordinate_cost_ge answers index coord _ _
theorem signForest_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (index : Nat)
    (output : HashOutput) :
    4608 ≤ cost answers (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest
  rw [cost_bind]
  exact (forestRows_cost_ge answers index output).trans (Nat.le_add_right _ _)
theorem signPayload_cost_ge (answers : SigGolfCandidate.T3.Correctness.Answers) (cache : Cache)
    (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) = some sig) :
    90 ≤ cost answers (ClaudeWCT.WCT9.Rev3.signPayload cache message) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at hs ⊢
  simp only [evalWithAnswerFn_bind] at hs
  rw [cost_bind]
  cases hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at hs
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [cost_bind, hd]
      have h := signForest_cost_ge answers (output.toNat % 2 ^ 31) output
      omega
end ClaudeWCT.W9.T3.FullCacheExpansionCost
end

section



namespace ClaudeWCT.W9.T3.ExpansionBudget
open OracleComp OracleSpec
open ClaudeWCT.WCT9 (Signature Witness digestAttemptLimit assembledSignature honestForest
  signForest_root assembled_forest_recovery toT3Signature)
open ClaudeWCT.WCT9.Rev3 (sign expand verify signPayload)
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SearchCost (cost cost_bind cost_pure cost_query cost_bound)
open SigGolfCandidate.T3.Correctness (Answers cacheRegion maskedTop PiecesAgree CacheTagCorrect
  keygen_correct keygen_cache_tag privateMac_count eval_buildTree_result builtTree honestPieces)
open SigGolfCandidate.T3.Cost (CBound GoodQuery Bound ValidDigits recoverLayerCost recoveryLayersCost
  leafHashCost bound_chain bound_leafHash bound_nodeHash bound_recoverLayer sum_finRange remaining_steps)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bound_recoverLayerPair (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (hd : ValidDigits lay digits) (hlen : digits.length = chainCount lay) (hsum : digits.sum = target lay) :
    CBound (fun _ => True) (recoverLayerCost lay) (ClaudeWCT.WCT9.recoverLayerPair sig index lay digits) := by
  unfold ClaudeWCT.WCT9.recoverLayerPair
  dsimp only
  refine (Bound.mapM_list (P := GoodQuery) (List.finRange (chainCount lay)) _
    (fun i => maxDigit lay i.val - digits.getD i.val 0) (fun i _ => bound_chain _ _ _ _ _ _ _)).bind'
    (l := leafHashCost lay + height lay) (fun ends hends => ?_) ?_
  · refine (bound_leafHash lay _ _ ends (by simpa using hends)).bind (fun root _ => ?_)
    refine ((Bound.foldlM_list (P := GoodQuery) (List.finRange (height lay - 1)) _
      (fun _ _ => True) (fun _ => 1) root trivial (fun i hi value _ => ?_)).bind
        (fun top _ => .pure _ 0 trivial)).mono_k (by simp)
    exact bound_nodeHash _ _ _ _ _ _
  · rw [sum_finRange (chainCount lay) (fun i => maxDigit lay i - digits.getD i 0),
      remaining_steps lay digits hd hlen hsum]
    simp only [recoverLayerCost]
    omega
theorem expandLayersBC_cost_le (answers : Answers) (cache : Cache) (index : Nat)
    (hcache : cache.region = cacheRegion (maskedTop answers)) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg pieces,
      evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) = some pieces →
      ∀ sig : Signature, PiecesAgree (toT3Signature sig) pieces n →
        cost answers (ClaudeWCT.WCT9.expandLayersBC sig index n msg) ≤
          cost answers (ClaudeWCT.WCT9.signLayersBC cache index n msg) + recoveryLayersCost n := by
  intro n
  induction n with
  | zero =>
      intro _ msg pieces _ sig _
      simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_pure, recoveryLayersCost]
      omega
  | succ n ih =>
      intro hn msg pieces he sig hagree
      have hsource := he
      simp only [ClaudeWCT.WCT9.signLayersBC, evalWithAnswerFn_bind] at he
      cases hs : evalWithAnswerFn answers (ClaudeWCT.WCT9.layerCounterSearch (Fin.ofNat 4 n)
        (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (ClaudeWCT.WCT9.layerCounterSearch_some answers (Fin.ofNat 4 n)
            (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg
            counterLimit 0 counter digits (by decide) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hls := decode_length_sum hd
          simp only [hs] at he
          by_cases hn0 : n = 0
          · subst n
            have hrec := cost_bound answers (bound_recoverLayer (toT3Signature sig) index (Fin.ofNat 4 0)
              digits hvalid hls.1 hls.2)
            simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, if_true,
              cost_pure, recoveryLayersCost, cost_bind, Nat.add_zero]
            omega
          · have hrec := cost_bound answers (bound_recoverLayerPair sig index (Fin.ofNat 4 n)
              digits hvalid hls.1 hls.2)
            simp only [hn0, if_false, evalWithAnswerFn_bind,
              eval_buildTree_result answers (Fin.ofNat 4 n) _ _ digits hvalid (route_leaf_bound index _)] at he
            cases hp : evalWithAnswerFn answers (ClaudeWCT.WCT9.signLayersBC cache index n
              (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                  (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) with
            | none => simp only [hp, evalWithAnswerFn_pure, reduceCtorEq] at he
            | some previous =>
                simp only [hp, evalWithAnswerFn_pure, Option.some.injEq] at he
                subst pieces
                obtain ⟨hlen, _⟩ := ClaudeWCT.WCT9.signLayersBC_expandLayersBC answers cache index hcache hindex
                  n (by omega) (by omega) _ previous hp
                change PiecesAgree (toT3Signature sig) (previous ++ [honestPieces answers (Fin.ofNat 4 n)
                  (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 digits]) (n + 1) at hagree
                have hlayer := PiecesAgree.last hlen (by omega) hagree
                have hrecover : evalWithAnswerFn answers
                    (ClaudeWCT.WCT9.recoverLayerPair sig index (Fin.ofNat 4 n) digits) =
                    ClaudeWCT.WCT9.builtPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
                  apply ClaudeWCT.WCT9.eval_recoverLayerPair_honest answers sig index (Fin.ofNat 4 n) digits hvalid
                  · intro i
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).values i = _
                    rw [hlayer]
                    simp [piecesSignature, honestPieces]
                  · intro j
                    change ((toT3Signature sig).layers (Fin.ofNat 4 n)).path j = _
                    rw [hlayer]
                    simp [piecesSignature, honestPieces]
                have hprevious := ih (by omega) _ previous hp sig (PiecesAgree.prefix hlen hagree)
                unfold ClaudeWCT.WCT9.builtPair at hrecover
                simp only [ClaudeWCT.WCT9.expandLayersBC, ClaudeWCT.WCT9.signLayersBC, cost_bind, hs, hn0,
                  if_false, hrecover, hp, eval_buildTree_result answers (Fin.ofNat 4 n) _ _ digits hvalid
                    (route_leaf_bound index _), recoveryLayersCost]
                cases hx : evalWithAnswerFn answers (ClaudeWCT.WCT9.expandLayersBC sig index n
                    (.pair (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                      (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).1
                      (ClaudeWCT.WCT9.topPair (Fin.ofNat 4 n)
                        (builtTree answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2)).2)) <;>
                  simp only [cost_pure, Nat.add_zero] <;> omega
theorem expand_cost_step (answers : Answers) (message : Message) (pk : Digest) (sig : Signature)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) = some (counter, output)) :
    cost answers (expand message pk sig) =
      cost answers (ClaudeWCT.WCT9.digestSearch sig.rho message 0 digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output) +
      cost answers (ClaudeWCT.WCT9.expandLayersBC sig (output.toNat % 2 ^ 31) 4
        (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.recoverFts sig (output.toNat % 2 ^ 31) output)))) := by
  simp only [ClaudeWCT.WCT9.Rev3.expand, ClaudeWCT.WCT9.expandWith, cost_bind, hd]
  split
  · split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
  · simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem signPayload_cost_step (answers : Answers) (cache : Cache) (message : Message)
    (counter : BitVec 32) (output : HashOutput)
    (hd : evalWithAnswerFn answers
      (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) = some (counter, output)) :
    cost answers (signPayload cache message) =
      cost answers (privateNonce message) +
      cost answers (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
        digestAttemptLimit) +
      cost answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output) +
      cost answers (ClaudeWCT.WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4
        (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2)) := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq]
  simp only [cost_bind, hd]
  split <;> simp only [cost_pure, Nat.add_zero, Nat.add_assoc]
theorem expand_cost_le_payload_add_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 := by
  rw [ClaudeWCT.WCT9.Rev3.signPayload_eq] at he
  simp only [evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers
    (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn answers (privateNonce message)) message 0
      digestAttemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hl : evalWithAnswerFn answers
        (ClaudeWCT.WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4
          (.forest (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).2)) with
      | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some pieces =>
          simp only [hl, evalWithAnswerFn_pure, Option.some.injEq] at he
          subst sig
          have hforest := assembled_forest_recovery answers
            (evalWithAnswerFn answers (privateNonce message)) (output.toNat % 2 ^ 31) output pieces
          have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
          have hlayer := expandLayersBC_cost_le answers cache (output.toNat % 2 ^ 31)
            hcache hindex 4 (by decide) _ pieces hl
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1 pieces)
            (fun _ _ => rfl)
          obtain ⟨post, hrecBound⟩ := hrecFts
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            (output.toNat % 2 ^ 31) output
          have hrec := cost_bound answers hrecBound
          have hexpand := expand_cost_step answers message pk
            (assembledSignature (evalWithAnswerFn answers (privateNonce message))
              (evalWithAnswerFn answers (ClaudeWCT.WCT9.signForest (output.toNat % 2 ^ 31) output)).1
              pieces)
            counter output (by simpa only [ClaudeWCT.WCT9.assembledSignature_rho] using hd)
          rw [hexpand, signPayload_cost_step answers cache message counter output hd]
          simp only [ClaudeWCT.WCT9.assembledSignature_rho] at hrec hlayer ⊢
          rw [hforest]
          omega
theorem sign_cost_ge_mac (answers : Answers) (cache : Cache) (message : Message) :
    2 ≤ cost answers (sign cache message) := by
  have hmac : cost answers (privateMac cache.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac]
  omega
theorem sign_cost_honest (answers : Answers) (message : Message) :
    cost answers (sign (evalWithAnswerFn answers keygen).2 message) =
      2 + cost answers (signPayload (evalWithAnswerFn answers keygen).2 message) := by
  have hvalid := keygen_cache_tag answers
  have hmac : cost answers (privateMac (evalWithAnswerFn answers keygen).2.region) = 2 := by
    simp only [SigGolfCandidate.T3.SearchCost.cost, privateMac_count, evalWithAnswerFn_map]
  simp only [CacheTagCorrect] at hvalid
  simp only [ClaudeWCT.WCT9.Rev3.sign, ClaudeWCT.WCT9.signWith, cost_bind, hmac, ← hvalid, ne_eq,
    not_true_eq_false, ite_false]
  rfl
theorem expand_cost_le_eight_sign_of (ftsRec : Nat)
    (hrecFts : ∀ sig index output, ∃ post,
      CBound post ftsRec (ClaudeWCT.WCT9.recoverFts sig index output))
    (hbudget : ftsRec + recoveryLayersCost 4 ≤ 622)
    (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) := by
  have hk := keygen_correct answers
  have hs' : evalWithAnswerFn answers (signPayload (evalWithAnswerFn answers keygen).2 message) =
      some sig := by
    rw [show sign (evalWithAnswerFn answers keygen).2 message =
      ClaudeWCT.WCT9.signWith digestAttemptLimit (evalWithAnswerFn answers keygen).2 message from rfl,
      ClaudeWCT.WCT9.signWith_valid_cache digestAttemptLimit answers _ message
        (keygen_cache_tag answers)] at hs
    exact hs
  have h := expand_cost_le_payload_add_of ftsRec hrecFts hbudget answers (evalWithAnswerFn answers keygen).2
    message sig hk.2.1 hs' (evalWithAnswerFn answers keygen).1
  have hmin := ClaudeWCT.W9.T3.FullCacheExpansionCost.signPayload_cost_ge answers
    (evalWithAnswerFn answers keygen).2 message sig hs'
  rw [sign_cost_honest]
  omega
theorem recoverFts_budget : 131 + recoveryLayersCost 4 ≤ 622 := by
  have h := SigGolfCandidate.T3.Cost.recoveryLayersCost_four
  omega
theorem expand_cost_le_payload_add (answers : Answers) (cache : Cache) (message : Message)
    (sig : Signature) (hcache : cache.region = cacheRegion (maskedTop answers))
    (he : evalWithAnswerFn answers (signPayload cache message) = some sig) (pk : Digest) :
    cost answers (expand message pk sig) ≤ cost answers (signPayload cache message) + 622 :=
  expand_cost_le_payload_add_of 131
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers cache message sig hcache he pk
theorem expand_cost_le_eight_sign (answers : Answers) (message : Message) (sig : Signature)
    (hs : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 message) = some sig) :
    cost answers (expand message (evalWithAnswerFn answers keygen).1 sig) ≤
      8 * cost answers (sign (evalWithAnswerFn answers keygen).2 message) :=
  expand_cost_le_eight_sign_of 131
    (fun sig index output => ⟨_, ClaudeWCT.WCT9.Cost.bound_recoverFts sig index output⟩) recoverFts_budget
    answers message sig hs
end ClaudeWCT.W9.T3.ExpansionBudget
end
