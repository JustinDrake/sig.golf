import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.T3.Secc.WotsMaskCharge

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
theorem count_maskAt_of_respects {α : Type} {program : M α} (h : Respects (Untouched a) program) :
    (SourceReplay.queried (maskAt answers a) program).length = (SourceReplay.queried answers program).length := by
  rw [queried_maskAt_of_respects answers a h]
theorem count_buildTree_maskAt (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    (SourceReplay.queried (maskAt answers a) (buildTree lay tree selected digits)).length =
      (SourceReplay.queried answers (buildTree lay tree selected digits)).length := by
  rw [Correctness.buildTree_eq, queried_length_bind (maskAt answers a), queried_length_bind answers,
    queried_length_treeRows, queried_length_treeRows, Correctness.eval_treeRows _ lay tree selected digits hvalid,
    Correctness.eval_treeRows _ lay tree selected digits hvalid]
  have hr : Correctness.leafRoot (maskAt answers a) lay tree = Correctness.leafRoot answers lay tree :=
    funext (leafRoot_maskAt answers a lay tree)
  rw [hr]
  dsimp only
  rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure,
    count_maskAt_of_respects answers a (respects_buildLevels a 3 _ _ _ _ (by decide))]
theorem count_keygenPayload_maskAt :
    (SourceReplay.queried (maskAt answers a) keygenPayload).length =
      (SourceReplay.queried answers keygenPayload).length := by
  rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
    count_buildTree_maskAt answers a 0 0 0 [] (Cost.validDigits_nil 0)]
end Mask
theorem queried_length_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    (SourceReplay.queried (maskAt answers a) keygen).length = (SourceReplay.queried answers keygen).length := by
  unfold keygen
  refine Mask.count_bind_of (Mask.eval_keygenPayload_maskAt answers a) (Mask.count_keygenPayload_maskAt answers a) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact Mask.count_maskAt_of_respects answers a (Mask.Respects.bind (Mask.respects_privateMac a region) fun _ => Mask.Respects.pure' _)
namespace Mask
open SigGolfCandidate.T3.Security.Wots.Mask
variable (answers : Answers) (a : ChainAddr)
theorem count_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      (SourceReplay.queried (maskAt answers a) (WCT9.signLayersBC cache index n msg)).length =
        (SourceReplay.queried answers (WCT9.signLayersBC cache index n msg)).length := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [WCT9.signLayersBC]
      refine count_bind_of (eval_maskAt_of_respects answers a (respects_layerCounterSearch a _ _ _ _ _ _))
        (count_maskAt_of_respects answers a (respects_layerCounterSearch a _ _ _ _ _ _)) ?_
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
          · rw [queried_length_bind, queried_length_bind, queried_length_signTop, queried_length_signTop]
            rfl
          · refine count_bind_of (eval_buildTree_maskAt answers a _ _ _ digits hvalid (route_leaf_bound index _)
                (fun hal _ => routeLeaf_alias a hindex hsearch htree hleaf hal))
              (count_buildTree_maskAt answers a _ _ _ digits hvalid) ?_
            rw [Correctness.eval_buildTree_result answers _ _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hmsg' : ∀ m', m + 1 = m' + 1 → WCT9.LayerMsg.pair
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (builtTree answers (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).1
                (WCT9.topPair (Fin.ofNat 4 (m + 1)) (builtTree answers (Fin.ofNat 4 (m + 1))
                  (route index (Fin.ofNat 4 (m + 1))).2)).2 =
                leafMsg answers (routeLeaf index (Fin.ofNat 4 m')) := fun m' hm' => by
              rw [show m' = m by omega]
              exact signedMsg_succ answers index m (by omega)
            refine count_bind_of (eval_signLayers_maskAt answers a htree hleaf cache index hindex (m + 1) (by omega)
              _ hmsg') (ih (by omega) _ hmsg') ?_
            cases evalWithAnswerFn answers (WCT9.signLayersBC cache index (m + 1) _) <;> rfl
end Mask
theorem queried_length_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (signPayload cache message)).length =
      (SourceReplay.queried answers (signPayload cache message)).length := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateNonce a message))
    (Mask.count_maskAt_of_respects answers a (Mask.respects_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_digestSearch a _ _ _ _))
    (Mask.count_maskAt_of_respects answers a (Mask.respects_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (ClaudeWCT.WCT9.digestSearch rho message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_signForest a _ _))
      (Mask.count_maskAt_of_respects answers a (Mask.respects_signForest a _ _)) ?_
    rw [ClaudeWCT.WCT9.eval_signForest]
    dsimp only
    have hmsg : ∀ m, 4 = m + 1 → WCT9.LayerMsg.forest (ClaudeWCT.WCT9.honestForest answers (output.toNat % 2 ^ 31)) =
        leafMsg answers (Mask.routeLeaf (output.toNat % 2 ^ 31) (Fin.ofNat 4 m)) := fun m hm => by
      obtain rfl : m = 3 := by omega
      rw [← Extract.honestForest_eq_wct9]
      exact Mask.signedMsg_top answers _ (Nat.mod_lt _ (by decide))
    refine Mask.count_bind_of (Mask.eval_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide))
      4 le_rfl _ hmsg) (Mask.count_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide)) 4
      le_rfl _ hmsg) ?_
    generalize evalWithAnswerFn answers (WCT9.signLayersBC cache (output.toNat % 2 ^ 31) 4 _) = pieces
    rcases pieces with _ | pieces <;> rfl
theorem queried_length_maskAt_coreSign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (sign cache message)).length =
      (SourceReplay.queried answers (sign cache message)).length := by
  rw [ClaudeWCT.W9.T3.Security.sign_eq]
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateMac a _))
    (Mask.count_maskAt_of_respects answers a (Mask.respects_privateMac a _)) ?_
  split
  · rfl
  · exact queried_length_maskAt_signPayload answers a htree hleaf cache message
theorem queried_length_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    (SourceReplay.queried (maskAt answers a) (FullGame.authenticatedSign published request)).length =
      (SourceReplay.queried answers (FullGame.authenticatedSign published request)).length := by
  unfold FullGame.authenticatedSign
  refine Mask.count_bind_of (Mask.eval_maskAt_of_respects answers a (Mask.respects_privateMac a _))
    (Mask.count_maskAt_of_respects answers a (Mask.respects_privateMac a _)) ?_
  split
  · exact queried_length_maskAt_signPayload answers a htree hleaf _ _
  · rfl
end ClaudeWCT.W9.T3.Security.Wots
