import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layers
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Wct
namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem keygen_pk (answers : Answers) : (evalWithAnswerFn answers WCT9.Rev3.keygen).1 = honestRoot answers 0 0 := by
  unfold WCT9.Rev3.keygen WCT9.keygen keygen keygenPayload
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [Correctness.eval_buildTree_levels answers 0 0 0 [] (Cost.validDigits_nil 0)]
  rfl
theorem layersWalkSpec_holds : WctExtract.LayersWalkSpec
    (fun answers w index qs => HitIn answers qs ∨
      ∃ lay : Layer, Diverge answers w index lay qs ∧ ∀ l : Layer, l.val < lay.val → Good answers w index l)
    (fun answers w index => ∀ l : Layer, Good answers w index l) := by
  intro answers w index root qs hidx hq h
  have htop : (walkTarget answers index 0).1 = honestRoot answers 0 0 := by
    simp only [walkTarget, route_top_tree index hidx]
  rcases layersP_walk answers w index hidx 4 le_rfl (root, 0, 0) (by rw [h, htop]) with
    hhit | ⟨lay, _, hdiv, hgood⟩ | ⟨hgood, hroot⟩
  · exact Or.inl (Or.inl (hhit.mono hq))
  · exact Or.inl (Or.inr ⟨lay, hdiv.mono hq, hgood⟩)
  · refine Or.inr ⟨fun l => hgood l l.isLt, ?_⟩
    have h4 : ((root, 0, 0) : LayerMessage) = walkTarget answers index 4 := by simpa using hroot
    simp [walkTarget, honestMsg] at h4
    exact h4
theorem verifyP_walk_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
            honestForest answers (N.toNat % 2 ^ 31) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases layersWalkSpec_holds answers w (N.toNat % 2 ^ 31) _ _ (Nat.mod_lt _ (by norm_num)) hqL (hpk ▸ hlay) with
    (hhit | hdiv) | ⟨hgood, hroot⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr ⟨hgood, hroot, hqF⟩)
theorem verifyP_extract_normal (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := WctExtract.verifyP_extract layersWalkSpec_holds answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hhit | hev | hgood
  · exact Or.inl hhit
  · rcases hev with hhit | hdiv
    · exact Or.inl hhit
    · exact Or.inr (Or.inl hdiv)
  · exact Or.inr (Or.inr hgood)
end ClaudeWCT.W9.T3M.Extract
