import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layer

namespace ClaudeWCT.W9.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem Diverge.mono {answers : Answers} {w : WBytes} {index : Nat} {lay : Layer} {qs qs' : List Spec.Domain}
    (h : Diverge answers w index lay qs) (hsub : ∀ q ∈ qs, q ∈ qs') : Diverge answers w index lay qs' := by
  obtain ⟨msg, digits, hfit, hne, hf, hs, hq⟩ := h
  exact ⟨msg, digits, hfit, hne, hf, hs, hsub _ hq⟩
theorem msgFits_honestMsg (answers : Answers) (index : Nat) (lay : Layer) :
    msgFits lay (honestMsg answers index lay) := by
  unfold honestMsg
  split
  · rename_i h; exact h
  · rename_i h; show lay.val = 3; omega
theorem ofNat_val (n : Nat) (hn : n < 4) : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt hn
theorem honestMsg_lower (answers : Answers) (index n : Nat) (h1 : 1 ≤ n) (h3 : n ≤ 3) :
    honestMsg answers index (Fin.ofNat 4 (n - 1)) =
      .pair (honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).1
        (honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2).2 := by
  have hv : (Fin.ofNat 4 (n - 1) : Layer).val = n - 1 := ofNat_val _ (by omega)
  have hl : (⟨(Fin.ofNat 4 (n - 1) : Layer).val + 1, by omega⟩ : Layer) = Fin.ofNat 4 n := by
    apply Fin.ext
    show (Fin.ofNat 4 (n - 1) : Layer).val + 1 = (Fin.ofNat 4 n : Layer).val
    rw [hv, ofNat_val n (by omega)]
    omega
  unfold honestMsg
  rw [dif_pos (by rw [hv]; omega)]
  simp only [hl]
theorem honestMsg_three (answers : Answers) (index : Nat) :
    honestMsg answers index (Fin.ofNat 4 3) = .forest (honestForest answers index) := by
  unfold honestMsg
  rw [dif_neg (by decide)]
private theorem queried_map_l {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem layersBC_succ_eq (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) :
    layersBC w index (n + 1) msg =
      if (wbcCtr w (Fin.ofNat 4 n)).toNat ≥ counterLimit then pure none else
      (shortHash (layerEncodingInputP (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w (Fin.ofNat 4 n)) (wbcPad w (Fin.ofNat 4 n))) >>= fun answer =>
        match decode (Fin.ofNat 4 n) answer with
        | some digits => if n = 0 then some <$> layerP w index (Fin.ofNat 4 n) digits
            else (layerPairP w index (Fin.ofNat 4 n) digits >>= fun pair =>
              layersBC w index n (.pair pair.1 pair.2))
        | _ => pure none) := by
  conv_lhs => unfold layersBC
  rfl
theorem layersBC_succ_split (answers : Answers) (w : WBytes) (index n : Nat) (msg : WCT9.LayerMsg) (out : Digest)
    (h : evalWithAnswerFn answers (layersBC w index (n + 1) msg) = some out) :
    ∃ digits, Frame answers w index (Fin.ofNat 4 n) msg digits ∧
      encodingQuery w index (Fin.ofNat 4 n) msg ∈ queried answers (layersBC w index (n + 1) msg) ∧
      (n = 0 → evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 n) digits) = out ∧
        ∀ q ∈ queried answers (layerP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersBC w index (n + 1) msg)) ∧
      (n ≠ 0 →
        evalWithAnswerFn answers (layersBC w index n
          (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
            (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)) = some out ∧
        (∀ q ∈ queried answers (layerPairP w index (Fin.ofNat 4 n) digits),
          q ∈ queried answers (layersBC w index (n + 1) msg)) ∧
        (∀ q ∈ queried answers (layersBC w index n
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2)),
          q ∈ queried answers (layersBC w index (n + 1) msg))) := by
  rw [layersBC_succ_eq] at h ⊢
  by_cases hc : (wbcCtr w (Fin.ofNat 4 n)).toNat ≥ counterLimit
  · rw [if_pos hc] at h; simp at h
  rw [if_neg hc] at h ⊢
  rw [evalWithAnswerFn_bind] at h
  rw [queried_bind]
  generalize hans : evalWithAnswerFn answers (shortHash (layerEncodingInputP (Fin.ofNat 4 n)
    (route index (Fin.ofNat 4 n)).2 (route index (Fin.ofNat 4 n)).1 msg (wbcCtr w (Fin.ofNat 4 n))
    (wbcPad w (Fin.ofNat 4 n)))) = answer at h ⊢
  cases hd : decode (Fin.ofNat 4 n) answer with
  | none => rw [hd] at h; simp at h
  | some digits =>
      rw [hd] at h
      simp only at h ⊢
      refine ⟨digits, ⟨by omega, by rw [hans]; exact hd⟩, ?_, ?_, ?_⟩
      · apply List.mem_append_left
        rw [queried_shortHash]; exact List.mem_singleton_self _
      · intro hn0
        subst hn0
        simp only [if_true] at h ⊢
        rw [evalWithAnswerFn_map] at h
        refine ⟨Option.some.inj h, fun q hq => List.mem_append_right _ ?_⟩
        rw [queried_map_l]; exact hq
      · intro hn0
        simp only [hn0, if_false] at h ⊢
        rw [evalWithAnswerFn_bind] at h
        refine ⟨h, fun q hq => ?_, fun q hq => ?_⟩
        · apply List.mem_append_right
          rw [queried_bind]; exact List.mem_append_left _ hq
        · apply List.mem_append_right
          rw [queried_bind]; exact List.mem_append_right _ hq
theorem layersBC_walk_n (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, 1 ≤ n → n ≤ 4 → ∀ msg : WCT9.LayerMsg, msgFits (Fin.ofNat 4 (n - 1)) msg →
    evalWithAnswerFn answers (layersBC w index n msg) = some (honestRoot answers 0 0) →
    HitIn answers (queried answers (layersBC w index n msg)) ∨
    (∃ lay : Layer, lay.val < n ∧ Diverge answers w index lay (queried answers (layersBC w index n msg)) ∧
      ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
    ((∀ l : Layer, l.val < n → Good answers w index l) ∧ msg = honestMsg answers index (Fin.ofNat 4 (n - 1)))
  | 0, h1, _, _, _, _ => absurd h1 (by decide)
  | n + 1, _, hn, msg, hfit, h => by
      classical
      obtain ⟨digits, hframe, henc, htop, hlow⟩ := layersBC_succ_split answers w index n msg _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := ofNat_val n (by omega)
      have hvalid := Cost.validDigits_decode hframe.2
      simp only [Nat.add_sub_cancel] at hfit ⊢
      have finish : HitIn answers (queried answers (layersBC w index (n + 1) msg)) ∨
          LayerShaped answers w index (Fin.ofNat 4 n) digits →
          (∀ l : Layer, l.val < n → Good answers w index l) →
          HitIn answers (queried answers (layersBC w index (n + 1) msg)) ∨
          (∃ lay : Layer, lay.val < n + 1 ∧
            Diverge answers w index lay (queried answers (layersBC w index (n + 1) msg)) ∧
            ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
          ((∀ l : Layer, l.val < n + 1 → Good answers w index l) ∧
            msg = honestMsg answers index (Fin.ofNat 4 n)) := by
        intro hx hgood
        rcases hx with hhit | hshape
        · exact Or.inl hhit
        by_cases heq : msg = honestMsg answers index (Fin.ofNat 4 n)
        · right; right
          refine ⟨fun l hl => ?_, heq⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact ⟨digits, heq ▸ hframe, hshape⟩
        · right; left
          exact ⟨Fin.ofNat 4 n, by omega, ⟨msg, digits, hfit, heq, hframe, hshape, henc⟩,
            fun l hl => hgood l (by omega)⟩
      by_cases hn0 : n = 0
      · subst hn0
        obtain ⟨hout, hq⟩ := htop rfl
        have hroot : evalWithAnswerFn answers (layerP w index (Fin.ofNat 4 0) digits) =
            honestRoot answers (Fin.ofNat 4 0) (route index (Fin.ofNat 4 0)).2 := by
          rw [hout, show (Fin.ofNat 4 0 : Layer) = 0 from rfl, route_top_tree index hidx]
        refine finish ?_ (fun l hl => absurd hl (by omega))
        rcases layerP_extract answers w index (Fin.ofNat 4 0) digits hidx hvalid hroot with hhit | hshape
        · exact Or.inl (hhit.mono hq)
        · exact Or.inr hshape
      · obtain ⟨hrest, hqP, hqR⟩ := hlow hn0
        have hfit' : msgFits (Fin.ofNat 4 (n - 1))
            (.pair (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).1
              (evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits)).2) := by
          show (Fin.ofNat 4 (n - 1) : Layer).val < 3
          rw [ofNat_val _ (by omega)]; omega
        rcases layersBC_walk_n answers w index hidx n (by omega) (by omega) _ hfit' hrest with
          hhit | ⟨lay, hlay, hdiv, hgood⟩ | ⟨hgood, hmsg⟩
        · exact Or.inl (hhit.mono hqR)
        · exact Or.inr (Or.inl ⟨lay, by omega, hdiv.mono hqR, hgood⟩)
        · rw [honestMsg_lower answers index n (by omega) (by omega)] at hmsg
          have hpair : evalWithAnswerFn answers (layerPairP w index (Fin.ofNat 4 n) digits) =
              honestPair answers (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2 := by
            simp only [WCT9.LayerMsg.pair.injEq] at hmsg
            exact Prod.ext hmsg.1 hmsg.2
          refine finish ?_ hgood
          rcases layerPairP_extract answers w index (Fin.ofNat 4 n) digits hidx hvalid (by rw [hval]; exact hn0)
              hpair with hhit | hshape
          · exact Or.inl (hhit.mono hqP)
          · exact Or.inr hshape
theorem layersBC_walk (answers : Answers) (w : WBytes) (index : Nat) (root : Digest) (hidx : index < 2 ^ 31)
    (h : evalWithAnswerFn answers (layersBC w index 4 (.forest root)) = some (honestRoot answers 0 0)) :
    HitIn answers (queried answers (layersBC w index 4 (.forest root))) ∨
      (∃ lay : Layer, Diverge answers w index lay (queried answers (layersBC w index 4 (.forest root))) ∧
        ∀ l : Layer, l.val < lay.val → Good answers w index l) ∨
      ((∀ l : Layer, Good answers w index l) ∧ root = honestForest answers index) := by
  rcases layersBC_walk_n answers w index hidx 4 (by decide) le_rfl (.forest root) rfl h with
    hhit | ⟨lay, _, hdiv, hgood⟩ | ⟨hgood, hmsg⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl ⟨lay, hdiv, hgood⟩)
  · refine Or.inr (Or.inr ⟨fun l => hgood l l.isLt, ?_⟩)
    rw [show (4 - 1 : Nat) = 3 from rfl, honestMsg_three] at hmsg
    simpa using hmsg
end ClaudeWCT.W9.T3M.Extract
