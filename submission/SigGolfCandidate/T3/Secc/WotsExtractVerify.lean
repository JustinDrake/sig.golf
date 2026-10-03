import SigGolfCandidate.T3.Secc.WotsExtractLayer

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersP_wots_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : Digest,
    evalWithAnswerFn answers (layersP w index n root) = some (Extract.walkTarget answers index 0) →
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersP w index n root))) ∨
    ((∀ l : Layer, l.val < n → Extract.Good answers w index l) ∧ root = Extract.walkTarget answers index n)
  | 0, _, root, h => by
      right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := Extract.layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_wots_walk answers w index hidx n (by omega) _ hrest with hprim | ⟨hgood, hv⟩
      · exact Or.inl (hprim.mono (entriesOf_mono hqR))
      · rw [Extract.walkTarget_root answers index n (by omega)] at hv
        rcases layer_wots answers w index (Fin.ofNat 4 n) root digits hidx hframe
            (queried answers (layersP w index (n + 1) root)) henc hqL hv with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          have hmsg' : Extract.honestMsg answers index (Fin.ofNat 4 n) = Extract.walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [Extract.walkTarget, dif_pos (show n < 4 by omega), hl]
          refine ⟨fun l hl => ?_, hmsg.trans hmsg'⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
theorem verifyP_walk_wots (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers (ftsP w (N.toNat % 2 ^ 31) (selections N)) =
            some (Extract.honestForest answers (N.toNat % 2 ^ 31)) ∧
          ∀ q ∈ queried answers (ftsP w (N.toNat % 2 ^ 31) (selections N)),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  rw [verifyP_eq_tail] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · have h0 : digestP m w = pure none := by unfold digestP; rw [if_pos hdc]
    rw [h0] at hv; simp at hv
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg hdc]
  rw [hD] at hv ⊢
  rw [Extract.queried_map]
  simp only [evalWithAnswerFn_map] at hv ⊢
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv ⊢
  try simp only at hv ⊢
  refine ⟨N, by omega, rfl, ?_, ?_⟩
  · apply List.mem_append_left
    unfold digest publicHash
    rw [show (liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) : M HashOutput) =
      liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) >>= pure from (bind_pure _).symm,
      queried_query_bind]
    exact List.mem_cons_self
  unfold verifyTailP at hv ⊢
  simp only at hv ⊢
  by_cases hsel : selectionsOk (selections N) = true
  swap
  · rw [if_pos (by simpa using hsel)] at hv; simp at hv
  rw [if_neg (by simpa using hsel)] at hv ⊢
  by_cases hg : digestGate N = true
  swap
  · rw [if_pos (by simpa using hg)] at hv; simp at hv
  rw [if_neg (by simpa using hg)] at hv ⊢
  refine ⟨hsel, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  generalize N.toNat % 2 ^ 31 = index at hidx hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers (ftsP w index (selections N)) = rr at hv ⊢
  rcases rr with _ | root
  · simp at hv
  simp only at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hL : evalWithAnswerFn answers (layersP w index 4 root) = ll at hv ⊢
  rcases ll with _ | root'
  · simp at hv
  simp only [evalWithAnswerFn_pure, beq_iff_eq] at hv
  subst hv
  have htop : Extract.walkTarget answers index 0 = root' := by
    rw [hpk]; simp only [Extract.walkTarget, route_top_tree index hidx]
  rcases layersP_wots_walk answers w index hidx 4 le_rfl root (by rw [hL, htop]) with hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono fun q hq => by simp only [List.mem_append]; tauto))
  have hroot' : root = Extract.honestForest answers index := by
    rw [hroot]; simp [Extract.walkTarget, Extract.honestMsg]
  exact Or.inr ⟨fun l => hgood l l.isLt, by rw [hroot'],
    fun q hq => by simp only [List.mem_append]; tauto⟩
theorem honestForest_eq_built (answers : Answers) (index : Nat) :
    Extract.honestForest answers index = evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) := by
  have h1 : Extract.honestForest answers index =
      (answers (.inl (.inr (Extract.honestInput answers (.forest index))))).extractLsb' 0 128 := rfl
  have h2 : evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) =
      (answers (.inl (.inr (pad64 (Extract.forestInput index
        ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))))).extractLsb' 0 128 :=
    rfl
  rw [h1, h2, FtsExtract.honestInput_forest]
theorem fts_structural (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (Extract.honestForest answers (N.toNat % 2 ^ 31))) :
    StructuralHitSrc answers (entriesOf answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)))) ∨
      FtsExtract.FtsShaped answers N w := by
  have h := FtsExtract.recoverFtsP_built_extract answers (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31)
    (selections N) _ (chosenOk_of N hS.1) hrun (honestForest_eq_built answers _)
  have hidx31 : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans hidx31 (by norm_num)
  rcases h with ⟨hq, hl⟩ | ⟨actual, hmem, ⟨hh, hsh⟩ | ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
  · right
    refine ⟨fun q hq' => ?_, fun c hc j hj => ?_⟩
    · rcases hq q hq' with hf | ⟨c, hc, l, n, hl, hn, rfl⟩
      · exact Or.inl (by rw [hf, FtsExtract.honestInput_forest])
      · refine Or.inr ⟨c, hc, ?_⟩
        rcases FtsExtract.honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
        · exact Or.inl ⟨n, hn', by rw [he]⟩
        · exact Or.inr ⟨level, hlev, n, hn', by rw [he]⟩
    · obtain ⟨hs, hp0, hp1⟩ := hl c hc j hj
      have m21 : (c * 3 + j) % 21 = 3 * c + j := by rw [Nat.mod_eq_of_lt (by omega)]; ring
      have m22 : (3 * c + j) % 22 = 3 * c + j := Nat.mod_eq_of_lt (by omega)
      have m22' : (3 * c + j + 1) % 22 = 3 * c + j + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [witDecP, padDecP, m21, m22, m22'] at hs hp0 hp1
      exact ⟨hs, hp0, hp1⟩
  · left
    exact structuralHit_intro (.forest _) actual hidx hidx31 hmem (by rw [FtsExtract.honestInput_forest]; exact hh)
      (by rw [FtsExtract.honestInput_forest]; exact hsh) trivial
  · left
    rcases FtsExtract.honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
    · exact structuralHit_intro (.ftsLeaf _ c n) actual ⟨by omega, hidx, by omega⟩ ⟨hidx31, hc, hn'⟩ hmem
        (by rw [← he]; exact hh) (by rw [← he]; exact hsh) trivial
    · exact structuralHit_intro (.ftsNode _ c level n) actual
        ⟨by omega, hidx, hlev, by simpa only [Nat.sub_sub] using hn'⟩
        ⟨hidx31, hc, hlev, by simpa only [Nat.sub_sub] using hn'⟩ hmem (by rw [← he]; exact hh)
        (by rw [← he]; exact hsh) trivial
theorem verifyP_wots_cases_src (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N w)) := by
  classical
  have hS := Extract.shaped_of_verifyP answers m pk w hv
  obtain ⟨N, hdc, hN, hdq, _, hcase⟩ := verifyP_walk_wots answers m pk w hpk hv
  rw [hN] at hS
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rw [ftsP_shaped N w hS] at hR hqV
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape⟩
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.WotsExtract
open SigGolfCandidate.T3.Correctness (Answers)
theorem WotsPrimitive.mono {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitive answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') : WotsPrimitive answers trace' := by
  rcases h with ⟨L, h⟩ | h | ⟨a, h⟩ | ⟨a, b, hab, h1, h2⟩ | ⟨a, hm, hc⟩
  · exact Or.inl ⟨L, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHit_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))
theorem verifyP_wots_cases (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitive answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_wots_cases_src answers m pk w hpk hv
  exact ⟨N, hdc, hN, hdq, hS, hcase.imp_left WotsPrimitiveSrc.toPrimitive⟩
end SigGolfCandidate.T3.Security.Wots
