import SigGolfCandidate.T3.Secc.WotsExtractVerify

/-!
# LR-34 (LR-5): W's refined extraction with route leaves (local copy, see `plan/REQUESTS.md` LR34-1)

Stream W's `verifyP_wots_cases_src` states encoding events at leaves with `SourceLeaf` (tree < 2^31); the large
route's residual run tests encoding hits only at G's presampled route-range leaves. W's walk produces every event at
`routeLeaf index lay` (`index < 2^31`), so this file re-runs W's last three walk steps (`layer_wots`,
`layersP_wots_walk`, `verifyP_walk_wots`, `verifyP_wots_cases_src`, verbatim up to the predicate) with
`WotsPrimitiveRoute index`, whose encoding event is at `routeLeaf index lay`.
-/

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- `WotsPrimitiveSrc` with the encoding event at a route leaf of `index`. -/
def WotsPrimitiveRoute (index : Nat) (answers : Answers) (trace : List Entry) : Prop :=
  (∃ lay, EncodingMatchAt answers trace (routeLeaf index lay)) ∨ StructuralHitSrc answers trace ∨
    (∃ a, SourceChain a ∧ TwoEdgeAt answers trace a) ∨
    (∃ a b, SourceChain a ∧ SourceChain b ∧ a ≠ b ∧ ContactAt answers trace a ∧ ContactAt answers trace b) ∨
    (∃ a, SourceChain a ∧ MarkerAt answers trace a ∧ ContactAt answers trace a)

theorem WotsPrimitiveRoute.mono {index : Nat} {answers : Answers} {trace trace' : List Entry}
    (h : WotsPrimitiveRoute index answers trace) (hsub : ∀ e ∈ trace, e ∈ trace') :
    WotsPrimitiveRoute index answers trace' := by
  rcases h with ⟨lay, h⟩ | h | ⟨a, ha, h⟩ | ⟨a, b, ha, hb, hab, h1, h2⟩ | ⟨a, ha, hm, hc⟩
  · exact Or.inl ⟨lay, encodingMatchAt_mono h hsub⟩
  · exact Or.inr (Or.inl (structuralHitSrc_mono h hsub))
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, twoEdgeAt_mono h hsub⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, ha, hb, hab, contactAt_mono h1 hsub, contactAt_mono h2 hsub⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, markerAt_mono hm hsub, contactAt_mono hc hsub⟩)))

/-- W's `layer_wots` with the encoding event at the route leaf. -/
theorem layer_wots_route (answers : Answers) (w : WBytes) (index : Nat) (lay : Layer) (msg : Digest)
    (digits : List Nat) (hidx : index < 2 ^ 31) (hframe : Extract.Frame answers w index lay msg digits)
    (qs : List Spec.Domain) (henc : Extract.encodingQuery w index lay msg ∈ qs)
    (hsub : ∀ q ∈ queried answers (layerP w index lay digits), q ∈ qs)
    (reaches : evalWithAnswerFn answers (layerP w index lay digits) =
      Extract.honestRoot answers lay (route index lay).2) :
    WotsPrimitiveRoute index answers (entriesOf answers qs) ∨
      (msg = Extract.honestMsg answers index lay ∧ Extract.Good answers w index lay) := by
  classical
  have hdec : decode (routeLeaf index lay).lay
      (low (answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay)))))) = some digits := hframe.2
  have hvalid := Cost.validDigits_decode hframe.2
  have hmono := entriesOf_mono (answers := answers) hsub
  have hencE : (encodingRow (routeLeaf index lay) msg (wctr w lay),
      answers (.inl (.inr (encodingRow (routeLeaf index lay) msg (wctr w lay))))) ∈ entriesOf answers qs :=
    mem_entriesOf henc
  have hsrc : SourceLeaf (routeLeaf index lay) := routeLeaf_source index lay hidx
  have hsrcC : ∀ i, i < chainCount lay → SourceChain ⟨routeLeaf index lay, i⟩ := fun i hi => ⟨hsrc, hi⟩
  rcases layerP_wots answers w index lay digits hidx hvalid reaches with hS | ⟨hmerkle, hchains⟩
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hS hmono)))
  have hcontact : ∀ i, i < chainCount lay → digits.getD i 0 < depth answers ⟨routeLeaf index lay, i⟩ →
      ContactAt answers (entriesOf answers qs) ⟨routeLeaf index lay, i⟩ := fun i hi hlt =>
    contactAt_mono ((hchains i hi).2 hlt).1 hmono
  obtain ⟨refDigest, hr⟩ := referenceDigits_decode answers (routeLeaf index lay)
  rcases word_cases hr hdec with heq | ⟨i, hu⟩ | ⟨i, h2⟩ | ⟨i, j, hij, hi, hj⟩
  · have hshape : Extract.LayerShaped answers w index lay digits := by
      refine ⟨hmerkle, fun i hi => ?_⟩
      have hdi : depth answers ⟨routeLeaf index lay, i⟩ = digits.getD i 0 := by
        unfold depth
        rw [heq]
      exact (hchains i hi).1 (le_of_eq hdi)
    by_cases hm : msg = Extract.honestMsg answers index lay
    · exact Or.inr ⟨hm, digits, hm ▸ hframe, hshape⟩
    · refine Or.inl (Or.inl ⟨lay, msg, wctr w lay, _, hencE, ?_, ?_⟩)
      · exact referenceInput_ne answers _ msg _ hdec (Or.inl (by rw [leafMsg_route]; exact hm))
      · rw [← heq]; exact hdec
  · have hlow : digits.getD i.val 0 + 1 = (referenceDigits answers (routeLeaf index lay)).getD i.val 0 := hu.2.2.1
    have hne : digits ≠ referenceDigits answers (routeLeaf index lay) := by
      intro he; rw [he] at hlow; omega
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt,
      ⟨msg, wctr w lay, _, digits, hencE, referenceInput_ne answers _ msg _ hdec (Or.inr hne), hdec, hlow, ?_⟩,
      hcontact i.val i.isLt (by show _ < (referenceDigits answers (routeLeaf index lay)).getD i.val 0; omega)⟩))))
    intro k hk
    by_cases hkc : k < chainCount lay
    · exact hu.2.2.2 ⟨k, hkc⟩ (fun he => hk (congrArg Fin.val he))
    · rw [List.getD_eq_default _ _ (by rw [referenceDigits_length]; exact not_lt.mp hkc)]
      exact Nat.zero_le _
  · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, hsrcC i.val i.isLt, ?_⟩)))
    have hlt : digits.getD i.val 0 < depth answers ⟨routeLeaf index lay, i.val⟩ := by
      have e1 : (decodedWord hdec i).val = digits.getD i.val 0 := rfl
      have e2 : (decodedWord hr i).val = depth answers ⟨routeLeaf index lay, i.val⟩ := rfl
      omega
    exact twoEdgeAt_mono (((hchains i.val i.isLt).2 hlt).2 h2) hmono
  · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨routeLeaf index lay, i.val⟩, ⟨routeLeaf index lay, j.val⟩,
      hsrcC i.val i.isLt, hsrcC j.val j.isLt, ?_, hcontact i.val i.isLt hi, hcontact j.val j.isLt hj⟩))))
    intro he
    exact hij (Fin.ext (ChainAddr.mk.inj he).2)

/-- W's `layersP_wots_walk` with route-leaf encoding events. -/
theorem layersP_wots_walk_route (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : Digest,
    evalWithAnswerFn answers (layersP w index n root) = some (Extract.walkTarget answers index 0) →
    WotsPrimitiveRoute index answers (entriesOf answers (queried answers (layersP w index n root))) ∨
    ((∀ l : Layer, l.val < n → Extract.Good answers w index l) ∧ root = Extract.walkTarget answers index n)
  | 0, _, root, h => by
      right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := Extract.layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_wots_walk_route answers w index hidx n (by omega) _ hrest with hprim | ⟨hgood, hv⟩
      · exact Or.inl (hprim.mono (entriesOf_mono hqR))
      · rw [Extract.walkTarget_root answers index n (by omega)] at hv
        rcases layer_wots_route answers w index (Fin.ofNat 4 n) root digits hidx hframe
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

/-- W's `verifyP_walk_wots` with route-leaf encoding events. -/
theorem verifyP_walk_wots_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
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
  rcases layersP_wots_walk_route answers w index hidx 4 le_rfl root (by rw [hL, htop]) with hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono fun q hq => by simp only [List.mem_append]; tauto))
  have hroot' : root = Extract.honestForest answers index := by
    rw [hroot]; simp [Extract.walkTarget, Extract.honestMsg]
  exact Or.inr ⟨fun l => hgood l l.isLt, by rw [hroot'],
    fun q hq => by simp only [List.mem_append]; tauto⟩

/-- **W's refined extraction with route-leaf encoding events.** -/
theorem verifyP_wots_cases_route (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveRoute (N.toNat % 2 ^ 31) answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsExtract.FtsShaped answers N w ∧
         ∀ q ∈ queried answers (ftsP w (N.toNat % 2 ^ 31) (selections N)),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  have hS := Extract.shaped_of_verifyP answers m pk w hv
  obtain ⟨N, hdc, hN, hdq, _, hcase⟩ := verifyP_walk_wots_route answers m pk w hpk hv
  rw [hN] at hS
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  have hqV' := hqV
  rw [ftsP_shaped N w hS] at hR hqV
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape, hqV'⟩

end SigGolfCandidate.T3.Security.WotsExtract
