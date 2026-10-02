import SigGolfCandidate.T3.Secc.SeccSufFts

/-! # B-SUF (2/4): a case-(C) expansion is the honest signing payload for its randomizer

`caseC_expansion_is_payload`: an expansion `expandN message pk σ = some (N, wit)` (under a fixed answers table)
whose witness bytes `witEnc N wit` have all four layers `Extract.Good` and an `FtsExtract.FtsShaped` FTS part is
exactly the signer's payload `payloadRecordForNonce published σ.rho message` under the same table:

* the digest search is the same program (`digestSearch σ.rho message 0 attemptLimit`), so the payload selects the
  same digest answer `N`;
* FTS: `FtsShaped` + the witness roundtrip (`witDecP_witEnc`, `padDecP_witEnc`) make every FTS query of
  `recoverFts σ` honest, so `SeccSufFts` gives the signer's secrets and proof lists; Core's correctness
  (`recoverFts_from_signer_lists`) then gives the honest forest root;
* layers, top-down by induction: the message of each layer is honest, so the expansion's `counterSearch` (whose
  counter is the witness counter that `Good`'s `Frame` decodes) and the signer's `counterSearch` coincide; `Good`'s
  `LayerShaped` makes the layer pieces Core's `honestPieces`, which is what `signLayers` emits (`buildTree`,
  `signTop` on an honest cache) and what `recoverLayer` maps to the next honest message.

**Adjustment of the BP-B statement.** The payload's layer-0 authentication path is read from the cache argument
(`topPath published`), so the statement needs `hcache : published.region = cacheRegion (maskedTop answers)` (true
for the honest key-generation cache, `Correctness.keygen_correct`); without it the claim is false. The
hypothesis `pk = honestRoot answers 0 0` of the contract is not needed and is kept only for interface parity. -/

namespace SigGolfCandidate.T3.Security.BSuf
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] buildFts buildTree

/-! ## The expansion, unfolded -/

/-- What a successful `expandN` computed. -/
theorem expandN_unfold (answers : Answers) (m : Message) (pk : Digest) (σ : Signature) (N : HashOutput)
    (wit : Witness) (he : evalWithAnswerFn answers (expandN m pk σ) = some (N, wit)) :
    ∃ counter rootF cs,
      evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) = some (counter, N) ∧
      evalWithAnswerFn answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)) = some rootF ∧
      evalWithAnswerFn answers (expandLayers σ (N.toNat % 2 ^ 31) 4 rootF) = some (pk, cs) ∧
      wit = ⟨σ, counter, fun lay => cs.getD lay.val 0⟩ := by
  simp only [expandN, evalWithAnswerFn_bind] at he
  cases hd : evalWithAnswerFn answers (digestSearch σ.rho m 0 attemptLimit) with
  | none => simp only [hd, evalWithAnswerFn_pure, reduceCtorEq] at he
  | some found =>
      obtain ⟨counter, output⟩ := found
      simp only [hd, evalWithAnswerFn_bind] at he
      cases hf : evalWithAnswerFn answers (recoverFts σ (output.toNat % 2 ^ 31) (selections output)) with
      | none => simp only [hf, evalWithAnswerFn_pure, reduceCtorEq] at he
      | some rootF =>
          simp only [hf, evalWithAnswerFn_bind] at he
          cases hl : evalWithAnswerFn answers (expandLayers σ (output.toNat % 2 ^ 31) 4 rootF) with
          | none => simp only [hl, evalWithAnswerFn_pure, reduceCtorEq] at he
          | some layers =>
              obtain ⟨root, cs⟩ := layers
              simp only [hl] at he
              split at he
              · simp only [evalWithAnswerFn_pure, reduceCtorEq] at he
              · rename_i hne
                simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at he
                obtain ⟨rfl, rfl⟩ := he
                have hroot : root = pk := by simpa using hne
                subst hroot
                exact ⟨counter, rootF, cs, rfl, hf, hl, rfl⟩

theorem expandLayers_length (answers : Answers) (σ : Signature) (index : Nat) :
    ∀ n (value root : Digest) (cs : List (BitVec 32)),
      evalWithAnswerFn answers (expandLayers σ index n value) = some (root, cs) → cs.length = n := by
  intro n
  induction n with
  | zero =>
      intro value root cs h
      simp only [expandLayers, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; rfl
  | succ n ih =>
      intro value root cs h
      simp only [expandLayers, evalWithAnswerFn_bind] at h
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
          (route index (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at h
      | some found =>
          obtain ⟨counter, digits⟩ := found
          simp only [hs, evalWithAnswerFn_bind] at h
          cases hr : evalWithAnswerFn answers (expandLayers σ index n
              (evalWithAnswerFn answers (recoverLayer σ index (Fin.ofNat 4 n) digits))) with
          | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at h
          | some res =>
              obtain ⟨root', cs'⟩ := res
              simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.2, List.length_append, ih _ _ _ hr]
              rfl

/-! ## Layers -/

/-- `LayerShaped` bytes of an encoded witness carry Core's honest layer pieces. -/
theorem layer_of_shaped (answers : Answers) (N : HashOutput) (wit : Witness) (lay : Layer) (digits : List Nat)
    (hs : Extract.LayerShaped answers (witEnc N wit) (N.toNat % 2 ^ 31) lay digits) :
    wit.signature.layers lay = piecesSignature lay (Correctness.honestPieces answers lay
      (route (N.toNat % 2 ^ 31) lay).2 (route (N.toNat % 2 ^ 31) lay).1 digits) := by
  apply LayerSignature.ext'
  · funext i
    rw [← wvalue_witEnc N wit lay i, (hs.2 i.val i.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]
  · funext j
    rw [← wpath_witEnc N wit lay j, (hs.1 j.val j.isLt).1]
    simp [piecesSignature, Correctness.honestPieces]

/-- The honest message of the layer handled by `n + 1` remaining expansion layers (layer `n`). -/
theorem honestMsg_lower (answers : Answers) (index n : Nat) (hn : n + 1 < 4) :
    Extract.honestMsg answers index (Fin.ofNat 4 n) =
      treeValue (Correctness.builtTree answers (Fin.ofNat 4 (n + 1)) (route index (Fin.ofNat 4 (n + 1))).2)
        (height (Fin.ofNat 4 (n + 1))) 0 := by
  have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
  have hl : (⟨n + 1, by omega⟩ : Layer) = Fin.ofNat 4 (n + 1) := Fin.ext (by simp; omega)
  simp only [Extract.honestMsg, hv, dif_pos (show n < 3 by omega), Extract.honestRoot, hl]

/-- **Layer induction.** Expanding the remaining `n` layers from the honest message of layer `n - 1`, with the
witness counters equal to the expansion's counters and every layer `Good`, the signer's `signLayers` succeeds on
the same message and emits exactly the expansion's layer pieces. -/
theorem layers_payload (answers : Answers) (published : T3.Cache)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (N : HashOutput) (wit : Witness)
    (hgood : ∀ lay : Layer, Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay) :
    ∀ n, n ≤ 4 → ∀ (value root : Digest) (cs : List (BitVec 32)),
      (∀ k, n = k + 1 → value = Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k)) →
      evalWithAnswerFn answers (expandLayers wit.signature (N.toNat % 2 ^ 31) n value) = some (root, cs) →
      (∀ lay : Layer, lay.val < n → wit.counters lay = cs.getD lay.val 0) →
      ∃ pieces, evalWithAnswerFn answers (signLayers published (N.toNat % 2 ^ 31) n value) = some pieces ∧
        pieces.length = n ∧ ∀ lay : Layer, lay.val < n →
          wit.signature.layers lay = piecesSignature lay (pieces.getD lay.val ([], [])) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  intro n
  induction n with
  | zero =>
      intro _ value root cs _ _ _
      refine ⟨[], by simp [signLayers], rfl, fun lay h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
      intro hn value root cs hval hexp hctr
      have hv : (Fin.ofNat 4 n : Layer).val = n := Nat.mod_eq_of_lt (by omega)
      have hmsg := hval n rfl
      simp only [expandLayers, evalWithAnswerFn_bind] at hexp
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2
          (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 value 0 counterLimit) with
      | none => simp only [hs, evalWithAnswerFn_pure, reduceCtorEq] at hexp
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hsome := Correctness.counterSearch_some answers (Fin.ofNat 4 n) (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).2
            (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 n)).1 value counterLimit 0 counter digits (by decide) hs
          have hvalid := Cost.validDigits_decode hsome.2.2
          simp only [hs, evalWithAnswerFn_bind] at hexp
          cases hr : evalWithAnswerFn answers (expandLayers wit.signature (N.toNat % 2 ^ 31) n
              (evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 n) digits))) with
          | none => simp only [hr, evalWithAnswerFn_pure, reduceCtorEq] at hexp
          | some res =>
              obtain ⟨root', cs'⟩ := res
              simp only [hr, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hexp
              obtain ⟨-, hcs⟩ := hexp
              have hlen := expandLayers_length answers wit.signature (N.toNat % 2 ^ 31) n _ _ _ hr
              -- the witness counter of layer `n` is the expansion's counter
              have hcounter : wit.counters (Fin.ofNat 4 n) = counter := by
                rw [hctr _ (by rw [hv]; omega), ← hcs, hv, List.getD_append_right _ _ _ _ (by omega), hlen]
                simp
              -- `Good`'s digits are the expansion's digits
              obtain ⟨digitsG, ⟨_, hdec⟩, hshape⟩ := hgood (Fin.ofNat 4 n)
              rw [wctr_witEnc, hcounter, ← hmsg, hsome.2.2, Option.some.injEq] at hdec
              subst hdec
              rename' digits => digitsG
              have hlayer := layer_of_shaped answers N wit (Fin.ofNat 4 n) digitsG hshape
              have hrec := Correctness.recoverLayer_honestPieces answers wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 n) digitsG
                hvalid hlayer
              by_cases hn0 : n = 0
              · subst hn0
                have ht : (route (N.toNat % 2 ^ 31) 0).2 = 0 := route_top_tree (N.toNat % 2 ^ 31) hidx
                have htop := Correctness.eval_signTop_honest answers published (route (N.toNat % 2 ^ 31) 0).1 digitsG hcache
                  (route_leaf_bound (N.toNat % 2 ^ 31) 0) hvalid
                refine ⟨[Correctness.honestPieces answers 0 0 (route (N.toNat % 2 ^ 31) 0).1 digitsG], ?_, rfl, ?_⟩
                · simp only [signLayers, evalWithAnswerFn_bind, hs, ite_true, evalWithAnswerFn_pure]
                  rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, htop]
                · intro lay hlay
                  have hl0 : lay = 0 := Fin.ext (by simp at hlay ⊢; omega)
                  subst hl0
                  rw [show (Fin.ofNat 4 0 : Layer) = 0 from rfl, ht] at hlayer
                  exact hlayer
              · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
                have hnext : evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1)) digitsG) =
                    Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 k) := by
                  rw [hrec, honestMsg_lower answers (N.toNat % 2 ^ 31) k (by omega)]
                obtain ⟨pieces, hpieces, hplen, hpagree⟩ := ih (by omega) _ root' cs'
                  (fun k' hk' => by rw [hnext]; congr; omega) hr
                  (fun lay hlay => by
                    rw [hctr lay (by omega), ← hcs, List.getD_append _ _ _ _ (by omega)])
                have htree := Correctness.eval_buildTree_result answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG hvalid
                  (route_leaf_bound (N.toNat % 2 ^ 31) _)
                refine ⟨pieces ++ [Correctness.honestPieces answers (Fin.ofNat 4 (k + 1))
                  (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2 (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).1 digitsG], ?_,
                  by simp [hplen], ?_⟩
                · rw [signLayers]
                  simp only [evalWithAnswerFn_bind, hs, htree, show k + 1 ≠ 0 by omega, ite_false]
                  have hroot : ((Correctness.builtTree answers (Fin.ofNat 4 (k + 1))
                      (route (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1))).2).getD (height (Fin.ofNat 4 (k + 1))) []).getD 0 0 =
                      evalWithAnswerFn answers (recoverLayer wit.signature (N.toNat % 2 ^ 31) (Fin.ofNat 4 (k + 1)) digitsG) := by
                    rw [hrec]; rfl
                  rw [hroot, hpieces]
                  rfl
                · intro lay hlay
                  by_cases hlt : lay.val < k + 1
                  · rw [hpagree lay hlt, List.getD_append _ _ _ _ (by omega)]
                  · have hle : lay = Fin.ofNat 4 (k + 1) := Fin.ext (by rw [hv]; omega)
                    subst hle
                    rw [hlayer, hv, List.getD_append_right _ _ _ _ (by omega), hplen]
                    simp

/-! ## The signer's FTS lists -/

/-- `FtsShaped` on the encoding of an expansion makes every FTS query of Core's recovery honest. -/
theorem fts_queries_honest (answers : Answers) (σ : Signature) (N : HashOutput) (wit : Witness)
    (hsig : wit.signature = σ) (hc : ChosenOk (selections N)) (hle : slotBase (selections N) 7 ≤ 124)
    (htail : ∀ k : Fin 124, slotBase (selections N) 7 ≤ k.val → wit.signature.proof k = 0)
    (hfts : FtsExtract.FtsShaped answers N (witEnc N wit)) :
    ∀ q ∈ queried answers (recoverFts σ (N.toNat % 2 ^ 31) (selections N)), HonQ answers q := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
  intro q hq
  have h := hfts.1 q (by
    rw [witDecP_witEnc N wit hc hle htail, padDecP_witEnc N wit hc hle, recoverFtsP_zero, hsig]
    exact hq)
  rcases h with h | ⟨c, hc7, ⟨leaf, hleaf, h⟩ | ⟨level, hlevel, node, hnode, h⟩⟩
  · exact ⟨.forest _, hidx, h⟩
  · exact ⟨.ftsLeaf _ c leaf, ⟨by omega, hidx, by omega⟩, h⟩
  · exact ⟨.ftsNode _ c level node, ⟨by omega, hidx, hlevel, by simpa only [Nat.sub_sub] using hnode⟩, h⟩

/-- The seven honest forest roots of PEX are Core's `forestRoots` (through PEX-F's checked `honestInput_forest`,
avoiding a kernel unfolding of `Extract.ftsLevels`). -/
theorem ftsRootsHonest_eq (answers : Answers) (index : Nat) :
    Extract.ftsRootsHonest answers index = Correctness.forestRoots answers index 7 := by
  have h := FtsExtract.honestInput_forest answers index
  rw [show Extract.honestInput answers (.forest index) =
    pad64 (Extract.forestInput index (Extract.ftsRootsHonest answers index)) from rfl] at h
  exact FtsExtract.forestInput_injective (Extract.ftsRootsHonest_length answers index)
    (by simp [Correctness.forestRoots]) h

/-! ## The main theorem -/

/-- **Honest-shaped bytes for a digest are unique.** A case-(C) expansion (all four layers `Good`, FTS part
`FtsShaped`) of `σ` is the signer's payload for the randomizer `σ.rho` under the same answers (BP-B §2.1; the
cache hypothesis `hcache` is the documented adjustment). -/
theorem caseC_expansion_is_payload (answers : Answers) (published : T3.Cache)
    (message : Message) (pk : Digest) (signature : Signature) (N : HashOutput) (wit : Witness)
    (hcache : published.region = Correctness.cacheRegion (Correctness.maskedTop answers))
    (_hpk : pk = Extract.honestRoot answers 0 0)
    (he : evalWithAnswerFn answers (expandN message pk signature) = some (N, wit))
    (hgood : ∀ lay : Layer, Extract.Good answers (witEnc N wit) (N.toNat % 2 ^ 31) lay)
    (hfts : FtsExtract.FtsShaped answers N (witEnc N wit)) :
    (evalWithAnswerFn answers (payloadRecordForNonce published signature.rho message)).1 = some signature := by
  have F := expandN_facts answers message pk signature N wit he
  obtain ⟨counter, rootF, cs, hds, hrf, hel, hwit⟩ := expandN_unfold answers message pk signature N wit he
  have hsel := selectionsOk_of_admissible N F.adm
  have hc := chosenOk_of N hsel
  have hle := slotBase_seven_le N hc F.adm
  have htail : ∀ k : Fin 124, slotBase (selections N) 7 ≤ k.val → wit.signature.proof k = 0 := by
    rw [F.sig]
    exact eval_recoverFtsP_tail answers signature 0 _ _ hc hle rootF (by rw [recoverFtsP_zero]; exact hrf)
  -- FTS lists
  have hq := fts_queries_honest answers signature N wit F.sig hc hle htail hfts
  have hproof := fts_proof_honest answers signature N rootF F.adm hrf hq
  have hsec := fts_secrets_honest answers signature N (fun c j => by
    have h := (hfts.2 c.val c.isLt j.val j.isLt).1
    rw [wsecret_witEnc N wit _ (by omega), F.sig] at h
    exact h)
  have hrf' := Correctness.recoverFts_from_signer_lists answers signature (N.toNat % 2 ^ 31) N F.adm hsec hproof
  have hrootF : rootF = evalWithAnswerFn answers (forestPk (N.toNat % 2 ^ 31)
      (Correctness.forestRoots answers (N.toNat % 2 ^ 31) 7)) := by
    rw [hrf] at hrf'; exact Option.some.inj hrf'
  -- layers
  have hmsg3 : rootF = Extract.honestMsg answers (N.toNat % 2 ^ 31) (Fin.ofNat 4 3) := by
    rw [hrootF, show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
    simp only [Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false, Extract.honestForest,
      ftsRootsHonest_eq]
  obtain ⟨pieces, hpieces, -, hpagree⟩ := layers_payload answers published hcache N wit hgood 4 le_rfl rootF pk cs
    (fun k hk => by obtain rfl : k = 3 := by omega
                    exact hmsg3)
    (by rw [F.sig]; exact hel)
    (fun lay _ => by rw [hwit])
  -- the payload
  unfold payloadRecordForNonce
  simp only [evalWithAnswerFn_bind, hds]
  rw [SigningRecords.payloadAfterDigest_forestRows]
  simp only [evalWithAnswerFn_bind, Correctness.eval_forestRows, evalWithAnswerFn_pure]
  rw [← hrootF, hpieces]
  simp only [evalWithAnswerFn_pure, Option.some.injEq]
  have hlay : ∀ lay : Layer, piecesSignature lay (pieces.getD lay.val ([], [])) = signature.layers lay := by
    intro lay
    have := hpagree lay lay.isLt
    rw [F.sig] at this
    exact this.symm
  rcases signature with ⟨rho, secrets, proof, layers⟩
  simp only [Signature.mk.injEq]
  exact ⟨trivial, funext fun i => (hsec i).symm, funext fun k => (hproof k).symm, funext hlay⟩

end SigGolfCandidate.T3.Security.BSuf
