import SigGolfCandidate.T3.Secc.SeccSufSigned

/-! # B-SUF (4/4): routing lemmas R3, R4, R6 of BP-B §2.1

All deterministic, under a fixed answers table.

* **R4** (`digestSearch_queried`, `digestSearch_accepts`, `rejected_trial_inadmissible`): the digest search
  queries trial `c` only after rejecting every earlier trial, and accepts the first admissible trial. Hence a
  queried trial whose answer is admissible (as `Shaped` requires) is the accepted one: a rejected signer trial
  contradicts `Shaped`.
* **R3** (`signLayers_good`, `selected_payload_succeeds`): if the signer selected the digest answer `N` and all
  four layers are `Good` for `N`'s index (any witness bytes), the payload succeeds: every honest layer message has
  a decoding counter below `counterLimit`, so each `counterSearch` from 0 succeeds.
* **R6** (`signer_digest_query`, `caseC_fresh_not_signer`, `caseC_fresh_first_occurrence`): the only digest-format
  queries of the authenticated signer are its digest-search trials for the request's message and nonce (every
  other public signer query carries a header tag in `{1,2,3,4,9,10,11}`, byte 17 of the input, while digest inputs
  carry tag 12). So in `CaseCFresh` no logged signer call ever queries the forgery's digest input (else R4 + R3
  make the forgery's digest signer-accepted with a successful signature, i.e. `SignedDigest`), and the first
  recorded occurrence of that input (`FirstHit.first_public_occurrence`) is a non-signer query on a fresh row. -/

namespace SigGolfCandidate.T3.Security.BPB
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final Correctness
open SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3M.SecurityExtraction (queried queried_bind queried_shortHash)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_seccSufRoute : DecidableEq T3.Cache := Classical.decEq _
attribute [local irreducible] buildFts buildTree

/-! ## Digest inputs -/

theorem digestInput_length (rho : Digest) (m : Message) (c : BitVec 32) : (digestInput rho m c).length = 64 := by
  simp [digestInput, SphincsSecurity.bytesLE_length]

theorem pad64_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) = digestInput rho m c := by
  simp [pad64, digestInput_length]

/-- The padded digest input determines randomizer, counter and message. -/
theorem digestInput_injective {rho rho' : Digest} {m m' : Message} {c c' : BitVec 32}
    (h : pad64 (digestInput rho m c) = pad64 (digestInput rho' m' c')) : rho = rho' ∧ c = c' ∧ m = m' := by
  rw [pad64_digestInput, pad64_digestInput] at h
  unfold digestInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp [SphincsSecurity.bytesLE_length])
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp [SphincsSecurity.bytesLE_length])
  have hh := SphincsSecurity.bytesLE_injective h2
  obtain ⟨-, -, -, -, hidx⟩ := header_injective (by decide) (by decide) (by decide) (by decide) c.isLt
    (by decide) (by decide) (by decide) (by decide) c'.isLt hh
  exact ⟨SphincsSecurity.bytesLE_injective h1, BitVec.eq_of_toNat_eq hidx, SphincsSecurity.bytesLE_injective h3⟩

/-! ## R4: the digest search -/

theorem digestSearch_succ (rho : Digest) (m : Message) (counter fuel : Nat) :
    digestSearch rho m counter (fuel + 1) = (digest rho m (BitVec.ofNat 32 counter) >>= fun output =>
      if digestAdmissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else digestSearch rho m (counter + 1) fuel) := rfl

theorem queried_digest (answers : Correctness.Answers) (rho : Digest) (m : Message) (c : BitVec 32) :
    queried answers (digest rho m c) = [.inl (.inr (pad64 (digestInput rho m c)))] := rfl

/-- The digest search queries trial `c` only after rejecting all earlier trials. -/
theorem digestSearch_queried (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (q : Spec.Domain), q ∈ queried answers (digestSearch rho m start fuel) →
      ∃ c, start ≤ c ∧ c < start + fuel ∧ q = .inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) ∧
        ∀ c', start ≤ c' → c' < c →
          digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false := by
  intro fuel
  induction fuel with
  | zero => intro start q hq; simp [digestSearch] at hq
  | succ fuel ih =>
      intro start q hq
      rw [digestSearch_succ, queried_bind, queried_digest] at hq
      rcases List.mem_append.mp hq with hq | hq
      · rw [List.mem_singleton] at hq
        exact ⟨start, le_rfl, by omega, hq, fun c' h1 h2 => by omega⟩
      · by_cases hadm : digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 start))) = true
        · rw [if_pos hadm] at hq; simp at hq
        · rw [if_neg hadm] at hq
          obtain ⟨c, h1, h2, h3, h4⟩ := ih (start + 1) q hq
          refine ⟨c, by omega, by omega, h3, fun c' h1' h2' => ?_⟩
          by_cases hc' : c' = start
          · subst hc'; simpa using hadm
          · exact h4 c' (by omega) h2'

/-- The digest search accepts the first admissible trial. -/
theorem digestSearch_accepts (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start c, start ≤ c → c < start + fuel →
      (∀ c', start ≤ c' → c' < c →
        digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false) →
      digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) = true →
      evalWithAnswerFn answers (digestSearch rho m start fuel) =
        some (BitVec.ofNat 32 c, evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) := by
  intro fuel
  induction fuel with
  | zero => intro start c h1 h2; omega
  | succ fuel ih =>
      intro start c h1 h2 hrej hadm
      rw [digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hc : c = start
      · subst hc
        rw [if_pos hadm, evalWithAnswerFn_pure]
      · rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) c (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2') hadm

/-- **R4.** A queried trial of the signer's digest search whose answer is admissible (as `Shaped` requires) is the
accepted trial: a rejected signer trial contradicts `Shaped`. -/
theorem rejected_trial_inadmissible (answers : Correctness.Answers) (rho : Digest) (m : Message) (c : Nat)
    (hq : (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 c)))) : Spec.Domain) ∈
      queried answers (digestSearch rho m 0 attemptLimit))
    (hadm : digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) = true) :
    evalWithAnswerFn answers (digestSearch rho m 0 attemptLimit) =
      some (BitVec.ofNat 32 c, evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c))) := by
  obtain ⟨c', _, hc', heq, hrej⟩ := digestSearch_queried answers rho m attemptLimit 0 _ hq
  have hcc : BitVec.ofNat 32 c = BitVec.ofNat 32 c' := by
    have h := congrArg (fun q : Spec.Domain => q) heq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at h
    exact (digestInput_injective h).2.1
  rw [hcc] at hadm ⊢
  exact digestSearch_accepts answers rho m attemptLimit 0 c' (Nat.zero_le _) hc' hrej hadm

/-! ## R3: a signer-selected digest with all layers `Good` has a successful payload -/

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt])

/-- A `Good` layer gives a decoding counter for its honest message, so the signer's counter search succeeds. -/
theorem counterSearch_good (answers : Correctness.Answers) (w : WBytes) (index : Nat) (lay : Layer)
    (hgood : Extract.Good answers w index lay) :
    ∃ found, evalWithAnswerFn answers (counterSearch lay (route index lay).2 (route index lay).1
      (Extract.honestMsg answers index lay) 0 counterLimit) = some found := by
  obtain ⟨digits, ⟨hlt, hdec⟩, -⟩ := hgood
  cases h : evalWithAnswerFn answers (counterSearch lay (route index lay).2 (route index lay).1
      (Extract.honestMsg answers index lay) 0 counterLimit) with
  | some found => exact ⟨found, rfl⟩
  | none =>
      have := (Correctness.counterSearch_none_iff answers lay _ _ _ counterLimit 0).mp h (wctr w lay).toNat hlt
      rw [Nat.zero_add, ofNat_toNat32, hdec] at this
      exact absurd this (by simp)

/-- The honest message of layer 3 is Core's forest public key on the source-built roots. -/
theorem honestMsg_three (answers : Correctness.Answers) (index : Nat) :
    Extract.honestMsg answers index (Fin.ofNat 4 3) =
      (evalWithAnswerFn answers (forestPk index (Correctness.forestRoots answers index 7)), 0, 0) := by
  rw [show (Fin.ofNat 4 3 : Layer) = 3 from rfl]
  simp only [Extract.honestMsg, show ¬((3 : Layer).val < 3) by decide, dite_false, Extract.honestForest,
    BSuf.ftsRootsHonest_eq]

/-- The signer's layer signing succeeds from every honest layer message when every layer is `Good`. -/
theorem signLayers_good (answers : Correctness.Answers) (cache : T3.Cache) (index : Nat) (w : WBytes)
    (hgood : ∀ lay : Layer, Extract.Good answers w index lay) :
    ∀ n, n ≤ 4 → ∀ value : Digest × BitVec 96 × Digest, (∀ k, n = k + 1 → value = Extract.honestMsg answers index (Fin.ofNat 4 k)) →
      ∃ pieces, evalWithAnswerFn answers (signLayers cache index n value) = some pieces := by
  intro n
  induction n with
  | zero => intro _ value _; exact ⟨[], by simp [signLayers]⟩
  | succ n ih =>
      intro hn value hval
      have hmsg := hval n rfl
      obtain ⟨⟨counter, digits⟩, hs⟩ := counterSearch_good answers w index (Fin.ofNat 4 n) (hgood _)
      rw [← hmsg] at hs
      have hvalid := Cost.validDigits_decode (Correctness.counterSearch_some answers _ _ _ _ counterLimit 0 counter
        digits (by decide) hs).2.2
      by_cases hn0 : n = 0
      · subst hn0
        rw [signLayers]
        simp only [evalWithAnswerFn_bind, hs, ite_true, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have htree := Correctness.eval_buildTree_result answers (Fin.ofNat 4 (k + 1))
          (route index (Fin.ofNat 4 (k + 1))).2 (route index (Fin.ofNat 4 (k + 1))).1 digits hvalid
          (route_leaf_bound index _)
        obtain ⟨pieces, hp⟩ := ih (by omega) ((((Correctness.builtTree answers (Fin.ofNat 4 (k + 1))
            (route index (Fin.ofNat 4 (k + 1))).2).getD (height (Fin.ofNat 4 (k + 1)) - 1) []).getD 0 0, 0, ((Correctness.builtTree answers (Fin.ofNat 4 (k + 1))
            (route index (Fin.ofNat 4 (k + 1))).2).getD (height (Fin.ofNat 4 (k + 1)) - 1) []).getD 1 0))
          (fun k' hk' => by
            have hkk : k' = k := by omega
            rw [hkk, BSuf.honestMsg_lower answers index k (by omega)]
            rfl)
        rw [signLayers]
        simp only [evalWithAnswerFn_bind, hs, htree, show k + 1 ≠ 0 by omega, ite_false, hp, evalWithAnswerFn_pure]
        exact ⟨_, rfl⟩

/-- **R3.** If the signer's search selected the digest answer `N` (`record.2 = some N`) and all four layers are
`Good` for `N`'s index, the signer's payload succeeds (with the signer's randomizer). -/
theorem selected_payload_succeeds (answers : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message)
    (N : HashOutput) (w : WBytes)
    (hsel : (evalWithAnswerFn answers (payloadRecordForNonce cache rho m)).2 = some N)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay) :
    ∃ sig, (evalWithAnswerFn answers (payloadRecordForNonce cache rho m)).1 = some sig ∧ sig.rho = rho := by
  obtain ⟨counter, hds, -⟩ := payloadRecord_selected_valid answers cache rho m N hsel
  have h1 : (evalWithAnswerFn answers (payloadRecordForNonce cache rho m)).1 =
      evalWithAnswerFn answers (payloadAfterDigest cache rho N) := by
    unfold payloadRecordForNonce
    simp only [evalWithAnswerFn_bind, hds, evalWithAnswerFn_pure]
  obtain ⟨pieces, hp⟩ := signLayers_good answers cache (N.toNat % 2 ^ 31) w hgood 4 le_rfl
    (evalWithAnswerFn answers (forestPk (N.toNat % 2 ^ 31) (Correctness.forestRoots answers (N.toNat % 2 ^ 31) 7)), 0, 0)
    (fun k hk => by
      obtain rfl : k = 3 := by omega
      exact (honestMsg_three answers _).symm)
  rw [h1, SigningRecords.payloadAfterDigest_forestRows]
  simp only [evalWithAnswerFn_bind, Correctness.eval_forestRows, hp, evalWithAnswerFn_pure]
  exact ⟨_, rfl, rfl⟩

/-! ## R6 (shape): the signer's only digest-format queries are digest-search trials

Every public query of the signer's payload work (`payloadAfterDigest`: FTS trees, forest pk, WOTS chains, leaf
pks, Merkle nodes, encodings) is `pad64` of an input whose header block (bytes `[16,32)`) is a `header` with tag in
`{1,2,3,4,9,10,11}`; a digest input's header tag is 12. The tag is byte 1 of the header block (`hdrTag`). -/

/-- Byte 1 of the header block of an input (the header's tag byte). -/
def hdrTag (input : HashInput) : Nat := ((Extract.hdrBlock input).getD 1 0).toNat

theorem header_byte1 (tag lay tree position index : Nat) :
    ((SphincsSecurity.bytesLE 16 (header tag lay tree position index)).getD 1 0).toNat = tag % 256 := by
  have h : (SphincsSecurity.bytesLE 16 (header tag lay tree position index)).getD 1 0 =
      ⟨(header tag lay tree position index).extractLsb' 8 8⟩ := rfl
  rw [h]
  show ((header tag lay tree position index).extractLsb' 8 8).toNat = tag % 256
  rw [BitVec.extractLsb'_toNat]
  unfold header
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  have h7 := nodeWord_lt tag position index
  generalize nodeWord tag position index = g at *
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  norm_num at h4 h5 h6 ⊢
  split_ifs <;> omega

theorem hdrTag_eq {input : HashInput} {tag lay tree position index : Nat}
    (h : Extract.hdrBlock input = SphincsSecurity.bytesLE 16 (header tag lay tree position index)) :
    hdrTag input = tag % 256 := by
  unfold hdrTag; rw [h]; exact header_byte1 _ _ _ _ _

theorem hdrBlock_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    Extract.hdrBlock (pad64 (digestInput rho m c)) = SphincsSecurity.bytesLE 16 (header 12 0 0 0 c.toNat) := by
  rw [pad64_digestInput]
  exact Extract.hdrBlock_prefix _ _ _

theorem hdrTag_digestInput (rho : Digest) (m : Message) (c : BitVec 32) :
    hdrTag (pad64 (digestInput rho m c)) = 12 := hdrTag_eq (hdrBlock_digestInput rho m c)

/-- Not a digest-format public query. -/
def NotDigestQ : T3.Spec.Domain → Prop
  | .inl (.inr input) => hdrTag input ≠ 12
  | _ => True

theorem shortHash_ok {input : HashInput} {tag lay tree position index : Nat}
    (h : Extract.hdrBlock (pad64 input) = SphincsSecurity.bytesLE 16 (header tag lay tree position index))
    (ht : tag % 256 ≠ 12) : AllQueriesSatisfy (shortHash input) NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (show hdrTag (pad64 input) ≠ 12 by rw [hdrTag_eq h]; exact ht)
  · intro _; exact SourceQueries.pure_allowed _ _

theorem privatePair_ok (tag lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NotDigestQ :=
  SourceQueries.privatePair_allowed NotDigestQ (fun _ => trivial) tag lay tree position index

theorem mask_ok (level index : Nat) : AllQueriesSatisfy (mask level index) NotDigestQ :=
  SourceQueries.mask_allowed NotDigestQ (fun _ => trivial) level index

theorem chain_ok (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDigestQ := by
  unfold chain
  exact SourceQueries.foldlM_allowed NotDigestQ _ _ (fun v step =>
    shortHash_ok (tag := 1) (by rw [chainInput_eq_zero]; exact Extract.hdrBlock_chainInputP _ _ _ _ _ _ _ _)
      (by decide)) _

theorem leafHash_ok (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDigestQ := by
  rw [Extract.leafHash_eq_shortHash]
  exact shortHash_ok (tag := 2) (Extract.hdrBlock_listInput _ _ _) (by decide)

theorem nodeHash_ok (tag lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDigestQ := by
  rw [nodeHash_eq_shortHash]
  exact shortHash_ok (by rw [pad64_nodeInputP]; exact BSuf.hdrBlock_nodeInputP _ _ _ _ _ _ _) ht

theorem nodeHash3_ok (lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash 3 lay tree heap left right) NotDigestQ :=
  nodeHash_ok 3 lay tree heap left right (by decide)

theorem ftsLeaf_ok (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) NotDigestQ := by
  rw [ftsLeaf_eq_shortHash]
  exact shortHash_ok (tag := 9) (by rw [pad64_ftsLeafInputP]; exact BSuf.hdrBlock_ftsLeafInputP _ _ _ _ _ _)
    (by decide)

theorem forestPk_ok (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) NotDigestQ := by
  rw [Extract.forestPk_eq_shortHash]
  exact shortHash_ok (tag := 11) (Extract.hdrBlock_listInput _ _ _) (by decide)

theorem encoding_ok (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter : BitVec 32) :
    AllQueriesSatisfy (shortHash (encodingInput lay tree leaf message counter)) NotDigestQ :=
  shortHash_ok (tag := 4) (by
    rw [Extract.hdrBlock_pad64 _ (by simp [encodingInput, SphincsSecurity.bytesLE_length])]
    exact Extract.hdrBlock_prefix _ _ _) (by decide)

theorem counterSearch_ok (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) :
    ∀ fuel counter, AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NotDigestQ := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter
      unfold counterSearch
      apply SourceQueries.bind_allowed _ (encoding_ok _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed _ _

theorem buildLevel_ok (tag lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDigestQ := by
  unfold buildLevel
  exact SourceQueries.mapM_allowed NotDigestQ _ _ fun _ => nodeHash_ok _ _ _ _ _ _ ht

theorem buildLevels_ok (tag lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDigestQ := by
  unfold buildLevels
  exact SourceQueries.foldlM_allowed NotDigestQ _ _ (fun _ _ =>
    SourceQueries.bind_allowed _ (buildLevel_ok _ _ _ _ _ _ ht) fun _ => SourceQueries.pure_allowed _ _) _

theorem buildLevels3_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 3 lay tree h leaves) NotDigestQ := buildLevels_ok 3 lay tree h leaves (by decide)

theorem buildLevels10_ok (lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels 10 lay tree h leaves) NotDigestQ := buildLevels_ok 10 lay tree h leaves (by decide)

section aesopShape
attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed SourceQueries.map_allowed
  SourceQueries.foldlM_allowed SourceQueries.mapM_allowed privatePair_ok mask_ok chain_ok leafHash_ok nodeHash3_ok
  ftsLeaf_ok forestPk_ok counterSearch_ok buildLevels3_ok buildLevels10_ok

theorem buildLeaf_ok (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDigestQ := by
  unfold buildLeaf; aesop (config := { maxRuleApplications := 1000 })

attribute [local aesop safe apply] buildLeaf_ok

theorem buildTree_ok (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDigestQ := by
  unfold buildTree; aesop (config := { maxRuleApplications := 1000 })

theorem buildFts_ok (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NotDigestQ := by
  unfold buildFts; aesop (config := { maxRuleApplications := 1000 })

theorem topPath_ok (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDigestQ := by
  unfold topPath; aesop (config := { maxRuleApplications := 1000 })

attribute [local aesop safe apply] buildTree_ok buildFts_ok topPath_ok

theorem signTop_ok (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDigestQ := by
  unfold signTop; aesop (config := { maxRuleApplications := 1000 })

attribute [local aesop safe apply] signTop_ok

theorem signLayers_ok (cache : T3.Cache) (index n : Nat) (message : Digest × BitVec 96 × Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NotDigestQ := by
  induction n generalizing message with
  | zero => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })
  | succ n ih => unfold signLayers; aesop (config := { maxRuleApplications := 1000 })

attribute [local aesop safe apply] signLayers_ok

theorem forestRows_ok (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (Correctness.forestRows index chosen) NotDigestQ := by
  unfold Correctness.forestRows; aesop (config := { maxRuleApplications := 1000 })

attribute [local aesop safe apply] forestRows_ok

theorem payloadAfterDigest_ok (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payloadAfterDigest cache rho output) NotDigestQ := by
  rw [SigningRecords.payloadAfterDigest_forestRows]; aesop (config := { maxRuleApplications := 1000 })

end aesopShape

/-- Every query of a program all of whose queries satisfy `P` satisfies `P`. -/
theorem allQ_queried {α : Type} (answers : Correctness.Answers) (P : T3.Spec.Domain → Prop) (program : M α)
    (h : AllQueriesSatisfy program P) : ∀ q ∈ queried answers program, P q := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      intro q hq
      rw [SecurityExtraction.queried_query_bind] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hi
      · exact ih _ (hn _) q hq

theorem queried_privateMac (answers : Correctness.Answers) (region : Region) :
    queried answers (privateMac region) =
      [.inr (.inl (header 14 0 0 0 0)), .inr (.inl (header 14 0 0 0 1))] := rfl

theorem queried_privateNonce (answers : Correctness.Answers) (m : Message) :
    queried answers (privateNonce m) = [.inr (.inr (.inl m))] := rfl

/-- **R6 (signer shape).** A digest-format query of the authenticated signer is a digest-search trial for the
request's message under the signer's nonce, on the published cache. -/
theorem signer_digest_query (answers : Correctness.Answers) (published : T3.Cache) (request : Request)
    (rho : Digest) (m : Message) (ctr : BitVec 32)
    (hq : (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
      queried answers (FullGame.authenticatedSign published request)) :
    request.cache = published ∧ request.message = m ∧
      rho = evalWithAnswerFn answers (privateNonce request.message) ∧
      (.inl (.inr (pad64 (digestInput rho m ctr))) : Spec.Domain) ∈
        queried answers (digestSearch rho m 0 attemptLimit) := by
  unfold FullGame.authenticatedSign at hq
  rw [queried_bind, queried_privateMac] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  by_cases hc : request.cache = published
  swap
  · rw [if_neg hc] at hq; simp at hq
  rw [if_pos hc, signPayload_factor, queried_bind, queried_privateNonce] at hq
  rcases List.mem_append.mp hq with hq | hq
  · simp at hq
  rw [queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · -- a trial of the digest search
    obtain ⟨c, -, -, heq, -⟩ := digestSearch_queried answers _ _ attemptLimit 0 _ hq
    simp only [Sum.inl.injEq, Sum.inr.injEq] at heq
    obtain ⟨hrho, hctr, hm⟩ := digestInput_injective heq
    subst hrho hm
    exact ⟨hc, rfl, rfl, hq⟩
  · -- the payload work makes no digest-format query
    exfalso
    generalize evalWithAnswerFn answers (digestSearch (evalWithAnswerFn answers (privateNonce request.message))
      request.message 0 attemptLimit) = found at hq
    rcases found with _ | ⟨_, output⟩
    · simp at hq
    · have := allQ_queried answers NotDigestQ _ (payloadAfterDigest_ok _ _ _) _ hq
      exact this (hdrTag_digestInput rho m ctr)

/-- The authenticated signer's answer under a table is the first component of its payload record. -/
theorem eval_authenticatedSign (answers : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn answers (FullGame.authenticatedSign published request) =
      if request.cache = published then
        (evalWithAnswerFn answers (payloadRecordForNonce published
          (evalWithAnswerFn answers (privateNonce request.message)) request.message)).1
      else none := by
  unfold FullGame.authenticatedSign
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    have := congrArg (evalWithAnswerFn answers) (payloadRecord_erasure request.cache request.message)
    rw [SigGolfCandidate.T3M.eval_map] at this
    rw [← this, hc]
    unfold payloadRecord
    rw [evalWithAnswerFn_bind]
  · rw [if_neg hc, if_neg hc, evalWithAnswerFn_pure]

/-- **R6 (no signer occurrence).** In case (C) (the forgery's digest answer `N` is `Shaped`, all four layers `Good`)
with no successful logged signature on the forgery's message and randomizer (`¬SignedDigest`), no logged signer
call queries the forgery's digest input: such a query would be a digest-search trial of that call (shape), hence
its accepted trial (R4, `Shaped` is admissible), hence a selected digest with all layers `Good`, hence a successful
signature with the forgery's randomizer (R3) — a `SignedDigest`. -/
theorem caseC_fresh_not_signer (answers : Correctness.Answers) (published : T3.Cache) (log : QueryLog Requests)
    (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (m : Message) (w : WBytes) (N : HashOutput)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w)
    (hgate : digestGate N = true)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay)
    (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∉
      queried answers (FullGame.authenticatedSign published entry.1) := by
  intro entry he hq
  obtain ⟨hc, hm, hrho, hq'⟩ := signer_digest_query answers published entry.1 _ _ _ hq
  rw [← ofNat_toNat32 (wdc w)] at hq'
  have hacc := rejected_trial_inadmissible answers (wrho w) m (wdc w).toNat hq'
    (by rw [ofNat_toNat32, hN]; simp [digestAdmissible, hS.2.1, hgate])
  rw [ofNat_toNat32, hN] at hacc
  have hsel : (evalWithAnswerFn answers (payloadRecordForNonce published (wrho w) m)).2 = some N := by
    unfold payloadRecordForNonce
    simp only [evalWithAnswerFn_bind, hacc, evalWithAnswerFn_pure]
  obtain ⟨sig, hsig, hsrho⟩ := selected_payload_succeeds answers published (wrho w) m N w hsel hgood
  apply hfresh
  refine ⟨entry, he, hm, sig, ?_, hsrho⟩
  rw [← (hres entry he).eval answers hagree, eval_authenticatedSign, if_pos hc, hm, ← hm, ← hrho, hm]
  exact hsig

/-- **R6 (routing statement for SEC's fresh-digest charging).** On a sample of the shared law in `CaseCFresh`,
the forgery's digest input is queried by no logged signer call, and its first recorded occurrence is on a row
that was uncached before it (so it is an adversary or verifier query whose answer `N` is fresh). -/
theorem caseC_fresh_first_occurrence (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (z : PaddedGame.TraceResult × Correctness.Answers) (hz : z ∈ (SeccLaw.completedExperiment adversary q hq).support)
    (hC : CaseCFresh adversary z) :
    ∃ generated ∈ support (FirstHit.record keygen (∅, ∅)),
      ∃ interaction ∈ support (FirstHit.record
        (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
          (adversary generated.value.1 generated.value.2)) generated.state),
        SourceReplay.Extends interaction.state (QueryRecorded.recordedTrace z.1).state ∧
        ∃ (message : Message) (witness : WBytes) (N : HashOutput),
          evalWithAnswerFn z.2 (digest (wrho witness) message (wdc witness)) = N ∧
          (∀ entry ∈ interaction.value.2,
            (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))) : Spec.Domain) ∉
              queried z.2 (FullGame.authenticatedSign generated.value.2 entry.1)) ∧
          ∃ first : LazyPrivate.State,
            (⟨first, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))), N⟩ :
              FirstHit.QueryEvent) ∈ (QueryRecorded.recordedTrace z.1).events ∧
            first.2 (pad64 (digestInput (wrho witness) message (wdc witness))) = none := by
  obtain ⟨hz1, hagree⟩ := SeccLaw.completed_agrees adversary q hq z hz
  obtain ⟨generated, hg, interaction, hi, hext, -, -, forgery, -, -, message, witness, -, hsigned, hC⟩ := hC
  obtain ⟨N, -, hN, ⟨prior, hev⟩, hS, hgate, hgood, -⟩ := hC
  have hai : ∀ input answer, SourceReplay.known interaction.state input = some answer → z.2 input = answer :=
    fun input answer hk => hagree input answer (SourceReplay.known_mono _ _ hext hk)
  have hres := logged_resolves generated.value.2 _ generated.state _ (FirstHit.recorded_support _ _ _ hi)
  refine ⟨generated, hg, interaction, hi, hext, message, witness, N, hN,
    caseC_fresh_not_signer z.2 generated.value.2 interaction.value.2 interaction.state hres hai message witness N
      hN hS hgate hgood hsigned, ?_⟩
  exact FirstHit.first_public_occurrence _ _ (PaddedExtraction.traced_record_support adversary q hq z.1 hz1)
    prior _ _ hev

/-! ## R6, counter form (BP-B §2.1 "Statement") -/

/-- An accepted digest search rejected every earlier trial. -/
theorem digestSearch_rejects (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start (c : BitVec 32) (N0 : HashOutput), start + fuel ≤ 2 ^ 32 →
      evalWithAnswerFn answers (digestSearch rho m start fuel) = some (c, N0) →
      ∀ c', start ≤ c' → c' < c.toNat →
        digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false := by
  intro fuel
  induction fuel with
  | zero => intro start c N0 _ h; simp [digestSearch] at h
  | succ fuel ih =>
      intro start c N0 hfit h c' h1 h2
      rw [digestSearch_succ, evalWithAnswerFn_bind] at h
      by_cases hadm : digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        have : c.toNat = start := by
          rw [← h.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [if_neg hadm] at h
        by_cases hc' : c' = start
        · subst hc'; simpa using hadm
        · exact ih (start + 1) c N0 (by omega) h c' (by omega) h2

/-- A failed digest search rejected every trial. -/
theorem digestSearch_none_rejects (answers : Correctness.Answers) (rho : Digest) (m : Message) :
    ∀ fuel start, evalWithAnswerFn answers (digestSearch rho m start fuel) = none →
      ∀ c', start ≤ c' → c' < start + fuel →
        digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 c'))) = false := by
  intro fuel
  induction fuel with
  | zero => intro start _ c' h1 h2; omega
  | succ fuel ih =>
      intro start h c' h1 h2
      rw [digestSearch_succ, evalWithAnswerFn_bind] at h
      by_cases hadm : digestAdmissible (evalWithAnswerFn answers (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure] at h; simp at h
      · rw [if_neg hadm] at h
        by_cases hc' : c' = start
        · subst hc'; simpa using hadm
        · exact ih (start + 1) h c' (by omega) (by omega)

/-- **R6 core (one signer call).** Let the forgery's digest answer `N` (at its counter `wdc w < attemptLimit`) be
`Shaped` with all four layers `Good`. A signer whose nonce for the forgery's message is the forgery's randomizer
either accepted a strictly earlier counter (so it never queried the forgery's digest input), or produced a
successful payload with the forgery's randomizer. Independent of logs and journals. -/
theorem signer_vs_forgery (answers : Correctness.Answers) (published : T3.Cache) (m : Message) (w : WBytes)
    (N : HashOutput) (hdc : (wdc w).toNat < attemptLimit)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w)
    (hgate : digestGate N = true)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay) :
    (∃ (c : BitVec 32) (N0 : HashOutput),
        evalWithAnswerFn answers (digestSearch (wrho w) m 0 attemptLimit) = some (c, N0) ∧
          c.toNat < (wdc w).toNat) ∨
      ∃ sig, (evalWithAnswerFn answers (payloadRecordForNonce published (wrho w) m)).1 = some sig ∧
        sig.rho = wrho w := by
  have hadm : digestAdmissible (evalWithAnswerFn answers (digest (wrho w) m
      (BitVec.ofNat 32 (wdc w).toNat))) = true := by
    rw [ofNat_toNat32, hN]; simp [digestAdmissible, hS.2.1, hgate]
  cases hd : evalWithAnswerFn answers (digestSearch (wrho w) m 0 attemptLimit) with
  | none =>
      exfalso
      have := digestSearch_none_rejects answers (wrho w) m attemptLimit 0 hd (wdc w).toNat (Nat.zero_le _) (by omega)
      rw [hadm] at this
      exact Bool.noConfusion this
  | some found =>
      obtain ⟨c, N0⟩ := found
      have hsome := Correctness.digestSearch_some answers (wrho w) m attemptLimit 0 c N0 (by decide) hd
      by_cases hlt : c.toNat < (wdc w).toNat
      · exact Or.inl ⟨c, N0, rfl, hlt⟩
      right
      rcases Nat.lt_or_ge (wdc w).toNat c.toNat with hgt | hge
      · exfalso
        have := digestSearch_rejects answers (wrho w) m attemptLimit 0 c N0 (by decide) hd (wdc w).toNat
          (Nat.zero_le _) hgt
        rw [hadm] at this
        exact Bool.noConfusion this
      · -- the forgery's trial is the accepted one: R3
        have hcw : c = wdc w := BitVec.eq_of_toNat_eq (by omega)
        subst hcw
        have hN0 : N0 = N := by rw [← hsome.2.2.1, hN]
        subst hN0
        have hsel : (evalWithAnswerFn answers (payloadRecordForNonce published (wrho w) m)).2 = some N0 := by
          unfold payloadRecordForNonce
          simp only [evalWithAnswerFn_bind, hd, evalWithAnswerFn_pure]
        exact selected_payload_succeeds answers published (wrho w) m N0 w hsel hgood

/-- **R6, counter form.** In case (C) with `¬SignedDigest`, every logged request on the forgery's message with the
published cache either used a different randomizer, or its digest search accepted a counter strictly below the
forgery's (so the signer only ever queried strictly earlier trials, never the forgery's digest input). Requests
with another cache query no digest at all (`signer_digest_query`). -/
theorem caseC_fresh_counter_cases (answers : Correctness.Answers) (published : T3.Cache) (log : QueryLog Requests)
    (state : LazyPrivate.State)
    (hres : ∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2)
    (hagree : ∀ input answer, SourceReplay.known state input = some answer → answers input = answer)
    (m : Message) (w : WBytes) (N : HashOutput) (hdc : (wdc w).toNat < attemptLimit)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w)
    (hgate : digestGate N = true)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay)
    (hfresh : ¬SignedDigest log m w) :
    ∀ entry ∈ log, entry.1.message = m → entry.1.cache = published →
      wrho w ≠ evalWithAnswerFn answers (privateNonce m) ∨
      ∃ (c : BitVec 32) (N0 : HashOutput),
        evalWithAnswerFn answers (digestSearch (wrho w) m 0 attemptLimit) = some (c, N0) ∧ c.toNat < (wdc w).toNat := by
  intro entry he hm hc
  by_cases hρ : wrho w = evalWithAnswerFn answers (privateNonce m)
  swap
  · exact Or.inl hρ
  right
  rcases signer_vs_forgery answers published m w N hdc hN hS hgate hgood with h | ⟨sig, hsig, hsrho⟩
  · exact h
  · exfalso
    apply hfresh
    refine ⟨entry, he, hm, sig, ?_, hsrho⟩
    rw [← (hres entry he).eval answers hagree, eval_authenticatedSign, if_pos hc, hm, ← hρ]
    exact hsig

/-- The authenticated record of a request on the published cache evaluates to the payload record for the signer's
nonce. -/
theorem eval_authenticatedRecord_published (answers : Correctness.Answers) (published : T3.Cache) (m : Message) :
    evalWithAnswerFn answers (FullGame.authenticatedRecord published ⟨m, published⟩) =
      evalWithAnswerFn answers (payloadRecordForNonce published (evalWithAnswerFn answers (privateNonce m)) m) := by
  unfold FullGame.authenticatedRecord
  simp only [evalWithAnswerFn_bind]
  rw [if_pos trivial]
  unfold payloadRecord
  rw [evalWithAnswerFn_bind]

/-- **R6, journal form** (for SEC's journal-based charging). Under `JournalOK` and an agreeing table, for a `Shaped`
all-`Good` forgery digest answer: the forgery's message has an uncached nonce (never signed), or a nonce other than
the forgery's randomizer, or an accepted counter strictly below the forgery's, or a successful journal signature
with the forgery's randomizer (the `SignedDigest` case). In the first three cases the signer never queried the
forgery's digest input (`signer_digest_query`, `digestSearch_queried`). -/
theorem caseC_journal_cases (published : T3.Cache) (history : MonitoredPrivate.History)
    (state : MonitoredPrivate.State) (journal : MonitoredPrivate.Journal)
    (hj : MonitoredPrivate.JournalOK published history state journal) (answers : Correctness.Answers)
    (hagree : ∀ input answer, SourceReplay.known state.source.2 input = some answer → answers input = answer)
    (m : Message) (w : WBytes) (N : HashOutput) (hdc : (wdc w).toNat < attemptLimit)
    (hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N) (hS : Shaped N w)
    (hgate : digestGate N = true)
    (hgood : ∀ lay : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) lay) :
    state.source.2.1 (.inr (.inl m)) = none ∨
      evalWithAnswerFn answers (privateNonce m) ≠ wrho w ∨
      (∃ (c : BitVec 32) (N0 : HashOutput),
        evalWithAnswerFn answers (digestSearch (wrho w) m 0 attemptLimit) = some (c, N0) ∧
          c.toNat < (wdc w).toNat) ∨
      ∃ entry ∈ journal, entry.1 = m ∧ ∃ sig, entry.2.1 = some sig ∧ sig.rho = wrho w := by
  rcases hj.2.2.1 m with hnone | hmem
  · exact Or.inl hnone
  right
  by_cases hρ : evalWithAnswerFn answers (privateNonce m) = wrho w
  swap
  · exact Or.inl hρ
  right
  rcases signer_vs_forgery answers published m w N hdc hN hS hgate hgood with h | ⟨sig, hsig, hsrho⟩
  · exact Or.inl h
  · right
    obtain ⟨entry, he, hkey⟩ := List.mem_map.mp hmem
    have hres := hj.2.1 entry he
    have hev := hres.eval answers hagree
    rw [hkey, eval_authenticatedRecord_published, hρ] at hev
    refine ⟨entry, he, hkey, sig, ?_, hsrho⟩
    rw [← hev, hsig]

end SigGolfCandidate.T3.Security.BPB
