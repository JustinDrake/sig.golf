import SigGolfCandidate.T3.Secc.PairGuessLazyDefs
namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def NotDN : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => x ∉ digestInputs
  | .inr (.inl _) => True
  | .inr (.inr (.inl _)) => False
  | .inr (.inr (.inr _)) => True
theorem not_digest_of_hdr {x : HashInput} {t l tr p ix : Nat} (hx : Extract.hdrBlock x = bytesLE 16 (header t l tr p ix))
    (ht : t % 256 ≠ 12) : x ∉ digestInputs := by
  intro hm
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hm
  rw [Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hx
  unfold digestInput at hx
  have h2 : bytesLE 16 (header 12 0 0 0 ctr.toNat) = bytesLE 16 (header t l tr p ix) :=
    (Extract.hdrBlock_prefix rho (header 12 0 0 0 ctr.toNat) (bytesLE 32 m)).symm.trans hx
  exact QuerySpace.header_ne_of_tag (by omega) (bytesLE_injective h2).symm
theorem not_digest_prefix (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 12) :
    pad64 (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest) ∉ digestInputs := by
  refine not_digest_of_hdr (t := t) (l := l) (tr := tr) (p := p) (ix := ix) ?_ ht
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  exact Extract.hdrBlock_prefix _ _ _
theorem probeInput_not_digest (f : FtsCoord) (c : Digest) : probeInput f c ∉ digestInputs :=
  not_digest_of_hdr (hdrBlock_probeInput f c) (by decide)
section DN
open SourceQueries
theorem shortHash_dn (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 12) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) NotDN := by
  unfold shortHash publicHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr (not_digest_prefix a l tr p ix rest ht))
    fun _ => pure_allowed _ _
theorem privatePair_dn (t l tr p ix : Nat) : AllQueriesSatisfy (privatePair t l tr p ix) NotDN := by
  unfold privatePair privateHash
  exact bind_allowed NotDN ((allQueriesSatisfy_query_iff _ _).mpr trivial) fun _ => pure_allowed _ _
theorem privateMac_dn (region : Region) : AllQueriesSatisfy (privateMac region) NotDN := by
  exact privateMac_allowed NotDN (fun _ => trivial) region
theorem chainStep_dn (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) NotDN := by
  unfold shortHash publicHash
  apply bind_allowed NotDN
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    intro hm
    obtain ⟨rho, m, ctr, he⟩ := mem_digestInputs.mp hm
    have hh := congrArg Extract.hdrBlock he
    rw [chainInput_padded, Extract.hdrBlock_pad64 _ (by rw [digestInput_length]; omega)] at hh
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hh
    rw [chainInput_header] at hh
    unfold digestInput at hh
    rw [Extract.hdrBlock_prefix] at hh
    exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ (bytesLE_injective hh)
  · intro _; exact pure_allowed _ _
theorem chain_dn (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NotDN := by
  unfold chain
  exact foldlM_allowed NotDN _ _ (fun v step => chainStep_dn lay tree leaf i step v) value
theorem leafHash_dn (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NotDN := by
  unfold leafHash
  exact shortHash_dn _ _ _ _ _ _ (by decide)
theorem nodeHash_dn {tag : Nat} (lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NotDN := by
  unfold nodeHash
  exact shortHash_dn _ _ _ _ _ _ ht
theorem mask_dn (level index : Nat) : AllQueriesSatisfy (mask level index) NotDN := by
  unfold mask pairedMask
  exact bind_allowed NotDN (privatePair_dn _ _ _ _ _) fun _ => pure_allowed _ _
theorem buildLeaf_dn (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NotDN := by
  unfold buildLeaf
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state pair
    apply bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    intro seeds
    apply foldlM_allowed NotDN
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed NotDN (chain_dn _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed NotDN (chain_dn _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed NotDN (leafHash_dn _ _ _ _) fun _ => pure_allowed _ _
theorem buildLevel_dn {tag : Nat} (lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NotDN := by
  unfold buildLevel
  exact mapM_allowed NotDN _ _ fun _ => nodeHash_dn _ _ _ _ _ ht
theorem buildLevels_dn {tag : Nat} (lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NotDN := by
  unfold buildLevels
  exact foldlM_allowed NotDN _ _ (fun levels level =>
    bind_allowed NotDN (buildLevel_dn _ _ _ _ _ ht) fun _ => pure_allowed _ _) _
theorem buildTree_dn (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NotDN := by
  unfold buildTree
  apply bind_allowed NotDN
  · exact foldlM_allowed NotDN _ _ (fun state leaf =>
      bind_allowed NotDN (buildLeaf_dn _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed NotDN (buildLevels_dn _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem maskedLevel_dn (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) NotDN := by
  unfold maskedLevel pairedMask
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun pair => bind_allowed NotDN (privatePair_dn _ _ _ _ _) (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
theorem keygenPayload_dn : AllQueriesSatisfy keygenPayload NotDN := by
  unfold keygenPayload
  apply bind_allowed NotDN (buildTree_dn _ _ _ _)
  intro built
  apply bind_allowed NotDN
  · exact mapM_allowed NotDN _ _ (fun level => maskedLevel_dn _ _)
  · intro _
    exact pure_allowed _ _
theorem keygen_dn : AllQueriesSatisfy keygen NotDN := by
  unfold keygen
  apply bind_allowed NotDN keygenPayload_dn
  intro generated
  exact bind_allowed NotDN (privateMac_dn _) fun _ => pure_allowed _ _
theorem counterSearch_dn (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NotDN := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold counterSearch
      apply bind_allowed NotDN
      · unfold encodingInput
        exact shortHash_dn _ _ _ _ _ _ (by decide)
      · intro answer
        split
        · exact ih _
        · exact pure_allowed _ _
theorem forestPk_dn (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) NotDN := by
  unfold forestPk
  exact shortHash_dn _ _ _ _ _ _ (by decide)
theorem topPath_dn (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NotDN := by
  unfold topPath
  exact mapM_allowed NotDN _ _ fun level =>
    bind_allowed NotDN (mask_dn _ _) fun _ => pure_allowed _ _
theorem signTop_dn (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NotDN := by
  unfold signTop
  exact bind_allowed NotDN (buildLeaf_dn _ _ _ _ _) fun _ =>
    bind_allowed NotDN (topPath_dn _ _) fun _ => pure_allowed _ _
theorem signLayers_dn (cache : T3.Cache) (index n : Nat) (message : Digest × BitVec 96 × Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NotDN := by
  induction n generalizing message with
  | zero => exact pure_allowed _ _
  | succ n ih =>
      unfold signLayers
      apply bind_allowed NotDN (counterSearch_dn _ _ _ _ _ _)
      intro found
      split
      · split
        · exact bind_allowed NotDN (signTop_dn _ _ _) fun _ => pure_allowed _ _
        · apply bind_allowed NotDN (buildTree_dn _ _ _ _)
          intro built
          obtain ⟨levels, values⟩ := built
          dsimp only
          apply bind_allowed NotDN (ih _)
          intro previous
          split
          · exact pure_allowed _ _
          · exact pure_allowed _ _
      · exact pure_allowed _ _
theorem ftsLeaf_dn (index coord leaf : Nat) (secret : Digest) : AllQueriesSatisfy (ftsLeaf index coord leaf secret) NotDN := by
  unfold ftsLeaf
  rw [zero16_eq]
  exact shortHash_dn 0 _ _ _ _ _ (by decide)
theorem buildFts_dn (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NotDN := by
  unfold buildFts
  apply bind_allowed NotDN
  · apply foldlM_allowed NotDN
    intro state pair
    apply bind_allowed NotDN (privatePair_dn _ _ _ _ _)
    intro seeds
    obtain ⟨left, right⟩ := seeds
    exact bind_allowed NotDN (ftsLeaf_dn _ _ _ _) fun _ =>
      bind_allowed NotDN (ftsLeaf_dn _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    exact bind_allowed NotDN (buildLevels_dn _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem signForest_dn (index : Nat) (chosen : List Selection) :
    AllQueriesSatisfy (Correctness.signForest index chosen) NotDN := by
  unfold Correctness.signForest
  apply foldlM_allowed NotDN
  intro state coord
  apply bind_allowed NotDN (buildFts_dn _ _)
  intro built
  obtain ⟨levels, secrets⟩ := built
  exact pure_allowed _ _
end DN
def nonceHalf (m : Message) : ChainGraph.HalfCoordinate := (.inr (.inl m), 0)
theorem nonceHalf_not_secret (m : Message) : nonceHalf m ∉ Set.range CanonGraph.secretCoordinate := by
  rintro ⟨i, hi⟩
  have h1 := congrArg Prod.fst hi
  cases i with
  | inl a => cases h1
  | inr f => cases h1
def nonceOther (m : Message) : CanonGraph.OtherHalf := ⟨nonceHalf m, nonceHalf_not_secret m⟩
section Rest
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyFree : DecidableEq T3.Cache := Classical.decEq _
noncomputable def digestOf (ω : Omega U) : digestInputs → HashOutput := fun x => finiteHashAnswer ∅ U ω.residual x.val
def nonceOf (ω : Omega U) : Message → Digest := fun m => ω.other (nonceOther m)
def SameRest (ω₁ ω₂ : Omega U) : Prop :=
  ω₁.seeds = ω₂.seeds ∧ ω₁.labels = ω₂.labels ∧
    (∀ x : U, x.val ∉ digestInputs → ω₁.residual x = ω₂.residual x) ∧
    (∀ h : CanonGraph.OtherHalf, (∀ m, h ≠ nonceOther m) → ω₁.other h = ω₂.other h)
theorem secrets_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) :
    ω₁.secrets fts = ω₂.secrets fts := by
  funext i
  cases i with
  | inl a => exact congrFun h.1 a
  | inr p => rfl
theorem programmed_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) (x : U)
    (hx : x.val ∉ digestInputs) :
    CanonGraph.programmed U hU (ω₁.secrets fts) ω₁.labels ω₁.residual x =
      CanonGraph.programmed U hU (ω₂.secrets fts) ω₂.labels ω₂.residual x := by
  rw [secrets_sameRest h fts, h.2.1]
  by_cases hc : ∃ node, x.val = CanonGraph.cell (ω₂.secrets fts) node ω₂.labels
  · obtain ⟨node, hnode⟩ := hc
    have hx' : x = CanonGraph.cellIn U hU (ω₂.secrets fts) node ω₂.labels := Subtype.ext hnode
    rw [hx', CanonGraph.programmed_at, CanonGraph.programmed_at]
  · have hn : ∀ node, x.val ≠ CanonGraph.cell (ω₂.secrets fts) node ω₂.labels := fun node he => hc ⟨node, he⟩
    rw [CanonGraph.programmed_other U hU _ _ _ _ hn, CanonGraph.programmed_other U hU _ _ _ _ hn]
    exact h.2.2.1 x hx
theorem private_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) (c : Coordinate)
    (hc : ∀ m, c ≠ .inr (.inl m)) :
    CanonGraph.privateEquiv.symm (ω₁.secrets fts, ω₁.other) c = CanonGraph.privateEquiv.symm (ω₂.secrets fts, ω₂.other) c := by
  have hhalf : ∀ k : Fin 2, CanonGraph.splitEquiv.symm (ω₁.secrets fts, ω₁.other) (c, k) =
      CanonGraph.splitEquiv.symm (ω₂.secrets fts, ω₂.other) (c, k) := by
    intro k
    by_cases hr : (c, k) ∈ Set.range CanonGraph.secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret, secrets_sameRest h fts]
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
      apply h.2.2.2
      intro m he
      have := congrArg (fun o : CanonGraph.OtherHalf => o.1.1) he
      exact hc m this
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem answers_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) (q : T3.Spec.Domain)
    (hq : NotDN q) : Omega.answers hU ω₁ fts q = Omega.answers hU ω₂ fts q := by
  rcases q with (n | x) | c
  · rfl
  · change finiteHashAnswer ∅ U (CanonGraph.programmed U hU (ω₁.secrets fts) ω₁.labels ω₁.residual) x =
      finiteHashAnswer ∅ U (CanonGraph.programmed U hU (ω₂.secrets fts) ω₂.labels ω₂.residual) x
    by_cases hxU : x ∈ U
    · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
      exact programmed_sameRest hU h fts ⟨x, hxU⟩ hq
    · simp only [finiteHashAnswer, dif_neg hxU]
  · apply private_sameRest h fts c
    rintro m rfl
    exact hq
theorem eval_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (fts : FtsCoord → Digest) {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program NotDN) :
    evalWithAnswerFn (Omega.answers hU ω₁ fts) program = evalWithAnswerFn (Omega.answers hU ω₂ fts) program :=
  eval_congr_allowed hp (answers_sameRest hU h fts)
theorem residual_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (x : HashInput) (hx : x ∉ digestInputs) :
    finiteHashAnswer ∅ U ω₁.residual x = finiteHashAnswer ∅ U ω₂.residual x := by
  by_cases hxU : x ∈ U
  · rw [finiteHashAnswer_none ∅ U _ _ hxU rfl, finiteHashAnswer_none ∅ U _ _ hxU rfl]
    exact h.2.2.1 ⟨x, hxU⟩ hx
  · simp only [finiteHashAnswer, dif_neg hxU]
theorem hashL_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) : hashL hU ω₁ = hashL hU ω₂ := by
  funext x
  unfold hashL
  cases hd : decodeProbe x with
  | some p =>
      have hx := eq_of_decodeProbe hd
      have hnd : x ∉ digestInputs := by rw [hx]; exact probeInput_not_digest _ _
      simp only [h.2.1, residual_sameRest h x hnd]
  | none =>
      by_cases hx : x ∈ digestInputs
      · simp only [if_pos hx]
      · simp only [if_neg hx]
        rw [answers_sameRest hU h (fun _ => 0) (.inl (.inr x)) hx]
theorem signerForest_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) : signerForest hU ω₁ = signerForest hU ω₂ := by
  funext output
  exact eval_sameRest hU h _ (signForest_dn _ _)
theorem signerLayers_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) : signerLayers hU ω₁ = signerLayers hU ω₂ := by
  funext request output
  unfold signerLayers
  rw [signerForest_sameRest hU h, eval_sameRest hU h _ (forestPk_dn _ _), eval_sameRest hU h _ (signLayers_dn _ _ _ _)]
theorem signL_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) : signL hU ω₁ = signL hU ω₂ := by
  funext published request
  unfold signL finishL
  simp only [signerLayers_sameRest hU h, signerForest_sameRest hU h]
theorem interactionL_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (published : T3.Cache) {α : Type} :
    (interactionL hU ω₁ published : OracleComp LazyPrivate.Interaction α → _) = interactionL hU ω₂ published := by
  unfold interactionL
  simp only [hashL_sameRest hU h, signL_sameRest hU h]
theorem programL_sameRest {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) {β : Type} :
    (programL hU ω₁ : M β → _) = programL hU ω₂ := by
  unfold programL
  simp only [hashL_sameRest hU h]
theorem worldGameL_congr {ω₁ ω₂ : Omega U} (h : SameRest ω₁ ω₂) (adversary : AdversaryP) :
    worldGameCore hU ω₁ adversary = worldGameCore hU ω₂ adversary := by
  unfold worldGameCore
  rw [eval_sameRest hU h _ keygen_dn]
  simp only [interactionL_sameRest hU h, programL_sameRest hU h]
end Rest
end SigGolfCandidate.T3.Security.BPair
