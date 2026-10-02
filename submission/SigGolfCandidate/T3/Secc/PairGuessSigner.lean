import SigGolfCandidate.T3.Secc.PairGuessWorld

/-!
# B-PAIR (2/4): the FTS secrets enter the honest computation only through the opened positions

On G's eager canonical table `Omega.answers hU ω fts` (chain seeds, other private halves, labels and residual
table from `ω`; FTS secrets `fts`):

* `answers_free`: two tables that differ only in `fts` agree on every `FtsFree` query (coins, public inputs that
  are not FTS-leaf probes, private coordinates that are not FTS secret pairs);
* `eval_free`: a program whose queries are all `FtsFree` evaluates identically under them; key generation,
  the nonce, the digest search, the forest pk and the four layers are `FtsFree`;
* `buildFts_levels_eq`: the levels of every FTS tree are the same lists (leaves are labels, nodes are cells);
* `sign_eval`: the authenticated signer is `signFrom` of the default table with the opened secrets
  `(openedPositions output).map fts`; hence **locality** (`sign_local`).
-/

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers treeValue)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The FTS-free queries -/

/-- A private coordinate holding two FTS secrets (`privatePair 8 coord index 0 pair`). -/
def IsFtsPair (c : Coordinate) : Prop := ∃ f : FtsCoord, c = .inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2))

/-- Queries whose answer does not depend on the FTS secrets. -/
def FtsFree : T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => decodeProbe x = none
  | .inr c => ¬IsFtsPair c

theorem not_isFtsPair_header {t l tr p ix : Nat} (ht : t % 256 ≠ 8) : ¬IsFtsPair (.inl (header t l tr p ix)) := by
  rintro ⟨f, hf⟩
  exact QuerySpace.header_ne_of_tag (by omega) (Sum.inl.inj hf)

theorem decodeProbe_prefix (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 9) :
    decodeProbe (pad64 (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) = none := by
  refine decodeProbe_of_hdr (t := t) (l := l) (tr := tr) (p := p) (ix := ix) ?_ ht
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega)]
  exact Extract.hdrBlock_prefix _ _ _

/-! ## Generic congruence -/

theorem eval_query' (A : Answers) (input : T3.Spec.Domain) :
    evalWithAnswerFn A (liftM (T3.Spec.query input)) = A input :=
  simulateQ_spec_query A input

/-- A program reading only queries of `P` evaluates identically under tables agreeing on `P`. -/
theorem eval_congr_allowed {P : T3.Spec.Domain → Prop} {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program P) {A A' : Answers} (h : ∀ q, P q → A q = A' q) :
    evalWithAnswerFn A program = evalWithAnswerFn A' program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_query', eval_query', h input hi]
      exact ih _ (hn _)

/-! ## FTS-free programs -/

section Free
open SourceQueries

theorem zero16_eq : zero16 = bytesLE 16 (0 : Digest) := by decide

theorem shortHash_free (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 9) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) FtsFree := by
  unfold shortHash publicHash
  exact bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix a l tr p ix rest ht))
    fun _ => pure_allowed _ _

theorem privatePair_free {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 8) :
    AllQueriesSatisfy (privatePair t l tr p ix) FtsFree := by
  unfold privatePair privateHash
  exact bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr (not_isFtsPair_header ht))
    fun _ => pure_allowed _ _

theorem privateNonce_free (message : Message) : AllQueriesSatisfy (privateNonce message) FtsFree := by
  unfold privateNonce privateHash
  refine bind_allowed FtsFree ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun _ => pure_allowed _ _
  rintro ⟨f, hf⟩
  cases hf

theorem privateMac_free (region : Region) : AllQueriesSatisfy (privateMac region) FtsFree := by
  unfold privateMac privateHash
  refine (allQueriesSatisfy_query_iff _ _).mpr ?_
  rintro ⟨f, hf⟩
  cases hf

theorem chainStep_free (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) FtsFree := by
  unfold chainInput
  rw [zero16_eq]
  exact shortHash_free 0 _ _ _ _ _ (by decide)

theorem chain_free (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) FtsFree := by
  unfold chain
  exact foldlM_allowed FtsFree _ _ (fun v step => chainStep_free lay tree leaf i step v) value

theorem leafHash_free (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) FtsFree := by
  unfold leafHash
  exact shortHash_free _ _ _ _ _ _ (by decide)

theorem nodeHash_free {tag : Nat} (lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 9) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) FtsFree := by
  unfold nodeHash
  exact shortHash_free _ _ _ _ _ _ ht

theorem mask_free (level index : Nat) : AllQueriesSatisfy (mask level index) FtsFree := by
  unfold mask
  exact bind_allowed FtsFree (privatePair_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _

theorem buildLeaf_free (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) FtsFree := by
  unfold buildLeaf
  apply bind_allowed FtsFree
  · apply foldlM_allowed FtsFree
    intro state pair
    apply bind_allowed FtsFree (privatePair_free _ _ _ _ (by decide))
    intro seeds
    apply foldlM_allowed FtsFree
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed FtsFree (chain_free _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed FtsFree (chain_free _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed FtsFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _

theorem buildLevel_free {tag : Nat} (lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 9) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) FtsFree := by
  unfold buildLevel
  exact mapM_allowed FtsFree _ _ fun _ => nodeHash_free _ _ _ _ _ ht

theorem buildLevels_free {tag : Nat} (lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 9) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) FtsFree := by
  unfold buildLevels
  exact foldlM_allowed FtsFree _ _ (fun levels level =>
    bind_allowed FtsFree (buildLevel_free _ _ _ _ _ ht) fun _ => pure_allowed _ _) _

theorem buildTree_free (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) FtsFree := by
  unfold buildTree
  apply bind_allowed FtsFree
  · exact foldlM_allowed FtsFree _ _ (fun state leaf =>
      bind_allowed FtsFree (buildLeaf_free _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed FtsFree (buildLevels_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _

theorem keygenPayload_free : AllQueriesSatisfy keygenPayload FtsFree := by
  unfold keygenPayload
  apply bind_allowed FtsFree (buildTree_free _ _ _ _)
  intro built
  apply bind_allowed FtsFree
  · exact mapM_allowed FtsFree _ _ fun level => mapM_allowed FtsFree _ _ fun i =>
      bind_allowed FtsFree (mask_free _ _) fun _ => pure_allowed _ _
  · intro _
    exact pure_allowed _ _

theorem keygen_free : AllQueriesSatisfy keygen FtsFree := by
  unfold keygen
  apply bind_allowed FtsFree keygenPayload_free
  intro generated
  exact bind_allowed FtsFree (privateMac_free _) fun _ => pure_allowed _ _

theorem counterSearch_free (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) FtsFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold counterSearch
      apply bind_allowed FtsFree
      · unfold encodingInput
        exact shortHash_free _ _ _ _ _ _ (by decide)
      · intro answer
        split
        · exact ih _
        · exact pure_allowed _ _

theorem digest_free (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) FtsFree := by
  unfold digest publicHash digestInput
  exact (allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix _ _ _ _ _ _ (by decide))

theorem digestSearch_free (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) FtsFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold digestSearch
      apply bind_allowed FtsFree (digest_free _ _ _)
      intro output
      split
      · exact pure_allowed _ _
      · exact ih _

theorem forestPk_free (index : Nat) (roots : List Digest) : AllQueriesSatisfy (forestPk index roots) FtsFree := by
  unfold forestPk
  exact shortHash_free _ _ _ _ _ _ (by decide)

theorem topPath_free (cache : T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) FtsFree := by
  unfold topPath
  apply bind_allowed FtsFree (buildLeaf_free _ _ _ _ _)
  intro sibling
  apply bind_allowed FtsFree (buildLeaf_free _ _ _ _ _)
  intro left
  apply bind_allowed FtsFree (buildLeaf_free _ _ _ _ _)
  intro right
  apply bind_allowed FtsFree (nodeHash_free _ _ _ _ _ (by decide))
  intro siblingPair
  apply bind_allowed FtsFree
  · exact mapM_allowed FtsFree _ _ fun level =>
      bind_allowed FtsFree (mask_free _ _) fun _ => pure_allowed _ _
  · intro _
    exact pure_allowed _ _

theorem signTop_free (cache : T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) FtsFree := by
  unfold signTop
  exact bind_allowed FtsFree (buildLeaf_free _ _ _ _ _) fun _ =>
    bind_allowed FtsFree (topPath_free _ _) fun _ => pure_allowed _ _

theorem signLayers_free (cache : T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) FtsFree := by
  induction n generalizing message with
  | zero => exact pure_allowed _ _
  | succ n ih =>
      unfold signLayers
      apply bind_allowed FtsFree (counterSearch_free _ _ _ _ _ _)
      intro found
      split
      · split
        · exact bind_allowed FtsFree (signTop_free _ _ _) fun _ => pure_allowed _ _
        · apply bind_allowed FtsFree (buildTree_free _ _ _ _)
          intro built
          obtain ⟨levels, values⟩ := built
          dsimp only
          apply bind_allowed FtsFree (ih _)
          intro previous
          split
          · exact pure_allowed _ _
          · exact pure_allowed _ _
      · exact pure_allowed _ _

end Free


/-! ## The eager table as a function of the FTS secrets -/

section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

theorem splitEquiv_symm_secret (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (i : CanonGraph.SecretIndex) :
    CanonGraph.splitEquiv.symm (s, o) (CanonGraph.secretCoordinate i) = s i := by
  have h := CanonGraph.splitEquiv_fst (CanonGraph.splitEquiv.symm (s, o))
  rw [Equiv.apply_symm_apply] at h
  exact (congrFun h i).symm

theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : (CanonGraph.splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [CanonGraph.splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl

theorem splitEquiv_symm_other (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range CanonGraph.secretCoordinate) : CanonGraph.splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (CanonGraph.splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm

theorem privateEquiv_symm_apply (s : CanonGraph.Secrets) (o : CanonGraph.OtherHalves) (c : Coordinate) :
    CanonGraph.privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (CanonGraph.splitEquiv.symm (s, o) (c, 0)) (CanonGraph.splitEquiv.symm (s, o) (c, 1)) :=
  rfl

/-- Private coordinates that are not FTS secret pairs do not depend on the FTS secrets. -/
theorem private_free (fts fts' : FtsCoord → Digest) (c : Coordinate) (hc : ¬IsFtsPair c) :
    CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other) c = CanonGraph.privateEquiv.symm (ω.secrets fts', ω.other) c := by
  have hhalf : ∀ h : Fin 2, CanonGraph.splitEquiv.symm (ω.secrets fts, ω.other) (c, h) =
      CanonGraph.splitEquiv.symm (ω.secrets fts', ω.other) (c, h) := by
    intro h
    by_cases hr : (c, h) ∈ Set.range CanonGraph.secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret]
      cases i with
      | inl a => rfl
      | inr p =>
          exfalso
          apply hc
          refine ⟨ofLeafPos p, ?_⟩
          have := congrArg Prod.fst hi
          exact this.symm
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]

/-- The FTS secret of the table is `fts`. -/
theorem secretNat_answers (fts : FtsCoord → Digest) (f : FtsCoord) :
    secretNat (Omega.answers hU ω fts) f.1.val f.2.1.val f.2.2.val = fts f := by
  have hc : CanonGraph.ftsCoordinate (toLeafPos f) =
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)), ⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩) := rfl
  have hs := splitEquiv_symm_secret (ω.secrets fts) ω.other (.inr (toLeafPos f))
  change CanonGraph.splitEquiv.symm (ω.secrets fts, ω.other) (CanonGraph.ftsCoordinate (toLeafPos f)) = fts f at hs
  rw [hc] at hs
  unfold secretNat privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (if f.2.2.val % 2 = 0 then (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)))).extractLsb' 0 128
    else (CanonGraph.privateEquiv.symm (ω.secrets fts, ω.other)
      (.inl (header 8 f.2.1.val f.1.val 0 (f.2.2.val / 2)))).extractLsb' 128 128) = fts f
  rw [privateEquiv_symm_apply, ChainGraph.joinOutput_low, ChainGraph.joinOutput_high]
  have h2 := Nat.mod_lt f.2.2.val (by decide : 0 < 2)
  split_ifs with he
  · have e : (⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 := Fin.ext he
    rw [e] at hs
    exact hs
  · have e : (⟨f.2.2.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 :=
      Fin.ext (by change f.2.2.val % 2 = 1; omega)
    rw [e] at hs
    exact hs

theorem secretAt_answers (fts : FtsCoord → Digest) (f : FtsCoord) : secretAt (Omega.answers hU ω fts) f = fts f :=
  secretNat_answers hU ω fts f

/-- A canonical FTS leaf cell is a probe. -/
theorem cell_ftsLeaf (s : CanonGraph.Secrets) (p : CanonGraph.FtsLeafPos) (labels : CanonGraph.Labels) :
    CanonGraph.cell s (.ftsLeaf p) labels = probeInput (ofLeafPos p) (CanonGraph.ftsOf s p) := rfl

/-- Cells of other positions read only the chain seeds of the secrets. -/
theorem cell_seeds (s s' : CanonGraph.Secrets) (hs : CanonGraph.seedsOf s = CanonGraph.seedsOf s')
    (node : CanonGraph.Node) (hnode : ∀ p, node ≠ .ftsLeaf p) (labels : CanonGraph.Labels) :
    CanonGraph.cell s node labels = CanonGraph.cell s' node labels := by
  cases node with
  | chain p => simp only [CanonGraph.cell, hs]
  | leaf L =>
      have he : CanonGraph.endLabel s labels L = CanonGraph.endLabel s' labels L := by
        funext i
        simp only [CanonGraph.endLabel, hs]
      simp only [CanonGraph.cell, he]
  | node n => rfl
  | ftsLeaf p => exact absurd rfl (hnode p)
  | ftsNode n => rfl
  | forest i => rfl

include hU in
theorem probeInput_mem (f : FtsCoord) (c : Digest) : probeInput f c ∈ U := by
  apply hU
  have h := CanonGraph.cell_mem (fun _ => c) (.ftsLeaf (toLeafPos f)) (fun _ => 0)
  rwa [cell_ftsLeaf] at h

/-- The table at a probe: the label on the honest secret, the residual row otherwise. -/
theorem answers_probe (fts : FtsCoord → Digest) (f : FtsCoord) (c : Digest) :
    Omega.answers hU ω fts (.inl (.inr (probeInput f c))) =
      if fts f = c then ω.labels (.ftsLeaf (toLeafPos f)) else
        SphincsSecurity.Concrete.finiteHashAnswer ∅ U ω.residual (probeInput f c) := by
  have hx := probeInput_mem hU f c
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U
      (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual) (probeInput f c) = _
  rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U _ _ hx rfl]
  split_ifs with he
  · have hcell : (⟨probeInput f c, hx⟩ : U) = CanonGraph.cellIn U hU (ω.secrets fts) (.ftsLeaf (toLeafPos f)) ω.labels := by
      apply Subtype.ext
      change probeInput f c = probeInput f (fts f)
      rw [he]
    rw [hcell, CanonGraph.programmed_at]
  · rw [CanonGraph.programmed_other, SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U _ _ hx rfl]
    intro node hnode
    have hpos : Extract.posOf (probeInput f c) = some (CanonGraph.Node.ftsLeaf (toLeafPos f)).toPos := by
      have := CanonGraph.posOf_cell (ω.secrets (fun _ => c)) (.ftsLeaf (toLeafPos f)) ω.labels
      rwa [cell_ftsLeaf] at this
    have hn := CanonGraph.cell_eq_of_posOf (ω.secrets fts) ω.labels hpos hnode
    subst hn
    rw [cell_ftsLeaf] at hnode
    exact he (probeInput_injective hnode).2.symm

/-- Non-probe public rows do not depend on the FTS secrets. -/
theorem answers_public (fts fts' : FtsCoord → Digest) (x : HashInput) (hx : decodeProbe x = none) :
    Omega.answers hU ω fts (.inl (.inr x)) = Omega.answers hU ω fts' (.inl (.inr x)) := by
  change SphincsSecurity.Concrete.finiteHashAnswer ∅ U
      (CanonGraph.programmed U hU (ω.secrets fts) ω.labels ω.residual) x =
    SphincsSecurity.Concrete.finiteHashAnswer ∅ U
      (CanonGraph.programmed U hU (ω.secrets fts') ω.labels ω.residual) x
  by_cases hxU : x ∈ U
  · rw [SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U _ _ hxU rfl,
      SphincsSecurity.Concrete.finiteHashAnswer_none ∅ U _ _ hxU rfl]
    have hnp : ∀ (s : CanonGraph.Secrets) p, x ≠ CanonGraph.cell s (.ftsLeaf p) ω.labels := by
      intro s p he
      rw [he, cell_ftsLeaf, decodeProbe_probeInput] at hx
      cases hx
    have hcells : ∀ node, CanonGraph.cell (ω.secrets fts) node ω.labels = x →
        CanonGraph.cell (ω.secrets fts') node ω.labels = x := by
      intro node hnode
      have hn : ∀ p, node ≠ .ftsLeaf p := by
        rintro p rfl
        exact hnp _ p hnode.symm
      rw [← cell_seeds (ω.secrets fts) (ω.secrets fts') rfl node hn]
      exact hnode
    by_cases hc : ∃ node, CanonGraph.cell (ω.secrets fts) node ω.labels = x
    · obtain ⟨node, hnode⟩ := hc
      have h1 : (⟨x, hxU⟩ : U) = CanonGraph.cellIn U hU (ω.secrets fts) node ω.labels := Subtype.ext hnode.symm
      have h2 : (⟨x, hxU⟩ : U) = CanonGraph.cellIn U hU (ω.secrets fts') node ω.labels :=
        Subtype.ext (hcells node hnode).symm
      rw [h1, CanonGraph.programmed_at, ← h1, h2, CanonGraph.programmed_at]
    · have hc' : ∀ node, x ≠ CanonGraph.cell (ω.secrets fts') node ω.labels := by
        intro node hnode
        apply hc
        refine ⟨node, ?_⟩
        have hn : ∀ p, node ≠ .ftsLeaf p := by
          rintro p rfl
          exact hnp _ p hnode
        rw [cell_seeds (ω.secrets fts) (ω.secrets fts') rfl node hn]
        exact hnode.symm
      rw [CanonGraph.programmed_other U hU _ _ _ _ (fun node h => hc ⟨node, h.symm⟩),
        CanonGraph.programmed_other U hU _ _ _ _ hc']
  · simp only [SphincsSecurity.Concrete.finiteHashAnswer, dif_neg hxU]

/-- Tables differing only in the FTS secrets agree on every FTS-free query. -/
theorem answers_free (fts fts' : FtsCoord → Digest) (q : T3.Spec.Domain) (hq : FtsFree q) :
    Omega.answers hU ω fts q = Omega.answers hU ω fts' q := by
  rcases q with (n | x) | c
  · rfl
  · exact answers_public hU ω fts fts' x hq
  · exact private_free ω fts fts' c hq

/-- FTS-free programs evaluate identically for all FTS secrets. -/
theorem eval_free (fts fts' : FtsCoord → Digest) {α : Type} {program : M α} (hp : AllQueriesSatisfy program FtsFree) :
    evalWithAnswerFn (Omega.answers hU ω fts) program = evalWithAnswerFn (Omega.answers hU ω fts') program :=
  eval_congr_allowed hp (answers_free hU ω fts fts')

end Table


/-! ## FTS trees: the levels do not depend on the secrets -/

theorem list_ext_getD {α : Type} {l l' : List α} (d : α) (hl : l.length = l'.length)
    (h : ∀ n, n < l.length → l.getD n d = l'.getD n d) : l = l' := by
  apply List.ext_getElem hl
  intro n h1 h2
  have := h n h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- Two level lists of the same shape with the same tree values are equal. -/
theorem levels_ext {levels levels' : List (List Digest)} (hs : Cost.LevelShape 11 11 levels)
    (hs' : Cost.LevelShape 11 11 levels')
    (h : ∀ level, level ≤ 11 → ∀ c, c < 2 ^ (11 - level) → treeValue levels level c = treeValue levels' level c) :
    levels = levels' := by
  apply list_ext_getD [] (by rw [hs.1, hs'.1])
  intro j hj
  have hj' : j ≤ 11 := by rw [hs.1] at hj; omega
  apply list_ext_getD 0 (by rw [hs.2 j hj', hs'.2 j hj'])
  intro c hc
  rw [hs.2 j hj'] at hc
  exact h j hj' c hc

section Levels
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildLevels Correctness.ftsRows

theorem buildFts_levels_value (fts fts' : FtsCoord → Digest) (index coord : Nat) (hindex : index < 2 ^ 31)
    (hcoord : coord < 7) (level c : Nat) (hlevel : level ≤ 11) (hc : c < 2 ^ (11 - level)) :
    treeValue (evalWithAnswerFn (Omega.answers hU ω fts) (buildFts index coord)).1 level c =
      treeValue (evalWithAnswerFn (Omega.answers hU ω fts') (buildFts index coord)).1 level c := by
  obtain ⟨-, -, hleaves, hnodes⟩ := Correctness.eval_buildFts_correct (Omega.answers hU ω fts) index coord
  obtain ⟨-, -, hleaves', hnodes'⟩ := Correctness.eval_buildFts_correct (Omega.answers hU ω fts') index coord
  have hsec : ∀ leaf (hleaf : leaf < 2048) (g : FtsCoord → Digest),
      (evalWithAnswerFn (Omega.answers hU ω g) (buildFts index coord)).2.getD leaf 0 =
        g (⟨index, hindex⟩, ⟨coord, hcoord⟩, ⟨leaf, hleaf⟩) := by
    intro leaf hleaf g
    rw [buildFts_secret _ _ _ _ hleaf]
    exact secretNat_answers hU ω g (⟨index, hindex⟩, ⟨coord, hcoord⟩, ⟨leaf, hleaf⟩)
  have hsec1 := fun leaf hleaf => hsec leaf hleaf fts
  have hsec2 := fun leaf hleaf => hsec leaf hleaf fts'
  generalize evalWithAnswerFn (Omega.answers hU ω fts) (buildFts index coord) = X at hleaves hnodes hsec1 ⊢
  generalize evalWithAnswerFn (Omega.answers hU ω fts') (buildFts index coord) = Y at hleaves' hnodes' hsec2 ⊢
  revert c
  induction level with
  | zero =>
      intro c hc
      have hc' : c < 2048 := by simpa using hc
      rw [hleaves c hc', hleaves' c hc', hsec1 c hc', hsec2 c hc', ftsLeaf_eq_shortHash, ftsLeaf_eq_shortHash]
      change ((Omega.answers hU ω fts) (.inl (.inr (probeInput (⟨index, hindex⟩, ⟨coord, hcoord⟩, ⟨c, hc'⟩) _)))).extractLsb' 0 128 =
        ((Omega.answers hU ω fts') (.inl (.inr (probeInput (⟨index, hindex⟩, ⟨coord, hcoord⟩, ⟨c, hc'⟩) _)))).extractLsb' 0 128
      rw [answers_probe, answers_probe, if_pos rfl, if_pos rfl]
  | succ level ih =>
      intro c hc
      have hlt : level < 11 := by omega
      have hsub : 11 - (level + 1) = 11 - level - 1 := by omega
      have hpow : 2 ^ (11 - level) = 2 * 2 ^ (11 - level - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hc1 : c < 2 ^ (11 - level - 1) := by rw [← hsub]; exact hc
      rw [hnodes level hlt c hc, hnodes' level hlt c hc, ih (by omega) (2 * c) (by omega),
        ih (by omega) (2 * c + 1) (by omega)]
      exact eval_free hU ω fts fts' (nodeHash_free _ _ _ _ _ (by decide))

/-- **The FTS levels are the same lists for all FTS secrets.** -/
theorem buildFts_levels_eq (fts fts' : FtsCoord → Digest) (index coord : Nat) (hindex : index < 2 ^ 31)
    (hcoord : coord < 7) :
    (evalWithAnswerFn (Omega.answers hU ω fts) (buildFts index coord)).1 =
      (evalWithAnswerFn (Omega.answers hU ω fts') (buildFts index coord)).1 :=
  levels_ext (Correctness.eval_buildFts_correct _ index coord).1 (Correctness.eval_buildFts_correct _ index coord).1
    (fun level hlevel c hc => buildFts_levels_value hU ω fts fts' index coord hindex hcoord level c hlevel hc)

end Levels


/-! ## The signer -/

theorem selection_bounds (output : HashOutput) (c : Nat) (hc : c < 7) :
    ((selections output).getD c ⟨0, []⟩).bucket < 8 ∧
      ∀ leaf ∈ ((selections output).getD c ⟨0, []⟩).leaves, leaf < 256 := by
  simp only [selections, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some]
  refine ⟨Nat.mod_lt _ (by decide), ?_⟩
  intro leaf hleaf
  rw [List.mem_mergeSort] at hleaf
  simp only [List.mem_map, List.mem_range] at hleaf
  obtain ⟨j, -, rfl⟩ := hleaf
  exact Nat.mod_lt _ (by decide)

/-- The opened secrets under `fts` at a digest output, in the signer's order. -/
def openedValues (fts : FtsCoord → Digest) (output : HashOutput) : List Digest := (openedPositions output).map fts

section Sign
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)

theorem forestOpened_answers (fts : FtsCoord → Digest) (output : HashOutput) (c : Fin 7) :
    Correctness.forestOpened (Omega.answers hU ω fts) (output.toNat % 2 ^ 31) c.val
        ((selections output).getD c.val ⟨0, []⟩) =
      (((selections output).getD c.val ⟨0, []⟩).leaves.map fun leaf =>
        (outputIndex output, c, leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf)).map fts := by
  obtain ⟨hb, hl⟩ := selection_bounds output c.val c.isLt
  have hsec : ∀ s (hs : s < 2048),
      (evalWithAnswerFn (Omega.answers hU ω fts) (buildFts (output.toNat % 2 ^ 31) c.val)).2.getD s 0 =
        fts (outputIndex output, c, ⟨s, hs⟩) := by
    intro s hs
    rw [buildFts_secret _ _ _ _ hs]
    exact secretNat_answers hU ω fts (outputIndex output, c, ⟨s, hs⟩)
  unfold Correctness.forestOpened
  generalize evalWithAnswerFn (Omega.answers hU ω fts) (buildFts (output.toNat % 2 ^ 31) c.val) = X at hsec ⊢
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro leaf hleaf
  have hlt : ((selections output).getD c.val ⟨0, []⟩).bucket * 256 + leaf < 2048 := by
    have := hl leaf hleaf; omega
  rw [Function.comp_apply, Function.comp_apply, hsec _ hlt]
  have hidx : (⟨_, hlt⟩ : Fin 2048) = leafIndex ((selections output).getD c.val ⟨0, []⟩).bucket leaf := by
    apply Fin.ext
    simp only [leafIndex]
    exact (Nat.mod_eq_of_lt hlt).symm
  rw [hidx]

theorem forestOpenPrefix_answers (fts : FtsCoord → Digest) (output : HashOutput) :
    Correctness.forestOpenPrefix (Omega.answers hU ω fts) (output.toNat % 2 ^ 31) (selections output) 7 =
      openedValues fts output := by
  unfold Correctness.forestOpenPrefix openedValues openedPositions
  rw [List.map_flatMap, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro c _
  exact forestOpened_answers hU ω fts output c

theorem forestInner_answers (fts fts' : FtsCoord → Digest) (index coord : Nat) (hindex : index < 2 ^ 31)
    (hcoord : coord < 7) (sel : Selection) :
    Correctness.forestInner (Omega.answers hU ω fts) index coord sel =
      Correctness.forestInner (Omega.answers hU ω fts') index coord sel := by
  unfold Correctness.forestInner
  rw [buildFts_levels_eq hU ω fts fts' index coord hindex hcoord]

theorem forestOuter_answers (fts fts' : FtsCoord → Digest) (index coord : Nat) (hindex : index < 2 ^ 31)
    (hcoord : coord < 7) (sel : Selection) :
    Correctness.forestOuter (Omega.answers hU ω fts) index coord sel =
      Correctness.forestOuter (Omega.answers hU ω fts') index coord sel := by
  unfold Correctness.forestOuter
  rw [buildFts_levels_eq hU ω fts fts' index coord hindex hcoord]

theorem forestProofPrefix_answers (fts fts' : FtsCoord → Digest) (index : Nat) (hindex : index < 2 ^ 31)
    (chosen : List Selection) :
    Correctness.forestProofPrefix (Omega.answers hU ω fts) index chosen 7 =
      Correctness.forestProofPrefix (Omega.answers hU ω fts') index chosen 7 := by
  unfold Correctness.forestProofPrefix
  apply List.flatMap_congr
  intro coord hcoord
  have hc : coord < 7 := List.mem_range.mp hcoord
  rw [forestInner_answers hU ω fts fts' index coord hindex hc, forestOuter_answers hU ω fts fts' index coord hindex hc]

theorem forestRoots_answers (fts fts' : FtsCoord → Digest) (index : Nat) (hindex : index < 2 ^ 31) :
    Correctness.forestRoots (Omega.answers hU ω fts) index 7 = Correctness.forestRoots (Omega.answers hU ω fts') index 7 := by
  unfold Correctness.forestRoots
  apply List.map_congr_left
  intro coord hcoord
  have hc : coord < 7 := List.mem_range.mp hcoord
  rw [buildFts_levels_eq hU ω fts fts' index coord hindex hc]

/-- The FTS part of the signer under `fts`: the opened secrets are `openedValues fts`, the rest is common. -/
theorem signForest_answers (fts : FtsCoord → Digest) (output : HashOutput) :
    evalWithAnswerFn (Omega.answers hU ω fts) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output)) =
      (openedValues fts output,
        (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
          (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))).2.1,
        (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
          (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))).2.2) := by
  have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  rw [Correctness.eval_signForest, Correctness.eval_signForest, forestOpenPrefix_answers,
    forestProofPrefix_answers hU ω fts (fun _ => 0) _ hindex, forestRoots_answers hU ω fts (fun _ => 0) _ hindex]


theorem signForest_roots (fts : FtsCoord → Digest) (output : HashOutput) :
    (evalWithAnswerFn (Omega.answers hU ω fts) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))).2.2 =
      (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
        (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))).2.2 := by
  have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  rw [Correctness.eval_signForest, Correctness.eval_signForest]
  exact forestRoots_answers hU ω fts (fun _ => 0) _ hindex

end Sign


/-! ## The signer's output as a function of the opened secrets -/

section Signer
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : Omega U)
noncomputable local instance instDecidableEqCache_pairGuessSigner : DecidableEq T3.Cache := Classical.decEq _

/-- The signer's nonce (common to all FTS secrets). -/
noncomputable def signerRho (request : Request) : Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (privateNonce request.message)

/-- The signer's digest search (common). -/
noncomputable def signerFound (request : Request) : Option (BitVec 32 × HashOutput) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
    (digestSearch (signerRho hU ω request) request.message 0 attemptLimit)

/-- The common FTS part (proof nodes, roots) of the signer at a digest output. -/
noncomputable def signerForest (output : HashOutput) : List Digest × List Digest × List Digest :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))

/-- The signer's layers (common). -/
noncomputable def signerLayers (request : Request) (output : HashOutput) : Option (List Pieces) :=
  evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (signLayers request.cache (output.toNat % 2 ^ 31) 4
    (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
      (forestPk (output.toNat % 2 ^ 31) (signerForest hU ω output).2.2)))

/-- The signer's output when the opened secrets at digest output `output` are `opener output`. -/
noncomputable def signWith (published : T3.Cache) (request : Request) (opener : HashOutput → List Digest) :
    Option Signature :=
  if request.cache = published then
    match signerFound hU ω request with
    | some (_, output) =>
        match signerLayers hU ω request output with
        | some pieces => some (Correctness.assembledSignature (signerRho hU ω request)
            (opener output, (signerForest hU ω output).2.1, (signerForest hU ω output).2.2) pieces)
        | none => none
    | none => none
  else none

/-- **The authenticated signer under FTS secrets `fts`.** -/
theorem sign_answers (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) =
      signWith hU ω published request (openedValues fts) := by
  unfold FullGame.authenticatedSign signWith
  simp only [evalWithAnswerFn_bind]
  split_ifs with hc
  · rw [Correctness.signPayload_eq]
    simp only [evalWithAnswerFn_bind]
    rw [eval_free hU ω fts (fun _ => 0) (privateNonce_free _)]
    rw [eval_free hU ω fts (fun _ => 0) (digestSearch_free _ _ _ _)]
    change _ = match signerFound hU ω request with
      | some (_, output) =>
          match signerLayers hU ω request output with
          | some pieces => some (Correctness.assembledSignature (signerRho hU ω request)
              (openedValues fts output, (signerForest hU ω output).2.1, (signerForest hU ω output).2.2) pieces)
          | none => none
      | none => none
    unfold signerFound signerRho
    cases evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
        (digestSearch (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (privateNonce request.message))
          request.message 0 attemptLimit) with
    | none => rfl
    | some found =>
        obtain ⟨counter, output⟩ := found
        simp only [evalWithAnswerFn_bind]
        rw [signForest_roots hU ω fts output]
        rw [eval_free hU ω fts (fun _ => 0) (forestPk_free _ _)]
        rw [eval_free hU ω fts (fun _ => 0) (signLayers_free _ _ _ _)]
        rw [signForest_answers hU ω fts output]
        unfold signerLayers signerForest
        cases evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (signLayers request.cache (output.toNat % 2 ^ 31) 4
            (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) (forestPk (output.toNat % 2 ^ 31)
              (evalWithAnswerFn (Omega.answers hU ω (fun _ => 0))
                (Correctness.signForest (output.toNat % 2 ^ 31) (selections output))).2.2))) with
        | none => rfl
        | some pieces => rfl
  · rfl


/-- The positions the signer opens (common to all FTS secrets). -/
noncomputable def signerOpened (published : T3.Cache) (request : Request) : List FtsCoord :=
  if request.cache = published then
    match signerFound hU ω request with
    | some (_, output) =>
        match signerLayers hU ω request output with
        | some _ => openedPositions output
        | none => []
    | none => []
  else []

theorem signedOutput_free (fts : FtsCoord → Digest) (message : Message) (signature : Signature) :
    signedOutput (Omega.answers hU ω fts) message signature =
      signedOutput (Omega.answers hU ω (fun _ => 0)) message signature := by
  unfold signedOutput
  rw [eval_free hU ω fts (fun _ => 0) (digestSearch_free _ _ _ _)]

theorem openedFor_eq (published : T3.Cache) (request : Request) :
    openedFor hU ω published request = signerOpened hU ω published request := by
  unfold openedFor signerOpened
  rw [sign_answers hU ω (fun _ => 0) published request]
  unfold signWith
  split_ifs with hc
  · cases hf : signerFound hU ω request with
    | none => rfl
    | some found =>
        obtain ⟨counter, output⟩ := found
        dsimp only
        cases hl : signerLayers hU ω request output with
        | none => rfl
        | some pieces =>
            dsimp only
            have ho : signedOutput (Omega.answers hU ω (fun _ => 0)) request.message
                (Correctness.assembledSignature (signerRho hU ω request)
                  (openedValues (fun _ => 0) output, (signerForest hU ω output).2.1, (signerForest hU ω output).2.2)
                  pieces) = some output := by
              unfold signedOutput
              rw [Correctness.assembledSignature_rho]
              change (signerFound hU ω request).map Prod.snd = some output
              rw [hf]
              rfl
            rw [ho]
  · rfl

/-- **Locality**: the signature depends on the FTS secrets only at the opened positions. -/
theorem sign_local (fts fts' : FtsCoord → Digest) (published : T3.Cache) (request : Request)
    (h : ∀ f ∈ openedFor hU ω published request, fts f = fts' f) :
    evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (Omega.answers hU ω fts') (FullGame.authenticatedSign published request) := by
  rw [openedFor_eq] at h
  rw [sign_answers, sign_answers]
  unfold signWith
  unfold signerOpened at h
  split_ifs with hc
  · rw [if_pos hc] at h
    cases hf : signerFound hU ω request with
    | none => rfl
    | some found =>
        obtain ⟨counter, output⟩ := found
        rw [hf] at h
        dsimp only at h ⊢
        cases hl : signerLayers hU ω request output with
        | none => rfl
        | some pieces =>
            rw [hl] at h
            dsimp only at h ⊢
            have hv : openedValues fts output = openedValues fts' output := List.map_congr_left h
            simp only [hv]
  · rfl

/-- A disclosed position of the world signer is opened by the returned signature, under every FTS secrets. -/
theorem sign_opened (fts : FtsCoord → Digest) (published : T3.Cache) (request : Request) (f : FtsCoord)
    (hf : f ∈ openedFor hU ω published request) :
    ∃ signature output,
      evalWithAnswerFn (Omega.answers hU ω fts) (FullGame.authenticatedSign published request) = some signature ∧
        signedOutput (Omega.answers hU ω fts) request.message signature = some output ∧
        f ∈ openedPositions output := by
  rw [openedFor_eq] at hf
  unfold signerOpened at hf
  rw [sign_answers]
  unfold signWith
  split_ifs at hf ⊢ with hc
  · cases hfd : signerFound hU ω request with
    | none => rw [hfd] at hf; cases hf
    | some found =>
        obtain ⟨counter, output⟩ := found
        rw [hfd] at hf
        dsimp only at hf ⊢
        cases hl : signerLayers hU ω request output with
        | none => rw [hl] at hf; cases hf
        | some pieces =>
            rw [hl] at hf
            refine ⟨_, output, rfl, ?_, hf⟩
            rw [signedOutput_free]
            unfold signedOutput
            rw [Correctness.assembledSignature_rho]
            change (signerFound hU ω request).map Prod.snd = some output
            rw [hfd]
            rfl
  · cases hf

end Signer

end SigGolfCandidate.T3.Security.BPair
