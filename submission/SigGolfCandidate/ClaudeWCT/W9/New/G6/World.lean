import SigGolfCandidate.ClaudeWCT.W9.New.CanonTable.ChainTable
import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeGame
import SigGolfCandidate.ClaudeWCT.WCT9.Forest
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCFull
import SigGolfCandidate.ClaudeWCT.GuessV2.WorldHash
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSplit
import SigGolfCandidate.T3.Secc.WotsEvents
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def IsSeedPair (c : Coordinate) : Prop :=
  ∃ a : Guess.ChainAddr, c = .inl (header 8 a.2.1.val a.1.val 0 (4 * a.2.2.1.val + a.2.2.2.val / 2))
def WFree : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr x) => Guess.decodeProbe x = none
  | .inr c => ¬IsSeedPair c
theorem not_isSeedPair_header {t l tr p ix : Nat} (ht : t % 256 ≠ 8) : ¬IsSeedPair (.inl (header t l tr p ix)) := by
  rintro ⟨a, ha⟩
  exact SigGolfCandidate.T3.QuerySpace.header_ne_of_tag (by omega) (Sum.inl.inj ha)
theorem hdrBlock_pad64_prefix (a : Digest) (h : BitVec 128) (rest : HashInput) :
    Guess.hdrBlock (pad64 (bytesLE 16 a ++ bytesLE 16 h ++ rest)) = bytesLE 16 h := by
  unfold Guess.hdrBlock pad64
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length _ _), List.take_left' (bytesLE_length _ _)]
theorem decodeProbe_prefix (a : Digest) {h : BitVec 128} (rest : HashInput) (ht : Guess.tagByte h ≠ 5) :
    Guess.decodeProbe (pad64 (bytesLE 16 a ++ bytesLE 16 h ++ rest)) = none :=
  Guess.decodeProbe_of_hdrBlock (hdrBlock_pad64_prefix a h rest) ht
theorem tagByte_header_ne {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 5) : Guess.tagByte (header t l tr p ix) ≠ 5 := by
  rw [Guess.tagByte_header]; exact ht
theorem tagByte_wctHeader_ne {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 5) :
    Guess.tagByte (WCT9.wctHeader t l tr p ix) ≠ 5 := by
  rw [Guess.tagByte_wctHeader]; exact ht
theorem eval_query' (A : Answers) (input : SigGolfCandidate.T3.Spec.Domain) :
    evalWithAnswerFn A (liftM (SigGolfCandidate.T3.Spec.query input)) = A input :=
  simulateQ_spec_query A input
theorem eval_congr_allowed {P : SigGolfCandidate.T3.Spec.Domain → Prop} {α : Type} {program : M α}
    (hp : AllQueriesSatisfy program P) {A A' : Answers} (h : ∀ q, P q → A q = A' q) :
    evalWithAnswerFn A program = evalWithAnswerFn A' program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, eval_query', eval_query', h input hi]
      exact ih _ (hn _)
section Free
open SourceQueries
theorem zero16_eq : zero16 = bytesLE 16 (0 : Digest) := by decide
theorem shortHash_free (a : Digest) {h : BitVec 128} (rest : HashInput) (ht : Guess.tagByte h ≠ 5) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 h ++ rest)) WFree := by
  unfold shortHash publicHash
  exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix a rest ht))
    fun _ => pure_allowed _ _
theorem shortHash_header_free (a : Digest) {t : Nat} (l tr p ix : Nat) (rest : HashInput) (ht : t % 256 ≠ 5) :
    AllQueriesSatisfy (shortHash (bytesLE 16 a ++ bytesLE 16 (header t l tr p ix) ++ rest)) WFree :=
  shortHash_free a rest (tagByte_header_ne l tr p ix ht)
theorem privatePair_free {t : Nat} (l tr p ix : Nat) (ht : t % 256 ≠ 8) :
    AllQueriesSatisfy (privatePair t l tr p ix) WFree := by
  unfold privatePair privateHash
  exact bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr (not_isSeedPair_header ht))
    fun _ => pure_allowed _ _
theorem privateNonce_free (message : Message) : AllQueriesSatisfy (privateNonce message) WFree := by
  unfold privateNonce privateHash
  refine bind_allowed WFree ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun _ => pure_allowed _ _
  rintro ⟨a, ha⟩
  cases ha
theorem privateMac_free (region : Region) : AllQueriesSatisfy (privateMac region) WFree := by
  have hquery (i : Nat) : AllQueriesSatisfy (privateHash (.inl (header 14 0 0 0 i))) WFree := by
    exact (allQueriesSatisfy_query_iff _ _).mpr (not_isSeedPair_header (by decide : 14 % 256 ≠ 8))
  unfold privateMac privateMacKey
  apply bind_allowed WFree
  · exact bind_allowed WFree (hquery 0) (fun _ => bind_allowed WFree (hquery 1) (fun _ => pure_allowed _ _))
  · intro key; exact pure_allowed _ _
theorem chainStep_free (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    AllQueriesSatisfy (shortHash (chainInput lay tree leaf i step value)) WFree := by
  unfold shortHash publicHash
  apply bind_allowed WFree
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    change Guess.decodeProbe (pad64 (chainInput lay tree leaf i step value)) = none
    rw [Guess.decodeProbe_eq_none, chainInput_padded]
    intro a p c he
    have hh := congrArg Guess.hdrBlock he
    rw [Guess.probeInput, Guess.hdrBlock_wctChainInput] at hh
    change ((chainInput lay tree leaf i step value).drop 16).take 16 = _ at hh
    rw [chainInput_header] at hh
    have hn := congrArg BitVec.toNat (bytesLE_injective hh)
    have hc := chainHeader_firstByte lay tree leaf i step
    rw [hn, Guess.wctHeader_toNat'] at hc
    omega
  · intro _; exact pure_allowed _ _
theorem chain_free (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) WFree := by
  unfold chain
  exact foldlM_allowed WFree _ _ (fun v step => chainStep_free lay tree leaf i step v) value
theorem leafHash_free (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) WFree := by
  unfold leafHash
  exact shortHash_header_free _ _ _ _ _ _ (by decide)
theorem nodeHash_free {tag : Nat} (lay tree heap : Nat) (left right : Digest) (ht : tag % 256 ≠ 5) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) WFree := by
  unfold nodeHash
  exact shortHash_header_free _ _ _ _ _ _ ht
theorem mask_free (level index : Nat) : AllQueriesSatisfy (mask level index) WFree := by
  unfold mask pairedMask
  exact bind_allowed WFree (privatePair_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem buildLeaf_free (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) WFree := by
  unfold buildLeaf
  apply bind_allowed WFree
  · apply foldlM_allowed WFree
    intro state pair
    apply bind_allowed WFree (privatePair_free _ _ _ _ (by decide))
    intro seeds
    apply foldlM_allowed WFree
    intro state half
    dsimp only
    split
    · exact pure_allowed _ _
    · apply bind_allowed WFree (chain_free _ _ _ _ _ _ _)
      intro value
      split
      · exact pure_allowed _ _
      · exact bind_allowed WFree (chain_free _ _ _ _ _ _ _) fun _ => pure_allowed _ _
  · intro state
    split
    · exact pure_allowed _ _
    · exact bind_allowed WFree (leafHash_free _ _ _ _) fun _ => pure_allowed _ _
theorem buildLevel_free {tag : Nat} (lay tree h level : Nat) (nodes : List Digest) (ht : tag % 256 ≠ 5) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) WFree := by
  unfold buildLevel
  exact mapM_allowed WFree _ _ fun _ => nodeHash_free _ _ _ _ _ ht
theorem buildLevels_free {tag : Nat} (lay tree h : Nat) (leaves : List Digest) (ht : tag % 256 ≠ 5) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) WFree := by
  unfold buildLevels
  exact foldlM_allowed WFree _ _ (fun levels level =>
    bind_allowed WFree (buildLevel_free _ _ _ _ _ ht) fun _ => pure_allowed _ _) _
theorem buildTree_free (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) WFree := by
  unfold buildTree
  apply bind_allowed WFree
  · exact foldlM_allowed WFree _ _ (fun state leaf =>
      bind_allowed WFree (buildLeaf_free _ _ _ _ _) fun _ => pure_allowed _ _) _
  · intro state
    exact bind_allowed WFree (buildLevels_free _ _ _ _ (by decide)) fun _ => pure_allowed _ _
theorem maskedLevel_free (nodes : List Digest) (level : Nat) :
    AllQueriesSatisfy (maskedLevel nodes level) WFree := by
  unfold maskedLevel pairedMask
  apply bind_allowed WFree
  · exact mapM_allowed WFree _ _ (fun pair => bind_allowed WFree (privatePair_free _ _ _ _ (by decide))
      (fun _ => pure_allowed _ _))
  · intro _; exact pure_allowed _ _
theorem keygenPayload_free : AllQueriesSatisfy keygenPayload WFree := by
  unfold keygenPayload
  apply bind_allowed WFree (buildTree_free _ _ _ _)
  intro built
  apply bind_allowed WFree
  · exact mapM_allowed WFree _ _ (fun level => maskedLevel_free _ _)
  · intro _
    exact pure_allowed _ _
theorem keygen_free : AllQueriesSatisfy keygen WFree := by
  unfold keygen
  apply bind_allowed WFree keygenPayload_free
  intro generated
  exact bind_allowed WFree (privateMac_free _) fun _ => pure_allowed _ _
theorem counterSearch_free (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold counterSearch
      apply bind_allowed WFree
      · unfold encodingInput
        exact shortHash_header_free _ _ _ _ _ _ (by decide)
      · intro answer
        split
        · exact ih _
        · exact pure_allowed _ _
theorem digest_free (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) WFree := by
  unfold digest publicHash digestInput
  exact (allQueriesSatisfy_query_iff _ _).mpr (decodeProbe_prefix _ _ (tagByte_header_ne _ _ _ _ (by decide)))
theorem wctDigestSearch_free (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) WFree := by
  induction fuel generalizing counter with
  | zero => exact pure_allowed _ _
  | succ fuel ih =>
      unfold WCT9.digestSearch
      apply bind_allowed WFree (digest_free _ _ _)
      intro output
      split
      · exact pure_allowed _ _
      · exact ih _
theorem topPath_free (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) WFree := by
  unfold topPath
  exact mapM_allowed WFree _ _ fun level =>
    bind_allowed WFree (mask_free _ _) fun _ => pure_allowed _ _
theorem signTop_free (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) WFree := by
  unfold signTop
  exact bind_allowed WFree (buildLeaf_free _ _ _ _ _) fun _ =>
    bind_allowed WFree (topPath_free _ _) fun _ => pure_allowed _ _
theorem signLayers_free (cache : SigGolfCandidate.T3.Cache) (index n : Nat) (message : Digest × BitVec 96 × Digest) :
    AllQueriesSatisfy (signLayers cache index n message) WFree := by
  induction n generalizing message with
  | zero => exact pure_allowed _ _
  | succ n ih =>
      unfold signLayers
      apply bind_allowed WFree (counterSearch_free _ _ _ _ _ _)
      intro found
      split
      · split
        · exact bind_allowed WFree (signTop_free _ _ _) fun _ => pure_allowed _ _
        · apply bind_allowed WFree (buildTree_free _ _ _ _)
          intro built
          obtain ⟨levels, values⟩ := built
          dsimp only
          apply bind_allowed WFree (ih _)
          intro previous
          split
          · exact pure_allowed _ _
          · exact pure_allowed _ _
      · exact pure_allowed _ _
theorem wctLeafHash_free (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) WFree := by
  unfold WCT9.leafHash
  exact shortHash_free _ _ (tagByte_wctHeader_ne _ _ _ _ (by decide))
theorem wctForestPk_free (index : Nat) (roots : List Digest) : AllQueriesSatisfy (WCT9.forestPk index roots) WFree := by
  unfold WCT9.forestPk
  exact shortHash_header_free _ _ _ _ _ _ (by decide)
theorem heapBuild_free (index coord : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord leaves) WFree := by
  unfold WCT9.heapBuild
  exact foldlM_allowed WFree _ _ (fun nodes heap =>
    bind_allowed WFree (nodeHash_free _ _ _ _ _ (by decide)) fun _ => pure_allowed _ _) _
end Free
section Table
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
open ClaudeWCT.W9.T3.Security.CanonGraph
theorem splitEquiv_symm_secret (s : Secrets) (o : OtherHalves) (i : SecretIndex) :
    splitEquiv.symm (s, o) (secretCoordinate i) = s i := by
  have h := splitEquiv_fst (splitEquiv.symm (s, o))
  rw [Equiv.apply_symm_apply] at h
  exact (congrFun h i).symm
theorem splitEquiv_snd (t : ChainGraph.HalfTable) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range secretCoordinate) : (splitEquiv t).2 ⟨h, hh⟩ = t h := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.Set.sumCompl]
  rfl
theorem splitEquiv_symm_other (s : Secrets) (o : OtherHalves) (h : ChainGraph.HalfCoordinate)
    (hh : h ∉ Set.range secretCoordinate) : splitEquiv.symm (s, o) h = o ⟨h, hh⟩ := by
  have e := splitEquiv_snd (splitEquiv.symm (s, o)) h hh
  rw [Equiv.apply_symm_apply] at e
  exact e.symm
theorem privateEquiv_symm_apply (s : Secrets) (o : OtherHalves) (c : Coordinate) :
    privateEquiv.symm (s, o) c =
      ChainGraph.joinOutput (splitEquiv.symm (s, o) (c, 0)) (splitEquiv.symm (s, o) (c, 1)) :=
  rfl
theorem private_free (g g' : WctPoint → Digest) (c : Coordinate) (hc : ¬IsSeedPair c) :
    privateEquiv.symm (CanonTable.worldSecrets ω.secrets g, ω.other) c =
      privateEquiv.symm (CanonTable.worldSecrets ω.secrets g', ω.other) c := by
  have hhalf : ∀ h : Fin 2, splitEquiv.symm (CanonTable.worldSecrets ω.secrets g, ω.other) (c, h) =
      splitEquiv.symm (CanonTable.worldSecrets ω.secrets g', ω.other) (c, h) := by
    intro h
    by_cases hr : (c, h) ∈ Set.range secretCoordinate
    · obtain ⟨i, hi⟩ := hr
      rw [← hi, splitEquiv_symm_secret, splitEquiv_symm_secret]
      cases i with
      | inl a => rw [CanonTable.worldSecrets_inl, CanonTable.worldSecrets_inl]
      | inr a =>
          exfalso
          apply hc
          exact ⟨a, (congrArg Prod.fst hi).symm⟩
    · rw [splitEquiv_symm_other _ _ _ hr, splitEquiv_symm_other _ _ _ hr]
  rw [privateEquiv_symm_apply, privateEquiv_symm_apply, hhalf 0, hhalf 1]
theorem answers_free (g g' : WctPoint → Digest) (q : SigGolfCandidate.T3.Spec.Domain) (hq : WFree q) :
    CanonTable.worldAnswers hU ω g q = CanonTable.worldAnswers hU ω g' q := by
  rcases q with (n | x) | c
  · rfl
  · exact (CanonTable.chainTable hU ω).answers_public g g' x hq
  · exact private_free ω g g' c hq
theorem eval_free (g g' : WctPoint → Digest) {α : Type} {program : M α} (hp : AllQueriesSatisfy program WFree) :
    evalWithAnswerFn (CanonTable.worldAnswers hU ω g) program =
      evalWithAnswerFn (CanonTable.worldAnswers hU ω g') program :=
  eval_congr_allowed hp (answers_free hU ω g g')
end Table
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def outIndex (output : HashOutput) : Nat := output.toNat % 2 ^ 31
def revealedCoords (output : HashOutput) : List Guess.GCoord :=
  (List.finRange 9).flatMap fun k => (List.finRange 7).filterMap fun t =>
    if h : 1 ≤ Guess.deficit output k t then
      some (Guess.chainOf output k t, ⟨3 - Guess.deficit output k t, by omega⟩)
    else none
theorem mem_revealedCoords {output : HashOutput} {c : Guess.GCoord} :
    c ∈ revealedCoords output ↔ ∃ (k : Fin 9) (t : Fin 7), 1 ≤ Guess.deficit output k t ∧
      c.1 = Guess.chainOf output k t ∧ c.2.val = 3 - Guess.deficit output k t := by
  unfold revealedCoords
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨k, t, ht⟩
    split_ifs at ht with h
    · cases ht
      exact ⟨k, t, h, rfl, rfl⟩
  · rintro ⟨k, t, h, h1, h2⟩
    refine ⟨k, t, ?_⟩
    rw [dif_pos h]
    obtain ⟨a, ⟨p, hp⟩⟩ := c
    simp only at h1 h2
    subst h1 h2
    rfl
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable local instance instDecidableEqCache_g6Signer : DecidableEq SigGolfCandidate.T3.Cache := Classical.decEq _
noncomputable abbrev wA (g : WctPoint → Digest) : Answers := CanonTable.worldAnswers hU ω g
def addrOf (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128) (t : Fin 7) : Guess.ChainAddr :=
  (⟨index, hindex⟩, k, j, t)
theorem wctChainValue_eq (A : Answers) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128)
    (word : WCT9.Rank) (t : Fin 7) :
    WCT9.chainValue A index k.val j.val word t = Guess.chainValue A (addrOf index hindex k j t) (3 - WCT9.digit word t) :=
  rfl
theorem chainEnd_eq (A : Answers) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) (j : Fin 128) (t : Fin 7) :
    WCT9.chainEnd A index k.val j.val t = Guess.chainValue A (addrOf index hindex k j t) 3 :=
  rfl
theorem chainValue_world (g : WctPoint → Digest) (a : Guess.ChainAddr) (p : Nat) (hp : p ≤ 3) :
    Guess.chainValue (wA hU ω g) a p = (CanonTable.chainTable hU ω).walkVal g a p :=
  (CanonTable.chainTable hU ω).chainValue_answers g a p hp
theorem walkVal_three (g g' : WctPoint → Digest) (a : Guess.ChainAddr) :
    (CanonTable.chainTable hU ω).walkVal g a 3 = (CanonTable.chainTable hU ω).walkVal g' a 3 := by
  simp [Guess.ChainTable.walkVal]
theorem chainEnd_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (j : Fin 128) (t : Fin 7) :
    WCT9.chainEnd (wA hU ω g) index k.val j.val t = WCT9.chainEnd (wA hU ω g') index k.val j.val t := by
  rw [chainEnd_eq _ index hindex, chainEnd_eq _ index hindex, chainValue_world hU ω g _ 3 le_rfl,
    chainValue_world hU ω g' _ 3 le_rfl, walkVal_three]
theorem childRoot_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9)
    (j : Nat) (hj : j < 128) :
    WCT9.childRoot (wA hU ω g) index k.val j = WCT9.childRoot (wA hU ω g') index k.val j := by
  unfold WCT9.childRoot
  have he : (fun t : Fin 7 => WCT9.chainEnd (wA hU ω g) index k.val j t) =
      (fun t : Fin 7 => WCT9.chainEnd (wA hU ω g') index k.val j t) := by
    funext t
    exact chainEnd_world hU ω g g' index hindex k ⟨j, hj⟩ t
  rw [he]
  exact eval_free hU ω g g' (wctLeafHash_free _ _ _ _)
theorem coordLeaves_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) :
    WCT9.coordLeaves (wA hU ω g) index k = WCT9.coordLeaves (wA hU ω g') index k := by
  unfold WCT9.coordLeaves
  exact congrArg List.ofFn (funext fun j : Fin 128 => childRoot_world hU ω g g' index hindex k j.val j.isLt)
theorem coordNodes_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) (k : Fin 9) :
    WCT9.coordNodes (wA hU ω g) index k = WCT9.coordNodes (wA hU ω g') index k := by
  unfold WCT9.coordNodes
  rw [coordLeaves_world hU ω g g' index hindex k]
  exact eval_free hU ω g g' (heapBuild_free _ _ _)
theorem coordinateRoot_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.coordinateRoot (wA hU ω g) index = WCT9.coordinateRoot (wA hU ω g') index := by
  funext k
  unfold WCT9.coordinateRoot
  rw [coordNodes_world hU ω g g' index hindex k]
theorem honestForest_world (g g' : WctPoint → Digest) (index : Nat) (hindex : index < 2 ^ 31) :
    WCT9.honestForest (wA hU ω g) index = WCT9.honestForest (wA hU ω g') index := by
  unfold WCT9.honestForest
  rw [coordinateRoot_world hU ω g g' index hindex]
  exact eval_free hU ω g g' (wctForestPk_free _ _)
theorem outIndex_lt (output : HashOutput) : outIndex output < 2 ^ 31 := Nat.mod_lt _ (by positivity)
theorem chainOf_eq_addrOf (output : HashOutput) (k : Fin 9) (t : Fin 7) :
    Guess.chainOf output k t = addrOf (outIndex output) (outIndex_lt output) k (WCT9.child output k) t := rfl
theorem expectedOpening_world (g g' : WctPoint → Digest) (output : HashOutput)
    (h : ∀ c ∈ revealedCoords output, g c = g' c) (k : Fin 9) :
    WCT9.expectedOpening (wA hU ω g) (outIndex output) output k =
      WCT9.expectedOpening (wA hU ω g') (outIndex output) output k := by
  unfold WCT9.expectedOpening
  rw [WCT9.buildCoordinate_result, WCT9.buildCoordinate_result,
    coordNodes_world hU ω g g' (outIndex output) (outIndex_lt output) k]
  congr 3
  funext t
  rw [wctChainValue_eq _ _ (outIndex_lt output), wctChainValue_eq _ _ (outIndex_lt output),
    chainValue_world hU ω g _ _ (by omega), chainValue_world hU ω g' _ _ (by omega)]
  unfold Guess.ChainTable.walkVal
  by_cases hd : 1 ≤ WCT9.digit (WCT9.rank output k) t
  · have hlt : 3 - WCT9.digit (WCT9.rank output k) t < 3 := by omega
    rw [dif_pos hlt, dif_pos hlt]
    apply h
    rw [mem_revealedCoords]
    exact ⟨k, t, hd, rfl, rfl⟩
  · have hlt : ¬3 - WCT9.digit (WCT9.rank output k) t < 3 := by omega
    rw [dif_neg hlt, dif_neg hlt]
noncomputable def signerCore (published : SigGolfCandidate.T3.Cache) (request : Request) :
    Option (Digest × HashOutput × List Pieces) :=
  if request.cache = published then
    match evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch (evalWithAnswerFn (wA hU ω 0)
        (privateNonce request.message)) request.message 0 WCT9.digestAttemptLimit) with
    | none => none
    | some (_, output) =>
        match evalWithAnswerFn (wA hU ω 0) (signLayers request.cache (output.toNat % 2 ^ 31) 4
            (WCT9.honestForest (wA hU ω 0) (output.toNat % 2 ^ 31), 0, 0)) with
        | none => none
        | some pieces => some (evalWithAnswerFn (wA hU ω 0) (privateNonce request.message), output, pieces)
  else none
def assembleWith (A : Answers) (core : Digest × HashOutput × List Pieces) : Signature :=
  WCT9.assembledSignature core.1 (List.ofFn (WCT9.expectedOpening A (outIndex core.2.1) core.2.1)) core.2.2
theorem eval_privateMac_bind (A : Answers) (region : Region) {β : Type} (next : M β) :
    evalWithAnswerFn A (privateMac region >>= fun _ => next) = evalWithAnswerFn A next := by
  rw [evalWithAnswerFn_bind]
theorem sign_answers (g : WctPoint → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) =
      (signerCore hU ω published request).map (assembleWith (wA hU ω g)) := by
  unfold FullGame.authenticatedSign signerCore
  rw [eval_privateMac_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    change evalWithAnswerFn (wA hU ω g) (WCT9.Rev3.signPayload request.cache request.message) = _
    rw [WCT9.Rev3.signPayload_eq, evalWithAnswerFn_bind, eval_free hU ω g 0 (privateNonce_free _),
      evalWithAnswerFn_bind, eval_free hU ω g 0 (wctDigestSearch_free _ _ _ _)]
    generalize evalWithAnswerFn (wA hU ω 0) (privateNonce request.message) = rho
    cases evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch rho request.message 0 WCT9.digestAttemptLimit) with
    | none => rfl
    | some found =>
        obtain ⟨ctr, output⟩ := found
        simp only
        rw [evalWithAnswerFn_bind, WCT9.eval_signForest, evalWithAnswerFn_bind]
        simp only
        rw [honestForest_world hU ω g 0 (output.toNat % 2 ^ 31) (outIndex_lt output),
          eval_free hU ω g 0 (signLayers_free _ _ _ _)]
        cases evalWithAnswerFn (wA hU ω 0) (signLayers request.cache (output.toNat % 2 ^ 31) 4
          (WCT9.honestForest (wA hU ω 0) (output.toNat % 2 ^ 31), 0, 0)) with
        | none => rfl
        | some pieces => rfl
  · rw [if_neg hc, if_neg hc]
    rfl
noncomputable def openedFor (published : SigGolfCandidate.T3.Cache) (request : Request) : List Guess.GCoord :=
  match signerCore hU ω published request with
  | none => []
  | some core => revealedCoords core.2.1
theorem map_assemble_congr {A A' : Answers} (o : Option (Digest × HashOutput × List Pieces))
    (h : ∀ core, o = some core → assembleWith A core = assembleWith A' core) :
    o.map (assembleWith A) = o.map (assembleWith A') := by
  cases o with
  | none => exact (Option.map_none _).trans (Option.map_none _).symm
  | some core => exact (Option.map_some _ _).trans ((congrArg some (h core rfl)).trans (Option.map_some _ _).symm)
theorem sign_local (g g' : WctPoint → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (h : ∀ c ∈ openedFor hU ω published request, g c = g' c) :
    evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (wA hU ω g') (FullGame.authenticatedSign published request) := by
  rw [sign_answers, sign_answers]
  apply map_assemble_congr
  intro core hcore
  unfold openedFor at h
  rw [hcore] at h
  exact congrArg (fun l => WCT9.assembledSignature core.1 l core.2.2)
    (congrArg List.ofFn (funext fun k => expectedOpening_world hU ω g g' core.2.1 h k))
theorem signerCore_search {published : SigGolfCandidate.T3.Cache} {request : Request}
    {core : Digest × HashOutput × List Pieces} (h : signerCore hU ω published request = some core) :
    ∃ ctr, evalWithAnswerFn (wA hU ω 0) (WCT9.digestSearch core.1 request.message 0 WCT9.digestAttemptLimit) =
      some (ctr, core.2.1) := by
  unfold signerCore at h
  split_ifs at h
  split at h
  · cases h
  · rename_i ctr output hfound
    split at h
    · cases h
    · cases h
      exact ⟨ctr, hfound⟩
theorem signedOutput_world (g : WctPoint → Digest) {published : SigGolfCandidate.T3.Cache} {request : Request}
    {core : Digest × HashOutput × List Pieces} (h : signerCore hU ω published request = some core) :
    CaseC.signedOutput (wA hU ω g) request.message (assembleWith (wA hU ω g) core) = some core.2.1 := by
  obtain ⟨ctr, hs⟩ := signerCore_search hU ω h
  unfold CaseC.signedOutput assembleWith
  rw [WCT9.assembledSignature_rho, eval_free hU ω g 0 (wctDigestSearch_free _ _ _ _), hs]
  rfl
theorem sign_opened (g : WctPoint → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (c : Guess.GCoord) (hc : c ∈ openedFor hU ω published request) :
    ∃ signature output, evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) = some signature ∧
      CaseC.signedOutput (wA hU ω g) request.message signature = some output ∧ c ∈ revealedCoords output := by
  unfold openedFor at hc
  cases hcore : signerCore hU ω published request with
  | none => rw [hcore] at hc; cases hc
  | some core =>
      rw [hcore] at hc
      refine ⟨assembleWith (wA hU ω g) core, core.2.1, ?_, signedOutput_world hU ω g hcore, hc⟩
      rw [sign_answers, hcore]
      rfl
end World
end ClaudeWCT.W9.T3.Security.WPair
end
section
namespace ClaudeWCT.Guess
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3
open SphincsSecurity.Concrete
open SphincsSecurity.Concrete.SecretGuessObservation
set_option backward.isDefEq.respectTransparency false
variable {E Memory : Type}
def CovMono (Cov : List E → ChainAddr → ℕ → Prop) : Prop :=
  (∀ l1 l2 a p, Cov l1 a p → Cov (l1 ++ l2) a p) ∧ (∀ l1 l2 a p, Cov l2 a p → Cov (l1 ++ l2) a p)
structure WTracks (T : ChainTable) (g : GCoord → Digest) (Cov : List E → ChainAddr → ℕ → Prop)
    (before after : State GCoord Digest Memory) (log : List E) (entries : List (HashInput × HashOutput)) : Prop where
  probes : after.probes ≤ before.probes + entries.length
  prefixTracks : PrefixTracks (Cov log) before after
  queried : ∀ c ans, (honestProbe (T.answers g) c, ans) ∈ entries → c ∈ after.retired
namespace WTracks
variable {T : ChainTable} {g : GCoord → Digest} {Cov : List E → ChainAddr → ℕ → Prop}
theorem refl (state : State GCoord Digest Memory) : WTracks T g Cov state state [] [] :=
  ⟨by simp, PrefixTracks.refl _ _, fun _ _ h => by cases h⟩
theorem trans (hc : CovMono Cov) {s1 s2 s3 : State GCoord Digest Memory} {l1 l2 : List E}
    {e1 e2 : List (HashInput × HashOutput)} (first : WTracks T g Cov s1 s2 l1 e1)
    (second : WTracks T g Cov s2 s3 l2 e2) : WTracks T g Cov s1 s3 (l1 ++ l2) (e1 ++ e2) := by
  refine ⟨?_, ?_, ?_⟩
  · have := first.probes
    have := second.probes
    simp only [List.length_append]
    omega
  · refine (first.prefixTracks.trans second.prefixTracks).mono ?_
    rintro a p (h | h)
    · exact hc.1 l1 l2 a p h
    · exact hc.2 l1 l2 a p h
  · intro c ans h
    rcases List.mem_append.mp h with h | h
    · exact second.prefixTracks.retired (first.queried c ans h)
    · exact second.queried c ans h
theorem coin {before after : State GCoord Digest Memory} (hg : before.guesses = after.guesses)
    (hr : before.retired = after.retired) (hp : after.probes = before.probes) :
    WTracks T g Cov before after [] [] := by
  refine ⟨by simp [hp], ⟨hg ▸ Finset.Subset.refl _, hr ▸ Finset.Subset.refl _, ?_⟩, fun _ _ h => by cases h⟩
  intro a p h
  left
  rw [hr]
  exact h
theorem of_prefix_false {before after : State GCoord Digest Memory} {log : List E}
    {entries : List (HashInput × HashOutput)} (hp : after.probes ≤ before.probes + entries.length)
    (ht : PrefixTracks (fun _ _ => False) before after)
    (hq : ∀ c ans, (honestProbe (T.answers g) c, ans) ∈ entries → c ∈ after.retired) :
    WTracks T g Cov before after log entries :=
  ⟨hp, ht.mono fun _ _ h => h.elim, hq⟩
theorem hashW {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    (environment : Environment auxSpec GCoord Digest Memory) (x : HashInput) (state : State GCoord Digest Memory)
    (result : HashOutput × State GCoord Digest Memory)
    (hr : fixedRun environment g (T.hashW (auxSpec := auxSpec) x) state result ≠ 0) :
    result.1 = T.answers g (.inl (.inr x)) ∧ WTracks T g Cov state result.2 [] [(x, result.1)] := by
  obtain ⟨h1, h2, h3, h4⟩ := T.fixedRun_hashW environment g x state result hr
  refine ⟨h1, of_prefix_false (by simpa using h3) h2 ?_⟩
  intro c ans h
  rw [List.mem_singleton] at h
  exact h4 c (congrArg Prod.fst h).symm
theorem disclose {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
    (environment : Environment auxSpec GCoord Digest Memory) (cs : List GCoord) (entry : E)
    (hcs : ∀ c ∈ cs, Cov [entry] c.1 c.2.val) (hpos : ∀ l a p p', p ≤ p' → Cov l a p → Cov l a p')
    (state : State GCoord Digest Memory) (result : List Digest × State GCoord Digest Memory)
    (hr : fixedRun environment g (discloseAll (auxSpec := auxSpec) cs) state result ≠ 0) :
    result.1 = cs.map g ∧ WTracks T g Cov state result.2 [entry] [] := by
  obtain ⟨h1, h2, -, h4⟩ := fixedRun_discloseAll environment g cs state result hr
  refine ⟨h1, ⟨by simp [h2], h4.mono ?_, fun _ _ h => by cases h⟩⟩
  rintro a p ⟨c, hc, rfl, hle⟩
  exact hpos _ _ _ _ hle (hcs c hc)
theorem guess {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c : GCoord)
    (hcov : ¬Cov log c.1 c.2.val) (hentry : ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries) :
    PrefixIn final.guesses c.1 c.2.val := by
  obtain ⟨ans, he⟩ := hentry
  exact prefixIn_guesses_of_tracks h.prefixTracks hinit (prefixIn_of_mem (h.queried c ans he)) hcov
theorem pair {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c c' : GCoord) (hne : c.1 ≠ c'.1)
    (hc : ¬Cov log c.1 c.2.val ∧ ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries)
    (hc' : ¬Cov log c'.1 c'.2.val ∧ ∃ ans, (honestProbe (T.answers g) c', ans) ∈ entries) :
    2 ≤ final.guesses.card :=
  two_le_card_of_prefixIn hne (h.guess hinit c hc.1 hc.2) (h.guess hinit c' hc'.1 hc'.2)
theorem one {init final : State GCoord Digest Memory} {log : List E} {entries : List (HashInput × HashOutput)}
    (h : WTracks T g Cov init final log entries) (hinit : init.retired = ∅) (c : GCoord)
    (hc : ¬Cov log c.1 c.2.val ∧ ∃ ans, (honestProbe (T.answers g) c, ans) ∈ entries) :
    final.guesses.Nonempty :=
  nonempty_of_prefixIn (h.guess hinit c hc.1 hc.2)
end WTracks
end ClaudeWCT.Guess
end
section
namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
abbrev WSpec := SecretGuessObservation.World unifSpec Guess.GCoord Digest
abbrev WState := SecretGuessObservation.State Guess.GCoord Digest PUnit
noncomputable def coinImpl : QueryImpl unifSpec ProbComp := fun n => liftM (unifSpec.query n)
noncomputable def env : SecretGuessObservation.Environment unifSpec Guess.GCoord Digest PUnit :=
  SecretGuessObservation.environment coinImpl
def init : WState := SecretGuessObservation.initialState PUnit.unit
theorem card_digest : Fintype.card Digest = 2 ^ 128 := by simp
def overwrite (positions : List Guess.GCoord) (values : List Digest) (c : Guess.GCoord) : Digest :=
  ((positions.zip values).find? (fun pv => decide (pv.1 = c))).elim 0 Prod.snd
theorem overwrite_map (g : Guess.GCoord → Digest) (positions : List Guess.GCoord) (c : Guess.GCoord)
    (hc : c ∈ positions) : overwrite positions (positions.map g) c = g c := by
  induction positions with
  | nil => cases hc
  | cons first rest ih =>
      unfold overwrite
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      by_cases he : first = c
      · subst he
        simp
      · simp only [he, decide_false]
        exact ih (by simpa [Ne.symm he] using List.mem_cons.mp hc |>.resolve_left (Ne.symm he))
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable def hashW (x : HashInput) : OracleComp WSpec HashOutput :=
  (CanonTable.chainTable hU ω).hashW (auxSpec := unifSpec) x
noncomputable def signW (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp WSpec (Option Signature) := do
  let positions := openedFor hU ω published request
  let values ← Guess.discloseAll (auxSpec := unifSpec) (V := Digest) positions
  pure (evalWithAnswerFn (wA hU ω (overwrite positions values)) (FullGame.authenticatedSign published request))
noncomputable def interactionW (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp WSpec (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signW hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programW {β : Type} : M β → OracleComp WSpec (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let answer ← hashW hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldGame (adversary : AdversaryP) :
    OracleComp WSpec (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen
  let interaction ← interactionW hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programW hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
end World
noncomputable def interactionT (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → ProbComp (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
          next coin
      | .inl (.inr x) => do
          let rest ← next (T (.inl (.inr x)))
          pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)
      | .inr request => do
          let rest ← next (evalWithAnswerFn T (FullGame.authenticatedSign published request))
          pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ :: rest.2.1,
            rest.2.2))
noncomputable def pairRun (T : Answers) (adversary : AdversaryP) :
    ProbComp (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn T SigGolfCandidate.T3.keygen
  let interaction ← interactionT T generated.2 (adversary generated.1 generated.2)
  let verdict := GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1)
  pure (evalWithAnswerFn T verdict, interaction.2.1,
    interaction.2.2 ++ Wots.entriesOf T (SourceReplay.queried T verdict))
section Couple
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
noncomputable abbrev fixedW (g : Guess.GCoord → Digest) : QueryImpl WSpec ProbComp :=
  SecretGuessObservation.fixedAnswers coinImpl g
theorem keygen_answers (g : Guess.GCoord → Digest) :
    evalWithAnswerFn (wA hU ω g) SigGolfCandidate.T3.keygen = evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen :=
  eval_free hU ω g 0 keygen_free
theorem fixed_hashW (g : Guess.GCoord → Digest) (x : HashInput) :
    simulateQ (fixedW g) (hashW hU ω x) = pure (wA hU ω g (.inl (.inr x))) :=
  (CanonTable.chainTable hU ω).fixed_hashW coinImpl g x
theorem fixed_signW (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    simulateQ (fixedW g) (signW hU ω published request) =
      pure (evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request)) := by
  unfold signW
  rw [simulateQ_bind, Guess.fixed_discloseAll, pure_bind, simulateQ_pure]
  congr 1
  apply sign_local
  intro c hc
  exact overwrite_map g _ c hc
theorem interactionW_pure (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionW hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionW_coin (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (WSpec.query (.inl n)) : OracleComp WSpec (Fin (n + 1))) >>= fun coin =>
        interactionW hU ω published (next coin)) := rfl
theorem interactionW_public (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => interactionW hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl
theorem interactionW_request (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionW hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (signW hU ω published request >>= fun signature => interactionW hU ω published (next signature) >>= fun rest =>
        pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl
theorem programW_pure {β : Type} (value : β) : programW hU ω (pure value : M β) = pure (value, []) := rfl
theorem programW_public {β : Type} (x : HashInput) (next : HashOutput → M β) :
    programW hU ω (liftM (SigGolfCandidate.T3.Spec.query (.inl (.inr x))) >>= next) =
      (hashW hU ω x >>= fun answer => programW hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl
theorem interactionT_pure (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (value : α) :
    interactionT T published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl
theorem interactionT_coin (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun coin => interactionT T published (next coin)) :=
  rfl
theorem interactionT_public (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (interactionT T published (next (T (.inl (.inr x)))) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, T (.inl (.inr x))) :: rest.2.2)) := rfl
theorem interactionT_request (T : Answers) (published : SigGolfCandidate.T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    interactionT T published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (interactionT T published (next (evalWithAnswerFn T (FullGame.authenticatedSign published request))) >>=
        fun rest => pure (rest.1, ⟨request, evalWithAnswerFn T (FullGame.authenticatedSign published request)⟩ ::
          rest.2.1, rest.2.2)) := rfl
theorem fixed_interactionW (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    simulateQ (fixedW g) (interactionW hU ω published program) = interactionT (wA hU ω g) published program := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [interactionW_pure, interactionT_pure, simulateQ_pure]
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin, interactionT_coin, simulateQ_bind, simulateQ_spec_query]
        exact bind_congr fun coin => ih coin
      · rw [interactionW_public, interactionT_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
      · rw [interactionW_request, interactionT_request, simulateQ_bind, fixed_signW, pure_bind, simulateQ_bind, ih]
        exact bind_congr fun rest => by rw [simulateQ_pure]
theorem fixed_programW (g : Guess.GCoord → Digest) {β : Type} (program : M β) (hp : PublicVerdict.Only program) :
    simulateQ (fixedW g) (programW hU ω program) =
      pure (evalWithAnswerFn (wA hU ω g) program,
        Wots.entriesOf (wA hU ω g) (SourceReplay.queried (wA hU ω g) program)) := by
  induction program using OracleComp.inductionOn with
  | pure value => rw [programW_pure, simulateQ_pure]; rfl
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public, simulateQ_bind, fixed_hashW, pure_bind, simulateQ_bind, ih _ (hn _), pure_bind,
          simulateQ_pure, SourceReplay.queried_query_bind, evalWithAnswerFn_bind, eval_query']
        rfl
      · exact hi.elim
theorem simulate_worldGame (g : Guess.GCoord → Digest) (adversary : AdversaryP) :
    simulateQ (fixedW g) (worldGame hU ω adversary) = pairRun (wA hU ω g) adversary := by
  unfold worldGame pairRun
  rw [← keygen_answers hU ω g]
  rw [simulateQ_bind, fixed_interactionW]
  apply bind_congr
  intro interaction
  rw [simulateQ_bind, fixed_programW _ _ _ _ (PaddedGame.verdict_public _ _), pure_bind, simulateQ_pure]
theorem fixed_worldGame (g : Guess.GCoord → Digest) (adversary : AdversaryP) :
    Prod.fst <$> SecretGuessObservation.fixedRun env g (worldGame hU ω adversary) init =
      𝒮[pairRun (wA hU ω g) adversary] := by
  rw [env, SecretGuessObservation.fixedRun_projection, simulate_worldGame]
end Couple
section Tracking
open SecretGuessObservation (runWith fixedRun fixedImpl afterTrial afterDisclosure)
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) (ω : CanonTable.Omega U)
def Cov (A : Answers) (log : QueryLog Requests) (a : Guess.ChainAddr) (p : Nat) : Prop := Disclosed A log a p
theorem cov_mono (A : Answers) : Guess.CovMono (Cov A) :=
  ⟨fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_left _ he) h,
    fun l1 l2 a p h => Disclosed.mono_log (fun e he => List.mem_append_right _ he) h⟩
abbrev Tracks (g : Guess.GCoord → Digest) (before after : WState) (log : QueryLog Requests)
    (entries : List Wots.Entry) : Prop :=
  Guess.WTracks (CanonTable.chainTable hU ω) g (Cov (wA hU ω g)) before after log entries
theorem Tracks.trans' {g : Guess.GCoord → Digest} {s1 s2 s3 : WState} {l1 l2 : QueryLog Requests}
    {e1 e2 : List Wots.Entry} (first : Tracks hU ω g s1 s2 l1 e1) (second : Tracks hU ω g s2 s3 l2 e2) :
    Tracks hU ω g s1 s3 (l1 ++ l2) (e1 ++ e2) :=
  Guess.WTracks.trans (cov_mono _) first second
theorem fixedRun_bind_nonzero {First Result : Type} (g : Guess.GCoord → Digest) (first : OracleComp WSpec First)
    (next : First → OracleComp WSpec Result) (state : WState) (result : Result × WState)
    (hr : fixedRun env g (first >>= next) state result ≠ 0) :
    ∃ middle, fixedRun env g first state middle ≠ 0 ∧ fixedRun env g (next middle.1) middle.2 result ≠ 0 :=
  Guess.fixedRun_bind_nonzero' env g first next state result hr
theorem fixedRun_pure_nonzero {Result : Type} (g : Guess.GCoord → Digest) (value : Result) (state : WState)
    (result : Result × WState) (hr : fixedRun env g (pure value) state result ≠ 0) : result = (value, state) :=
  Guess.fixedRun_pure_nonzero' env g value state result hr
theorem fixed_coin_tracks (g : Guess.GCoord → Digest) (n : Nat) (state : WState) (result : Fin (n + 1) × WState)
    (hr : fixedRun env g (liftM (WSpec.query (.inl n))) state result ≠ 0) : Tracks hU ω g state result.2 [] [] := by
  unfold fixedRun runWith at hr
  rw [simulateQ_spec_query] at hr
  simp only [fixedImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  exact Guess.WTracks.refl state
theorem fixed_hashW_tracks (g : Guess.GCoord → Digest) (x : HashInput) (state : WState) (result : HashOutput × WState)
    (hr : fixedRun env g (hashW hU ω x) state result ≠ 0) :
    result.1 = wA hU ω g (.inl (.inr x)) ∧ Tracks hU ω g state result.2 [] [(x, result.1)] :=
  Guess.WTracks.hashW env x state result hr
theorem fixed_signW_tracks (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) (request : Request)
    (state : WState) (result : Option Signature × WState)
    (hr : fixedRun env g (signW hU ω published request) state result ≠ 0) :
    result.1 = evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) ∧
      Tracks hU ω g state result.2 [⟨request, result.1⟩] [] := by
  unfold signW at hr
  obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have hsig : evalWithAnswerFn (wA hU ω (overwrite (openedFor hU ω published request) middle.1))
      (FullGame.authenticatedSign published request) =
      evalWithAnswerFn (wA hU ω g) (FullGame.authenticatedSign published request) := by
    have h1 := (Guess.fixedRun_discloseAll env g (openedFor hU ω published request) state middle hm).1
    rw [h1]
    exact sign_local hU ω _ _ published request fun c hc => overwrite_map g _ c hc
  refine ⟨hsig, ?_⟩
  have hcov : ∀ c ∈ openedFor hU ω published request,
      Cov (wA hU ω g) [⟨request, evalWithAnswerFn (wA hU ω (overwrite (openedFor hU ω published request) middle.1))
        (FullGame.authenticatedSign published request)⟩] c.1 c.2.val := by
    intro c hc
    rw [hsig]
    obtain ⟨signature, output, hs, ho, hrev⟩ := sign_opened hU ω g published request c hc
    obtain ⟨k, t, hu, h1, h2⟩ := mem_revealedCoords.mp hrev
    refine ⟨output, mem_loggedOutputs.mpr ⟨_, List.mem_singleton_self _, signature, hs, ho⟩, ?_, ?_, ?_⟩
    · rw [h1]; rfl
    · rw [h1]; rfl
    · rw [h1, h2]; exact le_rfl
  exact (Guess.WTracks.disclose env (openedFor hU ω published request) _ hcov
    (fun l a p p' hpp' hc => Disclosed.mono_pos hpp' hc) state middle hm).2
theorem interactionW_tracks (g : Guess.GCoord → Digest) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) (state : WState)
    (result : (α × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env g (interactionW hU ω published program) state result ≠ 0) :
    Tracks hU ω g state result.2 result.1.2.1 result.1.2.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [interactionW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionW_coin] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        have h := Tracks.trans' hU ω (fixed_coin_tracks hU ω g n state middle hm) (ih middle.1 middle.2 result hr)
        simpa only [List.nil_append] using h
      · rw [interactionW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2 (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · rw [interactionW_request] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_signW_tracks hU ω g published request state middle hm).2
          (ih middle.1 middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
theorem programW_tracks (g : Guess.GCoord → Digest) {β : Type} (program : M β) (hp : PublicVerdict.Only program)
    (state : WState) (result : (β × List Wots.Entry) × WState)
    (hr : fixedRun env g (programW hU ω program) state result ≠ 0) :
    Tracks hU ω g state result.2 [] result.1.2 := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [programW_pure] at hr
      have h := fixedRun_pure_nonzero g _ state result hr
      subst h
      exact Guess.WTracks.refl state
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hp
      rcases input with (n | x) | c
      · exact hi.elim
      · rw [programW_public] at hr
        obtain ⟨middle, hm, hr⟩ := fixedRun_bind_nonzero g _ _ state result hr
        obtain ⟨tail, ht, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
        have h := fixedRun_pure_nonzero g _ _ result hr
        subst h
        have h := Tracks.trans' hU ω (fixed_hashW_tracks hU ω g x state middle hm).2
          (ih middle.1 (hn _) middle.2 tail ht)
        simpa only [List.nil_append, List.singleton_append] using h
      · exact hi.elim
theorem worldGame_tracking (g : Guess.GCoord → Digest) (adversary : AdversaryP)
    (result : (Bool × QueryLog Requests × List Wots.Entry) × WState)
    (hr : fixedRun env g (worldGame hU ω adversary) init result ≠ 0) :
    result.2.probes ≤ result.1.2.2.length ∧
      ∀ c, GuessedIn (wA hU ω g) result.1.2.1 result.1.2.2 c → Guess.PrefixIn result.2.guesses c.1 c.2.val := by
  unfold worldGame at hr
  obtain ⟨interaction, hi, hr⟩ := fixedRun_bind_nonzero g _ _ init result hr
  obtain ⟨verdict, hv, hr⟩ := fixedRun_bind_nonzero g _ _ _ result hr
  have h := fixedRun_pure_nonzero g _ _ result hr
  subst h
  have t := Tracks.trans' hU ω (interactionW_tracks hU ω g _ _ init interaction hi)
    (programW_tracks hU ω g _ (PaddedGame.verdict_public _ _) _ verdict hv)
  rw [List.append_nil] at t
  refine ⟨by simpa [init, SecretGuessObservation.initialState] using t.probes, ?_⟩
  intro c hc
  exact t.guess (by simp [init, SecretGuessObservation.initialState]) c hc.1 hc.2
end Tracking
end ClaudeWCT.W9.T3.Security.WPair
end
