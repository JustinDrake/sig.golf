import SigGolfCandidate.T3.Secc.CanonGraphHonest
import SigGolfCandidate.SphincsSecurity.Proof.Base.FirstSuccessFamily
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableOverwrite

namespace SigGolfCandidate.T3.Security.CanonEncoding
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open SphincsSecurity.Concrete
open SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers)
open CanonGraph
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
abbrev EncLeaf := {L : LeafPos // L.Source}
def EncLeaf.toWots (L : EncLeaf) : Wots.LeafAddr := ⟨L.1.lay, L.1.tree.val, L.1.leaf.val⟩
theorem route_tree_lt (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    (route index lay).2 < 2 ^ treeBits lay := by
  fin_cases lay <;> simp [route, treeBits, height] <;> omega
theorem route_source (index : Nat) (hindex : index < 2 ^ 31) (lay : Layer) :
    ∃ L : EncLeaf, L.toWots = ⟨lay, (route index lay).2, (route index lay).1⟩ := by
  have hleaf := route_leaf_bound index lay
  have htree := route_tree_lt index hindex lay
  have ht31 : (route index lay).2 < 2 ^ 31 := lt_of_lt_of_le htree
    (Nat.pow_le_pow_right (by decide) (by fin_cases lay <;> decide))
  have hl4096 : (route index lay).1 < 4096 := lt_of_lt_of_le hleaf (by
    calc 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
      _ = 4096 := by norm_num)
  exact ⟨⟨⟨lay, ⟨(route index lay).2, ht31⟩, ⟨(route index lay).1, hl4096⟩⟩, htree, hleaf⟩, rfl⟩
theorem childIndex_lt (L : EncLeaf) : L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val < 2 ^ 31 := by
  obtain ⟨⟨lay, tree, leaf⟩, ht, hl⟩ := L
  change tree.val < 2 ^ treeBits lay at ht
  change leaf.val < 2 ^ height lay at hl
  change tree.val * 2 ^ height lay + leaf.val < 2 ^ 31
  fin_cases lay <;> simp [treeBits, height] at ht hl ⊢ <;> omega
def childIndex (L : EncLeaf) : Fin (2^31) :=
  ⟨L.1.tree.val * 2 ^ height L.1.lay + L.1.leaf.val, childIndex_lt L⟩
def msgLabel (labels : Labels) (L : EncLeaf) : Digest :=
  if h : L.1.lay.val < 3 then
    treeLabel labels ⟨L.1.lay.val + 1, by omega⟩ (childIndex L) (height ⟨L.1.lay.val + 1, by omega⟩) 0
  else (labels (.forest (childIndex L))).extractLsb' 0 128
theorem leafMsg_eq {answers : Answers} {labels : Labels} (h : Agrees answers labels) (L : EncLeaf) :
    Wots.leafMsg answers L.toWots = msgLabel labels L := by
  unfold Wots.leafMsg msgLabel EncLeaf.toWots
  dsimp only
  split_ifs with hlay
  · exact honestRoot_eq h ⟨L.1.lay.val + 1, by omega⟩ (childIndex L)
  · exact honestForest_eq h (childIndex L)
def encKey (labels : Labels) (x : EncLeaf × Fin (2^22)) : QuerySpace.EncodingKey :=
  ((x.1.1.lay, x.1.1.tree, x.1.1.leaf, msgLabel labels x.1), x.2)
theorem encKey_injective (labels : Labels) : Function.Injective (encKey labels) := by
  rintro ⟨⟨⟨lay, tree, leaf⟩, hL⟩, c⟩ ⟨⟨⟨lay', tree', leaf'⟩, hL'⟩, c'⟩ heq
  simp only [encKey, Prod.mk.injEq] at heq
  obtain ⟨⟨h1, h2, h3, -⟩, h4⟩ := heq
  subst h1 h2 h3 h4
  rfl
theorem encodingQuery_ne_cell (key : QuerySpace.EncodingKey) (secrets : Secrets) (node : Node) (labels : Labels) :
    QuerySpace.encodingQuery key ≠ cell secrets node labels := by
  intro heq
  have h1 : Extract.hdrBlock (QuerySpace.encodingQuery key) =
      bytesLE 16 (header 4 key.1.1.val key.1.2.1.val 0 key.1.2.2.1.val) :=
    QuerySpace.queryHeader_encoding _ _ _ _ _
  rw [heq, hdrBlock_cell] at h1
  have h2 := bytesLE_injective h1
  cases node with
  | chain point =>
      exact chainHeader_ne_header _ _ _ _ _ _ _ _ _ _ h2
  | _ =>
      simp only [Node.toPos, Extract.Pos.hdr] at h2
      exact QuerySpace.header_ne_of_tag (by decide) h2
noncomputable def encCell (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (x : EncLeaf × Fin (2^22)) : U :=
  ⟨QuerySpace.encodingQuery (encKey labels x), hE (encodingQuery_mem _)⟩
theorem encCell_injective (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    Function.Injective (encCell U hE labels) := by
  intro left right heq
  exact encKey_injective labels (QuerySpace.encodingQuery_injective (congrArg Subtype.val heq))
def decodeAt (L : EncLeaf) (answer : HashOutput) : Option Digest :=
  if (decode L.1.lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none
theorem decodeAt_eq_some (L : EncLeaf) (answer : HashOutput) (d : Digest) :
    decodeAt L answer = some d ↔ answer.extractLsb' 0 128 = d ∧ (decode L.1.lay d).isSome := by
  unfold decodeAt
  split_ifs with hs
  · constructor
    · intro he; cases he; exact ⟨rfl, hs⟩
    · rintro ⟨rfl, -⟩; rfl
  · constructor
    · intro he; cases he
    · rintro ⟨rfl, h⟩; exact absurd h hs
theorem decodeAt_eq_none (L : EncLeaf) (answer : HashOutput) :
    decodeAt L answer = none ↔ decode L.1.lay (answer.extractLsb' 0 128) = none := by
  unfold decodeAt
  split_ifs with hs
  · simp only [false_iff]
    intro hn; rw [hn] at hs; exact absurd hs (by decide)
  · simp only [true_iff]
    cases hd : decode L.1.lay (answer.extractLsb' 0 128) with
    | none => rfl
    | some w => rw [hd] at hs; exact absurd rfl hs
abbrev Selection := Option (Fin (2^22) × Digest)
abbrev Selections := EncLeaf → Selection
noncomputable def selectionsOf (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (table : U → HashOutput) : Selections :=
  fun L => FirstSuccessTable.select (decodeAt L) (fun c => table (encCell U hE labels (L, c)))
noncomputable def selectionLaw : PMF Selections :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.selected (decodeAt L) (2^22))
noncomputable def rowsLaw (selections : Selections) : PMF (EncLeaf → Fin (2^22) → HashOutput) :=
  FinitePmfProduct.law (fun L => FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L))
theorem rowsLaw_apply (selections : Selections) (rows : EncLeaf → Fin (2^22) → HashOutput) :
    rowsLaw selections rows =
      ∏ L, FirstSuccessTable.afterSelect (decodeAt L) (2^22) (selections L) (rows L) :=
  FinitePmfProduct.apply _ _
theorem afterSelect_some (L : EncLeaf) (i : Fin (2^22)) (d : Digest) :
    FirstSuccessTable.afterSelect (decodeAt L) (2^22) (some (i, d)) =
      FirstSuccessTable.constrained (FirstSuccessTable.allowed (decodeAt L) i d) := rfl
theorem afterSelect_none (L : EncLeaf) :
    FirstSuccessTable.afterSelect (decodeAt L) (2^22) none =
      FirstSuccessTable.constrained (fun _ => FirstSuccessTable.invalid (decodeAt L)) := rfl
theorem mem_allowed (L : EncLeaf) (i : Fin (2^22)) (d : Digest) (c : Fin (2^22)) (answer : HashOutput) :
    answer ∈ FirstSuccessTable.allowed (decodeAt L) i d c ↔
      (c < i → decode L.1.lay (answer.extractLsb' 0 128) = none) ∧
        (c = i → answer.extractLsb' 0 128 = d ∧ (decode L.1.lay d).isSome) := by
  unfold FirstSuccessTable.allowed
  split_ifs with hlt heq
  · rw [FirstSuccessTable.mem_invalid, decodeAt_eq_none]
    exact ⟨fun h => ⟨fun _ => h, fun he => absurd (he ▸ hlt) (lt_irrefl _)⟩, fun h => h.1 hlt⟩
  · subst heq
    rw [FirstSuccessTable.mem_fiber, decodeAt_eq_some]
    exact ⟨fun h => ⟨fun h' => absurd h' (lt_irrefl _), fun _ => h⟩, fun h => h.2 rfl⟩
  · simp only [Finset.mem_univ, true_iff]
    exact ⟨fun h => absurd h hlt, fun h => absurd h heq⟩
theorem selected_mul_rowsLaw (results : Selections) (tables : EncLeaf → Fin (2^22) → HashOutput) :
    selectionLaw results * rowsLaw results tables =
      if (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) = results then
        PMF.uniformOfFintype (EncLeaf → Fin (2^22) → HashOutput) tables else 0 := by
  rw [selectionLaw, rowsLaw, FinitePmfProduct.apply, FinitePmfProduct.apply, ← Finset.prod_mul_distrib]
  simp only [FirstSuccessTable.selected_mul_afterSelect]
  by_cases h : (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) = results
  · rw [if_pos h]
    have hcoordinate (L : EncLeaf) : FirstSuccessTable.select (decodeAt L) (tables L) = results L := congrFun h L
    simp only [hcoordinate, if_true, FirstSuccessTable.full_eq_uniform]
    rw [← FinitePmfProduct.apply (fun _ : EncLeaf => PMF.uniformOfFintype (Fin (2^22) → HashOutput)) tables,
      FinitePmfProduct.uniform]
  · rw [if_neg h]
    have hex : ∃ L, FirstSuccessTable.select (decodeAt L) (tables L) ≠ results L := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨L, hL⟩ := hex
    exact Finset.prod_eq_zero (by simp) (if_neg hL)
theorem uniform_bind_eq_selected {Result : Type}
    (next : Selections → (EncLeaf → Fin (2^22) → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (EncLeaf → Fin (2^22) → HashOutput)).bind
        (fun tables => next (fun L => FirstSuccessTable.select (decodeAt L) (tables L)) tables) =
      selectionLaw.bind (fun results => (rowsLaw results).bind (next results)) := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, selected_mul_rowsLaw, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun tables => ?_
  rw [tsum_eq_single (fun L => FirstSuccessTable.select (decodeAt L) (tables L))]
  · rw [if_pos rfl]
  · intro results hne
    rw [if_neg (Ne.symm hne)]
theorem selectionsOf_join (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (rows : EncLeaf × Fin (2^22) → HashOutput) (outside : UniformTableSplit.Outside (encCell U hE labels) → HashOutput) :
    selectionsOf U hE labels (UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels) rows outside) =
      fun L => FirstSuccessTable.select (decodeAt L) (fun c => rows (L, c)) := by
  funext L
  unfold selectionsOf
  apply congrArg (FirstSuccessTable.select (decodeAt L))
  funext c
  exact UniformTableSplit.join_embed _ _ rows outside (L, c)
theorem residual_selection_bind {Result : Type} (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (next : Selections → (U → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (U → HashOutput)).bind (fun residual => next (selectionsOf U hE labels residual) residual) =
      selectionLaw.bind (fun selections => (rowsLaw selections).bind (fun rows =>
        (PMF.uniformOfFintype (UniformTableSplit.Outside (encCell U hE labels) → HashOutput)).bind (fun outside =>
          next selections (UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
            (Function.uncurry rows) outside)))) := by
  rw [UniformTableSplit.uniform_bind_split (encCell U hE labels) (encCell_injective U hE labels)]
  simp_rw [selectionsOf_join]
  have huncurry := PMF.uniformOfFintype_map_of_bijective (Equiv.curry EncLeaf (Fin (2^22)) HashOutput).symm
    (Equiv.curry EncLeaf (Fin (2^22)) HashOutput).symm.bijective
  rw [← huncurry, PMF.bind_map]
  exact uniform_bind_eq_selected (fun results rows =>
    (PMF.uniformOfFintype (UniformTableSplit.Outside (encCell U hE labels) → HashOutput)).bind
      (fun outside => next results (UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (Function.uncurry rows) outside)))
noncomputable def selectionResidual (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    PMF (Selections × (U → HashOutput)) :=
  selectionLaw.bind (fun selections => (rowsLaw selections).bind (fun rows =>
    (PMF.uniformOfFintype (UniformTableSplit.Outside (encCell U hE labels) → HashOutput)).map (fun outside =>
      (selections, UniformTableSplit.join (encCell U hE labels) (encCell_injective U hE labels)
        (Function.uncurry rows) outside))))
theorem selectionResidual_eq (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) :
    selectionResidual U hE labels =
      (PMF.uniformOfFintype (U → HashOutput)).map (fun residual => (selectionsOf U hE labels residual, residual)) := by
  have h := residual_selection_bind U hE labels (fun selections residual => PMF.pure (selections, residual))
  simp only [PMF.map, selectionResidual, Function.comp_def] at h ⊢
  exact h.symm
theorem selectionResidual_support (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (r : Selections × (U → HashOutput)) (hr : r ∈ (selectionResidual U hE labels).support) :
    r.1 = selectionsOf U hE labels r.2 := by
  rw [selectionResidual_eq, PMF.support_map] at hr
  obtain ⟨residual, -, rfl⟩ := hr
  rfl
section SelectionBind
noncomputable local instance instSampleableTypeHashOutput_canonEncoding : SampleableType HashOutput := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonEncoding (U : Finset HashInput) : SampleableType (U → HashOutput) := SampleableType.ofFintype _
theorem residual_bind_selection {Result : Type} (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels)
    (next : Selections → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let residual ← ($ᵗ (U → HashOutput) : ProbComp _)
      next (selectionsOf U hE labels residual) residual] =
      (𝒮[selectionResidual U hE labels] >>= fun r => 𝒮[next r.1 r.2]) := by
  rw [selectionResidual_eq]
  simp only [← PMF.monad_map_eq_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, evalSPMF_bind, evalSPMF_pure,
    Function.comp_apply, evalSPMF_uniformSample]
noncomputable local instance instFintypeCoordinate_canonEncoding : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_canonEncoding : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeLabels_canonEncoding : SampleableType Labels := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeSecrets_canonEncoding : SampleableType Secrets := SampleableType.ofFintype _
noncomputable local instance instSampleableTypeOtherHalves_canonEncoding : SampleableType OtherHalves := SampleableType.ofFintype _
theorem tables_selection_bind {Result : Type} (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (next : FullGame.FullTable → (U → HashOutput) → ProbComp Result) :
    𝒮[do
      let privateTable ← ($ᵗ FullGame.FullTable : ProbComp _)
      let publicTable ← ($ᵗ (U → HashOutput) : ProbComp _)
      next privateTable publicTable] =
      (𝒮[($ᵗ Secrets : ProbComp _)] >>= fun secrets => 𝒮[($ᵗ OtherHalves : ProbComp _)] >>= fun other =>
        𝒮[($ᵗ Labels : ProbComp _)] >>= fun labels => 𝒮[selectionResidual U hE labels] >>= fun r =>
          𝒮[next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels r.2)]) := by
  rw [tables_bind U hU next]
  simp only [evalSPMF_bind]
  refine congrArg _ (funext fun secrets => congrArg _ (funext fun other => congrArg _ (funext fun labels => ?_)))
  rw [← evalSPMF_bind]
  exact residual_bind_selection U hE labels
    (fun _ residual => next (privateEquiv.symm (secrets, other)) (programmed U hU secrets labels residual))
end SelectionBind
theorem selectionsOf_programmed (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (secrets : Secrets) (labels : Labels) (residual : U → HashOutput) :
    selectionsOf U hE labels (programmed U hU secrets labels residual) = selectionsOf U hE labels residual := by
  funext L
  unfold selectionsOf
  congr 1
  funext c
  apply programmed_other
  intro node heq
  exact encodingQuery_ne_cell _ secrets node labels heq
theorem selection_valid (U : Finset HashInput) (hE : encInputs ⊆ U) (labels : Labels) (table : U → HashOutput)
    (L : EncLeaf) (r : Fin (2^22) × Digest) (hr : selectionsOf U hE labels table L = some r) :
    ∃ w, decode L.1.lay r.2 = some w := by
  have h := (FirstSuccessTable.select_some_iff _ _ r.1 r.2).mp hr
  obtain ⟨-, hs⟩ := (decodeAt_eq_some L _ r.2).mp h.1
  exact Option.isSome_iff_exists.mp hs
theorem counterSearch_select (answers : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest)
    (decodeLay : HashOutput → Option Digest)
    (hdecode : ∀ answer, decodeLay answer =
      if (decode lay (answer.extractLsb' 0 128)).isSome then some (answer.extractLsb' 0 128) else none) :
    ∀ fuel start, evalWithAnswerFn answers (counterSearch lay tree leaf message start fuel) =
      (FirstSuccessTable.select decodeLay (fun i : Fin fuel =>
          answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message (start + i.val)))))).bind
        fun r => (decode lay r.2).map fun digits => (BitVec.ofNat 32 (start + r.1.val), digits) := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      simp only [counterSearch, evalWithAnswerFn_bind, eval_shortHash]
      rw [FirstSuccessTable.select]
      have h0 : answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message (start + (0 : Fin (fuel + 1)).val)))) =
          answers (.inl (.inr (pad64 (encodingInput lay tree leaf message (BitVec.ofNat 32 start))))) := by
        simp only [Fin.val_zero, Nat.add_zero, Sampling.encodingTrial]
      rw [h0, hdecode]
      generalize answers (.inl (.inr (pad64 (encodingInput lay tree leaf message (BitVec.ofNat 32 start))))) = A
      cases hd : decode lay (A.extractLsb' 0 128) with
      | some digits =>
          simp only [hd, Option.isSome_some, if_true, evalWithAnswerFn_pure, Option.bind_some, Option.map_some,
            Fin.val_zero, Nat.add_zero]
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false]
          rw [ih (start + 1)]
          have htail : (fun i : Fin fuel => answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message
              (start + (i.succ).val))))) =
              (fun i : Fin fuel => answers (.inl (.inr (Sampling.encodingTrial lay tree leaf message
                (start + 1 + i.val))))) := by
            funext i
            rw [Fin.val_succ, show start + (i.val + 1) = start + 1 + i.val by omega]
          rw [htail]
          cases FirstSuccessTable.select decodeLay (fun i : Fin fuel => answers (.inl (.inr
              (Sampling.encodingTrial lay tree leaf message (start + 1 + i.val))))) with
          | none => rfl
          | some r =>
              simp only [Option.map_some, Option.bind_some, Fin.val_succ,
                show start + (r.1.val + 1) = start + 1 + r.1.val by omega]
theorem answers_encCell (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (x : EncLeaf × Fin (2^22)) :
    answers (.inl (.inr (encCell U hE labels x).val)) = residual (encCell U hE labels x) := by
  rw [hpub]
  apply programmed_other
  intro node heq
  exact encodingQuery_ne_cell _ _ node labels heq
theorem referenceSearch_eq (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (L : EncLeaf) :
    Wots.referenceSearch answers L.toWots =
      (selectionsOf U hE labels residual L).bind fun r =>
        (decode L.1.lay r.2).map fun digits => (BitVec.ofNat 32 r.1.val, digits) := by
  have hagrees := agrees_of_programmed U hU answers labels residual hpub
  unfold Wots.referenceSearch
  rw [leafMsg_eq hagrees L]
  change evalWithAnswerFn answers (counterSearch L.1.lay L.1.tree.val L.1.leaf.val (msgLabel labels L) 0
    counterLimit) = _
  rw [counterSearch_select answers L.1.lay L.1.tree.val L.1.leaf.val (msgLabel labels L) (decodeAt L)
    (fun _ => rfl) counterLimit 0]
  unfold selectionsOf
  have hrows : (fun i : Fin counterLimit => answers (.inl (.inr (Sampling.encodingTrial L.1.lay L.1.tree.val
      L.1.leaf.val (msgLabel labels L) (0 + i.val))))) = fun c => residual (encCell U hE labels (L, c)) := by
    funext c
    rw [Nat.zero_add]
    exact answers_encCell U hU hE answers labels residual hpub (L, c)
  rw [hrows]
  simp only [Nat.zero_add]
  rfl
theorem referenceDigits_eq (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (L : EncLeaf) :
    Wots.referenceDigits answers L.toWots =
      ((selectionsOf U hE labels residual L).bind fun r => decode L.1.lay r.2).getD (Wots.dummyDigits L.1.lay) := by
  unfold Wots.referenceDigits
  rw [referenceSearch_eq U hU hE answers labels residual hpub L]
  congr 1
  cases selectionsOf U hE labels residual L with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      cases decode L.1.lay r.2 <;> rfl
theorem referenceInput_eq (U : Finset HashInput) (hU : canonInputs ⊆ U) (hE : encInputs ⊆ U)
    (answers : Answers) (labels : Labels) (residual : U → HashOutput)
    (hpub : ∀ x : U, answers (.inl (.inr x.val)) = programmed U hU (secretsOf answers) labels residual x)
    (L : EncLeaf) :
    Wots.referenceInput answers L.toWots =
      (selectionsOf U hE labels residual L).map fun r => (encCell U hE labels (L, r.1)).val := by
  have hagrees := agrees_of_programmed U hU answers labels residual hpub
  unfold Wots.referenceInput
  rw [referenceSearch_eq U hU hE answers labels residual hpub L, leafMsg_eq hagrees L]
  cases hsel : selectionsOf U hE labels residual L with
  | none => rfl
  | some r =>
      obtain ⟨w, hw⟩ := selection_valid U hE labels residual L r hsel
      simp only [Option.bind_some, hw, Option.map_some]
      rfl
end SigGolfCandidate.T3.Security.CanonEncoding
