import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingFreshRow
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableObservation
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableSplit

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingSelectionRows (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  match selection with
  | none => fun _ => FirstSuccessTable.invalid decodeEncodingOutput
  | some (index, word) => FirstSuccessTable.allowed decodeEncodingOutput index word
noncomputable def encodingSelectionAllowed (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  if ∀ coordinate, (encodingSelectionRows selection coordinate).Nonempty then encodingSelectionRows selection
  else fun _ => Finset.univ
theorem encodingSelectionAllowed_nonempty (selection : ReferenceSelection) :
    ∀ coordinate, (encodingSelectionAllowed selection coordinate).Nonempty := by
  unfold encodingSelectionAllowed
  split_ifs with hrows
  · exact hrows
  · exact fun _ => Finset.univ_nonempty
theorem encodingSelectionAllowed_fresh (selection : ReferenceSelection) (dummy : Encoding) (coordinate : Fin encodingAttemptLimit) :
    FreshEncodingSupport ((selection.map Prod.snd).getD dummy) (encodingSelectionAllowed selection coordinate) := by
  unfold encodingSelectionAllowed
  split_ifs
  · cases selection with
    | none => exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
    | some selected =>
        obtain ⟨index, word⟩ := selected
        exact firstSuccess_allowed_fresh index word coordinate
  · exact Or.inl rfl
private theorem uniformTable_rows_eq {rows rows' : Fin encodingAttemptLimit → Finset HashOutput} (h : rows = rows')
    (hrows : ∀ coordinate, (rows coordinate).Nonempty) (hrows' : ∀ coordinate, (rows' coordinate).Nonempty) :
    uniformTable rows hrows = uniformTable rows' hrows' := by
  subst h
  rfl
theorem encoding_afterSelect_complete (selection : ReferenceSelection) :
    𝒮[FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection] =
      complete (encodingSelectionAllowed selection) := by
  rw [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection)]
  have hafter : FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      FirstSuccessTable.constrained (encodingSelectionRows selection) := by
    cases selection with
    | none => rfl
    | some selected =>
        obtain ⟨index, word⟩ := selected
        rfl
  rw [hafter, FirstSuccessTable.constrained]
  split_ifs with hrows
  · rw [uniformTable_rows_eq (show encodingSelectionRows selection = encodingSelectionAllowed selection from
      (if_pos hrows).symm) hrows (encodingSelectionAllowed_nonempty selection)]
  · rw [FirstSuccessTable.full, uniformTable_rows_eq (show (fun _ => Finset.univ) = encodingSelectionAllowed selection from
      (if_neg hrows).symm) _ (encodingSelectionAllowed_nonempty selection)]
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
noncomputable def encodingFamilyAllowed (selections : ReferenceFamily) (row : EncodingRow) : Finset HashOutput :=
  encodingSelectionAllowed (selections row.1) row.2
theorem encodingFamilyAllowed_nonempty (selections : ReferenceFamily) :
    ∀ row, (encodingFamilyAllowed selections row).Nonempty :=
  fun row => encodingSelectionAllowed_nonempty (selections row.1) row.2
theorem encoding_afterSelect_uniform (selection : ReferenceSelection) :
    FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit selection =
      uniformTable (encodingSelectionAllowed selection) (encodingSelectionAllowed_nonempty selection) := by
  apply PMF.ext
  intro table
  have h := congrArg (fun law : SPMF (Fin encodingAttemptLimit → HashOutput) => law table)
    (encoding_afterSelect_complete selection)
  simpa only [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection), PMF.evalSPMF_eq, SPMF.liftM_apply] using h
theorem encoding_family_uniform (selections : ReferenceFamily) :
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).map Function.uncurry =
        uniformTable (encodingFamilyAllowed selections) (encodingFamilyAllowed_nonempty selections) := by
  simp only [FirstSuccessFamily.afterSelect, encoding_afterSelect_uniform, uniformTable_eq_product]
  exact FinitePmfProduct.uncurry (fun position coordinate =>
    PMF.uniformOfFinset (encodingSelectionAllowed (selections position) coordinate)
      (encodingSelectionAllowed_nonempty (selections position) coordinate))
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete.UniformTableSplit
open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Index Cell Answer : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
theorem join_eq_iff (table : Cell → Answer) (rows : Index → Answer) (outside : Outside embed → Answer) :
    table = join embed hinj rows outside ↔ rows = table ∘ embed ∧ outside = fun cell : Outside embed => table cell.val := by
  constructor
  · intro heq
    subst table
    constructor
    · funext index
      exact (join_embed embed hinj rows outside index).symm
    · funext cell
      exact (join_outside embed hinj rows outside cell).symm
  · rintro ⟨rfl, rfl⟩
    exact (join_split embed hinj table).symm
attribute [local irreducible] join
section Mass
attribute [local instance 10000] Classical.propDecidable
theorem bind_map_join_apply (left : PMF (Index → Answer)) (right : PMF (Outside embed → Answer)) (table : Cell → Answer) :
    (left.bind fun rows => right.map (join embed hinj rows)) table =
      left (table ∘ embed) * right (fun cell => table cell.val) := by
  simp only [PMF.bind_apply, PMF.map_apply]
  rw [tsum_eq_single (table ∘ embed)]
  · rw [tsum_eq_single (fun cell : Outside embed => table cell.val)]
    · rw [if_pos (join_split embed hinj table).symm]
    · intro outside hne
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table _ outside).mp h).2)
  · intro rows hne
    have hz : (∑' outside : Outside embed → Answer,
        if table = join embed hinj rows outside then right outside else 0) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro outside
      exact if_neg (fun h => hne ((join_eq_iff embed hinj table rows outside).mp h).1)
    rw [hz, mul_zero]
end Mass
variable [Fintype Index] [Fintype Cell] [DecidableEq Cell]
include hinj in
theorem prod_embed_mul_outside {M : Type} [CommMonoid M] (f : Cell → M) :
    (∏ index, f (embed index)) * (∏ cell : Outside embed, f cell.val) = ∏ cell, f cell := by
  letI : Fintype (Set.range embed) := Subtype.fintype (Set.range embed)
  have he : (∏ index, f (embed index)) = ∏ cell : Set.range embed, f cell.val :=
    Fintype.prod_equiv (Equiv.ofInjective embed hinj) _ _ (fun _ => rfl)
  rw [he]
  convert Fintype.prod_subtype_mul_prod_subtype (Set.range embed) f using 1
  congr 1
  exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
variable [DecidableEq Index] [Fintype Answer]
theorem product_join (left : Index → PMF Answer) (right : Outside embed → PMF Answer) :
    (FinitePmfProduct.law left).bind (fun rows => (FinitePmfProduct.law right).map (join embed hinj rows)) =
      FinitePmfProduct.law (join embed hinj left right) := by
  apply PMF.ext
  intro table
  rw [bind_map_join_apply]
  simp only [FinitePmfProduct.apply]
  have hp := prod_embed_mul_outside embed hinj (fun cell => join embed hinj left right cell (table cell))
  simpa only [join_embed, join_outside, Function.comp_def] using hp
variable [DecidableEq Answer]
omit [Fintype Cell] [DecidableEq Index] [Fintype Answer] [DecidableEq Answer] in
theorem join_nonempty (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    ∀ cell, (join embed hinj left right cell).Nonempty := by
  intro cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    rw [join_embed]
    exact hl index
  · change (join embed hinj left right (⟨cell, hc⟩ : Outside embed).val).Nonempty
    rw [join_outside]
    exact hr ⟨cell, hc⟩
theorem uniformTable_join (left : Index → Finset Answer) (right : Outside embed → Finset Answer)
    (hl : ∀ index, (left index).Nonempty) (hr : ∀ cell, (right cell).Nonempty) :
    (uniformTable left hl).bind (fun rows => (uniformTable right hr).map (join embed hinj rows)) =
      uniformTable (join embed hinj left right) (join_nonempty embed hinj left right hl hr) := by
  simp only [uniformTable_eq_product, product_join]
  apply congrArg FinitePmfProduct.law
  funext cell
  by_cases hc : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hc
    simp only [join_embed]
  · change join embed hinj _ _ (⟨cell, hc⟩ : Outside embed).val = _
    rw [join_outside]
    have hrow := join_outside embed hinj left right (⟨cell, hc⟩ : Outside embed)
    simp only [hrow]
end SphincsSecurity.Concrete.UniformTableSplit
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs UniformTableSplit.join
noncomputable def referenceEncodingAllowed (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : canonicalEncodingInputs parameter → Finset HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (encodingFamilyAllowed selections) (fun _ => Finset.univ)
theorem referenceEncodingAllowed_nonempty (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : ∀ cell, (referenceEncodingAllowed parameter messages selections cell).Nonempty :=
  UniformTableSplit.join_nonempty _ _ _ _ (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
noncomputable def referenceEncodingPrior (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : PMF (canonicalEncodingInputs parameter → HashOutput) :=
  (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit selections).bind
    (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (referenceFamilyCell parameter messages) → HashOutput)).map
      (UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
        (Function.uncurry rows)))
theorem referenceEncodingPrior_uniform (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    referenceEncodingPrior parameter messages selections =
      uniformTable (referenceEncodingAllowed parameter messages selections)
        (referenceEncodingAllowed_nonempty parameter messages selections) := by
  have h := UniformTableSplit.uniformTable_join (referenceFamilyCell parameter messages)
    (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => Finset.univ)
    (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
  rw [uniformTable_univ, ← encoding_family_uniform selections, PMF.bind_map] at h
  exact h
theorem referenceEncodingPrior_complete (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    𝒮[referenceEncodingPrior parameter messages selections] = complete (referenceEncodingAllowed parameter messages selections) := by
  rw [referenceEncodingPrior_uniform, complete_of_nonempty _ (referenceEncodingAllowed_nonempty parameter messages selections)]
theorem referenceEncodingAllowed_fresh (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter)
    (position : EncodingPosition) (hposition : AtEncodingPosition parameter cell.val position) :
    FreshEncodingSupport (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx)
      (referenceEncodingAllowed parameter messages selections cell) := by
  by_cases hc : cell ∈ Set.range (referenceFamilyCell parameter messages)
  · obtain ⟨row, rfl⟩ := hc
    have hp := atEncodingPosition_unique hposition
      (show AtEncodingPosition parameter (referenceFamilyCell parameter messages row).val row.1 from ⟨_, rfl⟩)
    subst position
    rw [referenceEncodingAllowed, UniformTableSplit.join_embed]
    exact encodingSelectionAllowed_fresh (selections row.1) (dummy row.1.lay row.1.tree row.1.leafIdx) row.2
  · have hrow := UniformTableSplit.join_outside (referenceFamilyCell parameter messages)
      (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => (Finset.univ : Finset HashOutput))
      (⟨cell, hc⟩ : UniformTableSplit.Outside (referenceFamilyCell parameter messages))
    exact Or.inl hrow
end SphincsSecurity.Concrete
end
