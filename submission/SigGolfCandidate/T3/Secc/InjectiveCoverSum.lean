import SigGolfCandidate.T3.Secc.InjectiveCover

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]

abbrev SplitEmbedding := Σ selected : Finset Target,
  (selected ↪ Source) × ((selectedᶜ : Finset Target) ↪ New)

noncomputable def oldSlots (embedding : Target ↪ Source ⊕ New) : Finset Target :=
  Finset.univ.filter fun slot => (embedding slot).isLeft

theorem mem_oldSlots (embedding : Target ↪ Source ⊕ New) (slot : Target) :
    slot ∈ oldSlots embedding ↔ (embedding slot).isLeft := by simp [oldSlots]

noncomputable def splitOld (embedding : Target ↪ Source ⊕ New) : oldSlots embedding ↪ Source where
  toFun slot := (embedding slot.val).getLeft ((mem_oldSlots embedding slot.val).mp slot.property)
  inj' := by
    intro first second h
    apply Subtype.ext
    apply embedding.injective
    have he := congrArg (Sum.inl (β := New)) h
    simpa only [Sum.inl_getLeft] using he

noncomputable def splitNew (embedding : Target ↪ Source ⊕ New) :
    ((oldSlots embedding)ᶜ : Finset Target) ↪ New where
  toFun slot := (embedding slot.val).getRight (Sum.not_isLeft.mp
    (fun h => (Finset.mem_compl.mp slot.property) ((mem_oldSlots embedding slot.val).mpr h)))
  inj' := by
    intro first second h
    apply Subtype.ext
    apply embedding.injective
    have he := congrArg (Sum.inr (α := Source)) h
    simpa only [Sum.inr_getRight] using he

noncomputable def splitEmbedding (embedding : Target ↪ Source ⊕ New) :
    SplitEmbedding (Target := Target) (Source := Source) (New := New) :=
  ⟨oldSlots embedding, splitOld embedding, splitNew embedding⟩

noncomputable def mergeEmbedding (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    Target ↪ Source ⊕ New where
  toFun slot := if h : slot ∈ parts.1 then .inl (parts.2.1 ⟨slot, h⟩)
    else .inr (parts.2.2 ⟨slot, Finset.mem_compl.mpr h⟩)
  inj' := by
    intro first second heq
    dsimp only at heq
    split_ifs at heq with hfirst hsecond hsecond
    · exact congrArg Subtype.val (parts.2.1.injective (Sum.inl.inj heq))
    · exact congrArg Subtype.val (parts.2.2.injective (Sum.inr.inj heq))

theorem oldSlots_merge (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    oldSlots (mergeEmbedding parts) = parts.1 := by
  ext slot
  by_cases h : slot ∈ parts.1 <;> simp [oldSlots, mergeEmbedding, h]

theorem merge_split (embedding : Target ↪ Source ⊕ New) :
    mergeEmbedding (splitEmbedding embedding) = embedding := by
  apply Function.Embedding.ext
  intro slot
  by_cases h : slot ∈ oldSlots embedding
  · simp only [mergeEmbedding, splitEmbedding, Function.Embedding.coeFn_mk, h,
      dite_true, splitOld, Sum.inl_getLeft]
  · simp only [mergeEmbedding, splitEmbedding, Function.Embedding.coeFn_mk, h,
      dite_false, splitNew, Sum.inr_getRight]

theorem merge_injective : Function.Injective
    (mergeEmbedding (Target := Target) (Source := Source) (New := New)) := by
  rintro ⟨left, oldLeft, newLeft⟩ ⟨right, oldRight, newRight⟩ heq
  have hsets : left = right := by
    have h := congrArg oldSlots heq
    simpa only [oldSlots_merge] using h
  subst right
  have hold : oldLeft = oldRight := by
    apply Function.Embedding.ext
    intro slot
    have h := congrArg (fun e : Target ↪ Source ⊕ New => e slot.val) heq
    simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, slot.property, dite_true,
      Sum.inl.injEq] using h
  have hnew : newLeft = newRight := by
    apply Function.Embedding.ext
    intro slot
    have h := congrArg (fun e : Target ↪ Source ⊕ New => e slot.val) heq
    simpa only [mergeEmbedding, Function.Embedding.coeFn_mk,
      Finset.mem_compl.mp slot.property, dite_false, Sum.inr.injEq] using h
  subst oldRight
  subst newRight
  rfl

noncomputable def sumEmbeddingEquiv :
    SplitEmbedding (Target := Target) (Source := Source) (New := New) ≃
      (Target ↪ Source ⊕ New) :=
  Equiv.ofBijective mergeEmbedding ⟨merge_injective, fun embedding =>
    ⟨splitEmbedding embedding, merge_split embedding⟩⟩

theorem merge_matches (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value)
    (parts : SplitEmbedding (Target := Target) (Source := Source) (New := New)) :
    (fun slot => Sum.elim oldValues newValues (mergeEmbedding parts slot)) = target ↔
      ((fun slot : parts.1 => oldValues (parts.2.1 slot)) = (fun slot => target slot.val) ∧
       (fun slot : (parts.1ᶜ : Finset Target) => newValues (parts.2.2 slot)) =
         (fun slot => target slot.val)) := by
  constructor
  · intro h
    constructor
    · funext slot
      have heq := congrFun h slot.val
      simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, slot.property, dite_true,
        Sum.elim_inl] using heq
    · funext slot
      have heq := congrFun h slot.val
      simpa only [mergeEmbedding, Function.Embedding.coeFn_mk,
        Finset.mem_compl.mp slot.property, dite_false, Sum.elim_inr] using heq
  · rintro ⟨hold, hnew⟩
    funext slot
    by_cases h : slot ∈ parts.1
    · simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, h, dite_true, Sum.elim_inl] using
        congrFun hold ⟨slot, h⟩
    · simpa only [mergeEmbedding, Function.Embedding.coeFn_mk, h, dite_false, Sum.elim_inr] using
        congrFun hnew ⟨slot, Finset.mem_compl.mpr h⟩

/-- The source-splitting recurrence is exact even for targets with repeated
values. This permits averaging it over the whole fresh target space, while
retaining (3r)_3 rather than relaxing to (3r)^3. -/
theorem score_sum_all (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score (Sum.elim oldValues newValues) target =
      ∑ selected : Finset Target,
        score oldValues (fun slot : selected => target slot.val) *
          score newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) := by
  classical
  rw [score, ← (sumEmbeddingEquiv (Target := Target) (Source := Source) (New := New)).sum_comp]
  change (∑ parts : SplitEmbedding (Target := Target) (Source := Source) (New := New),
    if (fun slot => Sum.elim oldValues newValues (mergeEmbedding parts slot)) = target then
      (1 : ENNReal) else 0) = _
  simp_rw [merge_matches]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, score, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro old _
  apply Finset.sum_congr rfl
  intro fresh _
  split_ifs <;> simp_all

end SigGolfCandidate.T3.BPORS.InjectiveCover
