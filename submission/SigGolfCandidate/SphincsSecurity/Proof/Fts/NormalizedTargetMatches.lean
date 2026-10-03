import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeContinuation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeFresh
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SubsetTargetAssignment

section



namespace SphincsSecurity.Concrete
open ENNReal
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {L : Type} [Fintype L] [Nonempty L]
def LocalTo (coords : Finset IndexGroup) (g : (IndexGroup → L) → ENNReal) : Prop :=
  ∀ first second : IndexGroup → L, (∀ i ∈ coords, first i = second i) → g first = g second
noncomputable def leafAverage (g : (IndexGroup → L) → ENNReal) : ENNReal :=
  ∑ leaves : IndexGroup → L, (Fintype.card (IndexGroup → L) : ENNReal)⁻¹ * g leaves
theorem LocalTo.mono {small large : Finset IndexGroup} {g : (IndexGroup → L) → ENNReal}
    (h : LocalTo small g) (hsub : small ⊆ large) : LocalTo large g :=
  fun first second hagree => h first second (fun i hi => hagree i (hsub hi))
theorem LocalTo.const (coords : Finset IndexGroup) (value : ENNReal) :
    LocalTo (L := L) coords (fun _ => value) := fun _ _ _ => rfl
theorem LocalTo.mul {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) : LocalTo (left ∪ right) (fun leaves => g leaves * h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second (fun i hi => hagree i (Finset.mem_union_left _ hi)),
    hh first second (fun i hi => hagree i (Finset.mem_union_right _ hi))]
theorem LocalTo.add {coords : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo coords g) (hh : LocalTo coords h) : LocalTo coords (fun leaves => g leaves + h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second hagree, hh first second hagree]
theorem LocalTo.sum {ι : Type} (s : Finset ι) {coords : Finset IndexGroup} {g : ι → (IndexGroup → L) → ENNReal}
    (hg : ∀ x ∈ s, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑ x ∈ s, g x leaves) := by
  intro first second hagree
  exact Finset.sum_congr rfl (fun x hx => hg x hx first second hagree)
theorem leafAverage_add (g h : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => g leaves + h leaves) = leafAverage g + leafAverage h := by
  simp only [leafAverage, mul_add, Finset.sum_add_distrib]
theorem leafAverage_mul_left (c : ENNReal) (g : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => c * g leaves) = c * leafAverage g := by
  simp only [leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem leafAverage_sum {ι : Type} (s : Finset ι) (g : ι → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑ x ∈ s, g x leaves) = ∑ x ∈ s, leafAverage (g x) := by
  simp only [leafAverage, Finset.mul_sum]
  exact Finset.sum_comm
theorem leafAverage_const (value : ENNReal) : leafAverage (L := L) (fun _ => value) = value := by
  unfold leafAverage
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]
theorem leafAverage_mono {g h : (IndexGroup → L) → ENNReal} (hle : ∀ leaves, g leaves ≤ h leaves) :
    leafAverage g ≤ leafAverage h :=
  Finset.sum_le_sum (fun leaves _ => mul_le_mul' le_rfl (hle leaves))
theorem leafAverage_mul_of_disjoint {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) (hdisjoint : Disjoint left right) :
    leafAverage (fun leaves => g leaves * h leaves) = leafAverage g * leafAverage h := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : IndexGroup => i ∈ left) (fun _ => L)
  let A := ∀ i : {i : IndexGroup // i ∈ left}, L
  let B := ∀ i : {i : IndexGroup // i ∉ left}, L
  obtain ⟨a0⟩ : Nonempty A := inferInstance
  obtain ⟨b0⟩ : Nonempty B := inferInstance
  let g' : A → ENNReal := fun a => g (e.symm (a, b0))
  let h' : B → ENNReal := fun b => h (e.symm (a0, b))
  have hge : ∀ leaves, g leaves = g' (e leaves).1 := by
    intro leaves
    apply hg
    intro i hi
    change leaves i = (e.symm ((e leaves).1, b0)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hhe : ∀ leaves, h leaves = h' (e leaves).2 := by
    intro leaves
    apply hh
    intro i hi
    have hnot : i ∉ left := fun hl => Finset.disjoint_left.mp hdisjoint hl hi
    change leaves i = (e.symm (a0, (e leaves).2)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hnot]
  let w : ENNReal := (Fintype.card (IndexGroup → L) : ENNReal)⁻¹
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card A : ENNReal) * Fintype.card B := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hw : w * (Fintype.card A : ENNReal) * Fintype.card B = 1 := by
    rw [mul_assoc, ← hcard]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hsum : ∀ F : A × B → ENNReal, (∑ leaves : IndexGroup → L, F (e leaves)) = ∑ ab : A × B, F ab :=
    fun F => Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hgh : leafAverage (fun leaves => g leaves * h leaves) = w * ((∑ a, g' a) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge, hhe]
    rw [hsum (fun ab => g' ab.1 * h' ab.2), Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hgavg : leafAverage g = w * ((Fintype.card B : ENNReal) * ∑ a, g' a) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge]
    rw [hsum (fun ab => g' ab.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hhavg : leafAverage h = w * ((Fintype.card A : ENNReal) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hhe]
    rw [hsum (fun ab => h' ab.2), Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hgh, hgavg, hhavg]
  calc
    w * ((∑ a, g' a) * ∑ b, h' b) = (w * (Fintype.card A : ENNReal) * Fintype.card B) * (w * ((∑ a, g' a) * ∑ b, h' b)) := by
      rw [hw, one_mul]
    _ = _ := by ring
theorem leafAverage_coord (i : IndexGroup) (f : L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => f (leaves i)) =
      (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f x := by
  let e := Equiv.piSplitAt i (fun _ : IndexGroup => L)
  let R := ∀ j : {j : IndexGroup // j ≠ i}, L
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card L : ENNReal) * Fintype.card R := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold leafAverage
  rw [← Finset.mul_sum]
  have hsum : (∑ leaves : IndexGroup → L, f (leaves i)) = (Fintype.card R : ENNReal) * ∑ x : L, f x := by
    rw [← Fintype.sum_equiv e.symm (fun value : L × R => f value.1) (fun leaves => f (leaves i))
      (fun value => by simp [e, Equiv.piSplitAt])]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hsum, hcard, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  calc
    _ = (Fintype.card L : ENNReal)⁻¹ * (((Fintype.card R : ENNReal)⁻¹ * Fintype.card R) * ∑ x : L, f x) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
theorem LocalTo.coord (i : IndexGroup) (f : L → ENNReal) :
    LocalTo {i} (fun leaves : IndexGroup → L => f (leaves i)) := by
  intro first second hagree
  dsimp only
  rw [hagree i (Finset.mem_singleton_self i)]
theorem LocalTo.prod {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x)) :
    LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) := by
  intro first second hagree
  apply Finset.prod_congr rfl
  intro x hx
  exact hg x hx first second (fun i hi => hagree i (Finset.mem_biUnion.mpr ⟨x, hx, hi⟩))
theorem leafAverage_prod_coord (U : Finset IndexGroup) (f : IndexGroup → L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => ∏ i ∈ U, f i (leaves i)) =
      ∏ i ∈ U, (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f i x := by
  induction U using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert i U hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hlocal : LocalTo U (fun leaves : IndexGroup → L => ∏ j ∈ U, f j (leaves j)) := by
        have h := LocalTo.prod (L := L) U (fun j => {j}) (g := fun j leaves => f j (leaves j))
          (fun j _ => LocalTo.coord j (f j))
        simpa using h
      rw [leafAverage_mul_of_disjoint (LocalTo.coord i (f i)) hlocal
        (Finset.disjoint_singleton_left.mpr hnot), leafAverage_coord, ih]
theorem leafAverage_prod_disjoint {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x))
    (hdisjoint : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (coords x) (coords y)) :
    leafAverage (fun leaves => ∏ x ∈ s, g x leaves) = ∏ x ∈ s, leafAverage (g x) := by
  induction s using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert a s hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hrest : LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) :=
        LocalTo.prod s coords (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      have hdisj : Disjoint (coords a) (s.biUnion coords) := by
        rw [Finset.disjoint_biUnion_right]
        intro x hx
        exact hdisjoint a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
          (fun h => hnot (h ▸ hx))
      rw [leafAverage_mul_of_disjoint (hg a (Finset.mem_insert_self a s)) hrest hdisj,
        ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy hxy => hdisjoint x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]
theorem leafAverage_tsum_plain {α : Type} (g : α → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑' x, g x leaves) = ∑' x, leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
theorem LocalTo.tsum_plain {α : Type} {coords : Finset IndexGroup} {g : α → (IndexGroup → L) → ENNReal}
    (hg : ∀ x, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑' x, g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => hg x first second hagree)
def ShapeLocal (F : (IndexGroup → L) → TargetShapeVector) : Prop :=
  ∀ groups remaining, TargetShapeValid groups remaining →
    LocalTo (groupCoordinates groups ∪ remaining) (fun leaves => F leaves groups remaining)
def RateLocal (rate : (IndexGroup → L) → TargetRate) : Prop :=
  ∀ coords, LocalTo coords (fun leaves => rate leaves coords)
theorem groupCoordinates_mono {small large : Finset (Finset IndexGroup)} (h : small ⊆ large) :
    groupCoordinates small ⊆ groupCoordinates large :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h
theorem mem_groupCoordinates {groups : Finset (Finset IndexGroup)} {i : IndexGroup} :
    i ∈ groupCoordinates groups ↔ ∃ group ∈ groups, i ∈ group := by
  simp [groupCoordinates]
theorem groupCoordinates_insert (selected : Finset IndexGroup) (groups : Finset (Finset IndexGroup)) :
    groupCoordinates (insert selected groups) = selected ∪ groupCoordinates groups := by
  simp [groupCoordinates, Finset.biUnion_insert]
theorem TargetShapeValid.disjoint_step {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    Disjoint (groupCoordinates removed ∪ selected) (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) := by
  rw [Finset.disjoint_left]
  intro i hleft hright
  rcases Finset.mem_union.mp hleft with hl | hl <;> rcases Finset.mem_union.mp hright with hr | hr
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    have hsecond' := Finset.mem_sdiff.mp hsecond
    have hne : first ≠ second := fun h => hsecond'.2 (h ▸ hfirst)
    exact Finset.disjoint_left.mp (hvalid.disjoint first (hremoved hfirst) second hsecond'.1 hne) hifirst hisecond
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    exact Finset.disjoint_left.mp (hvalid.remaining first (hremoved hfirst)) hifirst (Finset.mem_sdiff.mp hr).1
  · obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    exact Finset.disjoint_left.mp (hvalid.remaining second (Finset.mem_sdiff.mp hsecond).1) hisecond (hselected hl)
  · exact (Finset.mem_sdiff.mp hr).2 hl
theorem step_coordinates_subset {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    (groupCoordinates removed ∪ selected) ∪ (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) ⊆
      groupCoordinates groups ∪ remaining := by
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | (hi | hi)
  · exact Or.inl (groupCoordinates_mono hremoved hi)
  · exact Or.inr (hselected hi)
  · exact Or.inl (groupCoordinates_mono Finset.sdiff_subset hi)
  · exact Or.inr (Finset.mem_sdiff.mp hi).1
theorem TargetShapeValid.groupCoordinates_nonempty {groups removed : Finset (Finset IndexGroup)}
    {remaining : Finset IndexGroup} (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups)
    (hne : removed ≠ ∅) : (groupCoordinates removed).Nonempty := by
  obtain ⟨group, hgroup⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi⟩ := hvalid.nonempty group (hremoved hgroup)
  exact ⟨i, mem_groupCoordinates.mpr ⟨group, hgroup, hi⟩⟩
theorem reuse_coordinates_subset {groups : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hselected : selected ⊆ remaining) :
    groupCoordinates (insert selected groups) ∪ (remaining \ selected) ⊆ groupCoordinates groups ∪ remaining := by
  rw [groupCoordinates_insert]
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | hi
  · exact Or.inr (hselected hi)
  · exact Or.inl hi
  · exact Or.inr (Finset.mem_sdiff.mp hi).1
theorem shapeLocal_query {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    (hF : ShapeLocal F) (harrival : RateLocal arrival) :
    ShapeLocal (fun leaves => targetShapeQuery (arrival leaves) (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeQuery targetArrivalStep
  apply (hF groups remaining hvalid).add
  apply LocalTo.sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have h := (harrival (groupCoordinates removed)).mul
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _)))
  refine h.mono ?_
  have hs := step_coordinates_subset (groups := groups) (remaining := remaining) (selected := ∅) hsub (Finset.empty_subset _)
  simpa only [Finset.union_empty, Finset.sdiff_empty] using hs
theorem shapeLocal_signing {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) (hF : ShapeLocal F) (hrate : RateLocal rate) :
    ShapeLocal (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeSigning targetFreshStep targetReuseStep
  refine ((hF groups remaining hvalid).add ?_).add ?_
  · apply LocalTo.sum
    intro removed hremoved
    apply LocalTo.sum
    intro selected hselected
    have hsubG := Finset.mem_powerset.mp hremoved
    have hsubR := Finset.mem_powerset.mp hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      exact LocalTo.const _ 0
    · simp only [hempty, if_false]
      exact ((hrate _).mul (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))).mono
        (step_coordinates_subset hsubG hsubR)
  · have hsum : LocalTo (groupCoordinates groups ∪ remaining) (fun leaves =>
        ∑ selected ∈ remaining.powerset.erase ∅, F leaves (insert selected groups) (remaining \ selected)) := by
      apply LocalTo.sum
      intro selected hselected
      have hne := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2
      exact (hF _ _ (hvalid.reuse hne hsub)).mono (reuse_coordinates_subset hsub)
    exact ((LocalTo.const ∅ reuse).mul hsum).mono (by rw [Finset.empty_union])
noncomputable def averagedShape (F : (IndexGroup → L) → TargetShapeVector) : TargetShapeVector :=
  fun groups remaining => leafAverage (fun leaves => F leaves groups remaining)
theorem leafAverage_query_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeQuery (arrival leaves) (F leaves)))
      (targetShapeQuery (constRate average) (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeQuery targetArrivalStep constRate
  rw [leafAverage_add, leafAverage_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have hdisjoint := hvalid.disjoint_step hsub (Finset.empty_subset remaining)
  simp only [Finset.union_empty, Finset.sdiff_empty] at hdisjoint
  rw [leafAverage_mul_of_disjoint (harrival _)
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _))) hdisjoint]
  exact mul_le_mul' (haverage _ (hvalid.groupCoordinates_nonempty hsub (Finset.mem_erase.mp hremoved).1)) le_rfl
theorem leafAverage_signing_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)))
      (targetShapeSigning (constRate average) reuse (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeSigning targetFreshStep constRate
  rw [leafAverage_add, leafAverage_add, leafAverage_mul_left, leafAverage_sum]
  apply add_le_add (add_le_add le_rfl _) _
  · apply Finset.sum_le_sum
    intro removed hremoved
    rw [leafAverage_sum]
    apply Finset.sum_le_sum
    intro selected hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      rw [leafAverage_const]
    · simp only [hempty, if_false]
      rw [leafAverage_mul_of_disjoint (hrate _)
        (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))
        (hvalid.disjoint_step (Finset.mem_powerset.mp hremoved) (Finset.mem_powerset.mp hselected))]
      apply mul_le_mul' (haverage _ _) le_rfl
      by_cases hr : removed = ∅
      · have hs : selected ≠ ∅ := fun h => hempty ⟨hr, h⟩
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact ⟨i, Finset.mem_union_right _ hi⟩
      · obtain ⟨i, hi⟩ := hvalid.groupCoordinates_nonempty (Finset.mem_powerset.mp hremoved) hr
        exact ⟨i, Finset.mem_union_left _ hi⟩
  · unfold targetReuseStep
    rw [leafAverage_sum]
theorem leafAverage_query_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) (queries : Nat) :
    ShapeLocal (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)))
        ((targetShapeQuery (constRate average))^[queries] (averagedShape F)) := by
  induction queries with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_query ih.1 harrival,
        (leafAverage_query_le ih.1 harrival haverage).trans (targetShapeQuery_mono _ ih.2)⟩
theorem leafAverage_signing_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) (signings : Nat) :
    ShapeLocal (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)))
        ((targetShapeSigning (constRate average) reuse)^[signings] (averagedShape F)) := by
  induction signings with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_signing reuse ih.1 hrate,
        (leafAverage_signing_le reuse ih.1 hrate haverage).trans (targetShapeSigning_mono _ reuse ih.2)⟩
theorem leafAverage_targetShapeEnvelope_le {F : (IndexGroup → L) → TargetShapeVector}
    {rate arrival : (IndexGroup → L) → TargetRate} (reuse : ENNReal) {uniform average : ENNReal}
    (hF : ShapeLocal F) (hrate : RateLocal rate) (harrival : RateLocal arrival)
    (huniform : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ uniform)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average)
    (queries signings : Nat) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeEnvelope (rate leaves) reuse (arrival leaves) queries signings (F leaves)))
      (targetShapeEnvelope (constRate uniform) reuse (constRate average) queries signings (averagedShape F)) := by
  have hq := leafAverage_query_iterate_le hF harrival haverage queries
  have hs := leafAverage_signing_iterate_le reuse hq.1 hrate huniform signings
  exact hs.2.trans (targetShapeSigning_iterate_mono _ reuse signings hq.2)
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      admissibleProbability *
        ∑' target, Pr[= target | signerViewSample] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]
theorem expected_uniformHashOutput_view_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * weight (hashOutputFewTimeView output)) =
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      weight (hashOutputFewTimeView output) =
        ∑' target, if hashOutputFewTimeView output = target then weight target else 0 := by
    rw [tsum_eq_single (hashOutputFewTimeView output) (fun other hother => if_neg (Ne.symm hother)), if_pos rfl]
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => hashOutputFewTimeView output = target | ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      rw [probEvent_uniformHashOutput_view (fun view => view = target), probEvent_eq_eq_probOutput]
theorem expected_uniformHashOutput_admissible_weight_le_uniform (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) ≤
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  rw [← expected_uniformHashOutput_view_weight]
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  split_ifs <;> simp
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
noncomputable def openedLeaves (source : FewTimeView) : Finset FtsLeaf := Finset.univ.image source.2
theorem mem_openedLeaves_iff {source : FewTimeView} {leaf : FtsLeaf} :
    leaf ∈ openedLeaves source ↔ leaf ∈ Set.range source.2 := by
  simp [openedLeaves]
theorem card_openedLeaves_le (source : FewTimeView) : (openedLeaves source).card ≤ ftsOpenings := by
  unfold openedLeaves
  exact Finset.card_image_le.trans (by simp)
theorem sourceSubsetMatch_leaves (index : Index) (leaves : IndexGroup → FtsLeaf) (source : FewTimeView)
    (required : Finset IndexGroup) (hne : required.Nonempty) :
    (sourceSubsetMatch (index, leaves) source required : ENNReal) =
      (if source.1 = index then 1 else 0) *
        ∏ i ∈ required, (if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0) := by
  unfold sourceSubsetMatch sourceTreeMatch
  rw [Nat.cast_prod]
  by_cases hindex : source.1 = index
  · simp only [hindex, true_and, if_true, one_mul, mem_openedLeaves_iff]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  · obtain ⟨i, hi⟩ := hne
    simp only [hindex, false_and, if_false, zero_mul, Nat.cast_zero]
    exact Finset.prod_eq_zero hi rfl
theorem sourceSubsetMatch_local (index : Index) (source : FewTimeView) (required : Finset IndexGroup) :
    LocalTo required (fun leaves : IndexGroup → FtsLeaf =>
      (sourceSubsetMatch (index, leaves) source required : ENNReal)) := by
  intro first second hagree
  dsimp only
  unfold sourceSubsetMatch sourceTreeMatch
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hagree i hi]
end SphincsSecurity.Concrete
end

section



set_option autoImplicit true
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]
noncomputable def coverNormalization : ENNReal := (Fintype.card FtsLeaf : ENNReal) / ftsOpenings
theorem coverNormalization_ne_top : coverNormalization ≠ ⊤ :=
  ENNReal.div_ne_top (by simp) (by simp [ftsOpenings])
theorem coverNormalization_ne_zero : coverNormalization ≠ 0 :=
  ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩
noncomputable def coverScale : ENNReal := (ftsOpenings : ENNReal) / Fintype.card FtsLeaf
theorem coverNormalization_mul_coverScale : coverNormalization * coverScale = 1 := by
  unfold coverNormalization coverScale
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
        (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
    _ = 1 := by
      rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp), one_mul]
noncomputable def normalizedSourceSubsetMatch (target source : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  coverNormalization ^ required.card * (sourceSubsetMatch target source required : ENNReal)
theorem normalizedSourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_prod, Finset.card_biUnion hdisjoint]
noncomputable def signerRate (target : FewTimeView) : TargetRate := fun coords =>
  ∑' source, Pr[= source | signerViewSample] * normalizedSourceSubsetMatch target source coords
noncomputable def arrivalRate (target : FewTimeView) : TargetRate := fun coords =>
  admissibleProbability * signerRate target coords
theorem expected_signer_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' source, Pr[= source | signerViewSample] *
      ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      signerRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint, signerRate]
theorem expected_hash_normalizedSourceSubsetMatch (target : FewTimeView) (coords : Finset IndexGroup) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        normalizedSourceSubsetMatch target (hashOutputFewTimeView output) coords else 0)) =
      arrivalRate target coords := by
  rw [expected_uniformHashOutput_admissible_weight (fun source => normalizedSourceSubsetMatch target source coords)]
  rfl
theorem expected_hash_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      arrivalRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint]
  exact expected_hash_normalizedSourceSubsetMatch target _
theorem LocalTo.tsum {α : Type} {coords : Finset IndexGroup} (weight : α → ENNReal)
    {g : α → (IndexGroup → FtsLeaf) → ENNReal} (hg : ∀ x, LocalTo coords (g x)) :
    LocalTo coords (fun leaves => ∑' x, weight x * g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => by rw [hg x first second hagree])
theorem leafAverage_tsum {α : Type} (weight : α → ENNReal) (g : α → (IndexGroup → FtsLeaf) → ENNReal) :
    leafAverage (fun leaves => ∑' x, weight x * g x leaves) = ∑' x, weight x * leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring
theorem normalizedSourceSubsetMatch_local (index : Index) (source : FewTimeView) (coords : Finset IndexGroup) :
    LocalTo coords (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) := by
  intro first second hagree
  dsimp only
  unfold normalizedSourceSubsetMatch
  have h := sourceSubsetMatch_local index source coords first second hagree
  dsimp only at h
  rw [h]
theorem leafAverage_normalizedSourceSubsetMatch_le (index : Index) (source : FewTimeView)
    (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) ≤
      if source.1 = index then 1 else 0 := by
  unfold normalizedSourceSubsetMatch
  simp only [sourceSubsetMatch_leaves index _ source coords hne]
  have hrewrite : (fun leaves : IndexGroup → FtsLeaf => coverNormalization ^ coords.card *
      ((if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0)) =
      fun leaves => (coverNormalization ^ coords.card * if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0 := by
    funext leaves
    ring
  have hprod := leafAverage_prod_coord (L := FtsLeaf) coords
    (fun _ leaf => if leaf ∈ openedLeaves source then (1 : ENNReal) else 0)
  rw [hrewrite, leafAverage_mul_left, hprod]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hindex : source.1 = index
  · simp only [hindex, if_true, mul_one]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_one'
    intro i _
    have hopened : ((openedLeaves source).card : ENNReal) ≤ ftsOpenings := by
      exact_mod_cast card_openedLeaves_le source
    calc
      coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ((openedLeaves source).card : ENNReal)) ≤
          coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ftsOpenings) := by gcongr
      _ = 1 := by
        unfold coverNormalization
        rw [div_eq_mul_inv]
        calc
          _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
              (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
          _ = 1 := by
            rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp),
              one_mul]
  · simp only [hindex, if_false, mul_zero, zero_mul, le_refl]
theorem signerRate_local (index : Index) : RateLocal (fun leaves => signerRate (index, leaves)) :=
  fun coords => LocalTo.tsum _ (fun source => normalizedSourceSubsetMatch_local index source coords)
theorem arrivalRate_local (index : Index) : RateLocal (fun leaves => arrivalRate (index, leaves)) := by
  intro coords first second hagree
  show admissibleProbability * signerRate (index, first) coords = admissibleProbability * signerRate (index, second) coords
  have h := signerRate_local index coords first second hagree
  dsimp only at h
  rw [h]
theorem leafAverage_signerRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => signerRate (index, leaves) coords) ≤ (Fintype.card Index : ENNReal)⁻¹ := by
  unfold signerRate
  rw [leafAverage_tsum]
  calc
    _ ≤ ∑' source, Pr[= source | signerViewSample] * (if source.1 = index then 1 else 0) :=
      ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl
        (leafAverage_normalizedSourceSubsetMatch_le index source coords hne))
    _ = _ := by
      rw [← probEvent_signerView_index index, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro source
      split_ifs <;> simp
theorem leafAverage_arrivalRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => arrivalRate (index, leaves) coords) ≤ cachedIndexRate := by
  unfold arrivalRate
  rw [leafAverage_mul_left]
  exact mul_le_mul' le_rfl (leafAverage_signerRate_le index coords hne)
end SphincsSecurity.Concrete
end
