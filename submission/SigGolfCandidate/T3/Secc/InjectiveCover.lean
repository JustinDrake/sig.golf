import SigGolfCandidate.T3.Secc.WeightedPrivateSelection

/-! An occurrence-assignment forecast that retains the falling factorial.
Assignments choose distinct opening occurrences within one BPORS coordinate.
Opening values themselves may repeat, and may have arbitrary joint laws. -/

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]

/-- Every assignment is an injection into opening occurrences. Repeated leaf
values at different occurrences are allowed and conservatively overcounted. -/
noncomputable def score (values : Source → Value) (target : Target → Value) : ENNReal :=
  ∑ embedding : Target ↪ Source,
    if (fun slot => values (embedding slot)) = target then 1 else 0

theorem score_card (values : Source → Value) (target : Target → Value) :
    score values target =
      (Fintype.card {embedding : Target ↪ Source //
        (fun slot => values (embedding slot)) = target} : ENNReal) := by
  classical
  simp [score, Fintype.card_subtype]

/-- Distinct covered target leaves have distinct occurrence witnesses. -/
theorem one_le_score (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) (hcovered : ∀ slot, ∃ source, values source = target slot) :
    1 ≤ score values target := by
  classical
  choose chosen hchosen using hcovered
  let embedding : Target ↪ Source := ⟨chosen, fun first second heq =>
    hinj ((hchosen first).symm.trans ((congrArg values heq).trans (hchosen second)))⟩
  have hmatch : (fun slot => values (embedding slot)) = target := funext hchosen
  have h := Finset.single_le_sum
    (f := fun e : Target ↪ Source =>
      if (fun slot => values (e slot)) = target then (1 : ENNReal) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ embedding)
  simpa only [hmatch, if_true, score] using h

/-- Averaging a fresh target gives the exact number of injective occurrence
assignments. No distributional assumption about the opening values is used. -/
theorem average_score (values : Source → Value) :
    finiteAverage (fun target : Target → Value => score values target) =
      ((Fintype.card Source).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal) ^ Fintype.card Target := by
  classical
  unfold finiteAverage score
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fun, Nat.cast_pow]

/-- For an injective target, any choice from the individual leaf fibers is
already an injective occurrence assignment. -/
noncomputable def matchingEquiv (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) :
    {embedding : Target ↪ Source // (fun slot => values (embedding slot)) = target} ≃
      (∀ slot : Target, {source : Source // values source = target slot}) where
  toFun embedding slot := ⟨embedding.val slot, congrFun embedding.property slot⟩
  invFun choices := ⟨⟨fun slot => (choices slot).val,
    fun first second heq => hinj ((choices first).property.symm.trans
      ((congrArg values heq).trans (choices second).property))⟩,
    funext (fun slot => (choices slot).property)⟩
  left_inv embedding := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    rfl
  right_inv choices := by
    funext slot
    rfl

theorem score_eq_fibers (values : Source → Value) (target : Target → Value)
    (hinj : Function.Injective target) :
    score values target =
      ∏ slot, (Fintype.card {source : Source // values source = target slot} : ENNReal) := by
  rw [score_card, Fintype.card_congr (matchingEquiv values target hinj),
    Fintype.card_pi, Nat.cast_prod]

def fiberSumEquiv (oldValues : Source → Value) (newValues : New → Value) (value : Value) :
    {source : Source ⊕ New // Sum.elim oldValues newValues source = value} ≃
      ({source : Source // oldValues source = value} ⊕
        {source : New // newValues source = value}) where
  toFun source := match source with
    | ⟨.inl source, h⟩ => .inl ⟨source, h⟩
    | ⟨.inr source, h⟩ => .inr ⟨source, h⟩
  invFun source := match source with
    | .inl source => ⟨.inl source.val, source.property⟩
    | .inr source => ⟨.inr source.val, source.property⟩
  left_inv source := by rcases source with ⟨source, h⟩; cases source <;> rfl
  right_inv source := by cases source <;> rfl

theorem fiber_card_sum (oldValues : Source → Value) (newValues : New → Value) (value : Value) :
    (Fintype.card {source : Source ⊕ New // Sum.elim oldValues newValues source = value} : ENNReal) =
      (Fintype.card {source : Source // oldValues source = value} : ENNReal) +
        (Fintype.card {source : New // newValues source = value} : ENNReal) := by
  rw [Fintype.card_congr (fiberSumEquiv oldValues newValues value), Fintype.card_sum, Nat.cast_add]

/-- Exact one-source growth, partitioned by the target slots filled by old
versus new openings. All coefficients remain nonnegative. This recurrence is
valid for the actual distinct target and keeps its injective birth average. -/
theorem score_sum (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) (hinj : Function.Injective target) :
    score (Sum.elim oldValues newValues) target =
      ∑ selected : Finset Target,
        score oldValues (fun slot : selected => target slot.val) *
          score newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) := by
  classical
  rw [score_eq_fibers _ _ hinj]
  simp_rw [fiber_card_sum]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro selected _
  have hold : Function.Injective (fun slot : selected => target slot.val) :=
    fun first second h => Subtype.ext (hinj h)
  have hnew : Function.Injective (fun slot : (selectedᶜ : Finset Target) => target slot.val) :=
    fun first second h => Subtype.ext (hinj h)
  rw [score_eq_fibers oldValues (fun slot : selected => target slot.val) hold,
    score_eq_fibers newValues (fun slot : (selectedᶜ : Finset Target) => target slot.val) hnew]
  exact congrArg₂ (fun a b : ENNReal => a * b)
    (Finset.prod_coe_sort selected
      (fun slot => (Fintype.card {source : Source // oldValues source = target slot} : ENNReal))).symm
    (Finset.prod_coe_sort (selectedᶜ : Finset Target)
      (fun slot => (Fintype.card {source : New // newValues source = target slot} : ENNReal))).symm

/-- The three-opening BPORS scale is (3r)_3, rather than the cubic relaxation.
This holds for arbitrary values attached to the r previous source records. -/
theorem three_opening_average (records : Nat) (values : Fin records × Fin 3 → Fin 128) :
    finiteAverage (fun target : Fin 3 → Fin 128 => score values target) =
      ((3 * records).descFactorial 3 : ENNReal) / (128 : ENNReal)^3 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, Nat.cast_ofNat] using
    (average_score (Target := Fin 3) values)

/-- The same occurrence construction supplies the two-opening near case. -/
theorem two_opening_average (records : Nat) (values : Fin records × Fin 3 → Fin 128) :
    finiteAverage (fun target : Fin 2 → Fin 128 => score values target) =
      ((3 * records).descFactorial 2 : ENNReal) / (128 : ENNReal)^2 := by
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm, Nat.cast_ofNat] using
    (average_score (Target := Fin 2) values)

end SigGolfCandidate.T3.BPORS.InjectiveCover
