import SigGolfCandidate.T3.Secc.InjectiveCoverSum

namespace SigGolfCandidate.T3.BPORS.InjectiveCover
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable {Target Source New Value : Type}
variable [Fintype Target] [Fintype Source] [Fintype New] [Fintype Value]
variable [DecidableEq Target] [DecidableEq Source] [DecidableEq New] [DecidableEq Value]

theorem score_source_le (embed : Source ↪ New) (oldValues : Source → Value)
    (newValues : New → Value) (target : Target → Value)
    (hvalues : ∀ source, newValues (embed source) = oldValues source) :
    score oldValues target ≤ score newValues target := by
  classical
  let liftMatch :
      {e : Target ↪ Source // (fun slot => oldValues (e slot)) = target} →
      {e : Target ↪ New // (fun slot => newValues (e slot)) = target} := fun e =>
    ⟨e.val.trans embed, funext (fun slot => (hvalues (e.val slot)).trans (congrFun e.property slot))⟩
  have hinj : Function.Injective liftMatch := by
    intro first second h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro slot
    apply embed.injective
    exact congrArg (fun e => e.val slot) h
  rw [score_card, score_card]
  exact_mod_cast Fintype.card_le_of_injective liftMatch hinj

theorem score_append_mono (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score oldValues target ≤ score (Sum.elim oldValues newValues) target :=
  score_source_le Function.Embedding.inl oldValues (Sum.elim oldValues newValues) target (fun _ => rfl)

theorem score_ne_top (values : Source → Value) (target : Target → Value) :
    score values target ≠ ⊤ := by
  rw [score_card]
  exact ENNReal.natCast_ne_top _

noncomputable def increment (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) : ENNReal :=
  score (Sum.elim oldValues newValues) target - score oldValues target

theorem before_add_increment (oldValues : Source → Value) (newValues : New → Value)
    (target : Target → Value) :
    score oldValues target + increment oldValues newValues target =
      score (Sum.elim oldValues newValues) target :=
  add_tsub_cancel_of_le (score_append_mono oldValues newValues target)

theorem finiteAverage_add {A : Type} [Fintype A] (first second : A → ENNReal) :
    finiteAverage (fun x => first x + second x) = finiteAverage first + finiteAverage second := by
  simp only [finiteAverage, Finset.sum_add_distrib, div_eq_mul_inv, add_mul]

/-- The average growth is the difference of the exact falling-factorial
counts. This is independent of all old and new opening values. -/
theorem average_increment [Nonempty Value] (oldValues : Source → Value)
    (newValues : New → Value) :
    finiteAverage (fun target : Target → Value => increment oldValues newValues target) =
      (((Fintype.card Source + Fintype.card New).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal)^Fintype.card Target) -
      (((Fintype.card Source).descFactorial (Fintype.card Target) : ENNReal) /
        (Fintype.card Value : ENNReal)^Fintype.card Target) := by
  have hsum : finiteAverage (fun target : Target → Value => score oldValues target) +
      finiteAverage (fun target : Target → Value => increment oldValues newValues target) =
        finiteAverage (fun target : Target → Value => score (Sum.elim oldValues newValues) target) := by
    rw [← finiteAverage_add]
    congr 1
    funext target
    exact before_add_increment oldValues newValues target
  have hcard : (Fintype.card Value : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfinite : finiteAverage (fun target : Target → Value => score oldValues target) ≠ ⊤ := by
    rw [average_score]
    exact ENNReal.div_ne_top (by finiteness) (pow_ne_zero _ hcard)
  have heq := congrArg (fun value => value -
      finiteAverage (fun target : Target → Value => score oldValues target)) hsum
  rw [ENNReal.add_sub_cancel_left hfinite] at heq
  simpa only [average_score, Fintype.card_sum] using heq

/-- An eligibility test can inspect the whole selected digest, for example
requiring the target index and bucket. Nonmatching selections expose nothing. -/
noncomputable def selectionGain (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (output : HashOutput) : ENNReal :=
  if eligible output then increment oldValues (newValues output) target else 0

noncomputable def afterSelection (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (selected : Option HashOutput) : ENNReal :=
  selected.elim (score oldValues target) (fun output =>
    if eligible output then score (Sum.elim oldValues (newValues output)) target
    else score oldValues target)

theorem afterSelection_eq (oldValues : Source → Value)
    (newValues : HashOutput → New → Value) (target : Target → Value)
    (eligible : HashOutput → Bool) (selected : Option HashOutput) :
    afterSelection oldValues newValues target eligible selected =
      score oldValues target + selected.elim 0 (selectionGain oldValues newValues target eligible) := by
  cases selected with
  | none => simp only [afterSelection, Option.elim_none, add_zero]
  | some output =>
      simp only [afterSelection, selectionGain, Option.elim_some]
      cases h : eligible output with
      | false => simp only [h, Bool.false_eq_true, if_false, add_zero]
      | true =>
          simp only [h, if_true]
          exact (before_add_increment oldValues (newValues output) target).symm

/-- One actual fresh-nonce signing request grows the occurrence forecast only
by the fresh accepted-source price and the weighted cache-reuse contribution.
The previous forecast is retained on rejection and on ineligible outputs. -/
theorem signing_update_le (cache : T3.Cache) (message : Message)
    (state : Security.LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl message)) = none)
    (oldValues : Source → Value) (newValues : HashOutput → New → Value)
    (target : Target → Value) (eligible : HashOutput → Bool) :
    expectedValue (Security.LazyPrivate.run (Security.signingRecord cache message) state)
      (fun result => afterSelection oldValues newValues target eligible result.1.2) ≤
      score oldValues target +
        (freshPrice (selectionGain oldValues newValues target eligible) +
          cacheWeight Sampling.digestDecode (selectionGain oldValues newValues target eligible) state.2 /
            (2 : ENNReal)^128) := by
  simp_rw [afterSelection_eq]
  rw [expectedValue_add]
  apply add_le_add
  · exact expectedValue_le_of_le _ (fun _ => le_rfl)
  · exact Security.LazyPrivate.signing_weight_le cache message state hfresh
      (selectionGain oldValues newValues target eligible)

end SigGolfCandidate.T3.BPORS.InjectiveCover
