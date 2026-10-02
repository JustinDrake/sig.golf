import SigGolfCandidate.T3.Secc.CaseCScore

/-!
# Stream CC: the near score (20 of the 21 openings covered)

For a missing opening `(missing, omitted)` (coordinate and raw leaf slot) the near term of a target `N` against the
exposures `X` multiplies the full three-leaf occurrence score of every other coordinate with the two-leaf occurrence
score (`omitted` removed) of the missing coordinate; the **near score** sums the 21 near terms (SEC's `NearCovered`
shape, with exact injective counting):

* `one_le_nearTermAt`: if `N`'s leaves are distinct and every opening except `(missing, omitted)` is exposed, the
  near term is at least one;
* `nearScore_append_mono`: the near score only grows when exposures are appended;
* `average_nearScore`: averaged over a uniform target it is exactly `fullNearPrice (labels X) / 2^128`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Injective occurrence assignments of the two leaves of `target` other than `omitted`, at `(i, c, b)`. -/
noncomputable def coordNearScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) (omitted : Fin 3) : ENNReal :=
  BPORS.InjectiveCover.score (slotValue X i c b) (omitted.removeNth target)

/-- The near term of `N` for the missing opening `(missing, omitted)`. -/
noncomputable def nearTermAt (X : List HashOutput) (N : HashOutput) (missing : Fin 7) (omitted : Fin 3) : ENNReal :=
  if digestGate N=true then
    ∏ c : Fin 7, if c = missing then coordNearScore X (outIdx N) c (outBucket N c) (outLeaves N c) omitted
      else coordScore X (outIdx N) c (outBucket N c) (outLeaves N c)
  else 0

/-- **The near score**: the sum of the 21 near terms. -/
noncomputable def nearScore (X : List HashOutput) (N : HashOutput) : ENNReal :=
  ∑ missing : Fin 7, ∑ omitted : Fin 3, nearTermAt X N missing omitted

/-! ## Near-covered targets score at least one -/

theorem one_le_nearTermAt (X : List HashOutput) (N : HashOutput) (missing : Fin 7) (omitted : Fin 3)
    (hinj : ∀ c, Function.Injective (outLeaves N c)) (hgate : digestGate N=true)
    (hcov : ∀ c j, (c, j) ≠ (missing, omitted) →
      ∃ s : Slot X (outIdx N) c (outBucket N c), slotValue X (outIdx N) c (outBucket N c) s = outLeaves N c j) :
    1 ≤ nearTermAt X N missing omitted := by
  simp only [nearTermAt,hgate,if_true]
  apply Finset.one_le_prod''
  intro c
  split_ifs with hc
  · subst hc
    apply BPORS.InjectiveCover.one_le_score
    · exact (hinj c).comp Fin.succAbove_right_injective
    · intro k
      exact hcov c (omitted.succAbove k) (fun h => Fin.succAbove_ne omitted k (Prod.mk.inj h).2)
  · exact BPORS.InjectiveCover.one_le_score _ _ (hinj c) fun j => hcov c j (fun h => hc (Prod.mk.inj h).1)

theorem nearTermAt_le_nearScore (X : List HashOutput) (N : HashOutput) (missing : Fin 7) (omitted : Fin 3) :
    nearTermAt X N missing omitted ≤ nearScore X N := by
  unfold nearScore
  calc
    nearTermAt X N missing omitted ≤ ∑ omitted' : Fin 3, nearTermAt X N missing omitted' :=
      Finset.single_le_sum (f := fun o => nearTermAt X N missing o) (fun _ _ => bot_le) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun m => ∑ o : Fin 3, nearTermAt X N m o) (fun _ _ => bot_le)
      (Finset.mem_univ missing)

/-! ## Monotonicity -/

theorem coordNearScore_append_mono (X Y : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16)
    (target : Fin 3 → Fin 128) (omitted : Fin 3) :
    coordNearScore X i c b target omitted ≤ coordNearScore (X ++ Y) i c b target omitted := by
  unfold coordNearScore
  apply BPORS.InjectiveCover.score_source_le (slotEmbed X Y i c b)
  intro s
  simp only [slotValue, slotEmbed, Function.Embedding.coeFn_mk, List.get_eq_getElem, Fin.val_castLE]
  rw [List.getElem_append_left s.1.1.isLt]

theorem nearScore_append_mono (X Y : List HashOutput) (N : HashOutput) : nearScore X N ≤ nearScore (X ++ Y) N := by
  unfold nearScore nearTermAt
  by_cases hg : digestGate N=true
  · simp only [hg,if_true]
    apply Finset.sum_le_sum
    intro missing _
    apply Finset.sum_le_sum
    intro omitted _
    apply Finset.prod_le_prod'
    intro c _
    split_ifs
    · exact coordNearScore_append_mono X Y _ c _ _ _
    · exact coordScore_append_mono X Y _ c _ _
  · simp only [hg,Bool.false_eq_true,if_false,Finset.sum_const_zero,le_refl]

/-! ## The average over a uniform target -/

theorem finiteAverage_sum {α ι : Type} [Fintype α] (s : Finset ι) (f : ι → α → ENNReal) :
    BPORS.finiteAverage (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, BPORS.finiteAverage (f i) := by
  unfold BPORS.finiteAverage
  rw [Finset.sum_comm, div_eq_mul_inv, Finset.sum_mul]
  simp only [div_eq_mul_inv]

theorem average_coordNearScore (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (b : Fin 16) (omitted : Fin 3) :
    BPORS.finiteAverage (fun target : Fin 3 → Fin 128 => coordNearScore X i c b target omitted) =
      ((3 * ((BPORS.History.atIndex i (labels X)).map fun row => row c).count b).descFactorial 2 : ENNReal) /
        128 ^ 2 := by
  rw [← BPORS.finiteAverage_equiv (Fin.insertNthEquiv (fun _ : Fin 3 => Fin 128) omitted)]
  have h : ∀ p : Fin 128 × (Fin 2 → Fin 128),
      coordNearScore X i c b (Fin.insertNthEquiv (fun _ : Fin 3 => Fin 128) omitted p) omitted =
        BPORS.InjectiveCover.score (slotValue X i c b) p.2 := by
    intro p
    unfold coordNearScore
    show BPORS.InjectiveCover.score (slotValue X i c b)
      (omitted.removeNth (Fin.insertNth (α := fun _ => Fin 128) omitted p.1 p.2)) = _
    rw [Fin.removeNth_insertNth]
  simp_rw [h]
  rw [BPORS.finiteAverage_pair]
  simp_rw [BPORS.History.finiteAverage_constant]
  rw [BPORS.InjectiveCover.average_score, card_slot, hits_eq_count]
  simp only [Fintype.card_fin, Nat.cast_ofNat]

/-- The missing coordinate, averaged over a uniform bucket and leaves: the near coordinate envelope. -/
theorem average_near_coordinate (X : List HashOutput) (i : Fin (2 ^ 31)) (c : Fin 7) (omitted : Fin 3) :
    BPORS.finiteAverage (fun d : Fin 16 × (Fin 3 → Fin 128) => coordNearScore X i c d.1 d.2 omitted) =
      BPORS.Numeric.nearCoordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) / 128 ^ 2 := by
  rw [BPORS.finiteAverage_pair]
  simp_rw [average_coordNearScore]
  unfold BPORS.finiteAverage BPORS.Numeric.nearCoordinateEnvelope
  simp only [Fintype.card_fin, Nat.cast_ofNat, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The near term at a fixed index, averaged over uniform buckets and leaves: SEC's near word envelope. -/
theorem average_near_at_index (X : List HashOutput) (i : Fin (2 ^ 31)) (missing : Fin 7) (omitted : Fin 3) :
    BPORS.finiteAverage (fun v : Fin 7 → Fin 16 × (Fin 3 → Fin 128) =>
        ∏ c : Fin 7, if c = missing then coordNearScore X i c (v c).1 (v c).2 omitted
          else coordScore X i c (v c).1 (v c).2)/64 =
      BPORS.History.nearWordEnvelope missing (BPORS.History.atIndex i (labels X)) := by
  rw [BPORS.finiteAverage_product 7 (fun c (d : Fin 16 × (Fin 3 → Fin 128)) =>
    if c = missing then coordNearScore X i c d.1 d.2 omitted else coordScore X i c d.1 d.2)]
  have hc : ∀ c : Fin 7, BPORS.finiteAverage (fun d : Fin 16 × (Fin 3 → Fin 128) =>
      if c = missing then coordNearScore X i c d.1 d.2 omitted else coordScore X i c d.1 d.2) =
      (if c = missing then BPORS.Numeric.nearCoordinateEnvelope
          ((BPORS.History.atIndex i (labels X)).map fun row => row c)
        else BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) * 128⁻¹) *
        (128 ^ 2)⁻¹ := by
    intro c
    by_cases h : c = missing
    · simp only [h, if_true]
      rw [average_near_coordinate, div_eq_mul_inv]
    · simp only [h, if_false]
      rw [average_coordinate, div_eq_mul_inv, mul_assoc, ← ENNReal.mul_inv (Or.inl (by norm_num))
        (Or.inl (by norm_num))]
      norm_num
  simp_rw [hc]
  unfold BPORS.History.nearWordEnvelope
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplit : (∏ c : Fin 7, if c = missing then BPORS.Numeric.nearCoordinateEnvelope
        ((BPORS.History.atIndex i (labels X)).map fun row => row c)
      else BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c) * 128⁻¹) =
      (∏ c : Fin 7, if c = missing then BPORS.Numeric.nearCoordinateEnvelope
        ((BPORS.History.atIndex i (labels X)).map fun row => row c)
      else BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c)) * (128⁻¹) ^ 6 := by
    rw [← Finset.prod_mul_prod_compl {missing}]
    rw [← Finset.prod_mul_prod_compl {missing} (fun c : Fin 7 => if c = missing then BPORS.Numeric.nearCoordinateEnvelope
        ((BPORS.History.atIndex i (labels X)).map fun row => row c)
      else BPORS.coordinateEnvelope ((BPORS.History.atIndex i (labels X)).map fun row => row c))]
    simp only [Finset.prod_singleton, if_true]
    rw [mul_assoc]
    congr 1
    have hcard : ({missing}ᶜ : Finset (Fin 7)).card = 6 := by
      rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro c hc
    have hne : c ≠ missing := by simpa using hc
    simp only [hne, if_false]
  rw [hsplit, div_eq_mul_inv, mul_assoc, mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv]

theorem average_nearTermAt (X : List HashOutput) (missing : Fin 7) (omitted : Fin 3) :
    BPORS.finiteAverage (fun N : HashOutput => nearTermAt X N missing omitted) =
      BPORS.finiteAverage (fun i : Fin (2 ^ 31) =>
        BPORS.History.nearWordEnvelope missing (BPORS.History.atIndex i (labels X))) := by
  change BPORS.finiteAverage (fun N : HashOutput => if digestGate N=true then
    (fun p : RawView => ∏ c : Fin 7, if c=missing then
      coordNearScore X p.1 c (p.2 c).1 (p.2 c).2 omitted
      else coordScore X p.1 c (p.2 c).1 (p.2 c).2) (rawView N) else 0)=_
  rw [average_gate_weight (fun p : RawView => ∏ c : Fin 7, if c=missing then
      coordNearScore X p.1 c (p.2 c).1 (p.2 c).2 omitted
      else coordScore X p.1 c (p.2 c).1 (p.2 c).2),BPORS.finiteAverage_pair,←finiteAverage_div]
  simp_rw [average_near_at_index]

/-- **Exact average** of the near score over a uniform target output. -/
theorem average_nearScore (X : List HashOutput) :
    BPORS.finiteAverage (fun N : HashOutput => nearScore X N) =
      BPORS.History.fullNearPrice (labels X) / 2 ^ 128 := by
  unfold nearScore
  rw [finiteAverage_sum]
  simp_rw [finiteAverage_sum, average_nearTermAt]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold BPORS.finiteAverage BPORS.History.fullNearPrice
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  generalize (∑ y : Fin (2 ^ 31), ∑ x : Fin 7,
    BPORS.History.nearWordEnvelope x (BPORS.History.atIndex y (labels X))) = S
  rw [show (2 : ENNReal) ^ 128 = 2 ^ 97 * 2 ^ 31 by rw [← pow_add],
    ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness))]
  have h97 : (2 : ENNReal) ^ 97 * (2 ^ 97)⁻¹ = 1 := ENNReal.mul_inv_cancel (by positivity) (by finiteness)
  calc (3 : ENNReal) * (S * (2 ^ 31)⁻¹) = 3 * S * ((2 ^ 97 * (2 ^ 97)⁻¹) * (2 ^ 31)⁻¹) := by
        rw [h97, one_mul, mul_assoc]
    _ = _ := by ring

end SigGolfCandidate.T3.Security.CaseC
