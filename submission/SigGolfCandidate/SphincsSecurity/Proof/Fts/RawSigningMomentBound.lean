import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Base.BinomialMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ReuseRawEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetIndexEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation

section





namespace SphincsSecurity.Concrete
open ENNReal
noncomputable def indexPowerVector (cache signings : ENNReal) : TargetIndexVector :=
  fun power degree => cache ^ power * signings ^ degree
def TargetIndexDegreeLE (bound : Nat) (first second : TargetIndexVector) : Prop :=
  ∀ power degree, power + degree ≤ bound → first power degree ≤ second power degree
theorem targetIndexCacheLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexCacheLower first) (targetIndexCacheLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h lower degree (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexTreeLower_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexTreeLower first) (targetIndexTreeLower second) := by
  intro power degree hdegree
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h power lower (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexReuseStep_degree_mono {bound : Nat} {first second : TargetIndexVector}
    (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexReuseStep first) (targetIndexReuseStep second) := by
  intro power degree hdegree
  unfold targetIndexReuseStep targetIndexTreeLower
  apply Finset.sum_le_sum
  intro lower hlower
  apply mul_le_mul' le_rfl
  exact h (power + 1) lower (by have := Finset.mem_range.mp hlower; omega)
theorem targetIndexSigning_degree_mono (uniform reuse : ENNReal)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound (targetIndexSigning uniform reuse first) (targetIndexSigning uniform reuse second) := by
  intro power degree hdegree
  exact add_le_add
    (add_le_add (h power degree hdegree) (mul_le_mul' le_rfl
      (add_le_add (add_le_add (targetIndexCacheLower_degree_mono h power degree hdegree)
        (targetIndexTreeLower_degree_mono h power degree hdegree))
        (targetIndexCacheLower_degree_mono (targetIndexTreeLower_degree_mono h) power degree hdegree))))
    (mul_le_mul' le_rfl (targetIndexReuseStep_degree_mono h power degree hdegree))
theorem targetIndexSigning_iterate_degree_mono (uniform reuse : ENNReal) (signings : Nat)
    {bound : Nat} {first second : TargetIndexVector} (h : TargetIndexDegreeLE bound first second) :
    TargetIndexDegreeLE bound ((targetIndexSigning uniform reuse)^[signings] first)
      ((targetIndexSigning uniform reuse)^[signings] second) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetIndexSigning_degree_mono uniform reuse ih
theorem ennreal_add_one_pow (value : ENNReal) (degree : Nat) :
    (value + 1) ^ degree = value ^ degree +
      ∑ lower ∈ Finset.range degree, (degree.choose lower : ENNReal) * value ^ lower := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_comm]
  apply congrArg (value ^ degree + ·)
  apply Finset.sum_congr rfl
  intro lower _
  exact mul_comm _ _
theorem indexPowerVector_cache_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) signings power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree := by
  simp only [indexPowerVector, ennreal_add_one_pow, add_mul, Finset.sum_mul, targetIndexCacheLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem targetIndexQuery_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (power degree : Nat) :
    targetIndexQuery rate (indexPowerVector cache signings) power degree =
      (1 - rate) * indexPowerVector cache signings power degree +
        rate * indexPowerVector (cache + 1) signings power degree := by
  rw [indexPowerVector_cache_succ, bernoulli_mix_increment hrate]
  rfl
theorem targetIndexQuery_binomialAverage (arrival rate : ENNReal) (steps : Nat)
    (moments : Nat → TargetIndexVector) (power degree : Nat) :
    targetIndexQuery arrival (fun p d => binomialAverage rate steps (fun count => moments count p d)) power degree =
      binomialAverage rate steps (fun count => targetIndexQuery arrival (moments count) power degree) := by
  simp only [targetIndexQuery, targetIndexCacheLower, binomialAverage_add,
    binomialAverage_mul_left, binomialAverage_sum]
theorem targetIndexQuery_iterate_power {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries power degree : Nat) :
    (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) power degree =
      binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings power degree) := by
  induction queries generalizing power degree with
  | zero => simp [binomialAverage_zero]
  | succ queries ih =>
      have hfun : (targetIndexQuery rate)^[queries] (indexPowerVector cache signings) =
          fun p d => binomialAverage rate queries (fun count => indexPowerVector (cache + count) signings p d) := by
        funext p d
        exact ih p d
      rw [Function.iterate_succ_apply', hfun, targetIndexQuery_binomialAverage]
      simp_rw [targetIndexQuery_power hrate]
      rw [binomialAverage_add, binomialAverage_mul_left, binomialAverage_mul_left, binomialAverage_succ]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
theorem targetIndexQuery_iterate_power_le {rate : ENNReal} (hrate : rate ≤ 1)
    (cache signings : ENNReal) (queries bound : Nat) :
    TargetIndexDegreeLE bound ((targetIndexQuery rate)^[queries] (indexPowerVector cache signings))
      (indexPowerVector (cache + queries * rate + bound) signings) := by
  intro power degree hdegree
  rw [targetIndexQuery_iterate_power hrate]
  simp only [indexPowerVector, binomialAverage_mul_right]
  apply mul_le_mul' _ le_rfl
  exact (binomialAverage_shifted_power_le hrate cache queries power).trans
    (pow_le_pow_left' (add_le_add le_rfl (Nat.cast_le.mpr (by omega : power ≤ bound))) power)
theorem targetIndexEnvelope_power_query_shift_le {rate : ENNReal} (hrate : rate ≤ 1)
    (uniform reuse cache signings : ENNReal) (queries signatures bound power degree : Nat)
    (hdegree : power + degree ≤ bound) :
    targetIndexEnvelope uniform reuse rate queries signatures (indexPowerVector cache signings) power degree ≤
      (targetIndexSigning uniform reuse)^[signatures]
        (indexPowerVector (cache + queries * rate + bound) signings) power degree :=
  targetIndexSigning_iterate_degree_mono uniform reuse signatures
    (targetIndexQuery_iterate_power_le hrate cache signings queries bound) power degree hdegree
theorem targetShapeEnvelope_sum_indexPower {α : Type} [Fintype α]
    (uniform reuse arrival : ENNReal) (queries signatures : Nat) (cache signings : α → ENNReal)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetShapeEnvelope (constRate uniform) reuse (constRate arrival) queries signatures
      (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) groups remaining =
      ∑ i, targetIndexEnvelope uniform reuse arrival queries signatures
        (indexPowerVector (cache i) (signings i)) groups.card remaining.card := by
  have hsum : (fun G R => ∑ i, indexPowerVector (cache i) (signings i) G.card R.card) =
      fun G R => ∑' i, liftTargetIndexVector (indexPowerVector (cache i) (signings i)) G R := by
    funext G R
    rw [tsum_fintype]
    rfl
  rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact targetShapeEnvelope_lift uniform reuse arrival queries signatures _ groups remaining hvalid
theorem reuseRawEnvelope_query_shift_le (key : SecretKey) (reuse : ENNReal)
    (queries signatures bound : Nat) (state : CoverLogState)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup)
    (hvalid : TargetShapeValid groups remaining) (hdegree : groups.card + remaining.card ≤ bound) :
    reuseRawEnvelope key reuse queries signatures state groups remaining ≤
      ∑ index : Index, (targetIndexSigning (Fintype.card Index : ENNReal)⁻¹ reuse)^[signatures]
        (indexPowerVector
          (cachedIndexMultiplicity key.parameter state.1 index +
            (queries : ENNReal) * cachedIndexRate + bound)
          ((signingSlotsAtIndex (observedOptionalSigningViews
            (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card : ENNReal))
        groups.card remaining.card := by
  have hrate : cachedIndexRate ≤ 1 := cachedIndexRate_le_one
  unfold reuseRawEnvelope observedRawIndexShapeVector liftTargetIndexVector targetIndexMoments
  change targetShapeEnvelope _ _ _ queries signatures
    (fun G R => ∑ index : Index, indexPowerVector _ _ G.card R.card) groups remaining ≤ _
  rw [targetShapeEnvelope_sum_indexPower _ _ _ _ _ _ _ groups remaining hvalid]
  apply Finset.sum_le_sum
  intro index _
  exact targetIndexEnvelope_power_query_shift_le hrate _ _ _ _ queries signatures bound _ _ hdegree
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete
open ENNReal
theorem targetIndexSigning_add (uniform reuse : ENNReal) (first second : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => first p d + second p d) =
      fun p d => targetIndexSigning uniform reuse first p d + targetIndexSigning uniform reuse second p d := by
  funext power degree
  simp only [targetIndexSigning, targetIndexCacheLower, targetIndexTreeLower, targetIndexReuseStep,
    mul_add, Finset.sum_add_distrib]
  ring
theorem targetIndexSigning_mul (uniform reuse scalar : ENNReal) (moments : TargetIndexVector) :
    targetIndexSigning uniform reuse (fun p d => scalar * moments p d) =
      fun p d => scalar * targetIndexSigning uniform reuse moments p d := by
  have hcache (values : TargetIndexVector) (p d : Nat) :
      targetIndexCacheLower (fun p d => scalar * values p d) p d =
        scalar * targetIndexCacheLower values p d := by
    simp only [targetIndexCacheLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  have htree (values : TargetIndexVector) : targetIndexTreeLower (fun p d => scalar * values p d) =
      fun p d => scalar * targetIndexTreeLower values p d := by
    funext p d
    simp only [targetIndexTreeLower, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lower _
    ring
  funext power degree
  simp only [targetIndexSigning, hcache, htree, targetIndexReuseStep]
  ring
theorem targetIndexSigning_iterate_add (uniform reuse : ENNReal) (steps : Nat) (first second : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => first p d + second p d) =
      fun p d => (targetIndexSigning uniform reuse)^[steps] first p d +
        (targetIndexSigning uniform reuse)^[steps] second p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_add]
theorem targetIndexSigning_iterate_mul (uniform reuse scalar : ENNReal) (steps : Nat) (moments : TargetIndexVector) :
    (targetIndexSigning uniform reuse)^[steps] (fun p d => scalar * moments p d) =
      fun p d => scalar * (targetIndexSigning uniform reuse)^[steps] moments p d := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [Function.iterate_succ_apply', ih, targetIndexSigning_mul]
theorem indexPowerVector_signing_succ (cache signings : ENNReal) :
    indexPowerVector cache (signings + 1) =
      fun p d => indexPowerVector cache signings p d + targetIndexTreeLower (indexPowerVector cache signings) p d := by
  funext power degree
  simp only [indexPowerVector, ennreal_add_one_pow, mul_add, Finset.mul_sum, targetIndexTreeLower]
  congr 1
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem indexPowerVector_diagonal_succ (cache signings : ENNReal) (power degree : Nat) :
    indexPowerVector (cache + 1) (signings + 1) power degree =
      indexPowerVector cache signings power degree + targetIndexCacheLower (indexPowerVector cache signings) power degree +
        targetIndexTreeLower (indexPowerVector cache signings) power degree +
        targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree := by
  rw [indexPowerVector_cache_succ, indexPowerVector_signing_succ]
  simp only [targetIndexCacheLower, mul_add, Finset.sum_add_distrib]
  ring
theorem targetIndexReuseStep_power (cache signings : ENNReal) (power degree : Nat) :
    targetIndexReuseStep (indexPowerVector cache signings) power degree =
      cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
  simp only [targetIndexReuseStep, targetIndexTreeLower, indexPowerVector, pow_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lower _
  ring
theorem targetIndexSigning_power {uniform reuse cache : ENNReal}
    (hprob : uniform + reuse * cache ≤ 1) (signings : ENNReal) (power degree : Nat) :
    targetIndexSigning uniform reuse (indexPowerVector cache signings) power degree =
      (1 - (uniform + reuse * cache)) * indexPowerVector cache signings power degree +
        uniform * indexPowerVector (cache + 1) (signings + 1) power degree +
        reuse * cache * indexPowerVector cache (signings + 1) power degree := by
  rw [indexPowerVector_diagonal_succ, indexPowerVector_signing_succ]
  simp only [targetIndexSigning, targetIndexReuseStep_power]
  have hsum : 1 - (uniform + reuse * cache) + (uniform + reuse * cache) = 1 :=
    tsub_add_cancel_of_le hprob
  calc
    _ = (1 - (uniform + reuse * cache) + (uniform + reuse * cache)) *
        indexPowerVector cache signings power degree + uniform *
          (targetIndexCacheLower (indexPowerVector cache signings) power degree +
            targetIndexTreeLower (indexPowerVector cache signings) power degree +
            targetIndexCacheLower (targetIndexTreeLower (indexPowerVector cache signings)) power degree) +
          reuse * cache * targetIndexTreeLower (indexPowerVector cache signings) power degree := by
      rw [hsum]
      ring
    _ = _ := by ring
noncomputable def indexSigningAverage (uniform reuse : ENNReal) :
    Nat → (ENNReal → ENNReal → ENNReal) → ENNReal → ENNReal → ENNReal
  | 0, f, cache, signings => f cache signings
  | steps + 1, f, cache, signings =>
      (1 - (uniform + reuse * cache)) * indexSigningAverage uniform reuse steps f cache signings +
        uniform * indexSigningAverage uniform reuse steps f (cache + 1) (signings + 1) +
        reuse * cache * indexSigningAverage uniform reuse steps f cache (signings + 1)
theorem targetIndexSigning_iterate_power {uniform reuse cache : ENNReal}
    (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ 1)
    (signings : ENNReal) (power degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) power degree =
      indexSigningAverage uniform reuse steps (fun c s => indexPowerVector c s power degree) cache signings := by
  induction steps generalizing cache signings power degree with
  | zero => rfl
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ 1 :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ 1 := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hfun : targetIndexSigning uniform reuse (indexPowerVector cache signings) =
          fun p d => (1 - (uniform + reuse * cache)) * indexPowerVector cache signings p d +
            uniform * indexPowerVector (cache + 1) (signings + 1) p d +
            reuse * cache * indexPowerVector cache (signings + 1) p d := by
        funext p d
        exact targetIndexSigning_power hbase signings p d
      rw [Function.iterate_succ_apply, hfun]
      simp only [targetIndexSigning_iterate_add, targetIndexSigning_iterate_mul]
      rw [ih hstay, ih hnext, ih hstay]
      rfl
theorem bernoulli_mix_rate_mono {rate nextRate first second : ENNReal}
    (hrate : rate ≤ nextRate) (hnext : nextRate ≤ 1) (hvalue : first ≤ second) :
    (1 - rate) * first + rate * second ≤ (1 - nextRate) * first + nextRate * second := by
  have hsum : first + (second - first) = second := add_tsub_cancel_of_le hvalue
  calc
    _ = first + rate * (second - first) := by
      conv_lhs => rhs; rw [← hsum]
      exact bernoulli_mix_increment (hrate.trans hnext) _ _
    _ ≤ first + nextRate * (second - first) := add_le_add le_rfl (mul_le_mul' hrate le_rfl)
    _ = _ := by
      rw [← bernoulli_mix_increment hnext, hsum]
theorem indexSigningAverage_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (f : ENNReal → ENNReal) (hmono : Monotone f) (signings : ENNReal) :
    indexSigningAverage uniform reuse steps (fun _ s => f s) cache signings ≤
      binomialAverage rate steps (fun count => f (signings + count)) := by
  induction steps generalizing cache signings with
  | zero => simp only [indexSigningAverage, binomialAverage_zero, Nat.cast_zero, add_zero, le_refl]
  | succ steps ih =>
      have hbase : uniform + reuse * cache ≤ rate :=
        (add_le_add le_rfl (mul_le_mul' le_rfl le_self_add)).trans hprob
      have hstay : uniform + reuse * (cache + steps) ≤ rate := by
        apply le_trans _ hprob
        gcongr
        exact Nat.le_succ steps
      have hnext : uniform + reuse * (cache + 1 + steps) ≤ rate := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hprob
      have hvalue : binomialAverage rate steps (fun count => f (signings + count)) ≤
          binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
        binomialAverage_mono rate steps (fun _ => hmono (add_le_add le_self_add le_rfl))
      calc
        _ ≤ (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            uniform * binomialAverage rate steps (fun count => f (signings + 1 + count)) +
            reuse * cache * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          add_le_add (add_le_add (mul_le_mul' le_rfl (ih hstay signings))
            (mul_le_mul' le_rfl (ih hnext (signings + 1))))
            (mul_le_mul' le_rfl (ih hstay (signings + 1)))
        _ = (1 - (uniform + reuse * cache)) *
              binomialAverage rate steps (fun count => f (signings + count)) +
            (uniform + reuse * cache) *
              binomialAverage rate steps (fun count => f (signings + 1 + count)) := by ring
        _ ≤ (1 - rate) * binomialAverage rate steps (fun count => f (signings + count)) +
            rate * binomialAverage rate steps (fun count => f (signings + 1 + count)) :=
          bernoulli_mix_rate_mono hbase hrate hvalue
        _ = _ := by
          simp only [binomialAverage_succ, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
theorem targetIndexSigning_iterate_power_le_binomialAverage {uniform reuse rate cache : ENNReal}
    (hrate : rate ≤ 1) (steps : Nat) (hprob : uniform + reuse * (cache + steps) ≤ rate)
    (signings : ENNReal) (degree : Nat) :
    (targetIndexSigning uniform reuse)^[steps] (indexPowerVector cache signings) 0 degree ≤
      binomialAverage rate steps (fun count => (signings + count) ^ degree) := by
  rw [targetIndexSigning_iterate_power steps (hprob.trans hrate)]
  simp only [indexPowerVector, pow_zero, one_mul]
  exact indexSigningAverage_le_binomialAverage hrate steps hprob (fun s => s ^ degree)
    (fun _ _ h => pow_le_pow_left' h degree) signings
end SphincsSecurity.Concrete
end
