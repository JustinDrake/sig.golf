import SigGolfCandidate.T3.Gate6.CachePotential
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexHashMoments

namespace SigGolfResearch.Gate6.NativeCache
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SphincsSecurity (Finite)
abbrev RCache := SigGolfCandidate.T3.Sampling.RCache
open SphincsSecurity.Concrete (enncard_cacheQuery_of_fresh)
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

/-- Accepted full 59-bit marks in the actual memoizing public RO cache. -/
noncomputable def entry (mark : MarkedLabel) (cache : RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun output => if Cache.Matches mark output then 1 else 0)
noncomputable def count (mark : MarkedLabel) (cache : RCache) : ENNReal := ∑' input,entry mark cache input

theorem count_empty (mark : MarkedLabel) : count mark ∅=0 := by simp [count,entry]

theorem count_cacheQuery (mark : MarkedLabel) (cache : RCache) (input : HashInput)
    (output : HashOutput) (hfresh : cache input=none) :
    count mark (cache.cacheQuery input output)=count mark cache+
      if Cache.Matches mark output then 1 else 0 := by
  unfold count
  rw [ENNReal.tsum_eq_add_tsum_ite (f := entry mark (cache.cacheQuery input output)) input,
    ENNReal.tsum_eq_add_tsum_ite (f := entry mark cache) input]
  simp only [entry,QueryCache.cacheQuery_self,hfresh,Option.elim_none,Option.elim_some,zero_add]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro other
  by_cases heq : other=input
  · simp [heq]
  · simp only [heq,if_false,QueryCache.cacheQuery_of_ne cache output heq]

theorem count_le_enncard (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≤ QueryCache.enncard cache := by
  unfold count
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hn : cache input=none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp [entry,hn])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset,(1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold entry
      cases cache input <;> simp only [Option.elim_none,Option.elim_some]
      · exact bot_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard

theorem enncard_ne_top (cache : RCache) (hfinite : Finite cache) : QueryCache.enncard cache ≠ ⊤ := by
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

theorem count_ne_top (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache) :
    count mark cache ≠ ⊤ := ne_top_of_le_ne_top (enncard_ne_top cache hfinite) (count_le_enncard mark cache hfinite)

noncomputable def Bad (cache : RCache) : Prop :=
  ∃ mark : MarkedLabel,(QueryCache.enncard cache).toReal*Cache.rate+2^47 < (count mark cache).toReal
noncomputable def score (q : Nat) (mark : MarkedLabel) (cache : RCache) : ℝ :=
  Cache.theta*(count mark cache).toReal+Cache.growth*((q : ℝ)-(QueryCache.enncard cache).toReal)-
    Cache.theta*(Cache.rate*q+2^47)
noncomputable def weight (q : Nat) (mark : MarkedLabel) (cache : RCache) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight (q : Nat) (cache : RCache) : ENNReal := ∑ mark : MarkedLabel,weight q mark cache

theorem score_cacheQuery (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (output : HashOutput) (hfresh : cache input=none) :
    score q mark (cache.cacheQuery input output)=score q mark cache+
      (if Cache.Matches mark output then Cache.theta else 0)-Cache.growth := by
  unfold score
  rw [count_cacheQuery mark cache input output hfresh,enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add (enncard_ne_top cache hfinite) (by finiteness),ENNReal.toReal_one]
  have hsum : (count mark cache+1).toReal=(count mark cache).toReal+1 := by
    rw [ENNReal.toReal_add (count_ne_top mark cache hfinite) ENNReal.one_ne_top,ENNReal.toReal_one]
  have hsum' : (1+count mark cache).toReal=1+(count mark cache).toReal := by
    rw [ENNReal.toReal_add ENNReal.one_ne_top (count_ne_top mark cache hfinite),ENNReal.toReal_one]
  split_ifs <;> (try rw [hsum]) <;> (try rw [hsum']) <;> (try simp only [add_zero]) <;> ring

theorem expected_weight_fresh (q : Nat) (mark : MarkedLabel) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => weight q mark (cache.cacheQuery input output)) ≤ weight q mark cache := by
  have he (output : HashOutput) : weight q mark (cache.cacheQuery input output)=
      if Cache.Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+Cache.theta-Cache.growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-Cache.growth)) := by
    unfold weight
    rw [score_cacheQuery q mark cache hfinite input output hfresh]
    split_ifs <;> simp
  simp_rw [he]
  change (∑' output,Pr[=output | ($ᵗ Cache.Output : ProbComp Cache.Output)]*_)≤_
  rw [Cache.expected_choice]
  have heFinite := Cache.eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le Cache.eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact Cache.bernoulli_shift_real (score q mark cache)

theorem expected_totalWeight_fresh (q : Nat) (cache : RCache) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input=none) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => totalWeight q (cache.cacheQuery input output)) ≤ totalWeight q cache := by
  unfold totalWeight
  rw [expectedValue_finsetSum]
  exact Finset.sum_le_sum fun mark _ => expected_weight_fresh q mark cache hfinite input hfresh

theorem totalWeight_bad (q : Nat) (cache : RCache) (hq : QueryCache.enncard cache≤q)
    (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  have hqR : 0≤(q : ℝ)-(QueryCache.enncard cache).toReal := by
    apply sub_nonneg.mpr
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hq
  have hprod := mul_nonneg (sub_nonneg.mpr Cache.growth_ge_center) hqR
  have hpositive := mul_nonneg Cache.theta_pos.le (sub_nonneg.mpr hmark.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  have hw : 1≤weight q mark cache := by
    calc
      1 = ENNReal.ofReal (Real.exp 0) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)
  exact hw.trans (Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))

theorem totalWeight_empty (q : Nat) : totalWeight q ∅ =
    (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark ∅=
      ENNReal.ofReal (Real.exp ((q : ℝ)*(Cache.growth-Cache.theta*Cache.rate)-Cache.theta*2^47)) := by
    unfold weight score
    simp only [count_empty,ENNReal.toReal_zero,QueryCache.enncard_empty,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

theorem initial_totalWeight_le (q : Nat) (hq : q≤2^127) : totalWeight q ∅≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty,← Cache.totalWeight_empty (Input := HashInput)]
  exact Cache.initial_totalWeight_le q hq

theorem not_bad_empty : ¬Bad ∅ := by
  rintro ⟨mark,h⟩
  norm_num [count_empty,QueryCache.enncard] at h

/-- Numerical completed-mark cap from the concrete 59-bit cache predicate.
It applies to the actual fresh-nonce target bound once that source decoder is installed. -/
theorem clean_point_bound_arithmetic (cache : RCache) (hfinite : Finite cache)
    (budget : Nat) (hsize : QueryCache.enncard cache≤budget) (hbudget : budget≤2^127)
    (hclean : ¬Bad cache) (mark : MarkedLabel) :
    1/(2 : ENNReal)^59+count mark cache/(2 : ENNReal)^128 ≤
      (17/16 : ENNReal)/(2 : ENNReal)^59 := by
  have hex : (count mark cache).toReal ≤ (QueryCache.enncard cache).toReal*Cache.rate+2^47 :=
    le_of_not_gt (fun h => hclean ⟨mark,h⟩)
  have hcache : (QueryCache.enncard cache).toReal≤(budget : ℝ) := by
    exact_mod_cast ENNReal.toReal_mono (by finiteness) hsize
  have hbudgetR : (budget : ℝ)≤2^127 := by exact_mod_cast hbudget
  have hscale := mul_le_mul_of_nonneg_right (hcache.trans hbudgetR) Cache.rate_nonneg
  apply (ENNReal.toReal_le_toReal (by have := count_ne_top mark cache hfinite;finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (ENNReal.div_ne_top (count_ne_top mark cache hfinite) (by norm_num))]
  simp only [ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  calc
    _ ≤ 1/(2 : ℝ)^59+((2 : ℝ)^127*Cache.rate+2^47)/(2 : ℝ)^128 := by
      apply add_le_add le_rfl
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ _ := by norm_num [Cache.rate_value]

end SigGolfResearch.Gate6.NativeCache
#print axioms SigGolfResearch.Gate6.NativeCache.expected_totalWeight_fresh
#print axioms SigGolfResearch.Gate6.NativeCache.initial_totalWeight_le
#print axioms SigGolfResearch.Gate6.NativeCache.clean_point_bound_arithmetic
