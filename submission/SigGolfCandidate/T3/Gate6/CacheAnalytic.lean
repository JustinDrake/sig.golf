import SigGolfCandidate.T3.Gate6.CacheModel
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
set_option maxHeartbeats 200000

noncomputable def theta : ℝ := 1/4096
noncomputable def growth : ℝ := rate*theta/(1-theta)

theorem theta_pos : 0<theta := by norm_num [theta]
theorem theta_lt_one : theta<1 := by norm_num [theta]

theorem growth_ge_center : theta*rate≤growth := by
  unfold growth
  apply (le_div_iff₀ (by linarith [theta_lt_one])).mpr
  nlinarith [mul_nonneg rate_nonneg (sq_nonneg theta)]

theorem bernoulli_mgf_real : rate*Real.exp theta+(1-rate)≤Real.exp growth := by
  have he := (Real.exp_bound_div_one_sub_of_interval' theta_pos theta_lt_one).le
  calc
    _ ≤ rate*(1/(1-theta))+(1-rate) := by gcongr;exact rate_nonneg
    _ = 1+growth := by unfold growth;field_simp [(sub_pos.mpr theta_lt_one).ne'];ring
    _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp growth

theorem centered_initial_exponent (q : Nat) (hq : q≤2^127) :
    (q : ℝ)*(growth-theta*rate)-theta*2^47≤-1000 := by
  have hqR : (q : ℝ)≤2^127 := by exact_mod_cast hq
  calc
    _ ≤ (2^127 : ℝ)*(growth-theta*rate)-theta*2^47 := by
      gcongr
      exact sub_nonneg.mpr growth_ge_center
    _ ≤ -1000 := by norm_num [growth,theta,rate_value]

theorem initial_tail_real (q : Nat) (hq : q≤2^127) :
    Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)≤(2^759 : ℝ)⁻¹ := by
  have hlog : Real.log (2 : ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    norm_num at h ⊢
    exact h
  calc
    _ ≤ Real.exp (-759*Real.log 2) := Real.exp_le_exp.mpr (by linarith [centered_initial_exponent q hq])
    _ = _ := by
      rw [neg_mul,Real.exp_neg]
      have he : Real.exp (759*Real.log 2)=(2 : ℝ)^759 := by
        simpa using (Real.exp_nat_mul (Real.log 2) 759).trans (congrArg (fun x : ℝ => x^759) (Real.exp_log (by norm_num : (0 : ℝ)<2)))
      rw [he]

theorem bernoulli_shift_real (x : ℝ) :
    rate*Real.exp (x+theta-growth)+(1-rate)*Real.exp (x-growth)≤Real.exp x := by
  have h := mul_le_mul_of_nonneg_left bernoulli_mgf_real (Real.exp_pos (x-growth)).le
  have he : Real.exp (x+theta-growth)=Real.exp (x-growth)*Real.exp theta := by rw [←Real.exp_add];congr 1;ring
  have hcancel : Real.exp (x-growth)*Real.exp growth=Real.exp x := by rw [←Real.exp_add];congr 1;ring
  rw [hcancel] at h
  rw [he]
  nlinarith

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.bernoulli_mgf_real
#print axioms SigGolfResearch.Gate6.Cache.initial_tail_real
