import SigGolfCandidate.T3.Gate6.CacheAnalytic
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 300000

noncomputable def score {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ℝ :=
  theta*(count mark cache : ℝ)+growth*((q : ℝ)-cache.entries.length)-theta*(rate*q+2^47)
noncomputable def weight {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input) : ENNReal :=
  ENNReal.ofReal (Real.exp (score q mark cache))
noncomputable def totalWeight {Input : Type} (q : Nat) (cache : Cache Input) : ENNReal :=
  ∑ mark : MarkedLabel,weight q mark cache

theorem expected_choice (mark : MarkedLabel) (yes no : ENNReal) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no)) =
      eRate*yes+(1-eRate)*no := by
  have hnot : Pr[fun d => ¬Matches mark d | ($ᵗ Output : ProbComp Output)] = 1-eRate := by
    have h := probEvent_compl ($ᵗ Output : ProbComp Output) (Matches mark)
    rw [probFailure_of_liftM_PMF,tsub_zero,probability_matches,add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hs (output : Output) : Pr[=output | ($ᵗ Output : ProbComp Output)]*(if Matches mark output then yes else no) =
      (if Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*yes+
      (if ¬Matches mark output then Pr[=output | ($ᵗ Output : ProbComp Output)] else 0)*no := by
    by_cases h : Matches mark output <;> simp [h]
  simp_rw [hs,ENNReal.tsum_add,ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,probability_matches,hnot]

theorem weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (output : Output) (fresh : lookup cache input=none) :
    weight q mark (insert cache input output fresh) =
      if Matches mark output then ENNReal.ofReal (Real.exp (score q mark cache+theta-growth))
      else ENNReal.ofReal (Real.exp (score q mark cache-growth)) := by
  unfold weight score
  rw [count_insert,insert_length]
  by_cases h : Matches mark output <;> simp only [h,if_true,if_false,Nat.cast_add,Nat.cast_one,Nat.cast_zero]
  all_goals congr 2 <;> ring

theorem expected_weight_insert {Input : Type} [DecidableEq Input] (q : Nat) (mark : MarkedLabel)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      weight q mark (insert cache input output fresh))≤weight q mark cache := by
  simp_rw [weight_insert]
  rw [expected_choice]
  have heFinite := eRate_finite
  apply (ENNReal.toReal_le_toReal (by finiteness) (by unfold weight;finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_sub_of_le eRate_le_one (by finiteness),ENNReal.toReal_one,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,weight]
  exact bernoulli_shift_real (score q mark cache)

theorem expected_totalWeight_insert {Input : Type} [DecidableEq Input] (q : Nat)
    (cache : Cache Input) (input : Input) (fresh : lookup cache input=none) :
    (∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
      totalWeight q (insert cache input output fresh))≤totalWeight q cache := by
  simp only [totalWeight,Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact Finset.sum_le_sum fun mark _ => expected_weight_insert q mark cache input fresh

theorem weight_bad {Input : Type} (q : Nat) (mark : MarkedLabel) (cache : Cache Input)
    (hq : cache.entries.length≤q)
    (hbad : (cache.entries.length : ℝ)*rate+2^47 < count mark cache) : 1≤weight q mark cache := by
  have hqR : 0≤(q : ℝ)-cache.entries.length := sub_nonneg.mpr (by exact_mod_cast hq)
  have hprod := mul_nonneg (sub_nonneg.mpr growth_ge_center) hqR
  have hpositive := mul_nonneg theta_pos.le (sub_nonneg.mpr hbad.le)
  have hs : 0 ≤ score q mark cache := by unfold score;nlinarith
  calc
    1 = ENNReal.ofReal (Real.exp 0) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs)

theorem totalWeight_bad {Input : Type} (q : Nat) (cache : Cache Input)
    (hq : cache.entries.length≤q) (hbad : Bad cache) : 1≤totalWeight q cache := by
  obtain ⟨mark,hmark⟩ := hbad
  exact (weight_bad q mark cache hq hmark).trans
    (show weight q mark cache≤totalWeight q cache from
      Finset.single_le_sum (f:=fun m => weight q m cache) (fun _ _ => zero_le) (Finset.mem_univ mark))

theorem totalWeight_empty {Input : Type} (q : Nat) :
    totalWeight q (empty : Cache Input) =
      (2^59 : ENNReal)*ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
  have hw (mark : MarkedLabel) : weight q mark (empty : Cache Input) =
      ENNReal.ofReal (Real.exp ((q : ℝ)*(growth-theta*rate)-theta*2^47)) := by
    unfold weight score count empty
    simp only [List.countP_nil,List.length_nil,Nat.cast_zero,mul_zero,zero_add,sub_zero]
    congr 2
    ring
  simp only [totalWeight,hw,Finset.sum_const,Finset.card_univ,markedLabel_card,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat]

theorem initial_totalWeight_le {Input : Type} (q : Nat) (hq : q≤2^127) :
    totalWeight q (empty : Cache Input)≤(2^700 : ENNReal)⁻¹ := by
  rw [totalWeight_empty]
  calc
    _ ≤ (2^59 : ENNReal)*ENNReal.ofReal ((2^759 : ℝ)⁻¹) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (initial_tail_real q hq))
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal (show (0 : ℝ)≤(2^759 : ℝ)⁻¹ by positivity)]
      rw [show (2 : ℝ)^759=2^59*2^700 by rw [←pow_add]]
      field_simp

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.expected_totalWeight_insert
#print axioms SigGolfResearch.Gate6.Cache.initial_totalWeight_le
