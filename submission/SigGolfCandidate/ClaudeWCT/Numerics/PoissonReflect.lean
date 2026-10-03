import SigGolfCandidate.ClaudeWCT.Numerics.Kernel
import SigGolfCandidate.SphincsSecurity.Proof.Base.BinomialMoments
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

section

namespace ClaudeWCT.Numerics.Kernel
def poissonCheckG (un ud ln ld : Nat) (f : Nat → Nat) (ok : Nat → Bool)
    (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    un * ln ^ r * ld ^ (R - r) * (fact R / fact r) * f r * Q ^ (9 * (R - r)) + s) 0
  (List.range (R + 1)).all ok &&
  Md * sn * (S * ld * (R + 1) + ln ^ (R + 1) * ud * dbase * Q ^ (9 * R)) ≤
    Mn * sd * ud * dbase * ld ^ (R + 1) * fact (R + 1) * Q ^ (9 * R)
theorem poissonCheck_eq_G (f : Nat → Nat) (ok : Nat → Bool) (dbase sn sd Mn Md R : Nat) :
    poissonCheck f ok dbase sn sd Mn Md R = poissonCheckG 27 200 513 256 f ok dbase sn sd Mn Md R :=
  rfl
def meanCheckW : Bool :=
  poissonCheckG 271 2000 513 256 (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 37 64 80
def meanTightCheckW : Bool :=
  poissonCheckG 271 2000 513 256 (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 1 10 80
def nearCheckW : Bool :=
  poissonCheckG 271 2000 513 256 (fun r => xNum r ^ 8 * xfNum r) (fun r => xOk r && xfOk r)
    (Nn ^ 9) (63 * A) 1 404 1 80
def diagCheckW : Bool :=
  poissonCheckG 271 2000 513 256 (fun r => yNum r ^ 9) yOk ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31)
    18400 100000000 80
theorem meanW_ok : meanCheckW = true := by decide +kernel
theorem meanTightW_ok : meanTightCheckW = true := by decide +kernel
theorem nearW_ok : nearCheckW = true := by decide +kernel
theorem diagW_ok : diagCheckW = true := by decide +kernel
end ClaudeWCT.Numerics.Kernel
end

section

namespace ClaudeWCT.Numerics.Kernel
theorem mean_ok : meanCheck = true := by decide +kernel
theorem mean_tight_ok : meanTightCheck = true := by decide +kernel
theorem near_ok : nearCheck = true := by decide +kernel
theorem diag_ok : diagCheck = true := by decide +kernel
end ClaudeWCT.Numerics.Kernel
end

section






namespace ClaudeWCT.Numerics.PoissonReflect
open ENNReal SphincsSecurity.Concrete
open scoped BigOperators
noncomputable def binomWeight (rate : ENNReal) (T r : ℕ) : ENNReal :=
  (T.choose r : ENNReal) * rate ^ r * (1 - rate) ^ (T - r)
noncomputable def finiteLaw (rate : ENNReal) (T : ℕ) (g : ℕ → ENNReal) : ENNReal :=
  ∑ r ∈ Finset.range (T + 1), (T.choose r : ENNReal) * (rate ^ r * (1 - rate) ^ (T - r) * g r)
theorem finiteLaw_succ (rate : ENNReal) (T : ℕ) (g : ℕ → ENNReal) :
    finiteLaw rate (T + 1) g =
      (1 - rate) * finiteLaw rate T g + rate * finiteLaw rate T (fun r => g (r + 1)) := by
  unfold finiteLaw
  rw [Finset.sum_choose_succ_mul (fun r m => rate ^ r * (1 - rate) ^ m * g r) T,
    Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    have hs : T + 1 - r = T - r + 1 := by have := Finset.mem_range.mp hr; omega
    rw [hs, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
theorem binomialAverage_eq_finiteLaw (rate : ENNReal) (T : ℕ) (g : ℕ → ENNReal) :
    binomialAverage rate T g = finiteLaw rate T g := by
  induction T generalizing g with
  | zero => simp [binomialAverage, finiteLaw]
  | succ T ih => rw [binomialAverage_succ, ih, ih, finiteLaw_succ]
theorem binomialAverage_eq_sum (rate : ENNReal) (T : ℕ) (g : ℕ → ENNReal) :
    binomialAverage rate T g = ∑ r ∈ Finset.range (T + 1), binomWeight rate T r * g r := by
  rw [binomialAverage_eq_finiteLaw]
  unfold finiteLaw binomWeight
  apply Finset.sum_congr rfl
  intro r _
  ring
theorem binomialAverage_atom (rate : ENNReal) (T r : ℕ) :
    binomialAverage rate T (fun v => if v = r then 1 else 0) = binomWeight rate T r := by
  rw [binomialAverage_eq_sum]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · unfold binomWeight
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
theorem binomialAverage_prefix (rate : ENNReal) (T L : ℕ) (g : ℕ → ENNReal) :
    binomialAverage rate T (fun r => if r < L then g r else 0) =
      ∑ r ∈ Finset.range L, binomWeight rate T r * g r := by
  have hform : (fun v => if v < L then g v else 0) =
      (fun v => ∑ r ∈ Finset.range L, (if v = r then (1 : ENNReal) else 0) * g r) := by
    funext v
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_range]
  rw [hform, binomialAverage_sum]
  simp_rw [binomialAverage_mul_right, binomialAverage_atom]
theorem binomialAverage_truncate (rate : ENNReal) (T L : ℕ) (g : ℕ → ENNReal) (B : ENNReal)
    (hB : ∀ r, L ≤ r → g r ≤ B) :
    binomialAverage rate T g ≤
      (∑ r ∈ Finset.range L, binomWeight rate T r * g r) +
        B * binomialAverage rate T (fun r => if L ≤ r then 1 else 0) := by
  have hpoint (r : ℕ) : g r ≤ (if r < L then g r else 0) + B * (if L ≤ r then 1 else 0) := by
    by_cases h : r < L
    · rw [if_pos h, if_neg (Nat.not_le.mpr h), mul_zero, add_zero]
    · rw [if_neg h, if_pos (Nat.le_of_not_gt h), mul_one, zero_add]
      exact hB r (Nat.le_of_not_gt h)
  refine (binomialAverage_mono rate T hpoint).trans_eq ?_
  rw [binomialAverage_add, binomialAverage_mul_left, binomialAverage_prefix]
theorem choose_le_pow_div (T k : ℕ) :
    (T.choose k : ENNReal) ≤ (T : ENNReal) ^ k / k.factorial := by
  simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_pow (Nat.cast_nonneg T),
    ENNReal.ofReal_div_of_pos (show 0 < (k.factorial : ℝ) by
      exact_mod_cast Nat.factorial_pos k)] using
    ENNReal.ofReal_le_ofReal (Nat.choose_le_pow_div (α := ℝ) k T)
theorem binomial_tail (rate : ENNReal) (hrate : rate ≤ 1) (T k : ℕ) :
    binomialAverage rate T (fun r => if k ≤ r then 1 else 0) ≤
      ((T : ENNReal) * rate) ^ k / k.factorial := by
  refine le_trans (binomialAverage_mono rate T (g := fun r => (r.choose k : ENNReal)) ?_) ?_
  · intro r
    split
    · next h => exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos h)
    · exact zero_le
  · rw [binomialAverage_choose hrate]
    refine (mul_le_mul' (choose_le_pow_div T k) le_rfl).trans_eq ?_
    simp only [div_eq_mul_inv, mul_pow, mul_right_comm]
theorem binomWeight_le (rate : ENNReal) (T R r : ℕ) (hr : r ≤ R) (lam u : ENNReal)
    (hlam : (T : ENNReal) * rate ≤ lam) (hu : (1 - rate) ^ (T - R) ≤ u) :
    binomWeight rate T r ≤ u * lam ^ r / r.factorial := by
  unfold binomWeight
  have h1 : (1 - rate) ^ (T - r) ≤ (1 - rate) ^ (T - R) :=
    pow_le_pow_right_of_le_one' tsub_le_self (Nat.sub_le_sub_left hr T)
  calc (T.choose r : ENNReal) * rate ^ r * (1 - rate) ^ (T - r)
      ≤ (T : ENNReal) ^ r / r.factorial * rate ^ r * u :=
        mul_le_mul' (mul_le_mul' (choose_le_pow_div T r) le_rfl) (h1.trans hu)
    _ = ((T : ENNReal) * rate) ^ r * u / r.factorial := by
        simp only [div_eq_mul_inv, mul_pow]; ring
    _ ≤ lam ^ r * u / r.factorial := by gcongr
    _ = u * lam ^ r / r.factorial := by rw [mul_comm (lam ^ r)]
theorem exp_lower (a : ℝ) : (2.7182818283 : ℝ) ^ 2 * (a - 1) ≤ Real.exp a := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (a - 2)
  have he : Real.exp a = Real.exp 1 ^ 2 * Real.exp (a - 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [he]
  rcases le_or_gt (a - 1) 0 with h | h
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) h) (by positivity)
  · exact mul_le_mul (pow_le_pow_left₀ (by norm_num) h1.le 2) (by linarith) h.le (by positivity)
theorem rejection_real (n : ℕ) (c a0 : ℝ) (hc : 0 < c) (ha0 : a0 * 2 ^ 31 ≤ n)
    (h : 1 / c ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1)) :
    (1 - 1 / 2 ^ 31 : ℝ) ^ n ≤ c := by
  have hp : (1 - 1 / 2 ^ 31 : ℝ) ≤ Real.exp (-(1 / 2 ^ 31)) := Real.one_sub_le_exp_neg _
  have h0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ 31 := by norm_num
  have hpow : (1 - 1 / 2 ^ 31 : ℝ) ^ n ≤ Real.exp (-(n / 2 ^ 31)) := by
    calc (1 - 1 / 2 ^ 31 : ℝ) ^ n ≤ Real.exp (-(1 / 2 ^ 31)) ^ n := pow_le_pow_left₀ h0 hp n
      _ = Real.exp (-(n / 2 ^ 31)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have ha : a0 ≤ n / 2 ^ 31 := by rw [le_div_iff₀ (by positivity)]; exact ha0
  have hexp : 1 / c ≤ Real.exp (n / 2 ^ 31) :=
    h.trans ((exp_lower a0).trans (Real.exp_le_exp.mpr ha))
  rw [Real.exp_neg] at hpow
  refine hpow.trans ?_
  rw [one_div] at hexp
  exact inv_le_of_inv_le₀ hc hexp
theorem rate_le_one : (2 ^ 31 : ENNReal)⁻¹ ≤ 1 :=
  ENNReal.inv_le_one.2 (one_le_pow₀ one_le_two)
theorem rejection_toReal (n : ℕ) :
    ((1 - (2 ^ 31 : ENNReal)⁻¹) ^ n).toReal = (1 - 1 / 2 ^ 31 : ℝ) ^ n := by
  rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le rate_le_one ENNReal.one_ne_top]
  simp [ENNReal.toReal_inv]
theorem rejection_ennreal (n un ud : ℕ) (hun : 0 < un) (hud : 0 < ud) (a0 : ℝ)
    (ha0 : a0 * 2 ^ 31 ≤ n) (h : (ud : ℝ) / un ≤ (2.7182818283 : ℝ) ^ 2 * (a0 - 1)) :
    (1 - (2 ^ 31 : ENNReal)⁻¹) ^ n ≤ (un : ENNReal) / ud := by
  have hfin : (1 - (2 ^ 31 : ENNReal)⁻¹) ^ n ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  have hfin' : (un : ENNReal) / ud ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top un) (by exact_mod_cast hud.ne')
  apply (ENNReal.toReal_le_toReal hfin hfin').mp
  rw [rejection_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  refine rejection_real n _ a0 (by positivity) ha0 ?_
  rwa [one_div_div]
def horizonT3 : ℕ := 4303355904
theorem horizonT3_eq : horizonT3 = 2 ^ 32 + 2 ^ 23 := by norm_num [horizonT3]
theorem rejection_T3 :
    (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (horizonT3 - 80) ≤ ((27 : ℕ) : ENNReal) / ((200 : ℕ) : ENNReal) := by
  refine rejection_ennreal _ 27 200 (by norm_num) (by norm_num) ((horizonT3 - 80 : ℕ) / 2 ^ 31)
    (by rw [div_mul_cancel₀ _ (by positivity)]) ?_
  norm_num [horizonT3]
theorem rejection_window (T : ℕ) (hT : 2 ^ 32 ≤ T) :
    (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (T - 80) ≤ ((271 : ℕ) : ENNReal) / ((2000 : ℕ) : ENNReal) := by
  refine rejection_ennreal _ 271 2000 (by norm_num) (by norm_num) ((2 ^ 32 - 80) / 2 ^ 31) ?_ ?_
  · rw [div_mul_cancel₀ _ (by positivity), Nat.cast_sub (by omega)]
    have : (2 : ℝ) ^ 32 ≤ T := by exact_mod_cast hT
    push_cast
    linarith
  · norm_num
theorem lam_le (T : ℕ) (hT : T ≤ 2 ^ 32 + 2 ^ 23) :
    (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ ≤ ((513 : ℕ) : ENNReal) / ((256 : ℕ) : ENNReal) := by
  have hfin : (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top T) (by simp)
  apply (ENNReal.toReal_le_toReal hfin (ENNReal.div_ne_top (by simp) (by simp))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have : (T : ℝ) ≤ 2 ^ 32 + 2 ^ 23 := by exact_mod_cast hT
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  linarith
theorem pow_lower_2_32 : (27 / 200 : ℝ) < (1 - 1 / 2 ^ 31 : ℝ) ^ (2 ^ 32 : ℕ) := by
  have hx : (0 : ℝ) < 1 - 1 / 2 ^ 31 := by norm_num
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  rw [← Real.exp_log (pow_pos hx _), Real.log_pow]
  have hδ := Real.add_one_le_exp (-(2 / (2 ^ 31 - 1) : ℝ))
  have he := Real.exp_one_lt_d9
  have h1 : -(2 + 2 / (2 ^ 31 - 1) : ℝ) ≤ ((2 ^ 32 : ℕ) : ℝ) * Real.log (1 - 1 / 2 ^ 31) := by
    have : ((2 ^ 32 : ℕ) : ℝ) * (1 - (1 - 1 / 2 ^ 31)⁻¹) = -(2 + 2 / (2 ^ 31 - 1)) := by norm_num
    rw [← this]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  refine lt_of_lt_of_le ?_ (Real.exp_le_exp.mpr h1)
  have hE : Real.exp (-(2 + 2 / (2 ^ 31 - 1))) =
      Real.exp (-(2 / (2 ^ 31 - 1))) / Real.exp 1 ^ 2 := by
    rw [_root_.eq_div_iff (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hE, lt_div_iff₀ (by positivity)]
  have he2 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 := pow_lt_pow_left₀ he (by positivity) (by norm_num)
  norm_num at he2 hδ ⊢
  linarith
theorem pmf0_gt_at_2_32 :
    (27 / 200 : ENNReal) < binomWeight (2 ^ 31)⁻¹ (2 ^ 32) 0 := by
  have hb : binomWeight (2 ^ 31)⁻¹ (2 ^ 32) 0 = (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 : ℕ) := by
    simp [binomWeight]
  rw [hb]
  have hfin : (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (2 ^ 32 : ℕ) ≠ ⊤ :=
    ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  apply (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top (by simp) (by simp)) hfin).mp
  rw [rejection_toReal, ENNReal.toReal_div]
  simp only [ENNReal.toReal_ofNat]
  exact pow_lower_2_32
theorem pmf_le_T3 (r : ℕ) (hr : r ≤ 80) :
    binomWeight (2 ^ 31)⁻¹ horizonT3 r ≤ 27 / 200 * (513 / 256) ^ r / r.factorial := by
  have h := binomWeight_le _ horizonT3 80 r hr _ _ (lam_le _ (by rw [horizonT3_eq])) rejection_T3
  simpa only [Nat.cast_ofNat] using h
theorem pmf_le_window (T : ℕ) (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23) (r : ℕ) (hr : r ≤ 80) :
    binomWeight (2 ^ 31)⁻¹ T r ≤ 271 / 2000 * (513 / 256) ^ r / r.factorial := by
  have h := binomWeight_le _ T 80 r hr _ _ (lam_le T hT2) (rejection_window T hT1)
  simpa only [Nat.cast_ofNat] using h
theorem tail_le (T : ℕ) (hT : T ≤ 2 ^ 32 + 2 ^ 23) (k : ℕ) :
    binomialAverage (2 ^ 31)⁻¹ T (fun r => if k ≤ r then 1 else 0) ≤
      (513 / 256) ^ k / k.factorial := by
  refine (binomial_tail _ rate_le_one T k).trans ?_
  have h := lam_le T hT
  simp only [Nat.cast_ofNat] at h
  gcongr
theorem fact_eq : ∀ n, Kernel.fact n = n.factorial
  | 0 => rfl
  | n + 1 => by rw [Kernel.fact, fact_eq n, Nat.factorial_succ]
theorem foldr_eq_sum (h : ℕ → ℕ) (l : List ℕ) :
    l.foldr (fun r s => h r + s) 0 = (l.map h).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
theorem range_foldr_eq_sum (h : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldr (fun r s => h r + s) 0 = ∑ r ∈ Finset.range n, h r := by
  rw [foldr_eq_sum]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
def termNum (un ln ld R : ℕ) (f : ℕ → ℕ) (r : ℕ) : ℕ :=
  un * ln ^ r * ld ^ (R - r) * (Kernel.fact R / Kernel.fact r) * f r * Kernel.Q ^ (9 * (R - r))
def denom (ud ld dbase R : ℕ) : ℕ :=
  ud * dbase * ld ^ (R + 1) * Kernel.fact (R + 1) * Kernel.Q ^ (9 * R)
theorem Q_pos : 0 < Kernel.Q := by decide
theorem denom_pos (ud ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    0 < denom ud ld dbase R := by
  unfold denom
  rw [fact_eq]
  have := Q_pos
  positivity
theorem term_eq (un ud ln ld dbase R r : ℕ) (f : ℕ → ℕ) (hr : r ≤ R) (hud : 0 < ud)
    (hld : 0 < ld) (hdb : 0 < dbase) :
    (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
        ((f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal)) =
      ((termNum un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denom ud ld dbase R : ℕ) := by
  have hQ := Q_pos
  have hD := denom_pos ud ld dbase R hud hld hdb
  have hne1 : (un : ENNReal) / ud * ((ln : ENNReal) / ld) ^ r / (r.factorial : ENNReal) *
      ((f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal)) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.div_ne_top _ (by exact_mod_cast (Nat.factorial_pos r).ne')
      apply ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hud.ne'))
      exact ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hld.ne'))
    · exact ENNReal.div_ne_top (by simp)
        (by exact_mod_cast (by positivity : 0 < dbase * Kernel.Q ^ (9 * r)).ne')
  have hne2 : ((termNum un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) /
      (denom ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold termNum denom
  rw [Nat.add_sub_cancel_left, fact_eq, fact_eq, fact_eq, Nat.factorial_succ (r + k)]
  have hdvd : r.factorial ∣ (r + k).factorial := Nat.factorial_dvd_factorial (Nat.le_add_right r k)
  have hf0 : ((r.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hfk : (((r + k).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Kernel.Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast [Nat.cast_div hdvd hf0]
  simp only [div_pow]
  field_simp
  ring
theorem tail_eq (ud ln ld dbase R : ℕ) (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) :
    ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) =
      ((ln ^ (R + 1) * ud * dbase * Kernel.Q ^ (9 * R) : ℕ) : ENNReal) /
        (denom ud ld dbase R : ℕ) := by
  have hQ := Q_pos
  have hD := denom_pos ud ld dbase R hud hld hdb
  have hne1 : ((ln : ENNReal) / ld) ^ (R + 1) / ((R + 1).factorial : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (by simp)
      (by exact_mod_cast hld.ne'))) (by exact_mod_cast (Nat.factorial_pos _).ne')
  have hne2 : ((ln ^ (R + 1) * ud * dbase * Kernel.Q ^ (9 * R) : ℕ) : ENNReal) /
      (denom ud ld dbase R : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by exact_mod_cast hD.ne')
  apply (ENNReal.toReal_eq_toReal_iff' hne1 hne2).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  unfold denom
  rw [fact_eq]
  have hf0 : (((R + 1).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hud' : (ud : ℝ) ≠ 0 := by exact_mod_cast hud.ne'
  have hld' : (ld : ℝ) ≠ 0 := by exact_mod_cast hld.ne'
  have hdb' : (dbase : ℝ) ≠ 0 := by exact_mod_cast hdb.ne'
  have hQ' : (Kernel.Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  push_cast
  simp only [div_pow]
  field_simp
theorem scale_le (sn sd Mn Md N D : ℕ) (hsd : 0 < sd) (hMd : 0 < Md) (hD : 0 < D)
    (h : Md * sn * N ≤ Mn * sd * D) :
    (sn : ENNReal) / sd * ((N : ENNReal) / D) ≤ (Mn : ENNReal) / Md := by
  have h1 : (sn : ENNReal) / sd * ((N : ENNReal) / D) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top (by simp) (by exact_mod_cast hsd.ne'))
      (ENNReal.div_ne_top (by simp) (by exact_mod_cast hD.ne'))
  have h2 : (Mn : ENNReal) / Md ≠ ⊤ := ENNReal.div_ne_top (by simp) (by exact_mod_cast hMd.ne')
  apply (ENNReal.toReal_le_toReal h1 h2).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
  have h' : sn * N * Md ≤ Mn * (sd * D) := by
    calc sn * N * Md = Md * sn * N := by ring
      _ ≤ Mn * sd * D := h
      _ = Mn * (sd * D) := by ring
  exact_mod_cast h'
theorem poissonCheckG_sound {un ud ln ld : ℕ} {f : ℕ → ℕ} {ok : ℕ → Bool}
    {dbase sn sd Mn Md R : ℕ}
    (hcheck : Kernel.poissonCheckG un ud ln ld f ok dbase sn sd Mn Md R = true)
    (hud : 0 < ud) (hld : 0 < ld) (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {rate : ENNReal} (hrate : rate ≤ 1) {T : ℕ}
    (hlam : (T : ENNReal) * rate ≤ (ln : ENNReal) / ld)
    (hu : (1 - rate) ^ (T - R) ≤ (un : ENNReal) / ud)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ R, g r ≤ (f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal))
    (htail : ∀ r, R < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage rate T g ≤ (Mn : ENNReal) / Md := by
  have hineq : Md * sn * ((∑ r ∈ Finset.range (R + 1), termNum un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Kernel.Q ^ (9 * R)) ≤ Mn * sd * denom ud ld dbase R := by
    have h := hcheck
    simp only [Kernel.poissonCheckG, Bool.and_eq_true, decide_eq_true_eq] at h
    have h2 := h.2
    rw [range_foldr_eq_sum] at h2
    unfold denom termNum
    refine h2.trans_eq ?_
    ring
  have hD := denom_pos ud ld dbase R hud hld hdb
  refine le_trans (mul_le_mul' le_rfl ?_) (scale_le sn sd Mn Md _ _ hsd hMd hD hineq)
  refine (binomialAverage_truncate rate T (R + 1) g 1 (fun r hr => htail r hr)).trans ?_
  have hsplit : ((((∑ r ∈ Finset.range (R + 1), termNum un ln ld R f r) * ld * (R + 1) +
      ln ^ (R + 1) * ud * dbase * Kernel.Q ^ (9 * R) : ℕ)) : ENNReal) / (denom ud ld dbase R : ℕ) =
      (∑ r ∈ Finset.range (R + 1),
        ((termNum un ln ld R f r * ld * (R + 1) : ℕ) : ENNReal) / (denom ud ld dbase R : ℕ)) +
      ((ln ^ (R + 1) * ud * dbase * Kernel.Q ^ (9 * R) : ℕ) : ENNReal) /
        (denom ud ld dbase R : ℕ) := by
    rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_add, Nat.cast_sum, ENNReal.add_div]
    congr 1
    simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [one_mul, hsplit]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro r hr
    have hr' : r ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [← term_eq un ud ln ld dbase R r f hr' hud hld hdb]
    exact mul_le_mul' (binomWeight_le rate T R r hr' _ _ hlam hu) (hpay r hr')
  · refine (binomial_tail rate hrate T (R + 1)).trans ?_
    rw [← tail_eq ud ln ld dbase R hud hld hdb]
    gcongr
theorem poissonCheckG_sound_horizon {un ud : ℕ} {f : ℕ → ℕ} {ok : ℕ → Bool}
    {dbase sn sd Mn Md : ℕ}
    (hcheck : Kernel.poissonCheckG un ud 513 256 f ok dbase sn sd Mn Md 80 = true)
    (hud : 0 < ud) (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {T : ℕ} (hT : T ≤ 2 ^ 32 + 2 ^ 23)
    (hu : (1 - (2 ^ 31 : ENNReal)⁻¹) ^ (T - 80) ≤ (un : ENNReal) / ud)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ (f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal))
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage (2 ^ 31)⁻¹ T g ≤ (Mn : ENNReal) / Md :=
  poissonCheckG_sound hcheck hud (by norm_num) hdb hsd hMd rate_le_one (lam_le T hT) hu g hpay
    htail
theorem poissonCheck_sound_T3 {f : ℕ → ℕ} {ok : ℕ → Bool} {dbase sn sd Mn Md : ℕ}
    (hcheck : Kernel.poissonCheck f ok dbase sn sd Mn Md 80 = true)
    (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ (f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal))
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage (2 ^ 31)⁻¹ horizonT3 g ≤ (Mn : ENNReal) / Md := by
  rw [Kernel.poissonCheck_eq_G] at hcheck
  exact poissonCheckG_sound_horizon hcheck (by norm_num) hdb hsd hMd (by rw [horizonT3_eq])
    rejection_T3 g hpay htail
theorem poissonCheckW_sound {f : ℕ → ℕ} {ok : ℕ → Bool} {dbase sn sd Mn Md : ℕ}
    (hcheck : Kernel.poissonCheckG 271 2000 513 256 f ok dbase sn sd Mn Md 80 = true)
    (hdb : 0 < dbase) (hsd : 0 < sd) (hMd : 0 < Md)
    {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
    (g : ℕ → ENNReal)
    (hpay : ∀ r ≤ 80, g r ≤ (f r : ENNReal) / ((dbase * Kernel.Q ^ (9 * r) : ℕ) : ENNReal))
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (sn : ENNReal) / sd * binomialAverage (2 ^ 31)⁻¹ T g ≤ (Mn : ENNReal) / Md :=
  poissonCheckG_sound_horizon hcheck (by norm_num) hdb hsd hMd hT2 (rejection_window T hT1) g
    hpay htail
theorem ratio_pow (a b k : ℕ) :
    ((a : ENNReal) / b) ^ k = ((a ^ k : ℕ) : ENNReal) / ((b ^ k : ℕ) : ENNReal) := by
  simp only [div_eq_mul_inv, mul_pow, Nat.cast_pow, ENNReal.inv_pow]
theorem ratio_pow8_mul (a c b : ℕ) :
    ((a : ENNReal) / b) ^ 8 * ((c : ENNReal) / b) =
      ((a ^ 8 * c : ℕ) : ENNReal) / ((b ^ 9 : ℕ) : ENNReal) := by
  simp only [div_eq_mul_inv, mul_pow, Nat.cast_mul, Nat.cast_pow, ENNReal.inv_pow]
  ring
theorem Q_pow (c r : ℕ) : (c * Kernel.Q ^ r) ^ 9 = c ^ 9 * Kernel.Q ^ (9 * r) := by
  rw [mul_pow, ← pow_mul, mul_comm r 9]
noncomputable def meanPay (r : ℕ) : ENNReal :=
  ((Kernel.xNum r : ENNReal) / ((Kernel.Nn * Kernel.Q ^ r : ℕ) : ENNReal)) ^ 9
noncomputable def nearPay (r : ℕ) : ENNReal :=
  ((Kernel.xNum r : ENNReal) / ((Kernel.Nn * Kernel.Q ^ r : ℕ) : ENNReal)) ^ 8 *
    ((Kernel.xfNum r : ENNReal) / ((Kernel.Nn * Kernel.Q ^ r : ℕ) : ENNReal))
noncomputable def diagPay (r : ℕ) : ENNReal :=
  ((Kernel.yNum r : ENNReal) / ((Kernel.Kc * Kernel.Nn ^ 2 * Kernel.Q ^ r : ℕ) : ENNReal)) ^ 9
theorem meanPay_eq (r : ℕ) : meanPay r =
    ((Kernel.xNum r ^ 9 : ℕ) : ENNReal) / ((Kernel.Nn ^ 9 * Kernel.Q ^ (9 * r) : ℕ) : ENNReal) := by
  rw [meanPay, ratio_pow, Q_pow]
theorem nearPay_eq (r : ℕ) : nearPay r =
    ((Kernel.xNum r ^ 8 * Kernel.xfNum r : ℕ) : ENNReal) /
      ((Kernel.Nn ^ 9 * Kernel.Q ^ (9 * r) : ℕ) : ENNReal) := by
  rw [nearPay, ratio_pow8_mul, Q_pow]
theorem diagPay_eq (r : ℕ) : diagPay r =
    ((Kernel.yNum r ^ 9 : ℕ) : ENNReal) /
      (((Kernel.Kc * Kernel.Nn ^ 2) ^ 9 * Kernel.Q ^ (9 * r) : ℕ) : ENNReal) := by
  rw [diagPay, ratio_pow, Q_pow]
section Certificates
variable (g : ℕ → ENNReal)
theorem mean_bound_T3 (hpay : ∀ r ≤ 80, g r ≤ meanPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ horizonT3 g ≤ 37 / 64 := by
  have h := poissonCheck_sound_T3 (f := fun r => Kernel.xNum r ^ 9) (ok := Kernel.xOk)
    (dbase := Kernel.Nn ^ 9) (sn := Kernel.A) (sd := 1) (Mn := 37) (Md := 64) Kernel.mean_ok
    (by decide) (by norm_num) (by norm_num) g (fun r hr => (hpay r hr).trans_eq (meanPay_eq r))
    htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h
theorem mean_tight_bound_T3 (hpay : ∀ r ≤ 80, g r ≤ meanPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ horizonT3 g ≤ 1 / 10 := by
  have h := poissonCheck_sound_T3 (f := fun r => Kernel.xNum r ^ 9) (ok := Kernel.xOk)
    (dbase := Kernel.Nn ^ 9) (sn := Kernel.A) (sd := 1) (Mn := 1) (Md := 10) Kernel.mean_tight_ok
    (by decide) (by norm_num) (by norm_num) g (fun r hr => (hpay r hr).trans_eq (meanPay_eq r))
    htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h
theorem near_bound_T3 (hpay : ∀ r ≤ 80, g r ≤ nearPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    63 * (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ horizonT3 g ≤ 404 := by
  have h := poissonCheck_sound_T3 (f := fun r => Kernel.xNum r ^ 8 * Kernel.xfNum r)
    (ok := fun r => Kernel.xOk r && Kernel.xfOk r)
    (dbase := Kernel.Nn ^ 9) (sn := 63 * Kernel.A) (sd := 1) (Mn := 404) (Md := 1) Kernel.near_ok
    (by decide) (by norm_num) (by norm_num) g (fun r hr => (hpay r hr).trans_eq (nearPay_eq r))
    htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] using h
theorem diag_bound_T3 (hpay : ∀ r ≤ 80, g r ≤ diagPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31)⁻¹ horizonT3 g ≤
      18400 / 100000000 := by
  have h := poissonCheck_sound_T3 (f := fun r => Kernel.yNum r ^ 9) (ok := Kernel.yOk)
    (dbase := (Kernel.Kc * Kernel.Nn ^ 2) ^ 9) (sn := Kernel.A ^ 2) (sd := 2 ^ 31) (Mn := 18400)
    (Md := 100000000) Kernel.diag_ok
    (by decide) (by norm_num) (by norm_num) g (fun r hr => (hpay r hr).trans_eq (diagPay_eq r))
    htail
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
variable {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32 + 2 ^ 23)
include hT1 hT2
theorem mean_bound_W (hpay : ∀ r ≤ 80, g r ≤ meanPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ T g ≤ 37 / 64 := by
  have h := poissonCheckW_sound (f := fun r => Kernel.xNum r ^ 9) (ok := Kernel.xOk)
    (dbase := Kernel.Nn ^ 9) (sn := Kernel.A) (sd := 1) (Mn := 37) (Md := 64) Kernel.meanW_ok
    (by decide) (by norm_num) (by norm_num) hT1 hT2 g
    (fun r hr => (hpay r hr).trans_eq (meanPay_eq r)) htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h
theorem mean_tight_bound_W (hpay : ∀ r ≤ 80, g r ≤ meanPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ T g ≤ 1 / 10 := by
  have h := poissonCheckW_sound (f := fun r => Kernel.xNum r ^ 9) (ok := Kernel.xOk)
    (dbase := Kernel.Nn ^ 9) (sn := Kernel.A) (sd := 1) (Mn := 1) (Md := 10) Kernel.meanTightW_ok
    (by decide) (by norm_num) (by norm_num) hT1 hT2 g
    (fun r hr => (hpay r hr).trans_eq (meanPay_eq r)) htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h
theorem near_bound_W (hpay : ∀ r ≤ 80, g r ≤ nearPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    63 * (Kernel.A : ENNReal) * binomialAverage (2 ^ 31)⁻¹ T g ≤ 404 := by
  have h := poissonCheckW_sound (f := fun r => Kernel.xNum r ^ 8 * Kernel.xfNum r)
    (ok := fun r => Kernel.xOk r && Kernel.xfOk r)
    (dbase := Kernel.Nn ^ 9) (sn := 63 * Kernel.A) (sd := 1) (Mn := 404) (Md := 1) Kernel.nearW_ok
    (by decide) (by norm_num) (by norm_num) hT1 hT2 g
    (fun r hr => (hpay r hr).trans_eq (nearPay_eq r)) htail
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] using h
theorem diag_bound_W (hpay : ∀ r ≤ 80, g r ≤ diagPay r)
    (htail : ∀ r, 80 < r → g r ≤ 1) :
    (Kernel.A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31)⁻¹ T g ≤ 18400 / 100000000 := by
  have h := poissonCheckW_sound (f := fun r => Kernel.yNum r ^ 9) (ok := Kernel.yOk)
    (dbase := (Kernel.Kc * Kernel.Nn ^ 2) ^ 9) (sn := Kernel.A ^ 2) (sd := 2 ^ 31) (Mn := 18400)
    (Md := 100000000) Kernel.diagW_ok
    (by decide) (by norm_num) (by norm_num) hT1 hT2 g
    (fun r hr => (hpay r hr).trans_eq (diagPay_eq r)) htail
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h
end Certificates
theorem poissonCheckG_ok {un ud ln ld : ℕ} {f : ℕ → ℕ} {ok : ℕ → Bool} {dbase sn sd Mn Md R : ℕ}
    (hcheck : Kernel.poissonCheckG un ud ln ld f ok dbase sn sd Mn Md R = true) :
    ∀ r ≤ R, ok r = true := by
  simp only [Kernel.poissonCheckG, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hcheck
  intro r hr
  exact hcheck.1 r (Nat.lt_succ_of_le hr)
theorem xOk_le_80 : ∀ r ≤ 80, Kernel.xOk r = true := poissonCheckG_ok Kernel.meanW_ok
theorem xfOk_le_80 : ∀ r ≤ 80, Kernel.xfOk r = true := fun r hr => by
  have h := poissonCheckG_ok Kernel.nearW_ok r hr
  simp only [Bool.and_eq_true] at h
  exact h.2
theorem yOk_le_80 : ∀ r ≤ 80, Kernel.yOk r = true := poissonCheckG_ok Kernel.diagW_ok
def smom (d : List (ℕ × ℤ)) (X : ℤ) (r : ℕ) : ℤ := (d.map fun e => e.2 * (X + e.1) ^ r).sum
def smom2 (d : List (ℕ × ℤ)) (X : ℤ) (r : ℕ) : ℤ := (d.map fun e => e.2 * smom d (X + e.1) r).sum
theorem wpos_sub_wneg (d : List (ℕ × ℤ)) (base r : ℕ) :
    (Kernel.wpos d base r : ℤ) - Kernel.wneg d base r = smom d base r := by
  unfold smom
  induction d with
  | nil => simp [Kernel.wpos, Kernel.wneg]
  | cons e d ih =>
      simp only [Kernel.wpos, Kernel.wneg, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
      push_cast
      have h := Int.toNat_sub_toNat_neg e.2
      linear_combination ((base : ℤ) + e.1) ^ r * h + ih
theorem wwfold_sub (d l : List (ℕ × ℤ)) (base r : ℕ) :
    ((l.foldr (fun e s => e.2.toNat * Kernel.wpos d (base + e.1) r +
        (-e.2).toNat * Kernel.wneg d (base + e.1) r + s) 0 : ℕ) : ℤ) -
      ((l.foldr (fun e s => e.2.toNat * Kernel.wneg d (base + e.1) r +
        (-e.2).toNat * Kernel.wpos d (base + e.1) r + s) 0 : ℕ) : ℤ) =
    (l.map fun e => e.2 * smom d ((base : ℤ) + e.1) r).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      push_cast at ih ⊢
      have h := Int.toNat_sub_toNat_neg e.2
      have hw := wpos_sub_wneg d (base + e.1) r
      push_cast at hw
      linear_combination
        ((Kernel.wpos d (base + e.1) r : ℤ) - Kernel.wneg d (base + e.1) r) * h + e.2 * hw + ih
theorem wwpos_sub_wwneg (d : List (ℕ × ℤ)) (base r : ℕ) :
    (Kernel.wwpos d base r : ℤ) - Kernel.wwneg d base r = smom2 d base r :=
  wwfold_sub d d base r
theorem xNum_eq (r : ℕ) (hr : r ≤ 80) :
    (Kernel.xNum r : ℤ) = smom Kernel.w1Data Kernel.B1 r := by
  have h := xOk_le_80 r hr
  simp only [Kernel.xOk, decide_eq_true_eq] at h
  rw [Kernel.xNum, Nat.cast_sub h, wpos_sub_wneg]
theorem xfNum_eq (r : ℕ) (hr : r ≤ 80) :
    (Kernel.xfNum r : ℤ) = smom Kernel.wfData Kernel.B1 r := by
  have h := xfOk_le_80 r hr
  simp only [Kernel.xfOk, decide_eq_true_eq] at h
  rw [Kernel.xfNum, Nat.cast_sub h, wpos_sub_wneg]
theorem yNum_eq (r : ℕ) (hr : r ≤ 80) :
    (Kernel.yNum r : ℤ) =
      smom Kernel.w2Data Kernel.B1 r + (Kernel.Kc - 1 : ℕ) * smom2 Kernel.w1Data Kernel.B2 r := by
  have h := yOk_le_80 r hr
  simp only [Kernel.yOk, decide_eq_true_eq] at h
  rw [Kernel.yNum, Nat.cast_sub h, ← wpos_sub_wneg, ← wwpos_sub_wwneg]
  simp only [Kernel.yPos, Kernel.yNeg]
  push_cast
  ring
end ClaudeWCT.Numerics.PoissonReflect
end
