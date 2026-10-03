import SigGolfCandidate.T3.Gate6.MomentNumeric
import SigGolfCandidate.T3.Gate6.SourceBudget
import SigGolfCandidate.T3.BPORS
import SigGolfCandidate.T3.Secc.WotsTransportSplit
import SigGolfCandidate.T3.Secc.PairGuessWorld

section


namespace SigGolfResearch.Gate3Closing115
open ENNReal SigGolfResearch.Gate6.Moments.Numeric
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
theorem mean_bound :
    (2:ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234≤37/64 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]
theorem variance_excess : (18400/100000000:ℚ)*(8/13)≤11324/100000000 := by norm_num
theorem reuse_bound : SigGolfResearch.Gate6.Budget.p0≤(1/64:ℚ) := by
  norm_num [SigGolfResearch.Gate6.Budget.p0]
theorem prefix_rate :
    ((3/2:ℚ)+4/8192+2/(8192^2))*(8192/8191)+4/8192*(8192/8191)^2+
      2*57/8192*(8192/8191)≤181/100 := by norm_num
theorem encoding_rate : (1:ℚ)+2*3306/8192*(8192/8191)≤181/100 := by norm_num
theorem small_excess_rate : (201:ℚ)*(11324/100000000)≤1/40 := by norm_num
theorem near_rate : (8192/8191:ℚ)*(404+21*201/2^25)≤405 := by norm_num
theorem small_first_rate : (181/100:ℚ)+1/40+1/1000≤37/20 := by norm_num
theorem pointwise_excess (v m : ℝ) (hm : m≤37/64) :
    (13/8)*max 0 (v-63/64)+2*m*v≤v^2+m^2 := by
  rcases le_total v (63/64) with hv|hv
  · rw [max_eq_left (sub_nonpos.mpr hv)];nlinarith [sq_nonneg (v-m)]
  · rw [max_eq_right (sub_nonneg.mpr hv)]
    nlinarith [sq_nonneg (v-m-13/16)]
theorem small_closing_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 1 / 2 ^ 13) :
    37 / 20 * y + 512 * y ^ 2 + 1 / 2 ^ 132 + (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : 512 * y ^ 2 ≤ y / 16 := by
    have h := mul_le_mul_of_nonneg_left hhigh hn
    have h2 : y ^ 2 = y * y := by ring
    rw [h2]
    have : (512 : ℝ) * (y * (1 / 2 ^ 13)) = y / 16 := by ring
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 16 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 128) / 16 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by norm_num)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 24 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 128) / 2 ^ 24 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy18 : y / 2 ^ 18 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy572 : y / 2 ^ 572 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy24 : y / 2 ^ 24 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  linarith
theorem large_closing_real (y : ℝ) (hlow : 1 / 2 ^ 13 ≤ y) :
    (2 * y - y ^ 2) + y * (11324 / 100000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 20) + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : y * (1 / 2 ^ 13) ≤ y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlow hn
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 2 ^ 119 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 13) / 2 ^ 119 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 687 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 13) / 2 ^ 687 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 139 := by
    have : (1 : ℝ) / 2 ^ 152 = (1 / 2 ^ 13) / 2 ^ 139 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy118 : y / 2 ^ 119 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy686 : y / 2 ^ 687 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy138 : y / 2 ^ 139 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  norm_num at hsq hy118 hy686 hy138 hy128 ⊢
  nlinarith
end SigGolfResearch.Gate3Closing115
#print axioms SigGolfResearch.Gate3Closing115.mean_bound
#print axioms SigGolfResearch.Gate3Closing115.variance_excess
#print axioms SigGolfResearch.Gate3Closing115.reuse_bound
#print axioms SigGolfResearch.Gate3Closing115.prefix_rate
#print axioms SigGolfResearch.Gate3Closing115.encoding_rate
#print axioms SigGolfResearch.Gate3Closing115.small_excess_rate
#print axioms SigGolfResearch.Gate3Closing115.near_rate
#print axioms SigGolfResearch.Gate3Closing115.small_first_rate
#print axioms SigGolfResearch.Gate3Closing115.pointwise_excess
#print axioms SigGolfResearch.Gate3Closing115.small_closing_real
#print axioms SigGolfResearch.Gate3Closing115.large_closing_real
end

section


namespace SigGolfCandidate.T3.Security.SeccClosing
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option exponentiation.threshold 1024
irreducible_def budgetSplit : Nat := 2 ^ 115
noncomputable irreducible_def smallCoefficient : ENNReal := 37 / 20
noncomputable irreducible_def smallQuadratic : ENNReal := 2 ^ 9
noncomputable irreducible_def smallAbsolute : ENNReal := ((2 : ENNReal) ^ 132)⁻¹
noncomputable irreducible_def excessRate : ENNReal := 11324 / 100000000
noncomputable irreducible_def cacheRate : ENNReal := ((2 : ENNReal) ^ 25)⁻¹
noncomputable irreducible_def largeReserveRate : ENNReal := ((2 : ENNReal) ^ 20)⁻¹
noncomputable irreducible_def largeReserveAbsolute : ENNReal := ((2 : ENNReal) ^ 132)⁻¹
noncomputable def secTerms (q : Nat) : ENNReal :=
  q / (2 : ENNReal) ^ 146 + (2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 152)⁻¹ + q / ((2 ^ 256 : Nat) : ENNReal)
noncomputable def smallBound (q : Nat) : ENNReal :=
  smallCoefficient * ((q : ENNReal) / 2 ^ 128) + smallQuadratic * ((q : ENNReal) / 2 ^ 128) ^ 2 + smallAbsolute
noncomputable def largeBound (q : Nat) : ENNReal :=
  ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) + (q : ENNReal) * excessRate / 2 ^ 128 +
    (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute
theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num
theorem one_le_budgetSplit : 1 ≤ budgetSplit := by
  rw [budgetSplit_def]
  norm_num
private theorem small_real (y : ℝ) (hlow : 1/2^128≤y) (hhigh : y≤1/2^13) :
    37/20*y+2^9*y^2+1/2^132+(y/2^18+1/2^700+1/2^152+y/2^128)≤2*y := by
  simpa only [show (2:ℝ)^9=512 by norm_num] using
    SigGolfResearch.Gate3Closing115.small_closing_real y hlow hhigh
private theorem large_real (y : ℝ) (hlow : 1/2^13≤y) :
    (2*y-y^2)+y*(11324/100000000)+y*(1/2^25)+y*(1/2^20)+1/2^132+
      (y/2^18+1/2^700+1/2^152+y/2^128)≤2*y :=
  SigGolfResearch.Gate3Closing115.large_closing_real y hlow
theorem small_closing (q : Nat) (hq : 1 ≤ q) (hsplit : q ≤ budgetSplit) :
    smallBound q + secTerms q ≤ (q : ENNReal) / 2 ^ 127 := by
  rw [budgetSplit_def] at hsplit
  unfold smallBound secTerms
  rw [smallCoefficient_def, smallQuadratic_def, smallAbsolute_def]
  have hlow : (1 : ℝ) / 2 ^ 128 ≤ (q : ℝ) / 2 ^ 128 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hq
  have hhigh : (q : ℝ) / 2 ^ 128 ≤ 1 / 2 ^ 13 := by
    have hq' : (q : ℝ) ≤ 2 ^ 115 := by exact_mod_cast hsplit
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h := small_real ((q : ℝ) / 2 ^ 128) hlow hhigh
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  convert h using 1 <;> ring
theorem large_closing (q : Nat) (hsplit : budgetSplit ≤ q) (hq : q ≤ 2 ^ 127) :
    largeBound q + secTerms q ≤ (q : ENNReal) / 2 ^ 127 := by
  rw [budgetSplit_def] at hsplit
  unfold largeBound secTerms
  rw [excessRate_def, cacheRate_def, largeReserveRate_def, largeReserveAbsolute_def]
  have hlow : (1 : ℝ) / 2 ^ 13 ≤ (q : ℝ) / 2 ^ 128 := by
    have hq' : (2 : ℝ) ^ 115 ≤ q := by exact_mod_cast hsplit
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hhigh : (q : ℝ) / 2 ^ 128 ≤ 1 / 2 := by
    have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hp : 0 ≤ 2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2 := by
    have hn : 0 ≤ (q : ℝ) / 2 ^ 128 := by positivity
    nlinarith
  have h := large_real ((q : ℝ) / 2 ^ 128) hlow
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.toReal_ofReal hp]
  convert h using 1 <;> ring
theorem largeBound_of_parts (q : Nat) (win contact certificate mass : ENNReal)
    (hsplit : win ≤ contact + certificate)
    (hpotential : contact + mass / 2 ^ 128 ≤ ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2))
    (hcertificate : certificate ≤ mass / 2 ^ 128 + (q : ENNReal) * excessRate / 2 ^ 128 +
      (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute) :
    win ≤ largeBound q := by
  unfold largeBound
  calc
    win ≤ contact + certificate := hsplit
    _ ≤ contact + (mass / 2 ^ 128 + (q : ENNReal) * excessRate / 2 ^ 128 +
        (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute) :=
      add_le_add le_rfl hcertificate
    _ = (contact + mass / 2 ^ 128) + (q : ENNReal) * excessRate / 2 ^ 128 +
        (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute := by
      simp only [add_assoc]
    _ ≤ _ := by gcongr
theorem probEvent_le_contact_add {β : Type} (law : PMF β) (win contact : β → Prop) (count : β → Prop)
    (hcount : ∀ value, win value → count value) :
    Pr[win | law] ≤ Pr[fun value => count value ∧ contact value | law] +
      Pr[fun value => win value ∧ ¬contact value | law] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hw : win value
  · have hc := hcount value hw
    by_cases hk : contact value
    · simp [hw, hc, hk]
    · simp [hw, hc, hk]
  · simp only [hw, if_false, zero_le]
theorem cleanWin_le_contact_add (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (Contact : FirstHit.Recorded Bool → Prop) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤
      Pr[fun result => result.2.2.base.source.1 ≤ q ∧ Contact (QueryRecorded.recordedTrace result) |
        PaddedGame.tracedExperiment adversary q hq] +
      Pr[fun result => QueryRecorded.CleanWin q result ∧ ¬Contact (QueryRecorded.recordedTrace result) |
        PaddedGame.tracedExperiment adversary q hq] := by
  classical
  simp only [probEvent_eq_tsum_ite]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hw : QueryRecorded.CleanWin q result
  · have hcount : result.2.2.base.source.1 ≤ q := hw.2.1
    by_cases hc : Contact (QueryRecorded.recordedTrace result)
    · simp [hw, hcount, hc]
    · simp [hw, hcount, hc]
  · simp only [hw, if_false, zero_le]
theorem large_route_of_contact (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (Contact : FirstHit.Recorded Bool → Prop) (digests : FirstHit.Recorded Bool → Nat)
    (hpotential : Pr[fun result => result.2.2.base.source.1 ≤ q ∧ Contact (QueryRecorded.recordedTrace result) |
        PaddedGame.tracedExperiment adversary q hq] +
      (∑' result, Pr[= result | PaddedGame.tracedExperiment adversary q hq] *
        (digests (QueryRecorded.recordedTrace result) : ENNReal)) / 2 ^ 128 ≤
      ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2))
    (hcertificate : Pr[fun result => QueryRecorded.CleanWin q result ∧ ¬Contact (QueryRecorded.recordedTrace result) |
        PaddedGame.tracedExperiment adversary q hq] ≤
      (∑' result, Pr[= result | PaddedGame.tracedExperiment adversary q hq] *
        (digests (QueryRecorded.recordedTrace result) : ENNReal)) / 2 ^ 128 +
        (q : ENNReal) * excessRate / 2 ^ 128 + (q : ENNReal) * cacheRate / 2 ^ 128 +
        (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  largeBound_of_parts q _ _ _ _ (cleanWin_le_contact_add adversary q hq Contact) hpotential hcertificate
theorem x_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (q : ENNReal) / 2 ^ 128 ≤ ((2 : ENNReal) ^ 13)⁻¹ := by
  rw [budgetSplit_def] at hsplit
  rw [ENNReal.div_le_iff (by positivity) (by finiteness)]
  calc
    (q : ENNReal) ≤ (2 ^ 115 : Nat) := by exact_mod_cast hsplit
    _ = ((2 : ENNReal) ^ 13)⁻¹ * 2 ^ 128 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem sq_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    ((q : ENNReal) / 2 ^ 128) ^ 2 ≤ ((2 : ENNReal) ^ 13)⁻¹ * ((q : ENNReal) / 2 ^ 128) := by
  rw [pow_two]
  exact mul_le_mul' (x_le_of_small q hsplit) le_rfl
theorem one_sub_x_ge_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (8191 / 8192 : ENNReal) ≤ 1 - (q : ENNReal) / 2 ^ 128 := by
  have hx := x_le_of_small q hsplit
  refine le_trans ?_ (tsub_le_tsub_left hx 1)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_pow]) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem div_sub_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (q : ENNReal) / ((2 ^ 128 - q : Nat) : ENNReal) ≤ (8192 / 8191 : ENNReal) * ((q : ENNReal) / 2 ^ 128) := by
  rw [budgetSplit_def] at hsplit
  have hlt : q < 2 ^ 128 := lt_of_le_of_lt hsplit (by norm_num)
  have hden : (0 : ℝ) < ((2 ^ 128 - q : Nat) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
  have hpos : ((2 ^ 128 - q : Nat) : ENNReal) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hlt).ne'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
  have hcast : ((2 ^ 128 - q : Nat) : ℝ) = 2 ^ 128 - (q : ℝ) := by
    rw [Nat.cast_sub hlt.le]
    norm_num
  rw [hcast] at hden ⊢
  have hq' : (q : ℝ) ≤ 2 ^ 115 := by exact_mod_cast hsplit
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [div_le_iff₀ hden]
  have : 8192 / 8191 * ((q : ℝ) / 2 ^ 128) * (2 ^ 128 - (q : ℝ)) =
      (q : ℝ) * (8192 / 8191 * (1 - (q : ℝ) / 2 ^ 128)) := by ring
  rw [this]
  have hx : (q : ℝ) / 2 ^ 128 ≤ 1 / 8192 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfac : 1 ≤ 8192 / 8191 * (1 - (q : ℝ) / 2 ^ 128) := by linarith
  nlinarith
theorem smallBound_of_le (q : Nat) (P c Q A : ENNReal) (hc : c ≤ smallCoefficient) (hQ : Q ≤ smallQuadratic)
    (hA : A ≤ smallAbsolute)
    (hP : P ≤ c * ((q : ENNReal) / 2 ^ 128) + Q * ((q : ENNReal) / 2 ^ 128) ^ 2 + A) : P ≤ smallBound q := by
  unfold smallBound
  exact hP.trans (by gcongr)
theorem securityP_of_routes
    (hsmall : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ budgetSplit →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ smallBound q)
    (hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), budgetSplit ≤ q →
      Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q) :
    SecurityP := by
  apply PaddedGame.securityP_of_clean_bound
  intro adversary q hpositive hq
  have key : Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] + secTerms q ≤
      (q : ENNReal) / 2 ^ 127 := by
    by_cases hs : q ≤ budgetSplit
    · exact (add_le_add (hsmall adversary q hq hpositive hs) le_rfl).trans (small_closing q hpositive hs)
    · exact (add_le_add (hlarge adversary q hq (by omega)) le_rfl).trans (large_closing q (by omega) hq)
  simpa only [secTerms, add_assoc] using key
end SigGolfCandidate.T3.Security.SeccClosing
end

section



namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
def IsDigestQuery (input : T3.Spec.Domain) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32),
    input = .inl (.inr (pad64 (digestInput rho message counter)))
def digestClass : SeccLaw.SampleClass := fun _ input => IsDigestQuery input
def signRatio : Nat := 201
noncomputable def nearPrice : ENNReal := 404
noncomputable def nearTerm (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (nearPrice * q / 2 ^ 128 + 21 * (signRatio * q : Nat) * SeccClosing.cacheRate / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700)
def CaseCSmallBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq digestClass +
        ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700
end SigGolfCandidate.T3.Security.Wots
end
