import SigGolfCandidate.T3.BPORS

/-!
# SECC closing arithmetic and final assembly (BP-C)

The exact remaining endpoint is `PaddedGame.securityP_of_clean_bound`: for every adversary and `1 ≤ q ≤ 2^127`,

    Pr[CleanWin q | tracedExperiment adversary q hq] + secTerms q ≤ q / 2^127,

where `secTerms q = q/2^146 + 2^-700 + 2^-224 + q/2^256` are SEC's fixed reduction errors.

The proof splits at `budgetSplit = 2^114` (x = q/2^128 ≤ 2^-14):

* **small route** (`1 ≤ q ≤ budgetSplit`): the per-class streams must deliver `Pr[CleanWin q] ≤ smallBound q`,
  `smallBound q = smallCoefficient·x + smallQuadratic·x² + smallAbsolute` with the allowances
  `7/4`, `2^11` and `2^-132` (`small_closing`).
* **large route** (`budgetSplit ≤ q ≤ 2^127`): the product-form ("every query at most two units") stream must deliver
  `Pr[CleanWin q] ≤ largeBound q`, `largeBound q = ofReal (2x − x²) + q·excessRate/2^128 + q·cacheRate/2^128 +
  q·largeReserveRate/2^128 + largeReserveAbsolute` (`large_closing`).

`securityP_of_routes` assembles both into `SecurityP`. All constants are irreducible so that the streams only use
the stated facts (`*_def`). `largeBound_of_parts` is the composition shape of the large route (stop/contact event,
potential with creation mass, and certificate charge).
-/

namespace SigGolfCandidate.T3.Security.SeccClosing
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final

set_option exponentiation.threshold 1024

/-- The budget at which the proof switches from the per-class (small) route to the product-form (large) route:
`x_s = 2^114 / 2^128 = 2^-14`. -/
irreducible_def budgetSplit : Nat := 2 ^ 114

/-- First-order small-route allowance: the largest per-query class rate plus every first-order extra term
(e.g. the crude-budget BPORS excess `signRatio·e`). At the split the model needs `1.5075 + 0.0020`. -/
noncomputable irreducible_def smallCoefficient : ENNReal := 7 / 4

/-- Second-order small-route allowance (coefficient of `x²`): pair guesses, near certificate plus one guess,
cache-exception terms of the near certificate, and any `x`-dependent part of a class rate moved here. -/
noncomputable irreducible_def smallQuadratic : ENNReal := 2 ^ 11

/-- Absolute small-route allowance (paid at `q = 1`): proposal-prefix tails and other `q`-independent terms.
An absolute term of size `2^-127` does not fit. -/
noncomputable irreducible_def smallAbsolute : ENNReal := ((2 : ENNReal) ^ 132)⁻¹

/-- BPORS full-certificate excess per unit of budget, relative to `2^-128` (SEC's `full_game_excess_price`). -/
noncomputable irreducible_def excessRate : ENNReal := 987 / 100000000

/-- Cache-exception allowance per unit of budget, relative to `2^-128` (`2^-25`). -/
noncomputable irreducible_def cacheRate : ENNReal := ((2 : ENNReal) ^ 25)⁻¹

/-- Reserve for crude extra first-order terms of the large-route streams, relative to `2^-128` (`2^-16`). -/
noncomputable irreducible_def largeReserveRate : ENNReal := ((2 : ENNReal) ^ 16)⁻¹

/-- Absolute reserve of the large route (`2^-132`). -/
noncomputable irreducible_def largeReserveAbsolute : ENNReal := ((2 : ENNReal) ^ 132)⁻¹

/-- SEC's fixed reduction errors, in the exact syntactic form of `securityP_of_clean_bound`. -/
noncomputable def secTerms (q : Nat) : ENNReal :=
  q / (2 : ENNReal) ^ 146 + (2 : ENNReal)⁻¹ ^ 700 + ((2 : ENNReal) ^ 224)⁻¹ + q / ((2 ^ 256 : Nat) : ENNReal)

/-- The small-route target the per-class streams must reach. -/
noncomputable def smallBound (q : Nat) : ENNReal :=
  smallCoefficient * ((q : ENNReal) / 2 ^ 128) + smallQuadratic * ((q : ENNReal) / 2 ^ 128) ^ 2 + smallAbsolute

/-- The large-route ("native" product-form) target. -/
noncomputable def largeBound (q : Nat) : ENNReal :=
  ENNReal.ofReal (2 * ((q : ℝ) / 2 ^ 128) - ((q : ℝ) / 2 ^ 128) ^ 2) + (q : ENNReal) * excessRate / 2 ^ 128 +
    (q : ENNReal) * cacheRate / 2 ^ 128 + (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute

theorem budgetSplit_le : budgetSplit ≤ 2 ^ 127 := by
  rw [budgetSplit_def]
  norm_num

theorem one_le_budgetSplit : 1 ≤ budgetSplit := by
  rw [budgetSplit_def]
  norm_num

/-! ## Real cores -/

private theorem small_real (y : ℝ) (hlow : 1 / 2 ^ 128 ≤ y) (hhigh : y ≤ 1 / 2 ^ 14) :
    7 / 4 * y + 2 ^ 11 * y ^ 2 + 1 / 2 ^ 132 + (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 224 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : 2 ^ 11 * y ^ 2 ≤ y / 8 := by
    have h := mul_le_mul_of_nonneg_left hhigh hn
    have h2 : y ^ 2 = y * y := by ring
    rw [h2]
    have : (2 : ℝ) ^ 11 * (y * (1 / 2 ^ 14)) = y / 8 := by ring
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 16 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 128) / 16 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by norm_num)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 572 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h224 : (1 : ℝ) / 2 ^ 224 ≤ y / 2 ^ 96 := by
    have : (1 : ℝ) / 2 ^ 224 = (1 / 2 ^ 128) / 2 ^ 96 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy18 : y / 2 ^ 18 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy572 : y / 2 ^ 572 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy96 : y / 2 ^ 96 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 1024 := div_le_div_of_nonneg_left hn (by norm_num) (by norm_num)
  linarith

private theorem large_real (y : ℝ) (hlow : 1 / 2 ^ 14 ≤ y) :
    (2 * y - y ^ 2) + y * (987 / 100000000) + y * (1 / 2 ^ 25) + y * (1 / 2 ^ 16) + 1 / 2 ^ 132 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 224 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have hsq : y * (1 / 2 ^ 14) ≤ y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlow hn
    nlinarith
  have habs : (1 : ℝ) / 2 ^ 132 ≤ y / 2 ^ 118 := by
    have : (1 : ℝ) / 2 ^ 132 = (1 / 2 ^ 14) / 2 ^ 118 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 686 := by
    have : (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 14) / 2 ^ 686 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have h224 : (1 : ℝ) / 2 ^ 224 ≤ y / 2 ^ 210 := by
    have : (1 : ℝ) / 2 ^ 224 = (1 / 2 ^ 14) / 2 ^ 210 := by ring
    rw [this]
    exact div_le_div_of_nonneg_right hlow (by positivity)
  have hy118 : y / 2 ^ 118 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy686 : y / 2 ^ 686 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy210 : y / 2 ^ 210 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  have hy128 : y / 2 ^ 128 ≤ y / 2 ^ 100 := div_le_div_of_nonneg_left hn (by positivity) (by norm_num)
  norm_num at hsq hy118 hy686 hy210 hy128 ⊢
  nlinarith

/-! ## Small route -/

/-- **Small-route closing.** For `1 ≤ q ≤ budgetSplit`, the small-route target plus SEC's fixed errors is at most
`q / 2^127` (margin `x/16`). -/
theorem small_closing (q : Nat) (hq : 1 ≤ q) (hsplit : q ≤ budgetSplit) :
    smallBound q + secTerms q ≤ (q : ENNReal) / 2 ^ 127 := by
  rw [budgetSplit_def] at hsplit
  unfold smallBound secTerms
  rw [smallCoefficient_def, smallQuadratic_def, smallAbsolute_def]
  have hlow : (1 : ℝ) / 2 ^ 128 ≤ (q : ℝ) / 2 ^ 128 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hq
  have hhigh : (q : ℝ) / 2 ^ 128 ≤ 1 / 2 ^ 14 := by
    have hq' : (q : ℝ) ≤ 2 ^ 114 := by exact_mod_cast hsplit
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h := small_real ((q : ℝ) / 2 ^ 128) hlow hhigh
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  convert h using 1 <;> ring

/-! ## Large route -/

/-- **Large-route closing.** For `budgetSplit ≤ q ≤ 2^127`, the product-form target plus SEC's fixed errors is at
most `q / 2^127` (relative margin `3.2·10^-5`). -/
theorem large_closing (q : Nat) (hsplit : budgetSplit ≤ q) (hq : q ≤ 2 ^ 127) :
    largeBound q + secTerms q ≤ (q : ENNReal) / 2 ^ 127 := by
  rw [budgetSplit_def] at hsplit
  unfold largeBound secTerms
  rw [excessRate_def, cacheRate_def, largeReserveRate_def, largeReserveAbsolute_def]
  have hlow : (1 : ℝ) / 2 ^ 14 ≤ (q : ℝ) / 2 ^ 128 := by
    have hq' : (2 : ℝ) ^ 114 ≤ q := by exact_mod_cast hsplit
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

/-- Composition shape of the large route: a contact (stop) event and a certificate event cover the clean win; the
product-form potential pays the contact probability together with the creation mass (one unit per digest query
before the first contact); the certificate charge is that mass plus the excess, cache and reserve terms. -/
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

/-- Generic contact split for any experiment (e.g. a completed experiment carrying an oracle completion): a win
whose budget event `count` holds either contacts or is contact-free. -/
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

/-- Every clean win either contacts an honest label within the budget or is contact-free. `Contact` is any
predicate on the actual recorded trace (for the large route: the first query that guesses a hidden child, hits an
honest output or matches an encoding reference word). -/
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

/-- **Large route on the actual trace.** For any contact predicate `Contact` and any count `digests` of the
digest queries made before the first contact, the two large-route obligations give `largeBound`:

* `hpotential` (product-form potential, through the residual-run coupling): contacts within the budget together with
  one `2^-128` unit per counted digest query cost at most `2x − x²`;
* `hcertificate` (case C, per digest query before the first contact): a contact-free clean win costs that digest
  mass plus the BPORS excess and the cache allowance, charged at the budget `q`, plus the large-route reserves.

In BP-B's test form (digest queries are one-unit stop tests inside `Contact`) take `digests := 0`. -/
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

/-! ## Helpers for the small-route streams -/

/-- Below the split, `x ≤ 2^-14`. -/
theorem x_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (q : ENNReal) / 2 ^ 128 ≤ ((2 : ENNReal) ^ 14)⁻¹ := by
  rw [budgetSplit_def] at hsplit
  rw [ENNReal.div_le_iff (by positivity) (by finiteness)]
  calc
    (q : ENNReal) ≤ (2 ^ 114 : Nat) := by exact_mod_cast hsplit
    _ = ((2 : ENNReal) ^ 14)⁻¹ * 2 ^ 128 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- Below the split a quadratic term is at most `2^-14` times the linear one. -/
theorem sq_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    ((q : ENNReal) / 2 ^ 128) ^ 2 ≤ ((2 : ENNReal) ^ 14)⁻¹ * ((q : ENNReal) / 2 ^ 128) := by
  rw [pow_two]
  exact mul_le_mul' (x_le_of_small q hsplit) le_rfl

/-- Below the split, `1 − x ≥ 16383/16384`, so a factor `1/(1 − x)` may be replaced by `16384/16383`. -/
theorem one_sub_x_ge_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (16383 / 16384 : ENNReal) ≤ 1 - (q : ENNReal) / 2 ^ 128 := by
  have hx := x_le_of_small q hsplit
  refine le_trans ?_ (tsub_le_tsub_left hx 1)
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_sub_of_le (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_pow]) (by finiteness)]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_inv, ENNReal.toReal_pow]

/-- Below the split, `q/(2^128 − q) ≤ (16384/16383)·x` (for the designer's near and pair terms). -/
theorem div_sub_le_of_small (q : Nat) (hsplit : q ≤ budgetSplit) :
    (q : ENNReal) / ((2 ^ 128 - q : Nat) : ENNReal) ≤ (16384 / 16383 : ENNReal) * ((q : ENNReal) / 2 ^ 128) := by
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
  have hq' : (q : ℝ) ≤ 2 ^ 114 := by exact_mod_cast hsplit
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [div_le_iff₀ hden]
  have : 16384 / 16383 * ((q : ℝ) / 2 ^ 128) * (2 ^ 128 - (q : ℝ)) =
      (q : ℝ) * (16384 / 16383 * (1 - (q : ℝ) / 2 ^ 128)) := by ring
  rw [this]
  have hx : (q : ℝ) / 2 ^ 128 ≤ 1 / 16384 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfac : 1 ≤ 16384 / 16383 * (1 - (q : ℝ) / 2 ^ 128) := by linarith
  nlinarith

/-- Monotone plug-in for the small route: any bound with smaller coefficients is a `smallBound`. -/
theorem smallBound_of_le (q : Nat) (P c Q A : ENNReal) (hc : c ≤ smallCoefficient) (hQ : Q ≤ smallQuadratic)
    (hA : A ≤ smallAbsolute)
    (hP : P ≤ c * ((q : ENNReal) / 2 ^ 128) + Q * ((q : ENNReal) / 2 ^ 128) ^ 2 + A) : P ≤ smallBound q := by
  unfold smallBound
  exact hP.trans (by gcongr)

/-! ## Final assembly -/

/-- **Final assembly.** `SecurityP` follows from the small-route bound below the split and the large-route bound
above it, both on the clean traced padded experiment, through `PaddedGame.securityP_of_clean_bound`. -/
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
