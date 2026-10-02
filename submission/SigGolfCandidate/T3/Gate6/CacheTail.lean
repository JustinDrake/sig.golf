import SigGolfCandidate.T3.Gate6.CachePotential
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ totalWeight
set_option maxHeartbeats 300000

/-- A bound for the actual lazy-cache process, with arbitrary adaptive
private-random query policy. The cache's type enforces unique input keys. -/
theorem run_bound {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) (q fuel : Nat)
    (history : History Input) (cache : Cache Input) (hcap : fuel+cache.entries.length≤q) :
    Pr[=true | run policy fuel history cache]≤totalWeight q cache := by
  induction fuel generalizing history cache with
  | zero =>
      by_cases hb : Bad cache
      · simpa [run,hb] using totalWeight_bad q cache (by omega) hb
      · simp [run,hb]
  | succ fuel ih =>
      by_cases hb : Bad cache
      · simpa [run,hb] using totalWeight_bad q cache (by omega) hb
      · simp only [run,if_neg hb,probOutput_bind_eq_tsum]
        calc
          _ ≤ ∑' input,Pr[=input | policy history]*totalWeight q cache := by
            apply ENNReal.tsum_le_tsum
            intro input
            apply mul_le_mul' le_rfl
            split <;> rename_i hf
            · exact ih _ _ (by omega)
            · rw [probOutput_bind_eq_tsum]
              calc
                _ ≤ ∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
                    totalWeight q (insert cache input output hf) := by
                  apply ENNReal.tsum_le_tsum
                  intro output
                  exact mul_le_mul' le_rfl (ih _ _ (by rw [insert_length];omega))
                _ ≤ _ := expected_totalWeight_insert q cache input hf
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- Across every prefix of at mostq adaptive queries, no59-bit mark exceeds
its distinct-fresh-cache expectation plus2^47 except with probability2^-700.
Repeated inputs reuse their previous output and cannot add cache records. -/
theorem adaptive_cache_tail {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) (q : Nat) (hq : q≤2^127) :
    Pr[=true | run policy q [] empty]≤(2^700 : ENNReal)⁻¹ :=
  (run_bound policy q q [] empty (by simp [empty])).trans (initial_totalWeight_le q hq)

theorem adaptive_cache_exception_rate {Input : Type} [DecidableEq Input]
    (policy : History Input → ProbComp Input) (q : Nat) (hq : q≤2^127) :
    Pr[=true | run policy q [] empty]≤(q : ENNReal)/2^153 := by
  by_cases hz : q=0
  · subst q
    simp [run,not_bad_empty]
  · calc
      _ ≤ (2^700 : ENNReal)⁻¹ := adaptive_cache_tail policy q hq
      _ ≤ (2^153 : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by omega))
      _ = (1 : ENNReal)/2^153 := by simp
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 1≤q by omega)) _

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.adaptive_cache_tail
#print axioms SigGolfResearch.Gate6.Cache.adaptive_cache_exception_rate
