import SigGolfCandidate.T3.Gate6.CacheTail
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ totalWeight
set_option maxHeartbeats 300000

/-- None stops without another query. A query includes its private-state
continuation, which receives the actual fresh or memoized output. -/
abbrev Decision (Input State : Type) := Option (Input × (Output → State))

noncomputable def stateRun {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) :
    Nat → State → History Input → Cache Input → ProbComp Bool
  | 0,_,_,cache => pure (decide (Bad cache))
  | steps+1,state,history,cache =>
    if Bad cache then pure true else do
      let choice ← policy state history
      match choice with
      | none => pure false
      | some (input,next) =>
          match fresh : lookup cache input with
          | some output => stateRun policy steps (next output) ((input,output)::history) cache
          | none => do
              let output ← ($ᵗ Output : ProbComp Output)
              stateRun policy steps (next output) ((input,output)::history) (insert cache input output fresh)

theorem stateRun_bound {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (q fuel : Nat)
    (state : State) (history : History Input) (cache : Cache Input)
    (hcap : fuel+cache.entries.length≤q) :
    Pr[=true | stateRun policy fuel state history cache]≤totalWeight q cache := by
  induction fuel generalizing state history cache with
  | zero =>
      by_cases hb : Bad cache
      · simpa [stateRun,hb] using totalWeight_bad q cache (by omega) hb
      · simp [stateRun,hb]
  | succ fuel ih =>
      by_cases hb : Bad cache
      · simpa [stateRun,hb] using totalWeight_bad q cache (by omega) hb
      · simp only [stateRun,if_neg hb,probOutput_bind_eq_tsum]
        calc
          _ ≤ ∑' choice,Pr[=choice | policy state history]*totalWeight q cache := by
            apply ENNReal.tsum_le_tsum
            intro choice
            apply mul_le_mul' le_rfl
            cases choice with
            | none => simp
            | some pair =>
                obtain ⟨input,next⟩ := pair
                dsimp only
                split <;> rename_i hf
                · exact ih _ _ _ (by omega)
                · rw [probOutput_bind_eq_tsum]
                  calc
                    _ ≤ ∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
                        totalWeight q (insert cache input output hf) := by
                      apply ENNReal.tsum_le_tsum
                      intro output
                      exact mul_le_mul' le_rfl (ih _ _ _ (by rw [insert_length];omega))
                    _ ≤ _ := expected_totalWeight_insert q cache input hf
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- All-mark/all-prefix concentration for a bounded lazy random oracle,
allowing persistent private state, private randomness, and early stopping. -/
theorem stateful_cache_tail {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (q : Nat) (hq : q≤2^127) :
    Pr[=true | stateRun policy q state [] empty]≤(2^700 : ENNReal)⁻¹ :=
  (stateRun_bound policy q q state [] empty (by simp [empty])).trans (initial_totalWeight_le q hq)

theorem stateful_cache_exception_rate {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (q : Nat) (hq : q≤2^127) :
    Pr[=true | stateRun policy q state [] empty]≤(q : ENNReal)/2^153 := by
  by_cases hz : q=0
  · subst q
    simp [stateRun,not_bad_empty]
  · calc
      _ ≤ (2^700 : ENNReal)⁻¹ := stateful_cache_tail policy state q hq
      _ ≤ (2^153 : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by omega))
      _ = (1 : ENNReal)/2^153 := by simp
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 1≤q by omega)) _


/-- Flexible linear charge, leaving the caller free to allocate the much
smaller cache exception separately from admissible-counter deficits. -/
theorem stateful_cache_linear_charge {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (q bits : Nat) (hq : q≤2^127) (hbits : bits≤700) :
    Pr[=true | stateRun policy q state [] empty]≤(q : ENNReal)/2^bits := by
  by_cases hz : q=0
  · subst q
    simp [stateRun,not_bad_empty]
  · calc
      _ ≤ (2^700 : ENNReal)⁻¹ := stateful_cache_tail policy state q hq
      _ ≤ (2^bits : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) hbits)
      _ = (1 : ENNReal)/2^bits := by simp
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 1≤q by omega)) _

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.stateful_cache_tail
#print axioms SigGolfResearch.Gate6.Cache.stateful_cache_exception_rate
