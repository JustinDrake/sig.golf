import SigGolfCandidate.T3.Gate6.StatefulCache
namespace SigGolfResearch.Gate6.Cache
open OracleComp ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ totalWeight
set_option maxHeartbeats 300000

/-- The global budget limits only fresh distinct inputs. The independent
fuel bounds total requests, so repeated cache hits do not spend fresh budget.
At the fresh-input cap, a further fresh request stops without sampling. -/
noncomputable def distinctRun {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (q : Nat) :
    Nat → State → History Input → Cache Input → ProbComp Bool
  | 0,_,_,cache => pure (decide (Bad cache))
  | steps+1,state,history,cache =>
    if Bad cache then pure true else do
      let choice ← policy state history
      match choice with
      | none => pure false
      | some (input,next) =>
          match fresh : lookup cache input with
          | some output => distinctRun policy q steps (next output) ((input,output)::history) cache
          | none =>
              if cache.entries.length<q then do
                let output ← ($ᵗ Output : ProbComp Output)
                distinctRun policy q steps (next output) ((input,output)::history) (insert cache input output fresh)
              else pure false

theorem distinctRun_bound {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (q fuel : Nat)
    (state : State) (history : History Input) (cache : Cache Input)
    (hcap : cache.entries.length≤q) :
    Pr[=true | distinctRun policy q fuel state history cache]≤totalWeight q cache := by
  induction fuel generalizing state history cache with
  | zero =>
      by_cases hb : Bad cache
      · simpa [distinctRun,hb] using totalWeight_bad q cache hcap hb
      · simp [distinctRun,hb]
  | succ fuel ih =>
      by_cases hb : Bad cache
      · simpa [distinctRun,hb] using totalWeight_bad q cache hcap hb
      · simp only [distinctRun,if_neg hb,probOutput_bind_eq_tsum]
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
                · exact ih _ _ _ hcap
                · split <;> rename_i hroom
                  · rw [probOutput_bind_eq_tsum]
                    calc
                      _ ≤ ∑' output,Pr[=output | ($ᵗ Output : ProbComp Output)]*
                          totalWeight q (insert cache input output hf) := by
                        apply ENNReal.tsum_le_tsum
                        intro output
                        exact mul_le_mul' le_rfl (ih _ _ _ (by rw [insert_length];omega))
                      _ ≤ _ := expected_totalWeight_insert q cache input hf
                  · simp
          _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- For every total-request horizon, the all-prefix/all-mark tail depends
only on the cap on distinct fresh random-oracle inputs. -/
theorem distinct_cache_tail {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (q horizon : Nat) (hq : q≤2^127) :
    Pr[=true | distinctRun policy q horizon state [] empty]≤(2^700 : ENNReal)⁻¹ :=
  (distinctRun_bound policy q horizon state [] empty (by simp [empty])).trans (initial_totalWeight_le q hq)


theorem distinct_zero_fresh_budget {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (horizon : Nat) :
    Pr[=true | distinctRun policy 0 horizon state [] empty]=0 := by
  cases horizon with
  | zero => simp [distinctRun,not_bad_empty]
  | succ n =>
      simp only [distinctRun,if_neg not_bad_empty,probOutput_bind_eq_tsum]
      apply ENNReal.tsum_eq_zero.mpr
      intro choice
      cases choice with
      | none => simp
      | some pair =>
          obtain ⟨input,next⟩ := pair
          simp [lookup,empty]

theorem distinct_cache_linear_charge {Input State : Type} [DecidableEq Input]
    (policy : State → History Input → ProbComp (Decision Input State)) (state : State)
    (q horizon bits : Nat) (hq : q≤2^127) (hbits : bits≤700) :
    Pr[=true | distinctRun policy q horizon state [] empty]≤(q : ENNReal)/2^bits := by
  by_cases hz : q=0
  · subst q
    rw [distinct_zero_fresh_budget]
    exact zero_le
  · calc
      _ ≤ (2^700 : ENNReal)⁻¹ := distinct_cache_tail policy state q horizon hq
      _ ≤ (2^bits : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) hbits)
      _ = (1 : ENNReal)/2^bits := by simp
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 1≤q by omega)) _

end SigGolfResearch.Gate6.Cache
#print axioms SigGolfResearch.Gate6.Cache.distinct_cache_tail
