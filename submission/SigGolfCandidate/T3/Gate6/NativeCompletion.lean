import SigGolfCandidate.T3.Gate6.NativeSearch

namespace SigGolfResearch.Gate6.NativeSearch
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3
open SigGolfCandidate.T3.Sampling
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def completeLabel (found : Option (BitVec 32 × HashOutput)) : ProbComp MarkedLabel :=
  found.elim ($ᵗ MarkedLabel) (fun value => pure (digestRecord value.2).1)

noncomputable def complete {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : ProbComp (Record × MarkedLabel) := do
  let record ← program
  let label ← completeLabel (observed record)
  pure (record,label)

/-- Completing exhaustion is ghost randomness and preserves the entire native
record, including the counter/output and final public oracle cache. -/
theorem complete_erasure {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) : 𝒮[Prod.fst <$> complete observed program]=𝒮[program] := by
  unfold complete
  simp only [map_bind,map_pure]
  trans 𝒮[program >>= fun record => pure record]
  · apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
    intro record
    exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails _ (by simp) _
  · simp

theorem completeLabel_point (found : Option (BitVec 32 × HashOutput)) (mark : MarkedLabel) :
    Pr[=mark | completeLabel found]=completedScore mark found := by
  cases found with
  | none => norm_num [completeLabel,completedScore,probOutput_uniformSample,markedLabel_card]
  | some value => simp only [completeLabel,completedScore,Option.elim_some,probOutput_pure,hit,eq_comm]

theorem complete_point {Record : Type} (observed : Record → Option (BitVec 32 × HashOutput))
    (program : ProbComp Record) (mark : MarkedLabel) :
    Pr[fun result => result.2=mark | complete observed program]=
      expectedValue program (fun record => completedScore mark (observed record)) := by
  rw [complete,probEvent_bind_eq_expectedValue]
  congr 1
  funext record
  rw [probEvent_bind_eq_expectedValue]
  simp only [probEvent_pure]
  rw [expectedValue_ite_one]
  rw [probEvent_eq_eq_probOutput]
  exact completeLabel_point (observed record) mark

noncomputable def recordLaw (secret : BitVec 256) (message : Message) (fuel : Nat) (cache : RCache) :
    PMF (((Option (BitVec 32 × HashOutput)) × RCache) × MarkedLabel) :=
  liftM (complete Prod.fst (($ᵗ Digest : ProbComp Digest) >>= fun rho =>
    roRun secret (search rho message fuel) cache))

/-- Concrete accepted marginal meets the proposal model's exact16/17 domination
condition over all2^59 labels, including counter-search exhaustion. -/
theorem recordLaw_scaled_cap (secret : BitVec 256) (message : Message)
    (fuel : Nat) (hlimit : fuel≤2^32) (cache : RCache) (hfinite : SphincsSecurity.Finite cache)
    (q : Nat) (hsize : QueryCache.enncard cache≤q) (hq : q≤2^127)
    (hclean : ¬NativeCache.Bad cache) (mark : MarkedLabel) :
    (16/17 : ENNReal)*((recordLaw secret message fuel cache).map Prod.snd) mark ≤
      (PMF.uniformOfFintype MarkedLabel) mark := by
  have hpoint := uniform_nonce_completed_cap secret message fuel hlimit cache hfinite q hsize hq hclean mark
  rw [← complete_point Prod.fst _ mark] at hpoint
  rw [← PMF.monad_map_eq_map,← PMF.probOutput_eq_apply,probOutput_map,
    PMF.uniformOfFintype_apply,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat]
  change (16/17 : ENNReal)*Pr[fun result => result.2=mark | complete Prod.fst
    (($ᵗ Digest : ProbComp Digest) >>= fun rho => roRun secret (search rho message fuel) cache)]≤_
  calc
    _ ≤ (16/17 : ENNReal)*((17/16 : ENNReal)/(2 : ENNReal)^59) := mul_le_mul' le_rfl hpoint
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_inv,ENNReal.toReal_pow]

end SigGolfResearch.Gate6.NativeSearch
#print axioms SigGolfResearch.Gate6.NativeSearch.complete_erasure
#print axioms SigGolfResearch.Gate6.NativeSearch.recordLaw_scaled_cap
