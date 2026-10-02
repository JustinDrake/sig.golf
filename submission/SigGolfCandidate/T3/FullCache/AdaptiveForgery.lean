import SigGolfCandidate.T3.FullCache.AdaptiveRun

namespace SiggolfT3Mac4.Adaptive
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

variable {Message Signature : Type}

def retagRegion (key : MacKey) (published : Cache) : MacKey :=
  retag key (chunks32 (regionBytes published.region)) published.tag

def BadRequest (published : Cache) (key : MacKey) (request : Request Message) : Prop :=
  request.cache.region ≠ published.region ∧
    tagRegion (retagRegion key published) request.cache.region = request.cache.tag

theorem retagRegion_tag (key : MacKey) (published : Cache) :
    tagRegion (retagRegion key published) published.region = published.tag :=
  macTagOf_retag key (chunks32 (regionBytes published.region)) published.tag

theorem request_bad_bound [SampleableType MacKey] (published : Cache) (request : Request Message) :
    Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] ≤
      (2 ^ 184 : ℝ≥0∞)⁻¹ := by
  by_cases hne : request.cache.region ≠ published.region
  · exact (probEvent_mono fun _ _ h => h.2).trans
      (probEvent_region_bad_le published.region request.cache.region hne published.tag request.cache.tag)
  · have hz : Pr[fun key : MacKey => BadRequest published key request | $ᵗ MacKey] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro key _ h
      exact hne h.1
    rw [hz]
    exact zero_le

theorem list_events_bound {X Y : Type} (mx : ProbComp X) (entries : List Y)
    (event : Y → X → Prop) (cap : ENNReal) (hc : ∀ entry ∈ entries,Pr[event entry | mx] ≤ cap) :
    Pr[fun x => ∃ entry ∈ entries,event entry x | mx] ≤ entries.length*cap := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      calc
        _ = Pr[fun x => event entry x ∨ ∃ entry ∈ entries,event entry x | mx] := by
          apply probEvent_ext
          intro x _
          simp
        _ ≤ Pr[event entry | mx]+Pr[fun x => ∃ entry ∈ entries,event entry x | mx] :=
          probEvent_or_le _ _ _
        _ ≤ cap+entries.length*cap :=
          add_le_add (hc entry (by simp)) (ih fun entry he => hc entry (by simp [he]))
        _ = _ := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
          rw [add_comm]

/-- The ideal adaptive transcript is independent of the retagged key. Repetitions,
failures, off-region requests, and arbitrary chosen tag guesses remain in the log. -/
theorem independent_log_bad_bound [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature))
    (limit : Nat) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) limit (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      limit*((2 : ENNReal)^184)⁻¹ := by
  simp only [map_eq_bind_pure_comp,Function.comp_def]
  rw [probEvent_bind_bind_swap,probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' x,Pr[=x | mx]*(limit*((2 : ENNReal)^184)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul' le_rfl
      rw [bind_pure_comp,probEvent_map]
      exact (list_events_bound ($ᵗ MacKey) ((logOf x).take limit)
        (fun entry key => BadRequest published key entry.1) _
        (fun entry _ => request_bad_bound published entry.1)).trans
        (mul_le_mul' (by exact_mod_cast List.length_take_le _ _) le_rfl)
    _ = (∑' x,Pr[=x | mx])*(limit*((2 : ENNReal)^184)⁻¹) := ENNReal.tsum_mul_right
    _ ≤ _ := mul_le_of_le_one_left zero_le tsum_probOutput_le_one

theorem lifetime_mac_charge [SampleableType MacKey] {X : Type}
    (published : Cache) (mx : ProbComp X) (logOf : X → QueryLog (Requests Message Signature)) :
    Pr[fun result : MacKey × X => BadIn (BadRequest published result.1) (2^32) (logOf result.2) |
      ($ᵗ MacKey : ProbComp _) >>= fun key => (fun x => (key,x)) <$> mx] ≤
      ((2 : ENNReal)^152)⁻¹ := by
  refine (independent_log_bad_bound published mx logOf (2^32)).trans ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]

end SiggolfT3Mac4.Adaptive
