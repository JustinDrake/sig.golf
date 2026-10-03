import SigGolfCandidate.T3.Secc.WotsTwoEdge

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  realRun idealRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
theorem contactAt_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] ≤
      (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) := by
  rw [reference_contactAt_eq adversary q a ha, reference_prefixCount_eq adversary q a ha, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  rw [mul_left_comm, mul_left_comm (2 / 2 ^ 128 : ENNReal)]
  apply mul_le_mul' le_rfl
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge adversary q a R endpoint result h)
  have hreal := seedGame_real_cost adversary q a R
  have h2 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_contact_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h2 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => Contact r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * ((2 / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h2
    _ = (2 / 2 ^ 128) * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ (2 / 2 ^ 128) * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
noncomputable def contactCount (s : RefSample) : Nat :=
  (sourceChains.filter fun a => ContactAt s.answers s.trace a).card
theorem expected_contactCount (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) =
      ∑ a ∈ sourceChains, Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] := by
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  apply tsum_congr
  intro s
  unfold contactCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : ContactAt s.answers s.trace a
  · rw [if_pos h, if_pos h, Nat.cast_one, mul_one]
  · rw [if_neg h, if_neg h, Nat.cast_zero, mul_zero]
theorem reference_contacts_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    ∑' s, referenceExperiment adversary q s * (contactCount s : ENNReal) ≤
      (2 / 2 ^ 128) * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  rw [expected_contactCount]
  calc (∑ a ∈ sourceChains, Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q]) *
        (1 - (q : ENNReal) / 2 ^ 128)
      = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) :=
        Finset.sum_le_sum fun a ha => contactAt_cost_le adversary q hq a ((mem_sourceChains a).mp ha)
    _ = (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s *
          ((∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ (2 / 2 ^ 128) * ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal) := by
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast prefixCount_sum_le s
end SigGolfCandidate.T3.Security.Wots
