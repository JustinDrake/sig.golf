import SigGolfCandidate.T3.Secc.WotsPrefixGame

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
def PrefixRow (answers : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr input) => ∃ a, WotsExtract.SourceChain a ∧ PrefixRowAt answers a input
  | _ => False
noncomputable def prefixClassCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRow s.answers (.inl (.inr e.1)))).length
@[irreducible] noncomputable def sourceChains : Finset ChainAddr :=
  (Finset.univ : Finset Layer).biUnion fun lay => (Finset.range (2 ^ 31)).biUnion fun tree =>
    (Finset.range (2 ^ height lay)).biUnion fun leaf =>
      (Finset.range (chainCount lay)).image fun chain => (⟨⟨lay, tree, leaf⟩, chain⟩ : ChainAddr)
theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> decide
theorem mem_sourceChains (a : ChainAddr) : a ∈ sourceChains ↔ WotsExtract.SourceChain a := by
  unfold sourceChains
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨lay, tree, htree, leaf, hleaf, chain, hchain, rfl⟩
    exact ⟨⟨htree, hleaf⟩, hchain⟩
  · intro ha
    exact ⟨a.key.lay, a.key.tree, ha.1.1, a.key.leaf, ha.1.2, a.chain, ha.2, rfl⟩
theorem prefixRowAt_unique {answers : Answers} {a b : ChainAddr} (ha : WotsExtract.SourceChain a)
    (hb : WotsExtract.SourceChain b) {input : HashInput} (hia : PrefixRowAt answers a input)
    (hib : PrefixRowAt answers b input) : a = b := by
  obtain ⟨s, v, hs, rfl⟩ := hia
  obtain ⟨s', v', hs', he⟩ := hib
  have h7a := Mask.depth_le_seven answers a
  have h7b := Mask.depth_le_seven answers b
  have hca : a.chain < 2 ^ 24 := by have := ha.2; have := Mask.chainCount_le a.key.lay; omega
  have hcb : b.chain < 2 ^ 24 := by have := hb.2; have := Mask.chainCount_le b.key.lay; omega
  have h := Mask.chainInput_eq_chainRow (a := b) hca hcb (by omega) (by omega) ((Mask.chainRow_eq a s v).symm.trans he)
  have hkey := h.1.eq_of_lt (by have := ha.1.1; omega)
    (by have := ha.1.2; have : 2 ^ height a.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le a.key.lay; omega); omega)
    (by have := hb.1.1; omega)
    (by have := hb.1.2; have : 2 ^ height b.key.lay ≤ 2 ^ 32 :=
      Nat.pow_le_pow_right (by norm_num) (by have := height_le b.key.lay; omega); omega)
  cases a; cases b
  simp only at hkey h ⊢
  rw [h.2.1, ← hkey]
theorem prefixCount_sum_le (s : RefSample) :
    ∑ a ∈ sourceChains, prefixCount a s ≤ prefixClassCount s := by
  unfold prefixCount prefixClassCount
  simp only [← List.countP_eq_length_filter]
  have h := SphincsSecurity.QueryCap.calls_sum_le sourceChains
    (fun a (e : Entry) => PrefixRowAt s.answers a e.1) (fun e => PrefixRow s.answers (.inl (.inr e.1)))
    ?_ s.trace
  · simpa only [SphincsSecurity.QueryCap.calls] using h
  · intro e
    by_cases hP : PrefixRow s.answers (.inl (.inr e.1))
    · rw [if_pos hP]
      obtain ⟨b, hb, hbe⟩ := hP
      rw [Finset.sum_eq_single b]
      · rw [if_pos hbe]
      · intro a ha hab
        rw [if_neg]
        intro hae
        exact hab (prefixRowAt_unique ((mem_sourceChains a).mp ha) hb hae hbe)
      · intro hb'
        exact absurd ((mem_sourceChains b).mpr hb) hb'
    · rw [if_neg hP]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro hae
      exact hP ⟨a, (mem_sourceChains a).mp ha, hae⟩
noncomputable def twoEdgeRate (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / 2 ^ 128) + 2 * ((q : ENNReal) / 2 ^ 128) ^ 2) / 2 ^ 128
theorem card_digest : ((Fintype.card Digest : ℕ) : ENNReal) = 2 ^ 128 := by
  rw [Fintype.card_bitVec]
  norm_num
theorem counted_le_cost (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary) :
    ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
        (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))
        (fun _ _ => none) r * (r.2.1.2 : ENNReal) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
        (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) := by
  conv_rhs => rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realRun_counted_forget,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hr : r ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
      (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))
      (fun _ _ => none)).support
  · apply mul_le_mul' le_rfl
    have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy _ _ _ r hr
    have hmem := PrefixGame.lazyRun_mem_support _ _ _ hlazy
    exact_mod_cast le_of_eq (seedGame_charge adversary q a R r.1 r.2.1 hmem)
  · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]
theorem twoEdgeAt_cost_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] ≤
      twoEdgeRate q * ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) := by
  rw [reference_twoEdgeAt_eq adversary q a ha, reference_prefixCount_eq adversary q a ha, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  rw [mul_left_comm, mul_left_comm (twoEdgeRate q)]
  apply mul_le_mul' le_rfl
  have hsmall : q < Fintype.card Digest := by simpa using hq
  have hcharge := fun endpoint result h => le_of_eq (seedGame_charge adversary q a R endpoint result h)
  have hreal := seedGame_real_cost adversary q a R
  have h1 := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal hsmall
  have h3 := SphincsSecurity.Concrete.PartialChainEndpoint.idealRun_cap_spent_lower
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (seedCost a R) q
    hcharge hreal
  rw [card_digest] at h1 h3
  calc (1 - (q : ENNReal) / 2 ^ 128) * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
          realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
            (fun _ _ => none)]
      ≤ (1 - (q : ENNReal) / 2 ^ 128) * (twoEdgeRate q * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) :=
        mul_le_mul' le_rfl h1
    _ = twoEdgeRate q * ((1 - (q : ENNReal) / 2 ^ 128) * ∑' result,
          idealRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
            (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery (seedGame adversary q a R endpoint) q)
            (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent q result.2.1 : ENNReal)) := by ring
    _ ≤ twoEdgeRate q * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl)
          (seedGame adversary q a R) (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
        mul_le_mul' le_rfl (h3.trans (counted_le_cost adversary q a R))
theorem reference_twoEdge_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) :
    Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] ≤
      twoEdgeRate q * (∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal)) /
        (1 - (q : ENNReal) / 2 ^ 128) := by
  have hpos : (1 - (q : ENNReal) / 2 ^ 128) ≠ 0 := by
    apply ne_of_gt
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hq
  apply (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl (by finiteness))).mpr
  have hunion : Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt s.answers s.trace a |
        referenceExperiment adversary q] ≤
      ∑ a ∈ sourceChains, Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] := by
    refine le_trans (le_of_eq ?_) (probEvent_exists_finset_le_sum sourceChains (referenceExperiment adversary q)
      (fun a s => TwoEdgeAt s.answers s.trace a))
    congr 1
    funext s
    apply propext
    constructor
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (mem_sourceChains a).mpr ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨a, (mem_sourceChains a).mp ha, h⟩
  calc Pr[fun s => ∃ a, WotsExtract.SourceChain a ∧ TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] *
        (1 - (q : ENNReal) / 2 ^ 128)
      ≤ (∑ a ∈ sourceChains, Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q]) *
          (1 - (q : ENNReal) / 2 ^ 128) := mul_le_mul' hunion le_rfl
    _ = ∑ a ∈ sourceChains, (1 - (q : ENNReal) / 2 ^ 128) *
          Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ ≤ ∑ a ∈ sourceChains, twoEdgeRate q * ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) :=
        Finset.sum_le_sum fun a ha => twoEdgeAt_cost_le adversary q hq a ((mem_sourceChains a).mp ha)
    _ = twoEdgeRate q * ∑' s, referenceExperiment adversary q s *
          ((∑ a ∈ sourceChains, prefixCount a s : ℕ) : ENNReal) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
        apply tsum_congr
        intro s
        rw [Nat.cast_sum, Finset.mul_sum]
    _ ≤ twoEdgeRate q * ∑' s, referenceExperiment adversary q s * (prefixClassCount s : ENNReal) := by
        apply mul_le_mul' le_rfl
        apply ENNReal.tsum_le_tsum
        intro s
        apply mul_le_mul' le_rfl
        exact_mod_cast prefixCount_sum_le s
end SigGolfCandidate.T3.Security.Wots
