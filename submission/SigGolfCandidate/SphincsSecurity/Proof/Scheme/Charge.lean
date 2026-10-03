import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Settled
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Slot

namespace SphincsSecurity
open OracleComp OracleSpec ENNReal
variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
def AtPosition (input : HashInput) (p : Position) : Prop :=
  ∃ payload, input = tweakableHashInput parameter p.domain payload
theorem atPosition_unique {input : HashInput} {p q : Position} (hp : AtPosition parameter input p)
    (hq : AtPosition parameter input q) : p = q := by
  obtain ⟨payload, hpayload⟩ := hp
  obtain ⟨payload', hpayload'⟩ := hq
  exact Position.domain_injective (tweakableHashInput_injective parameter
    (Position.domain_inRange p) (Position.domain_inRange q) (hpayload ▸ hpayload')).1
theorem le_cacheQuery {cache : QueryCache HashSpec} {input : HashInput} {answer : HashOutput}
    (huncached : cache input = none) : cache ≤ cache.cacheQuery input answer := by
  intro x u hx
  by_cases hxeq : x = input
  · rw [hxeq, huncached] at hx
    simp at hx
  · rwa [QueryCache.cacheQuery_of_ne _ _ hxeq]
def Finite (cache : QueryCache HashSpec) : Prop := {input | cache input ≠ none}.Finite
theorem finite_empty : Finite (∅ : QueryCache HashSpec) := by
  simp [Finite]
theorem Finite.of_enncard_le {cache : QueryCache HashSpec} {q : Nat}
    (hle : QueryCache.enncard cache ≤ (q : ℝ≥0∞)) : Finite cache := by
  rw [QueryCache.enncard] at hle
  have hfiniteToSet : cache.toSet.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop] at hle
    exact not_top_le_coe hle
  let cachedInputs : Set HashInput := {input | cache input ≠ none}
  have hsubset : cachedInputs ⊆ Sigma.fst '' cache.toSet := by
    intro input hcached
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
    exact ⟨⟨input, answer⟩, hanswer, rfl⟩
  exact (hfiniteToSet.image Sigma.fst).subset hsubset
theorem Finite.cachedInputs_ncard_toENNReal_eq_enncard
    {cache : QueryCache HashSpec} (hfinite : Finite cache) :
    ({input | cache input ≠ none}.ncard : ℝ≥0∞) = QueryCache.enncard cache := by
  let cachedInputs : Set HashInput := {input | cache input ≠ none}
  have himage : Sigma.fst '' cache.toSet = cachedInputs := by
    ext input
    constructor
    · rintro ⟨⟨cachedInput, answer⟩, hcached, heq⟩
      subst input
      change cache cachedInput = some answer at hcached
      exact Option.ne_none_iff_exists'.mpr ⟨answer, hcached⟩
    · intro hcached
      obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hcached
      exact ⟨⟨input, answer⟩, hanswer, rfl⟩
  have hinjective : Set.InjOn Sigma.fst cache.toSet := by
    rintro ⟨leftInput, leftAnswer⟩ hleft ⟨rightInput, rightAnswer⟩ hright heq
    simp only at heq
    subst rightInput
    change cache leftInput = some leftAnswer at hleft
    change cache leftInput = some rightAnswer at hright
    have hanswer : leftAnswer = rightAnswer := by
      rw [hleft] at hright
      exact Option.some.inj hright
    subst rightAnswer
    rfl
  have hencard : cachedInputs.encard = cache.toSet.encard := by
    rw [← himage]
    exact hinjective.encard_image
  have hcast := hfinite.cast_ncard_eq.trans hencard
  simpa only [cachedInputs, QueryCache.enncard, ENat.toENNReal_coe] using
    congrArg ENat.toENNReal hcast
theorem finite_cacheQuery {cache : QueryCache HashSpec} (hfinite : Finite cache)
    (input : HashInput) (answer : HashOutput) : Finite (cache.cacheQuery input answer) := by
  refine Set.Finite.subset (hfinite.insert input) fun x hx => ?_
  by_cases hxeq : x = input
  · exact Set.mem_insert_iff.mpr (Or.inl hxeq)
  · refine Set.mem_insert_iff.mpr (Or.inr ?_)
    simpa only [Set.mem_setOf_eq, QueryCache.cacheQuery_of_ne _ _ hxeq] using hx
end SphincsSecurity
