import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Execution

section

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
theorem exists_seed_not_hit (inputs : List HashInput) (hsize : inputs.length < 2 ^ 207) :
    ∃ seed, ¬SeedHitLog inputs seed := by
  classical
  by_contra h
  have hall : ∀ seed, SeedHitLog inputs seed := by simpa using h
  have hone : Pr[SeedHitLog inputs | sampleMasterSeed] = 1 := by
    simp [hall]
  have hlt : (inputs.length : ℝ≥0∞) / ((2 ^ 207 : Nat) : ℝ≥0∞) < 1 :=
    ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact_mod_cast hsize)
  exact (not_lt_of_ge (hone ▸ probEvent_seedHitLog_le inputs)) hlt
theorem hashQueryBound_query_bind_of {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hcost : (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) ≤ q)
    (hnext : ∀ result ∈ support ((romImpl input).run cache),
      HashQueryBound (next result.1) result.2
        (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0))) :
    HashQueryBound (liftM (OracleWorld.query input) >>= next) cache q := by
  intro result hresult
  rw [countHashQueries_query_bind, run'_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, htail⟩ := hresult
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, support_map] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  have h := hnext step hstep (tail.1.1,
    tail.1.2)
  have htail' : tail.1 ∈ support ((simulateQ romImpl
      (countHashQueries (next step.1))).run' step.2) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨tail, htail, rfl⟩
  have := h htail'
  cases input <;> simp_all
  omega
noncomputable def cacheAfter (cache : QueryCache HashSpec) (input : OracleWorld.Domain)
    (answer : OracleWorld.Range input) : QueryCache HashSpec :=
  match input with
  | .inl _ => cache
  | .inr input => match cache input with
    | none => cache.cacheQuery input answer
    | some _ => cache
theorem romImpl_support_cacheAfter (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) :
    result.2 = cacheAfter cache input result.1 := by
  cases input with
  | inl input =>
      change result ∈ support ((fun answer => (answer, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp _)) at hresult
      rw [support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      rfl
  | inr input =>
      change result ∈ support ((randomOracle input).run cache) at hresult
      cases hc : cache input with
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          simp [cacheAfter, hc]
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simp [cacheAfter, hc]
theorem romImpl_support_transfer (bad : HashInput → Prop) (left right : QueryCache HashSpec)
    (h : AgreeOutside bad left right) (input : OracleWorld.Domain) (hinput : ¬hashBad bad input)
    (answer : OracleWorld.Range input)
    (hanswer : (answer, cacheAfter right input answer) ∈ support ((romImpl input).run right)) :
    (answer, cacheAfter left input answer) ∈ support ((romImpl input).run left) ∧
      AgreeOutside bad (cacheAfter left input answer) (cacheAfter right input answer) := by
  cases input with
  | inl input =>
      dsimp [OracleWorld] at answer hanswer ⊢
      constructor
      · change (answer, left) ∈ support ((fun answer => (answer, left)) <$>
          (liftM (unifSpec.query input) : ProbComp _))
        rw [support_map]
        exact ⟨answer, mem_support_query input answer, rfl⟩
      · exact h
  | inr input =>
      have heq := h input hinput
      dsimp [cacheAfter] at hanswer ⊢
      change (answer, _) ∈ support ((randomOracle input).run right) at hanswer
      change (answer, _) ∈ support ((randomOracle input).run left) ∧ _
      cases hl : left input with
      | none =>
          have hr : right input = none := heq.symm.trans hl
          simp only [hr] at hanswer ⊢
          constructor
          · rw [QueryImpl.withCaching_run_none _ hl, support_map]
            exact ⟨answer, mem_support_uniformSample _, rfl⟩
          · exact h.cacheQuery input answer
      | some value =>
          have hr : right input = some value := heq.symm.trans hl
          simp only [hr] at hanswer ⊢
          rw [QueryImpl.withCaching_run_some _ hr, support_pure, Set.mem_singleton_iff] at hanswer
          have ha : answer = value := congrArg Prod.fst hanswer
          subst answer
          exact ⟨by rw [QueryImpl.withCaching_run_some _ hl]; simp, h⟩
theorem hashQueryBound_of_seed_caches {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec)
    (cache : QueryCache HashSpec) (hsize : inputs.length + q < 2 ^ 207)
    (hagree : ∀ seed, ¬SeedHitLog inputs seed →
      AgreeOutside (fun input => SeedHit input seed) (caches seed) cache)
    (hbound : ∀ seed, ¬SeedHitLog inputs seed → HashQueryBound computation (caches seed) q) :
    HashQueryBound computation cache q := by
  induction computation using OracleComp.inductionOn generalizing q inputs caches cache with
  | pure value =>
      intro result hresult
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
        map_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le q
  | query_bind input next ih =>
      obtain ⟨seed, hseed⟩ := exists_seed_not_hit inputs (by omega)
      obtain ⟨step, hstep⟩ := probComp_support_nonempty ((romImpl input).run (caches seed))
      have hcost := (hashQueryBound_query_bind input next (caches seed) q
        (hbound seed hseed) step hstep).1
      apply hashQueryBound_query_bind_of input next cache q hcost
      intro result hresult
      have hcache := romImpl_support_cacheAfter input cache result hresult
      rcases result with ⟨answer, nextCache⟩
      dsimp at hcache
      subst nextCache
      have havoid (seed : MasterSeed) (hseed : ¬SeedHitLog (prependHash input inputs) seed) :
          ¬hashBad (fun input => SeedHit input seed) input ∧ ¬SeedHitLog inputs seed := by
        change ¬TraceHits (fun input => SeedHit input seed) (prependHash input inputs) at hseed
        rw [traceHits_prepend] at hseed
        exact not_or.mp hseed
      have htransfer (seed : MasterSeed) (hseed : ¬SeedHitLog (prependHash input inputs) seed) :=
        romImpl_support_transfer (fun input => SeedHit input seed) (caches seed) cache
          (hagree seed (havoid seed hseed).2) input (havoid seed hseed).1 answer hresult
      apply ih answer
        (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0))
        (prependHash input inputs) (fun seed => cacheAfter (caches seed) input answer)
        (cacheAfter cache input answer)
      · cases input <;> simp_all [prependHash]
      · intro seed hseed
        exact (htransfer seed hseed).2
      · intro seed hseed
        exact (hashQueryBound_query_bind input next (caches seed) q
          (hbound seed (havoid seed hseed).2) _ (htransfer seed hseed).1).2
end SphincsSecurity.Seeded
end

section


open OracleComp OracleSpec
namespace SphincsSecurity.Seeded
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} {spec : OracleSpec ι}
inductive Erases (known : QueryCache spec) {α : Type} :
    OracleComp spec α → OracleComp spec α → Prop
  | pure (value : α) : Erases known (pure value) (pure value)
  | query (input : spec.Domain) (left right : spec.Range input → OracleComp spec α)
      (next : ∀ answer, Erases known (left answer) (right answer)) :
      Erases known (liftM (spec.query input) >>= left) (liftM (spec.query input) >>= right)
  | skip (input : spec.Domain) (answer : spec.Range input)
      (hknown : known input = some answer) (next : spec.Range input → OracleComp spec α)
      (right : OracleComp spec α) (tail : Erases known (next answer) right) :
      Erases known (liftM (spec.query input) >>= next) right
  | cached (input : spec.Domain) (answer : spec.Range input)
      (hknown : known input = some answer) (left right : spec.Range input → OracleComp spec α)
      (tail : Erases known (left answer) (right answer)) :
      Erases known (liftM (spec.query input) >>= left) (liftM (spec.query input) >>= right)
  | trans {left middle right : OracleComp spec α}
      (first : Erases known left middle) (second : Erases known middle right) : Erases known left right
theorem Erases.refl {α : Type} (known : QueryCache spec) (computation : OracleComp spec α) :
    Erases known computation computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure value
  | query_bind input next ih => exact .query input next next ih
theorem Erases.bind {α β : Type} {known : QueryCache spec} {left right : OracleComp spec α}
    (h : Erases known left right) (nextLeft nextRight : α → OracleComp spec β)
    (hnext : ∀ value, Erases known (nextLeft value) (nextRight value)) :
    Erases known (left >>= nextLeft) (right >>= nextRight) := by
  induction h generalizing β with
  | pure value => simpa only [pure_bind] using hnext value
  | query input left right _ ih =>
      simpa only [bind_assoc] using Erases.query input _ _ (fun answer => ih answer nextLeft nextRight hnext)
  | skip input answer hknown next right _ ih =>
      simpa only [bind_assoc] using Erases.skip input answer hknown _ _ (ih nextLeft nextRight hnext)
  | cached input answer hknown left right _ ih =>
      simpa only [bind_assoc] using Erases.cached input answer hknown _ _ (ih nextLeft nextRight hnext)
  | trans _ _ first second =>
      exact .trans (first nextLeft nextLeft (fun _ => Erases.refl known _))
        (second nextLeft nextRight hnext)
theorem Erases.map {α β : Type} {known : QueryCache spec} {left right : OracleComp spec α}
    (h : Erases known left right) (f : α → β) : Erases known (f <$> left) (f <$> right) := by
  simpa only [bind_pure_comp] using h.bind (fun a => Pure.pure (f a)) (fun a => Pure.pure (f a))
    (fun a => Erases.pure (f a))
theorem Erases.bind_known {α β : Type} {known : QueryCache spec} {left : OracleComp spec α}
    {value : α} (h : Erases known left (Pure.pure value)) (next : α → OracleComp spec β)
    (right : OracleComp spec β) (tail : Erases known (next value) right) :
    Erases known (left >>= next) right :=
  .trans (by simpa only [pure_bind] using h.bind next next (fun _ => Erases.refl known _)) tail
def worldKnown (known : QueryCache HashSpec) : QueryCache OracleWorld
  | .inl _ => none
  | .inr input => known input
theorem Erases.lift_hash {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp HashSpec α} (h : Erases known left right) :
    Erases (worldKnown known) (liftM left : OracleComp OracleWorld α) (liftM right) := by
  induction h with
  | pure value => simpa only [liftM_pure] using Erases.pure value
  | query input left right _ ih =>
      simp only [liftM_bind]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _)
        (liftM (OracleWorld.query (.inr input)) >>= _)
      exact Erases.query (known := worldKnown known) (Sum.inr input) _ _ ih
  | skip input answer hknown next right _ ih =>
      simp only [liftM_bind]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _) _
      exact Erases.skip (known := worldKnown known) (Sum.inr input) answer hknown _ _ ih
  | cached input answer hknown left right _ ih =>
      simp only [liftM_bind]
      change Erases _ (liftM (OracleWorld.query (.inr input)) >>= _)
        (liftM (OracleWorld.query (.inr input)) >>= _)
      exact Erases.cached (known := worldKnown known) (Sum.inr input) answer hknown _ _ ih
  | trans _ _ first second => exact .trans first second
theorem romImpl_preserves_known (known cache : QueryCache HashSpec) (h : known ≤ cache)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) : known ≤ result.2 := by
  apply h.trans
  apply simulateQ_romImpl_cache_le (liftM (OracleWorld.query input) : OracleComp OracleWorld _) cache result
  simpa only [simulateQ_spec_query] using hresult
theorem Erases.evalDist_run {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) :
    𝒮[(simulateQ romImpl left).run cache] = 𝒮[(simulateQ romImpl right).run cache] := by
  induction h generalizing cache with
  | pure value => rfl
  | query input left right _ ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact evalSPMF_bind_congr fun result hresult =>
        ih result.1 result.2 (romImpl_preserves_known known cache hcache input result hresult)
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          change 𝒮[(randomOracle (spec := HashSpec) input).run cache >>= _] = _
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          exact ih cache hcache
  | cached input answer hknown left right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          change 𝒮[(randomOracle (spec := HashSpec) input).run cache >>= _] =
            𝒮[(randomOracle (spec := HashSpec) input).run cache >>= _]
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind]
          exact ih cache hcache
  | trans _ _ first second => exact (first cache hcache).trans (second cache hcache)
theorem Erases.hashQueryBound {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) (q : Nat)
    (hbound : HashQueryBound left cache q) : HashQueryBound right cache q := by
  induction h generalizing cache q with
  | pure value => exact hbound
  | query input left right _ ih =>
      obtain ⟨step, hstep⟩ := probComp_support_nonempty ((romImpl input).run cache)
      have hcost := (hashQueryBound_query_bind input left cache q hbound step hstep).1
      apply hashQueryBound_query_bind_of input right cache q hcost
      intro result hresult
      exact ih result.1 result.2 (romImpl_preserves_known known cache hcache input result hresult) _
        (hashQueryBound_query_bind input left cache q hbound result hresult).2
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          have hstep : (answer, cache) ∈ support ((romImpl (.inr input)).run cache) := by
            change (answer, cache) ∈ support ((randomOracle (spec := HashSpec) input).run cache)
            rw [QueryImpl.withCaching_run_some _ hc]
            simp
          exact (ih cache hcache _ (hashQueryBound_query_bind _ _ _ _ hbound _ hstep).2).mono (Nat.sub_le _ _)
  | cached input answer hknown left right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          have hrun : (romImpl (.inr input)).run cache = Pure.pure (answer, cache) :=
            QueryImpl.withCaching_run_some _ hc
          have hstep : (answer, cache) ∈ support ((romImpl (.inr input)).run cache) := by
            rw [hrun]
            simp
          have hb := hashQueryBound_query_bind (.inr input) left cache q hbound _ hstep
          apply hashQueryBound_query_bind_of (.inr input) right cache q hb.1
          intro result hresult
          rw [hrun, mem_support_pure_iff] at hresult
          subst result
          exact ih cache hcache _ hb.2
  | trans _ _ first second => exact second cache hcache q (first cache hcache q hbound)
end SphincsSecurity.Seeded
end
