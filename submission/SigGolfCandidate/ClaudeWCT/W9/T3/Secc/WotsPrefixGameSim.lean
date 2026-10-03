import SigGolfCandidate.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGameSim : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
noncomputable def routeImpl (a : ChainAddr) (d : Nat) (R : RefTables adversary) :
    QueryImpl RefWorld (OracleComp (SeedSpec d))
  | .inl (.inl n) => liftM ((SeedSpec d).query (.inl n))
  | .inl (.inr input) =>
      match rowOf a d input with
      | some p => (fun w => ChainGraph.joinOutput w (high (restTable R (.inl (.inr input))))) <$>
          liftM ((SeedSpec d).query (.inr p))
      | none => pure (restTable R (.inl (.inr input)))
  | .inr _ => pure ()
noncomputable def fillTable (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) : Answers :=
  restTable (ov a (restDepth a R) R (fun _ _ => endpoint, endpoint))
theorem prefixStep_none {T : Answers} {a : ChainAddr} {input : HashInput} (h : prefixStep T a input = none) :
    ¬∃ step value, step < depth T a ∧ input = chainRow a step value := by
  unfold prefixStep at h
  split at h
  · cases h
  · assumption
theorem maskAt_ov_fill (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    maskAt (restTable (ov a (restDepth a R) R x)) a = maskAt (fillTable a R (evaluate x.1 x.2)) a := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  set e := evaluate x.1 x.2 with he
  have hdx : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hdf : depth (fillTable a R e) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)
  apply maskAt_congr
  · intro input hp
    have hnone : rowOf a (restDepth a R) input = none := by
      rw [rowOf_none_iff]
      have := prefixStep_none hp
      rw [hdx] at this
      exact this
    unfold fillTable
    rw [restTable_ov_nonprefix a R x input hnone, restTable_ov_nonprefix a R _ input hnone]
  · intro coin
    rfl
  · intro coordinate hc
    unfold fillTable
    rw [restTable_ov_private a R x coordinate hc, restTable_ov_private a R _ coordinate hc]
  · unfold fillTable
    rw [restTable_ov_seed, restTable_ov_seed, siblingHalf_setSeed, siblingHalf_setSeed]
  · rw [hdx, hdf]
  · rw [frontierValue_ov]
    unfold fillTable
    rw [frontierValue_ov]
    exact (evaluate_const _ e).symm
theorem referenceGame_fill (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (q : Nat) :
    referenceGame (restTable (ov a (restDepth a R) R x)) adversary q =
      referenceGame (fillTable a R (evaluate x.1 x.2)) adversary q := by
  rw [← referenceGame_maskAt _ a htree hleaf, maskAt_ov_fill a R x, referenceGame_maskAt _ a htree hleaf]
end PrefixGame
open PrefixGame in
noncomputable def seedGame (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) : OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (PrefixGame.routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R endpoint) adversary q))
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem fixed_route (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ((fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) ∘ₛ routeImpl a d R) =
      (SphincsSecurity.Concrete.OtsPrefix.uniformImpl ∘ₛ refImpl (restTable (ov a d R x))) := by
  funext query
  rcases query with (n | input) | u
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl]
    cases hp : rowOf a d input with
    | none =>
        simp only [simulateQ_pure]
        rw [restTable_ov_nonprefix a R x input hp]
    | some p =>
        have hin := rowOf_some hp
        simp only [simulateQ_map, simulateQ_spec_query, simulateQ_pure]
        simp only [fixedImpl, QueryImpl.add_apply_inr]
        rw [hin, restTable_ov_prefix a hd R x p.1 p.2, ← PMF.monad_pure_eq_pure, map_pure]
  · simp only [QueryImpl.apply_compose, routeImpl, refImpl, simulateQ_pure]
theorem fixed_seedGame (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1) (seedGame adversary q a R (evaluate x.1 x.2)) =
      (liftM (offlineRun (restTable (ov a (restDepth a R) R x)) adversary q) : PMF SeedResult) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold seedGame
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl
theorem route_step_observed (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) (input : RefWorld.Domain) (observed : Fin d → Digest → Option Digest)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables (routeImpl a d R input)
      observed).support) (i : Fin d) (v : Digest) :
    result.2 i v = if input = .inl (.inr (chainRow a i v)) then some (tables i v) else observed i v := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
    simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simp
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        rw [if_neg]
        intro he
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_query_bind] at hr
        simp only [observedImpl, StateT.run_mk, PMF.pure_bind, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
        subst hr
        have hin := rowOf_some hp
        simp only [record]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [Function.update_self, hin, if_true]
        · have hne : input ≠ chainRow a i v := by
            rw [hin]
            intro he
            obtain ⟨hs, hv⟩ := chainRow_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          rw [if_neg (fun he => hne (Sum.inr.inj (Sum.inl.inj he)))]
          by_cases h1 : i = p.1
          · subst h1
            have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
            simp only [Function.update_self, Function.update_of_ne h2]
          · simp only [Function.update_of_ne h1]
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simp
theorem observed_rows (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary)
    (tables : Fin d → Digest → Digest) {β : Type} (computation : OracleComp RefWorld β) :
    ∀ (observed : Fin d → Digest → Option Digest) (result : (β × List RefWorld.Domain) × (Fin d → Digest → Option Digest)),
      result ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl tables
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation)) observed).support →
      ∀ (i : Fin d) (v : Digest), result.2 i v =
        if (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ result.1.2 then some (tables i v) else observed i v := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro observed result hr i v
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure,
        SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure, PMF.mem_support_pure_iff] at hr
      subst hr
      simp only [List.not_mem_nil, if_false]
  | query_bind input next ih =>
      intro observed result hr i v
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query, observedRun_bind,
        PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [simulateQ_bind, observedRun_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨tail, htail, hr⟩ := hr
      simp only [simulateQ_pure, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_pure,
        PMF.mem_support_pure_iff] at hr
      subst hr
      have hstep := route_step_observed a hd R tables input observed middle hmiddle i v
      have htl := ih middle.1 middle.2 tail htail i v
      simp only [List.mem_cons]
      rw [htl, hstep]
      by_cases h1 : (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ tail.1.2
      · simp only [h1, or_true, if_true]
      · simp only [h1, if_false, or_false]
        by_cases h2 : input = .inl (.inr (chainRow a i v))
        · simp only [h2, if_true]
        · simp only [h2, if_false]
          rw [if_neg (fun he => h2 he.symm)]
theorem route_step_count (a : ChainAddr) {d : Nat} (R : RefTables adversary) (input : RefWorld.Domain)
    (first : RefWorld.Range input × Nat)
    (hfirst : first ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (routeImpl a d R input))) :
    first.2 = if PrefixQuery a d input then 1 else 0 := by
  rcases input with (n | input) | u
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_query, support_map, Set.mem_image] at hfirst
    obtain ⟨answer, -, rfl⟩ := hfirst
    rw [if_neg, if_neg]
    · rintro ⟨i, v, he⟩
      cases he
    · exact fun h => h
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
        subst hfirst
        rw [if_neg]
        rintro ⟨i, v, he⟩
        exact rowOf_none hp (i, v) (Sum.inr.inj (Sum.inl.inj he))
    | some p =>
        simp only [routeImpl, hp, SphincsSecurity.QueryCap.counted_map, SphincsSecurity.QueryCap.counted_query,
          support_map, Set.mem_image] at hfirst
        obtain ⟨⟨answer, count⟩, hcount, rfl⟩ := hfirst
        obtain ⟨w, -, hw⟩ := hcount
        simp only [Prod.mk.injEq] at hw
        dsimp only
        rw [← hw.2, if_pos (show (IsPrefixQuery (Sum.inr p : (SeedSpec d).Domain) : Prop) from trivial),
          if_pos ⟨p.1, p.2, by rw [rowOf_some hp]⟩]
  · simp only [routeImpl, SphincsSecurity.QueryCap.counted_pure, mem_support_pure_iff] at hfirst
    subst hfirst
    rw [if_neg]
    rintro ⟨i, v, he⟩
    cases he
theorem counted_rows (a : ChainAddr) {d : Nat} (R : RefTables adversary) {β : Type}
    (computation : OracleComp RefWorld β) :
    ∀ result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (routeImpl a d R) (SphincsSecurity.QueryCap.recorded computation))),
      result.2 = SphincsSecurity.QueryCap.calls (PrefixQuery a d) result.1.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro result hr
      simp only [SphincsSecurity.QueryCap.recorded_pure, simulateQ_pure, SphincsSecurity.QueryCap.counted_pure,
        mem_support_pure_iff] at hr
      subst hr
      rfl
  | query_bind input next ih =>
      intro result hr
      rw [SphincsSecurity.QueryCap.recorded_query_bind, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hr
      obtain ⟨first, hfirst, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨second, hsecond, hr⟩ := hr
      rw [mem_support_pure_iff] at hr
      subst hr
      rw [simulateQ_bind, SphincsSecurity.QueryCap.counted_bind, mem_support_bind_iff] at hsecond
      obtain ⟨tail, htail, hsecond⟩ := hsecond
      simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure, pure_bind, mem_support_pure_iff] at hsecond
      subst hsecond
      have hstep := route_step_count a R input first hfirst
      have htl := ih first.1 tail htail
      simp only [SphincsSecurity.QueryCap.calls_cons, hstep, htl, Nat.add_zero]
end PrefixGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
open PrefixGame in
noncomputable def seedCost {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) (result : SeedResult) :
    Nat :=
  SphincsSecurity.QueryCap.calls (PrefixQuery a (restDepth a R)) result.2
open PrefixGame in
theorem seedGame_charge (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (endpoint : Digest) (result : SeedResult × Nat)
    (h : result ∈ support (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint))) :
    result.2 = seedCost a R result.1 := by
  unfold seedGame at h
  revert h
  exact PrefixGame.counted_rows (d := restDepth a R) a R (referenceGame (PrefixGame.fillTable a R endpoint) adversary q) result
theorem referenceGame_queryBound (T : Answers) (adversary : AdversaryP) (q : Nat) :
    (referenceGame T adversary q).IsQueryBoundP RefCharged q := by
  unfold referenceGame
  exact SphincsSecurity.QueryCap.run_queryBound RefCharged (offlineGame T adversary) q
open PrefixGame in
theorem seedGame_real_cost (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (result : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)))
    (h : result ∈ (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
      (fun _ _ => none)).support) :
    seedCost a R result.2.1 ≤ q := by
  have hlazy := SphincsSecurity.Concrete.PartialChainEndpoint.realRun_support_lazy
    (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R) (fun _ _ => none) result h
  have hseed : result.2.1 ∈ support (seedGame adversary q a R result.1) := by
    revert hlazy
    exact lazyRun_mem_support (seedGame adversary q a R result.1) (fun _ _ => none) result.2
  have hrec : result.2.1 ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    unfold seedGame at hseed
    revert hseed
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (PrefixGame.routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) result.2.1
  have hcount : (result.2.1.1, SphincsSecurity.QueryCap.calls RefCharged result.2.1.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged
        (referenceGame (PrefixGame.fillTable a R result.1) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result.2.1, hrec, rfl⟩
  have hbound := referenceGame_queryBound (PrefixGame.fillTable a R result.1) adversary q
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q hbound _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
end ClaudeWCT.W9.T3.Security.Wots
