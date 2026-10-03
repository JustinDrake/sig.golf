import SigGolfCandidate.T3.Secc.WotsRestartBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsContacts
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsTwoEdge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGame
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameSim
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
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {β : Type}
variable {adversary : AdversaryP}
noncomputable def pausedSeed (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  simulateQ (routeImpl a (restDepth a R) R) (pausedFull stop (referenceGame (fillTable a R endpoint) adversary q) [])
theorem pausedSeed_snd (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) : Prod.snd <$> pausedSeed adversary q a R stop endpoint = seedGame adversary q a R endpoint := by
  unfold pausedSeed seedGame
  rw [← simulateQ_map, pausedFull_snd]
noncomputable def seedBefore (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) ((List Entry × OracleComp RefWorld SeedResult) × Nat) :=
  SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryPause.run stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
noncomputable def seedAfter (a : ChainAddr) (R : RefTables adversary)
    (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat) :
    OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (routeImpl a (restDepth a R) R) middle.1.2
theorem seedBefore_after (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) :
    (do
      let middle ← seedBefore adversary q a R stop endpoint
      let result ← seedAfter a R middle
      pure (middle.1.1, result)) = pausedSeed adversary q a R stop endpoint := by
  unfold seedBefore seedAfter pausedSeed pausedFull
  simp only [simulateQ_bind, simulateQ_pure]
  conv_rhs => rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))]
  rw [bind_map_left]
theorem seedGame_support_cost (q : Nat) (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest)
    (result : SeedResult) (h : result ∈ support (seedGame adversary q a R endpoint)) : seedCost a R result ≤ q := by
  have hrec : result ∈ support (SphincsSecurity.QueryCap.recorded
      (referenceGame (fillTable a R endpoint) adversary q)) := by
    unfold seedGame at h
    revert h
    exact SphincsSecurity.QueryCap.simulate_oracle_mem_support (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) result
  have hcount : (result.1, SphincsSecurity.QueryCap.calls RefCharged result.2) ∈
      support (SphincsSecurity.QueryCap.counted RefCharged (referenceGame (fillTable a R endpoint) adversary q)) := by
    rw [← SphincsSecurity.QueryCap.recorded_counted, support_map]
    exact ⟨result, hrec, rfl⟩
  have hle := SphincsSecurity.QueryCap.counted_le_of_queryBound RefCharged _ q
    (referenceGame_queryBound (fillTable a R endpoint) adversary q) _ hcount
  refine le_trans ?_ hle
  unfold seedCost SphincsSecurity.QueryCap.calls
  apply List.countP_mono_left
  intro query _ hq
  simp only [decide_eq_true_eq] at hq ⊢
  obtain ⟨i, v, rfl⟩ := hq
  trivial
theorem checkpoint_budget (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ q ∧ queryCount result.2 ≤ q := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hmem := lazyRun_mem_support _ _ _ hfull
  have htotal : middle.1.2 + result.1.2 ≤ q := by
    have hc := seedGame_charge adversary q a R endpoint _ hmem
    have hs := seedGame_support_cost q a R endpoint result.1.1 (by
      have := SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (seedGame adversary q a R endpoint)
      rw [← this, support_map]
      exact ⟨_, hmem, rfl⟩)
    simp only at hc
    omega
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  have hrows := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ middle.2 result hresult
  constructor <;> omega
theorem checkpoint_charge (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + 2 * result.1.2 ≤ 2 * seedCost a R result.1.1 := by
  have hcomp : (do
      let m ← seedBefore adversary q a R stop endpoint
      let r ← SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R m)
      pure (r.1, m.2 + r.2)) = SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint) := by
    unfold seedBefore seedAfter seedGame
    conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [], simulateQ_bind,
      SphincsSecurity.QueryCap.counted_bind]
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
        (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedGame adversary q a R endpoint)) (fun _ _ => none)).support := by
    rw [← hcomp, lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨middle, hmiddle, ?_⟩
    rw [lazyRun_bind, PMF.mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff]
  have hc := seedGame_charge adversary q a R endpoint _ (lazyRun_mem_support _ _ _ hfull)
  simp only at hc
  have hpast := SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_counted_queryCount_le
    SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ (fun _ _ => none) middle hmiddle
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.queryCount_empty, Nat.zero_add] at hpast
  omega
theorem route_step_lazy (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (input : RefWorld.Domain)
    (memory : List Entry) (observed : Fin d → Digest → Option Digest) (hinv : RowsInv a memory observed)
    (result : RefWorld.Range input × (Fin d → Digest → Option Digest))
    (hr : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (routeImpl a d R input) observed).support) :
    RowsInv a (stepTrace input result.1 memory) result.2 := by
  rcases input with (n | input) | u
  · simp only [routeImpl] at hr
    rw [show (liftM ((SeedSpec d).query (.inl n)) : OracleComp (SeedSpec d) _) =
        liftM ((SeedSpec d).query (.inl n)) >>= pure from (bind_pure _).symm,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
    simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff,
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff,
      Function.comp_def] at hr
    obtain ⟨answer, _, rfl⟩ := hr
    simpa [stepTrace, entryOf] using hinv
  · cases hp : rowOf a d input with
    | none =>
        simp only [routeImpl, hp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
          PMF.mem_support_pure_iff] at hr
        subst hr
        intro i v w
        rw [hinv i v w]
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨answer, hm, hl⟩
          exact ⟨answer, Or.inl hm, hl⟩
        · rintro ⟨answer, hm | hm, hl⟩
          · exact ⟨answer, hm, hl⟩
          · exact absurd (congrArg Prod.fst hm).symm (rowOf_none hp (i, v))
    | some p =>
        simp only [routeImpl, hp] at hr
        rw [map_eq_bind_pure_comp, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_query_bind] at hr
        simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff, Function.comp_def,
          SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure, PMF.mem_support_pure_iff] at hr
        obtain ⟨w₀, hw₀, rfl⟩ := hr
        have hin := rowOf_some hp
        subst hin
        intro i v w
        simp only [stepTrace, entryOf, List.mem_append, List.mem_singleton]
        by_cases hpi : p = (i, v)
        · subst hpi
          simp only [record, Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            refine ⟨_, Or.inr rfl, ?_⟩
            simp only [low, ChainGraph.joinOutput_low]
          · rintro ⟨answer, hm | hm, hl⟩
            ·
              have hold := (hinv i v w).mpr ⟨answer, hm, hl⟩
              simp only [hold, SphincsSecurity.Concrete.PartialChainEndpoint.rowLaw, PMF.mem_support_pure_iff] at hw₀
              exact hw₀
            · have := congrArg Prod.snd hm
              simp only at this
              rw [← hl, this, low, ChainGraph.joinOutput_low]
        · have hne : chainRow a p.1 p.2 ≠ chainRow a i v := by
            intro he
            obtain ⟨hs, hv⟩ := Mask.chainRow_inj (by have := p.1.isLt; omega) (by have := i.isLt; omega) he
            exact hpi (Prod.ext (Fin.ext hs) hv)
          have hrec : record observed p w₀ i v = observed i v := by
            simp only [record]
            by_cases h1 : i = p.1
            · subst h1
              have h2 : v ≠ p.2 := fun h2 => hpi (Prod.ext rfl h2.symm)
              simp only [Function.update_self, Function.update_of_ne h2]
            · simp only [Function.update_of_ne h1]
          rw [hrec, hinv i v w]
          constructor
          · rintro ⟨answer, hm, hl⟩
            exact ⟨answer, Or.inl hm, hl⟩
          · rintro ⟨answer, hm | hm, hl⟩
            · exact ⟨answer, hm, hl⟩
            · exact absurd (congrArg Prod.fst hm).symm hne
  · simp only [routeImpl, SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_pure,
      PMF.mem_support_pure_iff] at hr
    subst hr
    simpa [stepTrace, entryOf] using hinv
theorem checkpoint_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support) :
    RowsInv a middle.1.1.1 middle.2 := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hplain : (middle.1.1, middle.2) ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none)).support := by
    rw [← SphincsSecurity.QueryCap.counted_forget IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
      (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])),
      SphincsSecurity.Concrete.PartialChainEndpoint.lazyRun_map, PMF.mem_support_map_iff]
    exact ⟨middle, hmiddle, rfl⟩
  have hcomp : lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (simulateQ (routeImpl a (restDepth a R) R) (SphincsSecurity.QueryPause.run stop stepTrace
        (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))
      (fun _ _ => none) =
      (simulateQ ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
        (SphincsSecurity.QueryPause.run stop stepTrace
          (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) [])).run
        (fun _ _ => none) := by
    unfold lazyRun
    rw [QueryImpl.simulateQ_compose]
  rw [hcomp] at hplain
  exact SphincsSecurity.QueryPause.run_simulation_invariant stop stepTrace
    ((lazyImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl) ∘ₛ routeImpl a (restDepth a R) R)
    (fun memory observed => RowsInv a memory observed)
    (fun memory observed hinv _ input result hresult =>
      route_step_lazy a hd R input memory observed hinv result (by
        simpa only [QueryImpl.apply_compose, lazyRun] using hresult))
    _ [] (fun _ _ => none) (rowsInv_nil a _) _ hplain
end PrefixGame
end ClaudeWCT.W9.T3.Security.Wots
