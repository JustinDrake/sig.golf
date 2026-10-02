import SigGolfCandidate.T3.Secc.WotsContacts
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPauseInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCheckpointContact
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCheckpointProjection
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainActualBudget

/-!
# Stream C (restart, base): pausing R3 at the first stop of its trace

For the checkpoint restarts (two contacts; stream E's marker-first branch) R3's recorded capped game is paused, at the
level of R3's own queries, the first time a stop predicate holds on the trace built so far (`PrefixGame.stepTrace`
appends the entry of every hash query with its answer).

* `PrefixGame.pausedFull stop G m₀`: pause the recorded game, then resume it; returns the pause memory and the result.
  `pausedFull_snd`: forgetting the memory is the recorded game (`QueryPause.resume`).
* `PrefixGame.paused_structure` (in any fixed world `refImpl T`): the memory is a prefix of the final trace
  (`m₀ ++ traceOf T qs`), no strictly shorter prefix beyond `m₀` stops, and the memory stops unless it is the whole
  trace.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
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

/-- The trace entry of one R3 query and its answer (hash queries only). -/
def entryOf : (query : RefWorld.Domain) → RefWorld.Range query → List Entry
  | .inl (.inr input), answer => [(input, (answer : HashOutput))]
  | .inl (.inl _), _ => []
  | .inr _, _ => []

/-- The pause memory: the trace so far. -/
def stepTrace (query : RefWorld.Domain) (answer : RefWorld.Range query) (memory : List Entry) : List Entry :=
  memory ++ entryOf query answer

/-- The answer of a fixed table to an R3 query (coins as the table's coins, ticks trivial). -/
def refAnswer (T : Answers) : (query : RefWorld.Domain) → RefWorld.Range query
  | .inl query => T (.inl query)
  | .inr _ => ()

/-- The entries `traceOf` records for one query under a fixed table. -/
theorem traceOf_cons (T : Answers) (query : RefWorld.Domain) (qs : List RefWorld.Domain) :
    traceOf T (query :: qs) = entryOf query (refAnswer T query) ++ traceOf T qs := by
  rcases query with (n | input) | u <;> rfl

/-- In R3's fixed world a query's entry is the one `traceOf` records. -/
theorem entryOf_refImpl (T : Answers) (query : RefWorld.Domain) (answer : RefWorld.Range query)
    (h : answer ∈ support (refImpl T query)) : entryOf query answer = entryOf query (refAnswer T query) := by
  rcases query with (n | input) | u
  · rfl
  · simp only [refImpl, mem_support_pure_iff] at h
    subst h
    rfl
  · rfl

theorem entryOf_length_le (query : RefWorld.Domain) (answer : RefWorld.Range query) :
    (entryOf query answer).length ≤ 1 := by
  rcases query with (n | input) | u <;> simp [entryOf]

variable {β : Type}

/-- Pause the recorded game at the first stop of its trace, then resume it. -/
noncomputable def pausedFull (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    OracleComp RefWorld (List Entry × (β × List RefWorld.Domain)) := do
  let paused ← SphincsSecurity.QueryPause.run stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory
  let result ← paused.2
  pure (paused.1, result)

theorem pausedFull_snd (stop : List Entry → Prop) (G : OracleComp RefWorld β) (memory : List Entry) :
    Prod.snd <$> pausedFull stop G memory = SphincsSecurity.QueryCap.recorded G := by
  unfold pausedFull
  simp only [map_bind, map_pure]
  conv_rhs => rw [← SphincsSecurity.QueryPause.resume stop stepTrace (SphincsSecurity.QueryCap.recorded G) memory]
  congr 1
  funext paused
  simp only [bind_pure]

/-- `QueryPause.run` commutes with mapping the result. -/
theorem run_map {Index Memory α γ : Type} {spec : OracleSpec Index} (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : spec.Domain) → spec.Range input → Memory → Memory) (f : α → γ)
    (computation : OracleComp spec α) (memory : Memory) :
    SphincsSecurity.QueryPause.run stop step (f <$> computation) memory =
      (fun paused => (paused.1, f <$> paused.2)) <$> SphincsSecurity.QueryPause.run stop step computation memory := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value =>
      simp only [map_pure, SphincsSecurity.QueryPause.run_pure]
  | query_bind input next ih =>
      rw [map_bind, SphincsSecurity.QueryPause.run_query_bind, SphincsSecurity.QueryPause.run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, map_pure, map_bind]
      · simp only [if_neg hs, map_bind, ih]

/-- One step of the paused recorded game. -/
theorem pausedFull_query_bind (stop : List Entry → Prop) (input : RefWorld.Domain)
    (next : RefWorld.Range input → OracleComp RefWorld β) (memory : List Entry) :
    pausedFull stop (liftM (RefWorld.query input) >>= next) memory =
      if stop memory then
        (fun result => (memory, result)) <$> SphincsSecurity.QueryCap.recorded (liftM (RefWorld.query input) >>= next)
      else liftM (RefWorld.query input) >>= fun answer =>
        (fun paused => (paused.1, (paused.2.1, input :: paused.2.2))) <$>
          pausedFull stop (next answer) (stepTrace input answer memory) := by
  unfold pausedFull
  rw [SphincsSecurity.QueryCap.recorded_query_bind, SphincsSecurity.QueryPause.run_query_bind]
  by_cases hs : stop memory
  · rw [if_pos hs, if_pos hs, pure_bind, ← SphincsSecurity.QueryCap.recorded_query_bind]
    simp only [bind_pure_comp]
  · rw [if_neg hs, if_neg hs, bind_assoc]
    congr 1
    funext answer
    have hmap : (SphincsSecurity.QueryCap.recorded (next answer) >>= fun result =>
        (pure (result.1, input :: result.2) : OracleComp RefWorld _)) =
        (fun result => (result.1, input :: result.2)) <$> SphincsSecurity.QueryCap.recorded (next answer) := by
      simp only [bind_pure_comp]
    rw [hmap, run_map]
    simp only [map_bind, bind_map_left, map_pure]

/-- **Structure of the pause in a fixed world**: the memory is a prefix of the final trace (extended from `memory`),
no prefix strictly between `memory` and the pause memory stops, and the pause memory stops unless it is the whole
trace. -/
theorem paused_structure (T : Answers) (stop : List Entry → Prop) (G : OracleComp RefWorld β) :
    ∀ (memory : List Entry) (result : List Entry × (β × List RefWorld.Domain)),
      result ∈ support (simulateQ (refImpl T) (pausedFull stop G memory)) →
        memory.length ≤ result.1.length ∧
        result.1 = (memory ++ traceOf T result.2.2).take result.1.length ∧
        (∀ j, memory.length ≤ j → j < result.1.length → ¬stop ((memory ++ traceOf T result.2.2).take j)) ∧
        (stop result.1 ∨ result.1 = memory ++ traceOf T result.2.2) := by
  induction G using OracleComp.inductionOn with
  | pure value =>
      intro memory result hr
      simp only [pausedFull, SphincsSecurity.QueryCap.recorded_pure, SphincsSecurity.QueryPause.run_pure, pure_bind,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst hr
      refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inr ?_⟩
      · simp
      · show memory = memory ++ traceOf T []
        rw [show traceOf T [] = [] from rfl, List.append_nil]
  | query_bind input next ih =>
      intro memory result hr
      rw [pausedFull_query_bind] at hr
      by_cases hs : stop memory
      · rw [if_pos hs] at hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨tail, -, rfl⟩ := hr
        refine ⟨le_refl _, ?_, fun j h1 h2 => by simp only at h2; omega, Or.inl hs⟩
        show memory = List.take memory.length (memory ++ _)
        rw [List.take_left' rfl]
      · rw [if_neg hs, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hr
        obtain ⟨answer, hanswer, hr⟩ := hr
        rw [simulateQ_map, support_map] at hr
        obtain ⟨paused, hpaused, rfl⟩ := hr
        obtain ⟨h1, h2, h3, h4⟩ := ih answer (stepTrace input answer memory) paused hpaused
        have hentry := entryOf_refImpl T input answer hanswer
        have htrace : stepTrace input answer memory ++ traceOf T paused.2.2 =
            memory ++ traceOf T (input :: paused.2.2) := by
          rw [traceOf_cons, stepTrace, hentry, List.append_assoc]
        rw [htrace] at h2 h3 h4
        have hlen : (stepTrace input answer memory).length ≤ memory.length + 1 := by
          have := entryOf_length_le input answer
          simp only [stepTrace, List.length_append]
          omega
        have hlen' : memory.length ≤ (stepTrace input answer memory).length := by
          simp only [stepTrace, List.length_append]
          omega
        refine ⟨le_trans hlen' h1, h2, ?_, h4⟩
        intro j hj1 hj2
        by_cases hj : (stepTrace input answer memory).length ≤ j
        · exact h3 j hj hj2
        · have hjm : j = memory.length := by omega
          rw [hjm, List.take_left' rfl]
          exact hs


/-! ## The per-address paused game -/

variable {adversary : AdversaryP}

/-- The per-address paused game: R3 paused at the first stop of its trace, routed as `seedGame`. -/
noncomputable def pausedSeed (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
  simulateQ (routeImpl a (restDepth a R) R) (pausedFull stop (referenceGame (fillTable a R endpoint) adversary q) [])

theorem pausedSeed_snd (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest) : Prod.snd <$> pausedSeed adversary q a R stop endpoint = seedGame adversary q a R endpoint := by
  unfold pausedSeed seedGame
  rw [← simulateQ_map, pausedFull_snd]

/-- The checkpoint part (counted): R3 run until the first stop. -/
noncomputable def seedBefore (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (stop : List Entry → Prop) (endpoint : Digest) :
    OracleComp (SeedSpec (restDepth a R)) ((List Entry × OracleComp RefWorld SeedResult) × Nat) :=
  SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (routeImpl a (restDepth a R) R)
    (SphincsSecurity.QueryPause.run stop stepTrace
      (SphincsSecurity.QueryCap.recorded (referenceGame (fillTable a R endpoint) adversary q)) []))

/-- The restart part: the paused remainder, routed. -/
noncomputable def seedAfter (a : ChainAddr) (R : RefTables adversary)
    (middle : (List Entry × OracleComp RefWorld SeedResult) × Nat) :
    OracleComp (SeedSpec (restDepth a R)) SeedResult :=
  simulateQ (routeImpl a (restDepth a R) R) middle.1.2

/-- Checkpoint then restart is the paused game. -/
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


/-- Every result of `seedGame` (any answers) costs at most `q`. -/
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

theorem lazyRun_bind {d : Nat} {α γ : Type} (first : OracleComp (SeedSpec d) α) (next : α → OracleComp (SeedSpec d) γ)
    (observed : Fin d → Digest → Option Digest) :
    lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (first >>= next) observed =
      (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl first observed).bind fun r =>
        lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl (next r.1) r.2 := by
  simp only [lazyRun, simulateQ_bind, StateT.run_bind, PMF.monad_bind_eq_bind]

/-- **Checkpoint budget** (the G4 budget hypotheses): along the checkpoint and the restart, the observed rows and the
restart's prefix queries stay within `q`. -/
theorem checkpoint_budget (q : Nat) (a : ChainAddr) (R : RefTables adversary) (stop : List Entry → Prop)
    (endpoint : Digest)
    (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hmiddle : middle ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (seedBefore adversary q a R stop endpoint) (fun _ _ => none)).support)
    (result : (SeedResult × Nat) × (Fin (restDepth a R) → Digest → Option Digest))
    (hresult : result ∈ (lazyRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl
      (SphincsSecurity.QueryCap.counted IsPrefixQuery (seedAfter a R middle.1)) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ q ∧ queryCount result.2 ≤ q := by
  -- the composed counted run is the counted `seedGame`
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

/-- **Checkpoint charge**: the restart charge `before + 2·after` of G4 is at most twice the total prefix cost. -/
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

/-! ## The observed rows at the checkpoint are `a`'s prefix rows of the pause memory -/

/-- The observed table holds exactly `a`'s prefix rows of a trace (with their low answers). -/
def RowsInv (a : ChainAddr) {d : Nat} (memory : List Entry) (observed : Fin d → Digest → Option Digest) : Prop :=
  ∀ (i : Fin d) (v w : Digest), observed i v = some w ↔ ∃ answer, (chainRow a i v, answer) ∈ memory ∧ low answer = w

theorem rowsInv_nil (a : ChainAddr) (d : Nat) : RowsInv a (d := d) [] (fun _ _ => none) := by
  intro i v w
  simp

/-- One lazily answered routed query preserves `RowsInv`. -/
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
            · -- an earlier entry: the row was already observed, with the same answer
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

/-- **At the checkpoint, the observed rows are `a`'s prefix rows of the pause memory.** -/
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

end SigGolfCandidate.T3.Security.Wots
