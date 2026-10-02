import SigGolfCandidate.T3.Secc.LargeResidualProbe

/-!
# LR-34 (2/4): the hidden-label world of the T3 large route (eager = lazy)

A residual *world* answers four requests (and an auxiliary spec: coins and presampled data):

* `read row charge` — a residual public row (uniform, cached in `rows`), no risk;
* `probe row test` — a residual public row together with a `Probe` (guess + hit); a fresh row stops the run when the
  probe triggers (one call, one probe), a cached row never stops (one call);
* `disclose coord charge` — reveal a hidden label (honest disclosure, or the honest answer of a known cell);
* `tick charge` — a charged query answered from the caller's own data.

`observedImpl labels table` runs the world with fixed (eager) labels and table; `lazyImpl` samples them from their
posteriors. `run_posterior` is the record's `AdaptiveResidualLabels.run_posterior` for this world: averaging the
eager observed run over the uniform labels and table is the lazy run (with the eager tables drawn from the final
posterior). The counters `calls/probes/mass` are LR-1's `Charges`; `Charge.mass` adds one unit of mass only while
`calls + 1 ≤ q` (LR-1's `MassStep` gate).
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- What a request adds to the counters. -/
inductive Charge where
  | none
  | call
  | mass
  deriving DecidableEq

/-- Requests of the residual world. -/
inductive Request (Coord Cell : Type) where
  | read (row : Cell) (charge : Charge)
  | probe (row : Cell) (test : Probe Coord)
  | disclose (coord : Coord) (charge : Charge)
  | tick (charge : Charge)

/-- Answer types of the residual requests. -/
abbrev ResidualSpec (Coord Cell : Type) : OracleSpec (Request Coord Cell)
  | .read _ _ => HashOutput
  | .probe _ _ => HashOutput
  | .disclose _ _ => Digest
  | .tick _ => Unit

/-- The residual world: an auxiliary spec (coins, presampled data) and the residual requests. -/
abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coord Cell : Type) :=
  auxSpec + ResidualSpec Coord Cell

/-- LR-1's counters. -/
structure Counters where
  calls : Nat
  probes : Nat
  mass : Nat

/-- Counter update of a charged request (mass gated by the budget `q`). -/
def Counters.charge (q : Nat) (counters : Counters) : Charge → Counters
  | .none => counters
  | .call => ⟨counters.calls + 1, counters.probes, counters.mass⟩
  | .mass => ⟨counters.calls + 1, counters.probes, counters.mass + (if counters.calls + 1 ≤ q then 1 else 0)⟩

/-- Counter update of a fresh probe. -/
def Counters.probe (counters : Counters) : Counters :=
  ⟨counters.calls + 1, counters.probes + 1, counters.mass⟩

/-- State of the residual world: posterior candidate sets, cached residual rows, counters. -/
structure State (Coord Cell : Type) where
  candidates : Coord → Finset Digest
  rows : ResidualTableCompletion.Cache Cell
  counters : Counters

section World
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

/-- After a read (or a cached probe, with `Charge.call`). -/
def readState (q : Nat) (state : State Coord Cell) (row : Cell) (answer : HashOutput) (charge : Charge) :
    State Coord Cell :=
  ⟨state.candidates, Function.update state.rows row (some answer), state.counters.charge q charge⟩

/-- After a surviving fresh probe (with the effective probe). -/
def probeState (state : State Coord Cell) (row : Cell) (test : Probe Coord) (answer : HashOutput) :
    State Coord Cell :=
  ⟨test.restrict state.candidates answer, Function.update state.rows row (some answer), state.counters.probe⟩

/-- After a stopping probe. -/
def stoppedState (state : State Coord Cell) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.probe⟩

/-- After a disclosure. -/
def disclosedState (q : Nat) (state : State Coord Cell) (coord : Coord) (value : Digest) (charge : Charge) :
    State Coord Cell :=
  ⟨discloseTableValue state.candidates coord value, state.rows, state.counters.charge q charge⟩

/-- After a tick. -/
def tickState (q : Nat) (state : State Coord Cell) (charge : Charge) : State Coord Cell :=
  ⟨state.candidates, state.rows, state.counters.charge q charge⟩

/-- The world with fixed (eager) labels and table. -/
noncomputable def observedImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (table row), readState q state row (table row) charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => if (test.effective state.candidates).keep labels (table row) then
          pure (some (table row), probeState state row (test.effective state.candidates) (table row))
        else pure (none, stoppedState state)
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (labels coord), disclosedState q state coord (labels coord) charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

/-- The world with labels and rows sampled from their posteriors. -/
noncomputable def lazyImpl (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat) :
    QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun state =>
      (liftM (aux input) : SPMF _) >>= fun answer => pure (some answer, state)
  | .inr (.read row charge) => OptionT.mk <| StateT.mk fun state =>
      reply state.rows row >>= fun answer => pure (some answer, readState q state row answer charge)
  | .inr (.probe row test) => OptionT.mk <| StateT.mk fun state =>
      match state.rows row with
      | some answer => pure (some answer, readState q state row answer .call)
      | none => observe (lazyResponse state.candidates (test.effective state.candidates))
          (pure (none, stoppedState state))
          (fun answer => pure (some answer, probeState state row (test.effective state.candidates) answer))
  | .inr (.disclose coord charge) => OptionT.mk <| StateT.mk fun state =>
      cell (state.candidates coord) >>= fun value => pure (some value, disclosedState q state coord value charge)
  | .inr (.tick charge) => OptionT.mk <| StateT.mk fun state =>
      pure (some (), tickState q state charge)

/-- Run a world computation (stop = `none`). -/
noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :
    SPMF (Option Result × State Coord Cell) :=
  (OptionT.run (simulateQ implementation computation)).run state

omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (value : Result) (state : State Coord Cell) : runWith implementation (pure value) state = pure (some value, state) := by
  simp only [runWith, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

omit [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (input : (World auxSpec Coord Cell).Domain)
    (next : (World auxSpec Coord Cell).Range input → OracleComp (World auxSpec Coord Cell) Result)
    (state : State Coord Cell) :
    runWith implementation (liftM ((World auxSpec Coord Cell).query input) >>= next) state =
      ((implementation input).run.run state >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => runWith implementation (next answer) result.2)) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (implementation input).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl

/-- The eager observed run. -/
noncomputable def observedRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (labels : Coord → Digest) (table : Cell → HashOutput)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (observedImpl aux q labels table) computation state

/-- The lazy run. -/
noncomputable def lazyRun {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell) :=
  runWith (lazyImpl aux q) computation state

/-- Keep the eager tables of a continuing run. -/
def retain {Result : Type} (labels : Coord → Digest) (table : Cell → HashOutput)
    (result : Option Result × State Coord Cell) :
    Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell :=
  (result.1.map (fun value => (labels, table, value)), result.2)

/-- Draw the eager tables of a continuing lazy run from the final posterior. -/
noncomputable def finish {Result : Type} (result : Option Result × State Coord Cell) :
    SPMF (Option ((Coord → Digest) × (Cell → HashOutput) × Result) × State Coord Cell) :=
  match result.1 with
  | none => pure (none, result.2)
  | some value => complete result.2.candidates >>= fun labels =>
      completeRows result.2.rows >>= fun table => pure (some (labels, table, value), result.2)

private theorem bind_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (next : A → SPMF B) :
    ((if p then left else right) >>= next) = if p then left >>= next else right >>= next := by
  split <;> rfl

private theorem map_if {A B : Type} (p : Prop) [Decidable p] (left right : SPMF A) (f : A → B) :
    f <$> (if p then left else right) = if p then f <$> left else f <$> right := by
  split <;> rfl

omit [Fintype Coord] [DecidableEq Coord] in
private theorem observe_response_eq (labels : Coord → Digest) (probe : Probe Coord) {Result : Type}
    (stopped : SPMF Result) (next : HashOutput → SPMF Result) :
    observe (response labels probe) stopped next =
      ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= fun answer =>
        if probe.keep labels answer then next answer else stopped) := by
  rw [observe, response, toPMF_bind_lift]
  simp only [← PMF.monad_bind_eq_bind, evalSPMF_bind, bind_assoc]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true, SPMF.toPMF_pure, SPMF.lift_pure, pure_bind]
  · simp only [h, if_false, SPMF.toPMF_failure, SPMF.lift_pure, pure_bind]

omit [Fintype Coord] [DecidableEq Coord] in
/-- One fresh probe: eager table read with the keep test = lazy response (fixed labels). -/
private theorem fixedLabels_fresh (labels : Coord → Digest) (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → (Cell → HashOutput) → SPMF Result) :
    (completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) table else stopped) =
        observe (response labels probe) stopped
          (fun answer => completeRows (Function.update cache input (some answer)) >>= next answer) := by
  rw [bind_fresh cache input hfresh (fun answer table => if probe.keep labels answer then next answer table else stopped),
    observe_response_eq]
  apply congrArg ((liftM (PMF.uniformOfFintype HashOutput) : SPMF _) >>= ·)
  funext answer
  by_cases h : probe.keep labels answer
  · simp only [h, if_true]
  · simp only [h, if_false, completeRows_bind_const]

private theorem bind_fresh_probe (candidates : Coord → Finset Digest)
    (ha : ∀ c, (candidates c).Nonempty) (cache : ResidualTableCompletion.Cache Cell) (input : Cell)
    (hfresh : cache input = none) (probe : Probe Coord) {Result : Type} (stopped : SPMF Result)
    (next : HashOutput → (Coord → Digest) → (Cell → HashOutput) → SPMF Result) :
    (complete candidates >>= fun labels => completeRows cache >>= fun table =>
      if probe.keep labels (table input) then next (table input) labels table else stopped) =
        observe (lazyResponse candidates probe) stopped (fun answer =>
          complete (probe.restrict candidates answer) >>= fun labels =>
            completeRows (Function.update cache input (some answer)) >>= next answer labels) := by
  have hfixed (labels : Coord → Digest) := fixedLabels_fresh labels cache input hfresh probe stopped
    (fun answer table => next answer labels table)
  simp_rw [hfixed]
  exact bind_response_stopped candidates ha probe stopped
    (fun answer labels => completeRows (Function.update cache input (some answer)) >>= next answer labels)

/-- **Eager = lazy** (the record's `run_posterior` for this world). -/
theorem run_posterior {Result : Type} (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
    (computation : OracleComp (World auxSpec Coord Cell) Result) (state : State Coord Cell)
    (ha : ∀ c, (state.candidates c).Nonempty) :
    (complete state.candidates >>= fun labels => completeRows state.rows >>= fun table =>
      retain labels table <$> observedRun aux q labels table computation state) =
        (lazyRun aux q computation state >>= finish) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [observedRun, lazyRun, runWith_pure, map_pure, pure_bind, retain, Option.map_some, finish]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
            StateT.run_mk, bind_assoc, pure_bind, map_bind, Option.elim_some]
          conv_lhs => enter [2, labels]; rw [RetainedObservation.bind_comm]
          rw [RetainedObservation.bind_comm]
          apply congrArg ((liftM (aux input) : SPMF _) >>= ·)
          funext answer
          exact ih answer state ha
      | inr input =>
          cases input with
          | read row charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              have hread (labels : Coord → Digest) := bind_read state.rows row
                (fun answer table => retain labels table <$>
                  runWith (observedImpl aux q labels table) (next answer) (readState q state row answer charge))
              simp_rw [hread]
              rw [RetainedObservation.bind_comm]
              apply congrArg (reply state.rows row >>= ·)
              funext answer
              exact ih answer (readState q state row answer charge) ha
          | probe row test =>
              cases hcache : state.rows row with
              | some answer =>
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, pure_bind, Option.elim_some]
                  have hrows : Function.update state.rows row (some answer) = state.rows := by
                    rw [← hcache, Function.update_eq_self]
                  have h := ih answer (readState q state row answer .call) ha
                  simp only [readState, hrows] at h ⊢
                  exact h
              | none =>
                  change HashOutput → OracleComp (World auxSpec Coord Cell) Result at next
                  dsimp only [OracleSpec.Range, World, ResidualSpec] at ih ⊢
                  simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                    StateT.run_mk, hcache, observe_bind, pure_bind, Option.elim_none, Option.elim_some, finish]
                  dsimp only [OracleSpec.Range, World, OracleSpec.add_apply_inr, ResidualSpec]
                  simp only [bind_if, pure_bind, Option.elim_none, Option.elim_some, map_if, map_pure, retain,
                    Option.map_none]
                  rw [bind_fresh_probe state.candidates ha state.rows row hcache (test.effective state.candidates)
                    (pure (none, stoppedState state))
                    (fun answer labels table => retain labels table <$>
                      runWith (observedImpl aux q labels table) (next answer)
                        (probeState state row (test.effective state.candidates) answer))]
                  apply observe_congr
                  intro answer hanswer
                  exact ih answer (probeState state row (test.effective state.candidates) answer)
                    (lazyResponse_nonempty state.candidates _ answer hanswer)
          | disclose coord charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
              rw [bind_disclose state.candidates coord (fun value labels => completeRows state.rows >>= fun table =>
                retain labels table <$> runWith (observedImpl aux q labels table) (next value)
                  (disclosedState q state coord value charge))]
              apply congrArg (cell (state.candidates coord) >>= ·)
              funext value
              exact ih value (disclosedState q state coord value charge)
                (discloseTableValue_nonempty state.candidates ha coord value)
          | tick charge =>
              simp only [observedRun, lazyRun, runWith_query_bind, observedImpl, lazyImpl, OptionT.run_mk,
                StateT.run_mk, pure_bind, Option.elim_some]
              exact ih () (tickState q state charge) ha

end World

end SigGolfCandidate.T3.Security.LargeResidual
