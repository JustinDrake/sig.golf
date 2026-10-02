import SigGolfCandidate.T3.Secc.LargeResidualRouter

/-!
# LR-34 (coupling, observed world): one request at a time

Closed forms of the eager observed world (`observedImpl`) on each request, and the generic `bind`/`map` rules of
`runWith`. With them a deterministic router computation (no coin) evaluates to a single `pure` outcome.

* `runWith_bind`, `runWith_map`;
* `observed_aux`, `observed_read`, `observed_probe_cached`, `observed_probe_fresh`, `observed_disclose`,
  `observed_tick` (the six request kinds), and their router forms `observed_coinReq`, `observed_readReq`,
  `observed_probeReq_cached`, `observed_probeReq_fresh`, `observed_discloseReq`, `observed_tickReq`,
  `observed_discloseAll`.
-/

namespace SigGolfCandidate.T3.Security.LargeResidual
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

theorem runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    runWith impl (comp >>= k) s =
      (runWith impl comp s >>= fun r => r.1.elim (pure (none, r.2)) (fun v => runWith impl (k v) r.2)) := by
  simp only [runWith, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation => (simulateQ impl comp).run.run s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v <;> rfl

theorem runWith_map {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (f : α → β) (comp : OracleComp (World auxSpec Coord Cell) α) (s : State Coord Cell) :
    runWith impl (f <$> comp) s = (fun r => (r.1.map f, r.2)) <$> runWith impl comp s := by
  rw [map_eq_bind_pure_comp, runWith_bind, map_eq_bind_pure_comp]
  apply congrArg (fun continuation => runWith impl comp s >>= continuation)
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => rfl
  | some v => simp only [Option.elim_some, Function.comp_def, runWith_pure, Option.map_some]

variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
  (labels : Coord → Digest) (table : Cell → HashOutput)

theorem observed_pure {β : Type} (v : β) (s : State Coord Cell) :
    observedRun aux q labels table (pure v) s = pure (some v, s) :=
  runWith_pure _ v s

theorem observed_aux {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem observed_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl

theorem observed_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observedRun aux q labels table (k v) (readState q s row v .call) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl

theorem observed_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      if (test.effective s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effective s.candidates) (table row))
      else pure (none, stoppedState s) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, h]
  split_ifs <;> simp only [pure_bind, Option.elim_some, Option.elim_none, observedRun]

theorem observed_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl

theorem observed_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    observedRun aux q labels table (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) := by
  rw [observedRun, runWith_query_bind]
  simp only [observedImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl

end Generic

/-! ## Router requests -/

section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (table : Cell U → HashOutput)

theorem observed_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (coinReq U n >>= k) s =
      ((liftM (aux (.coin n)) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table (.coin n) k s

theorem observed_initReq {β : Type} (k : AuxData → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (initReq U >>= k) s =
      ((liftM (aux .init) : SPMF _) >>= fun v => observedRun aux q labels table (k v) s) :=
  observed_aux aux q labels table .init k s

theorem observed_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (readReq U row ch >>= k) s =
      observedRun aux q labels table (k (table row)) (readState q s row (table row) ch) :=
  observed_read aux q labels table row ch k s

theorem observed_probeReq_cached {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (v : HashOutput)
    (h : s.rows row = some v) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      observedRun aux q labels table (k v) (readState q s row v .call) :=
  observed_probe_cached aux q labels table row test k s v h

theorem observed_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    observedRun aux q labels table (probeReq U row test >>= k) s =
      if (test.effective s.candidates).keep labels (table row) then
        observedRun aux q labels table (k (table row)) (probeState s row (test.effective s.candidates) (table row))
      else pure (none, stoppedState s) :=
  observed_probe_fresh aux q labels table row test k s h

theorem observed_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseReq U c ch >>= k) s =
      observedRun aux q labels table (k (labels c)) (disclosedState q s c (labels c) ch) :=
  observed_disclose aux q labels table c ch k s

theorem observed_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    observedRun aux q labels table (tickReq U ch >>= k) s =
      observedRun aux q labels table (k ()) (tickState q s ch) :=
  observed_tick aux q labels table ch k s

/-- The world state after uncharged disclosures of a list of (label/secret) coordinates. -/
def discloseStates (q : Nat) (labels : WCoord → Digest) (s : State WCoord (Cell U)) (cs : List Coord) :
    State WCoord (Cell U) :=
  cs.foldl (fun s c => disclosedState q s (.inl c) (labels (.inl c)) .none) s

theorem observed_discloseAll {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    observedRun aux q labels table (discloseAll U cs >>= k) s =
      observedRun aux q labels table (k (cs.map fun c => (c, labels (.inl c)))) (discloseStates U q labels s cs) := by
  induction cs generalizing s k with
  | nil => simp only [discloseAll, pure_bind, List.map_nil, discloseStates, List.foldl_nil]
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [observed_discloseReq]
      simp only [pure_bind]
      rw [ih]
      rfl

end Router

end SigGolfCandidate.T3.Security.LargeResidual
