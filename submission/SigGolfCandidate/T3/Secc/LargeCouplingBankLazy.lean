import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs

/-!
# LR-34 (bank, lazy world): one request at a time, in expectation

Closed forms of the lazy world (`lazyImpl`) on each router request, the expectation of a bind (`ev_runWith_bind`),
and the uncharged disclosure of a list of label/secret coordinates (`ev_discloseAll_le`: the rows, the counters and
the nonce candidate sets are untouched).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Generic
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]

/-- **The expectation of a bind** of a world run: stops pay at once, continuations are averaged. -/
theorem ev_runWith_bind {α β : Type}
    (impl : QueryImpl (World auxSpec Coord Cell) (OptionT (StateT (State Coord Cell) SPMF)))
    (comp : OracleComp (World auxSpec Coord Cell) α) (k : α → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) (pay : Option β × State Coord Cell → ENNReal) :
    expectedValue (runWith impl (comp >>= k) s) pay =
      expectedValue (runWith impl comp s) (fun r => r.1.elim (pay (none, r.2))
        (fun v => expectedValue (runWith impl (k v) r.2) pay)) := by
  rw [runWith_bind, expectedValue_bind]
  congr 1
  funext r
  rcases r with ⟨v, s'⟩
  cases v with
  | none => simp only [Option.elim_none, expectedValue_pure]
  | some v => rfl

variable (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)

theorem lazy_pure {β : Type} (v : β) (s : State Coord Cell) :
    lazyRun aux q (pure v) s = pure (some v, s) :=
  runWith_pure _ v s

theorem lazy_aux' {β : Type} (i : AuxIndex) (k : auxSpec.Range i → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inl i)) >>= k) s =
      ((liftM (aux i) : SPMF _) >>= fun v => lazyRun aux q (k v) s) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem lazy_read {β : Type} (row : Cell) (ch : Charge) (k : HashOutput → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.read row ch))) >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem lazy_probe_cached {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      lazyRun aux q (k v) (readState q s row v .call) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, pure_bind, Option.elim_some]
  rfl

theorem lazy_probe_fresh {β : Type} (row : Cell) (test : Probe Coord)
    (k : HashOutput → OracleComp (World auxSpec Coord Cell) β) (s : State Coord Cell) (h : s.rows row = none) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.probe row test))) >>= k) s =
      observe (lazyResponse s.candidates (test.effective s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effective s.candidates) y)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, h, observe_bind, pure_bind, Option.elim_none,
    Option.elim_some]
  rfl

theorem lazy_disclose {β : Type} (c : Coord) (ch : Charge) (k : Digest → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.disclose c ch))) >>= k) s =
      (cell (s.candidates c) >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind, Option.elim_some]
  rfl

theorem lazy_tick {β : Type} (ch : Charge) (k : Unit → OracleComp (World auxSpec Coord Cell) β)
    (s : State Coord Cell) :
    lazyRun aux q (liftM ((World auxSpec Coord Cell).query (.inr (.tick ch))) >>= k) s =
      lazyRun aux q (k ()) (tickState q s ch) := by
  rw [lazyRun, runWith_query_bind]
  simp only [lazyImpl, OptionT.run_mk, StateT.run_mk, pure_bind, Option.elim_some]
  rfl

/-- A bound on every branch of an observation bounds its expectation. -/
theorem ev_observe_le {Answer Result : Type} (response : SPMF Answer) (stopped : SPMF Result)
    (next : Answer → SPMF Result) (g : Result → ENNReal) (B : ENNReal)
    (hs : expectedValue stopped g ≤ B) (hn : ∀ y, expectedValue (next y) g ≤ B) :
    expectedValue (observe response stopped next) g ≤ B := by
  unfold observe
  rw [expectedValue_bind]
  apply expectedValue_le_of_le
  intro o
  cases o with
  | none => exact hs
  | some y => exact hn y

/-- A bound on every sample bounds the expectation of a bind. -/
theorem ev_bind_le {α β : Type} (mx : SPMF α) (f : α → SPMF β) (g : β → ENNReal) (B : ENNReal)
    (h : ∀ x, expectedValue (f x) g ≤ B) : expectedValue (mx >>= f) g ≤ B := by
  rw [expectedValue_bind]
  exact expectedValue_le_of_le _ h

end Generic

/-! ## Router requests -/

section Router
variable (U : Finset HashInput) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)

theorem lazy_coinReq {β : Type} (n : Nat) (k : Fin (n + 1) → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (coinReq U n >>= k) s = ((liftM (aux (.coin n)) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q (.coin n) k s

theorem lazy_initReq {β : Type} (k : AuxData → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (initReq U >>= k) s = ((liftM (aux .init) : SPMF _) >>= fun v => lazyRun aux q (k v) s) :=
  lazy_aux' aux q .init k s

theorem lazy_readReq {β : Type} (row : Cell U) (ch : Charge) (k : HashOutput → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (readReq U row ch >>= k) s =
      (reply s.rows row >>= fun y => lazyRun aux q (k y) (readState q s row y ch)) :=
  lazy_read aux q row ch k s

theorem lazy_probeReq_cached {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (v : HashOutput)
    (h : s.rows row = some v) :
    lazyRun aux q (probeReq U row test >>= k) s = lazyRun aux q (k v) (readState q s row v .call) :=
  lazy_probe_cached aux q row test k s v h

theorem lazy_probeReq_fresh {β : Type} (row : Cell U) (test : Probe WCoord)
    (k : HashOutput → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) (h : s.rows row = none) :
    lazyRun aux q (probeReq U row test >>= k) s =
      observe (lazyResponse s.candidates (test.effective s.candidates)) (pure (none, stoppedState s))
        (fun y => lazyRun aux q (k y) (probeState s row (test.effective s.candidates) y)) :=
  lazy_probe_fresh aux q row test k s h

theorem lazy_discloseReq {β : Type} (c : WCoord) (ch : Charge) (k : Digest → OracleComp (RWorld U) β)
    (s : State WCoord (Cell U)) :
    lazyRun aux q (discloseReq U c ch >>= k) s =
      (cell (s.candidates c) >>= fun v => lazyRun aux q (k v) (disclosedState q s c v ch)) :=
  lazy_disclose aux q c ch k s

theorem lazy_tickReq {β : Type} (ch : Charge) (k : Unit → OracleComp (RWorld U) β) (s : State WCoord (Cell U)) :
    lazyRun aux q (tickReq U ch >>= k) s = lazyRun aux q (k ()) (tickState q s ch) :=
  lazy_tick aux q ch k s

/-- What uncharged label/secret disclosures keep: rows, counters and the nonce candidate sets. -/
def DiscFrame (s s' : State WCoord (Cell U)) : Prop :=
  s'.rows = s.rows ∧ s'.counters = s.counters ∧ ∀ m : Message, s'.candidates (.inr m) = s.candidates (.inr m)

theorem DiscFrame.refl (s : State WCoord (Cell U)) : DiscFrame U s s := ⟨rfl, rfl, fun _ => rfl⟩

theorem DiscFrame.trans {s1 s2 s3 : State WCoord (Cell U)} (h1 : DiscFrame U s1 s2) (h2 : DiscFrame U s2 s3) :
    DiscFrame U s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun m => (h2.2.2 m).trans (h1.2.2 m)⟩

theorem discFrame_disclose (s : State WCoord (Cell U)) (c : Coord) (v : Digest) :
    DiscFrame U s (disclosedState q s (.inl c) v .none) := by
  refine ⟨rfl, rfl, fun m => ?_⟩
  simp only [disclosedState, discloseTableValue]
  rw [Function.update_of_ne (by simp)]

/-- **Uncharged disclosures of label/secret coordinates**, in expectation. -/
theorem ev_discloseAll_le {β : Type} (cs : List Coord) (k : List (Coord × Digest) → OracleComp (RWorld U) β)
    (pay : Option β × State WCoord (Cell U) → ENNReal) (B : ENNReal) (s : State WCoord (Cell U))
    (h : ∀ pairs s', DiscFrame U s s' → expectedValue (lazyRun aux q (k pairs) s') pay ≤ B) :
    expectedValue (lazyRun aux q (discloseAll U cs >>= k) s) pay ≤ B := by
  induction cs generalizing s k with
  | nil =>
      simp only [discloseAll, pure_bind]
      exact h [] s (DiscFrame.refl U s)
  | cons c rest ih =>
      simp only [discloseAll, bind_assoc]
      rw [lazy_discloseReq]
      apply ev_bind_le
      intro v
      simp only [pure_bind]
      exact ih _ _ fun pairs s' hs' => h _ s' ((discFrame_disclose U q s c v).trans U hs')

end Router

end SigGolfCandidate.T3.Security.LargeCoupling
