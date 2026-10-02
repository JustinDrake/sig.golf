import SigGolfCandidate.T3.Secc.CaseCNearHandlers

/-!
# Stream CC: a ghost environment over B-PAIR's lazy world (reuse flag, fresh-only exposures)

`envG` runs exactly as B-PAIR's environment `env` (any `Environment AuxSpecL FtsCoord Digest LazyMem` whose trials and
disclosures keep the memory, e.g. `envL`) on the first memory component, and keeps a ghost `NearGhost`:

* at a nonce draw `v` of `m`: `lastFresh := (nonce of m undrawn)`, and if fresh `reused ||= Reuse rows v m`;
* at an exposure `o`: `fresh ++= o` iff `lastFresh` (the first signing of a message only).

`run_project`: every run of `envG` projects onto the run of `env` (the ghost is invisible to the world), so any
payoff on `env`'s final state has the same expectation under `envG`.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The bank's ghost. -/
structure NearGhost where
  reused : Bool
  lastFresh : Bool
  fresh : List HashOutput

def NearGhost.empty : NearGhost := ⟨false, false, []⟩

/-- The ghost update of an auxiliary step (`mem`: the world memory before the step). -/
noncomputable def ghostStep (mem : BPair.LazyMem) : (i : BPair.AuxL) → BPair.AuxSpecL.Range i → NearGhost → NearGhost
  | .nonce m, v, g =>
      { g with lastFresh := decide (mem.nonces m = none),
               reused := g.reused || (decide (mem.nonces m = none) && decide (Reuse mem.rows v m)) }
  | .expose o, _, g => if g.lastFresh then { g with fresh := g.fresh ++ o.toList } else g
  | _, _, g => g

/-- The world state seen by `env`. -/
def projS (s : SecretGuessObservation.State BPair.FtsCoord Digest (BPair.LazyMem × NearGhost)) : BPair.WStateL :=
  ⟨s.allowed, s.retired, s.guesses, s.probes, s.memory.1⟩

/-- **The ghost environment.** -/
noncomputable def envG (env : SecretGuessObservation.Environment BPair.AuxSpecL BPair.FtsCoord Digest BPair.LazyMem) :
    SecretGuessObservation.Environment BPair.AuxSpecL BPair.FtsCoord Digest (BPair.LazyMem × NearGhost) where
  auxiliary st i := (fun r => (r.1, (r.2, ghostStep st.memory.1 i r.1 st.memory.2))) <$> env.auxiliary (projS st) i
  trial mem c v hit := (env.trial mem.1 c v hit, mem.2)
  disclosure mem c v := (env.disclosure mem.1 c v, mem.2)

abbrev GState := SecretGuessObservation.State BPair.FtsCoord Digest (BPair.LazyMem × NearGhost)

def initG : GState := SecretGuessObservation.initialState (BPair.LazyMem.empty, NearGhost.empty)

theorem projS_initG : projS initG = BPair.initL := rfl

section Project
variable (env : SecretGuessObservation.Environment BPair.AuxSpecL BPair.FtsCoord Digest BPair.LazyMem) (slot : Nat)

theorem liftM_map_pmf {α β : Type} (f : α → β) (p : PMF α) :
    (liftM (f <$> p) : SPMF β) = f <$> (liftM p : SPMF α) :=
  evalSPMF_map p f

theorem step_project (q : BPair.WSpecL.Domain) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> (SecretGuessObservation.forcedImpl (envG env) slot q).run s =
      (SecretGuessObservation.forcedImpl env slot q).run (projS s) := by
  rcases q with i | (⟨c, v⟩ | c)
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    change (fun r => (r.1, projS r.2)) <$> ((fun result => (result.1, { s with memory := result.2 })) <$>
      (liftM ((fun r => (r.1, (r.2, ghostStep s.memory.1 i r.1 s.memory.2))) <$> env.auxiliary (projS s) i) : SPMF _)) =
      (fun result => (result.1, { projS s with memory := result.2 })) <$> (liftM (env.auxiliary (projS s) i) : SPMF _)
    rw [liftM_map_pmf, Functor.map_map, Functor.map_map]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, StateT.run_mk]
    rw [Functor.map_map]
    have h1 : SecretGuessObservation.forcedTrial slot s c v = SecretGuessObservation.forcedTrial slot (projS s) c v := by
      have hA : (projS s).allowed = s.allowed := rfl
      have hP : (projS s).probes = s.probes := rfl
      have hR : (projS s).retired = s.retired := rfl
      unfold SecretGuessObservation.forcedTrial SecretGuessObservation.EligibleAt
      rw [hA, hP, hR]
    rw [h1]
    rfl
  · simp only [SecretGuessObservation.forcedImpl, SecretGuessObservation.lazyImpl, StateT.run_mk]
    rw [Functor.map_map]
    rfl

/-- **The ghost run projects onto the world run.** -/
theorem run_project {β : Type} (W : OracleComp BPair.WSpecL β) (s : GState) :
    (fun r => (r.1, projS r.2)) <$> SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s =
      SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s) := by
  induction W using OracleComp.inductionOn generalizing s with
  | pure b =>
      simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind q next ih =>
      rw [SecretGuessObservation.runWith_query_bind, SecretGuessObservation.runWith_query_bind, map_bind]
      simp_rw [ih]
      rw [← step_project env slot q s, bind_map_left]

/-- Expectations of world payoffs are unchanged by the ghost. -/
theorem expectedValue_project {β : Type} (W : OracleComp BPair.WSpecL β) (s : GState)
    (payoff : β × BPair.WStateL → ENNReal) :
    expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl env slot) W (projS s)) payoff =
      expectedValue (SecretGuessObservation.runWith (SecretGuessObservation.forcedImpl (envG env) slot) W s)
        (fun r => payoff (r.1, projS r.2)) := by
  rw [← run_project env slot W s, expectedValue_map]

end Project

end SigGolfCandidate.T3.Security.CaseC
