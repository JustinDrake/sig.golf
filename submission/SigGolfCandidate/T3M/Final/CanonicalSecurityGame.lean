import SigGolfCandidate.T3M.Final.CanonicalSecurityRom
import SigGolfCandidate.T3M.Final.BridgeAbs
import SigGolfCandidate.T3M.CanonicalFinal.SecurityP

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Bridge
open SigGolfCandidate.T3M.Final
open T3.Security (Requests forwardWorld)
open SphincsSecurity (OracleWorld)

def publicHandler : QueryImpl Spec (OracleComp SSpec)
  | .inl (.inl n) => (SSpec.query (.inl (.inl n)) : OracleComp SSpec _)
  | .inl (.inr input) => (SSpec.query (.inl (.inr input)) : OracleComp SSpec _)
  | .inr _ => pure (0 : BitVec 256)

def publicLift {α : Type} (p : M α) : OracleComp SSpec α := simulateQ publicHandler p

theorem runA_publicLift {α : Type} (p : M α) (hp : AllQueriesSatisfy p isPublic) :
    runA (publicLift p)=(fun a => (a,[])) <$> p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    simp only [publicLift,simulateQ_bind,simulateQ_spec_query]
    cases q with
    | inl x =>
      cases x with
      | inl n => exact hp.1.elim
      | inr input =>
        change runA ((SSpec.query (.inl (.inr input)) : OracleComp SSpec _) >>= _)=_
        rw [runA_inl_bind,map_bind]
        exact bind_congr fun a => ih a (hp.2 a)
    | inr c => exact hp.1.elim

def adaptedAdversary (A : AdversaryP) : AdversaryP := fun pk cache => do
  let some f ← A pk cache | pure none
  publicLift (adaptForgery f)

theorem runA_bind_general {α β : Type} (p : OracleComp SSpec α) (k : α → OracleComp SSpec β) :
    runA (p >>= k)=(do
      let a ← runA p
      let b ← runA (k a.1)
      pure (b.1,a.2++b.2)) := by
  simp only [runA,simulateQ_bind,WriterT.run_bind,map_eq_bind_pure_comp]
  rfl

theorem runA_adapted (A : AdversaryP) (pk : Digest) (cache : Cache) :
    runA (adaptedAdversary A pk cache)=(do
      let a ← runA (A pk cache)
      let g ← match a.1 with
        | none => pure none
        | some f => adaptForgery f
      pure (g,a.2)) := by
  unfold adaptedAdversary
  rw [runA_bind_general]
  refine bind_congr fun a => ?_
  cases a.1 with
  | none => simp [runA_pure]
  | some f =>
    rw [runA_publicLift _ (T3M.allQ_mono (pubGood_adaptForgery f) (fun _ h => h.1))]
    simp only [bind_map_left,List.append_nil]

noncomputable def finishC (pk : Digest) (log : QueryLog Requests) (o : Option ForgeryP) : M Bool := do
  let some f := o | pure false
  let b ← checkForgeryC pk log f
  pure (decide (log.length≤2^32) && b)

noncomputable def finishAdapted (pk : Digest) (log : QueryLog Requests) (o : Option ForgeryP) : M Bool := do
  let some f := o | pure false
  let b ← adaptedCheck pk log f
  pure (decide (log.length≤2^32) && b)

theorem gameC_eq (A : AdversaryP) :
    CanonicalFinal.gameP A=(do
      let kp ← keygen
      let a ← runA (A kp.1 kp.2)
      finishC kp.1 a.2 a.1) := rfl

theorem gameP_adapted_eq (A : AdversaryP) :
    gameP (adaptedAdversary A)=(do
      let kp ← keygen
      let a ← runA (A kp.1 kp.2)
      finishAdapted kp.1 a.2 a.1) := by
  unfold gameP
  change (keygen >>= fun kp => runA (adaptedAdversary A kp.1 kp.2) >>= _)=_
  refine bind_congr fun kp => ?_
  rw [runA_adapted,bind_assoc]
  refine bind_congr fun a => ?_
  cases a.1 with
  | none => simp [finishAdapted]
  | some f =>
    unfold finishAdapted adaptedCheck
    simp only [pure_bind,bind_assoc]
    exact bind_congr fun g => by cases g <;> simp only [pure_bind,Bool.and_false]

#print axioms gameP_adapted_eq
theorem pubGood_finishC (pk : Digest) (log : QueryLog Requests) (o : Option ForgeryP) :
    AllQueriesSatisfy (finishC pk log o) PubGood := by
  cases o with
  | none => exact allQ_pure _
  | some f => exact allQ_bind (pubGood_checkC _ _ _) fun _ => allQ_pure _

theorem pubGood_finishAdapted (pk : Digest) (log : QueryLog Requests) (o : Option ForgeryP) :
    AllQueriesSatisfy (finishAdapted pk log o) PubGood := by
  cases o with
  | none => exact allQ_pure _
  | some f => exact allQ_bind (pubGood_adaptedCheck _ _ _) fun _ => allQ_pure _

theorem finish_counted_eval (answers : Correctness.Answers) (pk : Digest)
    (log : QueryLog Requests) (o : Option ForgeryP) :
    WinCount (evalWithAnswerFn answers (Cost.countCalls (finishC pk log o)))
      (evalWithAnswerFn answers (Cost.countCalls (finishAdapted pk log o))) := by
  cases o with
  | none => simp [finishC,finishAdapted,WinCount,Cost.countCalls]
  | some f =>
    unfold finishC finishAdapted
    dsimp only
    rw [counted_bind_eval,counted_bind_eval]
    simp only [Cost.countCalls,Cost.countWith_pure,evalWithAnswerFn_pure,Nat.add_zero]
    intro hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨hl,hb⟩ := hb
    have hh := check_counted_eval answers pk log f hb
    exact ⟨by simp only [Bool.and_eq_true];exact ⟨hl,hh.1⟩,hh.2⟩

theorem finish_hash_event (sk : BitVec 256) (pk : Digest) (log : QueryLog Requests)
    (o : Option ForgeryP) (c q : Nat) (cache : QueryCache AHash) :
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ randomOracle (countFrom (fun _ => 1) (hrealize sk (finishC pk log o)) c)).run' cache] ≤
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ randomOracle (countFrom (fun _ => 1) (hrealize sk (finishAdapted pk log o)) c)).run' cache] := by
  apply randomOracle_event_mono_cache
  intro hash he
  rw [countFrom_shift,evalWithAnswerFn_map] at he ⊢
  change (evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (finishC pk log o)))).1=true ∧
      c+(evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (finishC pk log o)))).2≤q at he
  change (evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (finishAdapted pk log o)))).1=true ∧
      c+(evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (finishAdapted pk log o)))).2≤q
  rw [←hrealize_count_calls sk _ (T3M.allQ_mono (pubGood_finishC pk log o) (fun _ h => h.hashGood.1)),eval_hrealize] at he
  rw [←hrealize_count_calls sk _ (T3M.allQ_mono (pubGood_finishAdapted pk log o) (fun _ h => h.hashGood.1)),eval_hrealize]
  have hh := finish_counted_eval (hashAnswers hash sk) pk log o he.1
  exact ⟨hh.1,by omega⟩

theorem finish_world_event (sk : BitVec 256) (pk : Digest) (log : QueryLog Requests)
    (o : Option ForgeryP) (c q : Nat) (cache : QueryCache AHash) :
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (finishC pk log o)) c)).run' cache] ≤
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (finishAdapted pk log o)) c)).run' cache] := by
  rw [realize_eq_liftM sk (T3M.allQ_mono (pubGood_finishC pk log o) (fun _ h => h.hashGood.1)),
    realize_eq_liftM sk (T3M.allQ_mono (pubGood_finishAdapted pk log o) (fun _ h => h.hashGood.1)),
    countFrom_liftM_hash _ (fun _ => rfl),countFrom_liftM_hash _ (fun _ => rfl)]
  rw [SphincsSecurity.romImpl,QueryImpl.simulateQ_add_liftM_right,QueryImpl.simulateQ_add_liftM_right]
  exact finish_hash_event sk pk log o c q cache

theorem bind_events_mono {α β γ : Type} (p : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (E : β → Prop) (F : γ → Prop) (h : ∀ a,Pr[E | f a]≤Pr[F | g a]) :
    Pr[E | p >>= f]≤Pr[F | p >>= g] := by
  rw [probEvent_bind_eq_tsum,probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => by gcongr;exact h a

theorem common_prefix_event {α : Type} (sk : BitVec 256) (p : M α) (f g : α → M Bool)
    (c q : Nat) (cache : QueryCache AHash)
    (h : ∀ a c cache,
      Pr[fun r => r.1=true ∧ r.2≤q |
        (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (f a)) c)).run' cache] ≤
      Pr[fun r => r.1=true ∧ r.2≤q |
        (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (g a)) c)).run' cache]) :
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (p >>= f)) c)).run' cache] ≤
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (p >>= g)) c)).run' cache] := by
  rw [Cost.realize_bind,Cost.realize_bind,countFrom_bind,countFrom_bind]
  simp only [simulateQ_bind,StateT.run'_eq,StateT.run_bind,map_bind]
  apply bind_events_mono
  intro a
  exact h a.1.1 a.1.2 a.2

theorem realExperimentC_event (A : AdversaryP) (q : Nat) :
    Pr[fun r => r.1=true ∧ r.2≤q | CanonicalFinal.realExperimentP A] ≤
      Pr[fun r => r.1=true ∧ r.2≤q | realExperimentP (adaptedAdversary A)] := by
  unfold CanonicalFinal.realExperimentP realExperimentP
  apply bind_events_mono
  intro sk
  rw [derivation_realize,derivation_realize,countHashQueries_eq,countHashQueries_eq,gameC_eq,gameP_adapted_eq]
  apply common_prefix_event
  intro kp c cache
  apply common_prefix_event
  intro a c cache
  exact finish_world_event sk kp.1 a.2 a.1 c q cache

theorem securityC_of_old (hS : SecurityP) : CanonicalFinal.SecurityP := by
  intro A q hq
  exact (realExperimentC_event A q).trans (hS (adaptedAdversary A) q hq)

#print axioms securityC_of_old
end SigGolfCandidate.T3M.CanonicalSource
