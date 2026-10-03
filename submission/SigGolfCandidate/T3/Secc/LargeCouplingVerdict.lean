import SigGolfCandidate.T3.Secc.LargeCouplingSigning

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingVerdict : DecidableEq T3.Cache := Classical.decEq _
section Monitor
variable (U : Finset HashInput) (A : Answers) (q : Nat)
theorem query_frozen (mon : Monitor) (h : mon.contact = true) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon := by
  unfold Monitor.query; rw [if_pos h]
theorem event_frozen (mon : Monitor) (h : mon.contact = true) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_frozen U A q mon h X answer
  · rfl
theorem events_frozen (mon : Monitor) (h : mon.contact = true) (events : List FirstHit.QueryEvent) :
    events.foldl (Monitor.event U A q) mon = mon := by
  induction events with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, event_frozen U A q mon h e, ih]
theorem query_over (mon : Monitor) (hc : mon.contact = false) (hq : q ≤ mon.calls) (X : HashInput)
    (y : HashOutput) : (mon.query U A q X y).contact = false ∧ q < (mon.query U A q X y).calls := by
  unfold Monitor.query
  rw [if_neg (by rw [hc]; decide), if_neg (fun h => by omega)]
  exact ⟨rfl, show q < mon.calls + 1 by omega⟩
theorem event_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (e : FirstHit.QueryEvent) :
    (mon.event U A q e).contact = false ∧ q < (mon.event U A q e).calls := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · exact ⟨hc, hq⟩
  · exact query_over U A q mon hc (by omega) X answer
  · exact ⟨hc, hq⟩
theorem events_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (events : List FirstHit.QueryEvent) :
    (events.foldl (Monitor.event U A q) mon).contact = false ∧ q < (events.foldl (Monitor.event U A q) mon).calls := by
  induction events generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := event_over U A q mon hc hq e
      exact ih _ h1 h2
end Monitor
noncomputable def routerEvent (U : Finset HashInput) (st : RouterState) (e : FirstHit.QueryEvent) : RouterState :=
  match e with
  | ⟨_, .inl (.inr X), y⟩ => st.next U X y
  | _ => st
def PhaseOutcome (U : Finset HashInput) (T : Answers) (vals : Coord → Digest) (nv : Message → Digest)
    (τ : Cell U → HashOutput) (a : AuxData) (q : Nat) {β : Type} (monF : Monitor) (value : β) (stF : RouterState)
    (out : Option (Option (β × RouterState))) (ws' : LargeResidual.State WCoord (Cell U)) : Prop :=
  (out = none ∧ monF.contact = true ∧ ws'.counters.calls ≤ q) ∨
    (out = some none ∧ monF.contact = false ∧ q < monF.calls) ∨
    (out = some (some (value, stF)) ∧ Rel U T vals nv τ a q monF stF ws')
section Verdict
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}
  (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
theorem routeVerdict_pure {β : Type} (v : β) (st : RouterState) :
    routeVerdict U a q (pure v : M β) st = pure (some (v, st)) := rfl
theorem routeVerdict_public {β : Type} (X : HashInput) (next : HashOutput → M β) (st : RouterState) :
    routeVerdict U a q (liftM (T3.Spec.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else (routeQuery U a st X >>= fun r => routeVerdict U a q (next r.1) r.2) := rfl
theorem routeVerdict_observed (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) {β : Type} (V : M β)
    (hV : PublicVerdict.Only V) :
    ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
      Rel U T vals nv τ a q mon st ws →
      ∃ out ws', observedRun aux q (Sum.elim vals nv) τ (routeVerdict U a q V st) ws = pure (out, ws') ∧
        PhaseOutcome U T vals nv τ a q ((Wots.Ref.pureRecord T V state).events.foldl (Monitor.event U T q) mon)
          (evalWithAnswerFn T V) ((Wots.Ref.pureRecord T V state).events.foldl (routerEvent U) st) out ws' := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro mon st ws state hrel
      refine ⟨some (some (v, st)), ws, ?_, Or.inr (Or.inr ⟨rfl, hrel⟩)⟩
      rw [routeVerdict_pure]
      exact observed_pure aux q _ τ _ ws
  | query_bind input next ih =>
      intro mon st ws state hrel
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hV
      rcases input with (n | X) | c
      · exact False.elim hi
      · rw [Wots.Ref.pureRecord_query_bind]
        simp only [List.foldl_cons]
        rw [routeVerdict_public]
        by_cases hb : q ≤ st.calls
        · rw [if_pos hb]
          refine ⟨some none, ws, observed_pure aux q _ τ _ ws, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩
          have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
          exact events_over U T q _ h1.1 h1.2 _
        · rw [if_neg hb]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed aux hcoh hrel hlt hq X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          · refine ⟨none, ws1, ?_, Or.inl ⟨rfl, ?_, hcalls⟩⟩
            · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
              rfl
            · change (List.foldl (Monitor.event U T q) (mon.query U T q X (T (.inl (.inr X)))) _).contact = true
              rw [events_frozen U T q _ hc]
              exact hc
          · obtain ⟨out, ws2, hrun2, hph⟩ := ih (T (.inl (.inr X))) (hn _) _ _ ws1 _ hrel1
            refine ⟨out, ws2, ?_, hph⟩
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            exact hrun2
      · exact False.elim hi
end Verdict
end SigGolfCandidate.T3.Security.LargeCoupling
