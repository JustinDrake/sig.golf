import SigGolfCandidate.T3.Secc.LargeCouplingVerdict
import SigGolfCandidate.T3.Secc.LargeCouplingFixed

/-!
# LR-34 (coupling, interaction): the routed interaction dominates the monitored fixed-world interaction

For a coherent eager table `T`, the adversary's interaction in the fixed world of `T` (`taggedFixed`) and the routed
interaction in the eager observed world use the same uniform coins; every hash query is simulated by
`routeQuery_observed`, every signing request by `routeSign_observed`. **`interaction_le`**: for any event `Final` of
the real run (read through the monitor fold and the router-state fold of its tagged steps) and any router event `F`
of the continued router run, if

* (leaf) `Final` at the end of the interaction implies `F` of the router's continuation (`K`) from any related state,
* (abort) `Final` implies the final monitor contacted or stayed within the budget,
* (stop) every stop within the budget satisfies `F`,

then `Pr[Final | real] ≤ Pr[F | router]`.
-/

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
noncomputable local instance instDecidableEqCache_largeCouplingInteraction : DecidableEq T3.Cache := Classical.decEq _

/-- The router state after one tagged step of the real run. -/
noncomputable def routerStep (U : Finset HashInput) (T : Answers) (nv : Message → Digest) (published : T3.Cache)
    (st : RouterState) : TaggedStep → RouterState
  | .world e => routerEvent U st e
  | .sign request _ _ => signedState T nv published st request

section Steps
variable (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)

theorem steps_over (mon : Monitor) (hc : mon.contact = false) (hq : q < mon.calls) (steps : List TaggedStep) :
    (steps.foldl (Monitor.step U A q published) mon).contact = false ∧
      q < (steps.foldl (Monitor.step U A q published) mon).calls := by
  induction steps generalizing mon with
  | nil => exact ⟨hc, hq⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).1
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            rfl
      · cases s with
        | world e => exact (event_over U A q mon hc hq e).2
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, hc]
            exact hq

theorem steps_frozen (mon : Monitor) (hc : mon.contact = true) (steps : List TaggedStep) :
    steps.foldl (Monitor.step U A q published) mon = mon := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = mon := by
        cases s with
        | world e => exact event_frozen U A q mon hc e
        | sign request out events => simp only [Monitor.step, Monitor.sign, hc, if_true]
      rw [h1, ih]

end Steps

section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)

theorem routeInteraction_pure {α : Type} (published : T3.Cache) (v : α) (st : RouterState) :
    routeInteraction U a published q (pure v : OracleComp LazyPrivate.Interaction α) st = pure (some ((v, []), st)) :=
  rfl

theorem routeInteraction_coin {α : Type} (published : T3.Cache) (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) st =
      (coinReq U n >>= fun c => routeInteraction U a published q (next c) st) := rfl

theorem routeInteraction_hash {α : Type} (published : T3.Cache) (X : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inl (.inr X))) >>= next) st =
      if q ≤ st.calls then pure none else
        (routeQuery U a st X >>= fun r => routeInteraction U a published q (next r.1) r.2) := rfl

theorem routeInteraction_request {α : Type} (published : T3.Cache) (request : Security.Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) (st : RouterState) :
    routeInteraction U a published q (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) st =
      (routeSign U a published st request >>= fun s =>
        routeInteraction U a published q (next s.1) s.2 >>= fun rest =>
          pure (rest.map fun res => ((res.1.1, ⟨request, s.1⟩ :: res.1.2), res.2))) := rfl

/-- **The routed interaction dominates the real fixed-world interaction** (any event pair, see the module doc). -/
theorem interaction_le (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q → F (none, ws')) →
      ∀ (mon : Monitor) (st : RouterState) (ws : LargeResidual.State WCoord (Cell U)) (state : LazyPrivate.State),
        Rel U T vals nv τ a q mon st ws → MemoOk T st →
        Pr[fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
              (t.steps.foldl (routerStep U T nv published) st) t.value t.state |
            taggedFixed T published program state] ≤
          Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
            (routeInteraction U a published q program st >>= K) ws] := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β Final K F hleaf habort hstop mon st ws state hrel hmemo
      rw [taggedFixed_pure, routeInteraction_pure, pure_bind, probEvent_pure]
      split_ifs with hf
      · exact hleaf mon st ws state v [] hrel hmemo hf
      · exact zero_le
  | query_bind input next ih =>
      intro β Final K F hleaf habort hstop mon st ws state hrel hmemo
      rcases input with (n | X) | request
      · -- a coin
        rw [taggedFixed_world, routeInteraction_coin, bind_assoc, observed_coinReq]
        rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply ENNReal.tsum_le_tsum
        intro c
        have hc : Pr[= c | Wots.Ref.fixedWorld T (.inl (.inl n))] =
            Pr[= c | (liftM (auxLaw initLaw (.coin n)) : SPMF (Fin (n + 1)))] := by
          change Pr[= c | (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))] = _
          simp [auxLaw, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.uniformOfFintype_apply]
        rw [hc]
        gcongr
        rw [probEvent_map]
        exact ih c Final K F hleaf habort hstop mon st ws _ hrel hmemo
      · -- an adversary hash query
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        · -- budget abort: the real event is impossible
          rw [if_pos hb]
          have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
              (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                last.state⟩ : Tagged α)) |
              taggedFixed T published (next (T (.inl (.inr X))))
                (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
            have h1 := query_over U T q mon hrel.contact (by rw [hrel.calls]; exact hb) X (T (.inl (.inr X)))
            refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
            intro t ht
            simp only [Function.comp_apply, List.foldl_cons] at ht
            have h2 := steps_over U T q published _ h1.1 h1.2 t.steps
            rcases habort _ _ _ _ ht with h | h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                = true at h
              rw [h2.1] at h
              cases h
            · change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).calls
                ≤ q at h
              omega
          rw [hzero]
          exact zero_le
        · rw [if_neg hb, bind_assoc]
          have hlt : st.calls < q := by omega
          obtain ⟨ws1, hout⟩ := routeQuery_observed (auxLaw initLaw) hcoh hrel hlt hq X
          rcases hout with ⟨hc, hrun, -, hcalls⟩ | ⟨hc, hrun, hrel1⟩
          · -- a stop: the router event holds
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rw [probEvent_pure, if_pos (hstop ws1 hcalls)]
            exact probEvent_le_one
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop _ _ ws1 _ hrel1 hmemo1
      · -- a signing request
        rw [taggedFixed_request, Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.authenticatedSign_hashOnly _ _),
          pure_bind, probEvent_map, routeInteraction_request, bind_assoc]
        obtain ⟨wsF, hrun, hrelF⟩ := routeSign_observed (auxLaw initLaw) hcoh hUpub published hpub hrel hmemo request
        rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
        simp only [Option.elim_some, bind_assoc, pure_bind]
        have hval : (Wots.Ref.pureRecord T (FullGame.authenticatedSign published request) state).value =
            evalWithAnswerFn T (FullGame.authenticatedSign published request) := Wots.Ref.pureRecord_value _ _ _
        rw [hval]
        set out := evalWithAnswerFn T (FullGame.authenticatedSign published request) with hout
        let Final' : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop :=
          fun m s v σ => Final m s (v.1, ⟨request, out⟩ :: v.2) σ
        let K' : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β :=
          fun rest => K (rest.map fun res => ((res.1.1, ⟨request, out⟩ :: res.1.2), res.2))
        have hleaf' : ∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st →
            Final' mon st (v, log) state →
            1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K' (some ((v, log), st))) ws] :=
          fun mon st ws state v log hrel hmemo hf => hleaf mon st ws state v (⟨request, out⟩ :: log) hrel hmemo hf
        have habort' : ∀ m s v σ, Final' m s v σ → m.contact = true ∨ m.calls ≤ q :=
          fun m s v σ hf => habort _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)

end Interaction

end SigGolfCandidate.T3.Security.LargeCoupling
