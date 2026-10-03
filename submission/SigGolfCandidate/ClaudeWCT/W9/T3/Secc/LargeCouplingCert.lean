import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingTable
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingShort
import SigGolfCandidate.T3.Secc.LargeCouplingCertShort
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeContactCertClean
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingContact
import SigGolfCandidate.T3.Secc.LargeCouplingCertChain
import SigGolfCandidate.T3.Secc.LargeCouplingBankSign
import SigGolfCandidate.T3.Secc.LargeCouplingContact
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingBankSign

section

namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell observedRun runWith_bind)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertInteraction : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem interaction_le' (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : SigGolfCandidate.T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
    {α : Type} (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (Final : Monitor → RouterState → (α × QueryLog Requests) → LazyPrivate.State → Prop)
      (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (F : Option β × LargeResidual.State WCoord (Cell U) → Prop),
      (∀ mon st ws state v log, Rel U T vals nv τ a q mon st ws → MemoOk T st → Final mon st (v, log) state →
        1 ≤ Pr[F | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (K (some ((v, log), st))) ws]) →
      (∀ m s v σ, Final m s v σ → m.contact = true ∨ m.calls ≤ q) →
      (∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
        F (none, ws') ∨ ∀ m s v σ, Final m s v σ → m.contact = false) →
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
      ·
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
      ·
        rw [taggedFixed_world, Wots.Ref.fixedWorld_public, pure_bind, probEvent_map, routeInteraction_hash]
        by_cases hb : q ≤ st.calls
        ·
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
          ·
            rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_none]
            rcases hstop ws1 hcalls with hF | hnc
            · rw [probEvent_pure, if_pos hF]
              exact probEvent_le_one
            · have hzero : Pr[(fun t => Final (t.steps.foldl (Monitor.step U T q published) mon)
                    (t.steps.foldl (routerStep U T nv published) st) t.value t.state) ∘
                  (fun last => (⟨last.value, .world ⟨state, .inl (.inr X), T (.inl (.inr X))⟩ :: last.steps,
                    last.state⟩ : Tagged α)) |
                  taggedFixed T published (next (T (.inl (.inr X))))
                    (FirstHit.advance state (.inl (.inr X)) (T (.inl (.inr X))))] = 0 := by
                refine le_antisymm ((probEvent_mono'' (q := fun _ => False) ?_).trans (by simp)) (zero_le)
                intro t ht
                simp only [Function.comp_apply, List.foldl_cons] at ht
                have h1 := hnc _ _ _ _ ht
                change (List.foldl (Monitor.step U T q published) (mon.query U T q X (T (.inl (.inr X)))) t.steps).contact
                  = false at h1
                rw [steps_frozen U T q published _ hc] at h1
                rw [hc] at h1
                cases h1
              rw [hzero]
              exact zero_le
          · rw [observedRun, runWith_bind, ← observedRun, hrun, pure_bind]
            simp only [Option.elim_some]
            have hmemo1 : MemoOk T (st.next U X (T (.inl (.inr X)))) := by
              intro m f hf
              apply hmemo m f
              unfold RouterState.next at hf
              split_ifs at hf <;> exact hf
            exact ih (T (.inl (.inr X))) Final K F hleaf habort hstop _ _ ws1 _ hrel1 hmemo1
      ·
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
        have hstop' : ∀ ws' : LargeResidual.State WCoord (Cell U), ws'.counters.calls ≤ q →
            F (none, ws') ∨ ∀ m s v σ, Final' m s v σ → m.contact = false := by
          intro ws' hws
          rcases hstop ws' hws with h | h
          · exact Or.inl h
          · exact Or.inr fun m s v σ hf => h _ _ _ _ hf
        exact ih out Final' K' F hleaf' habort' hstop' _ _ wsF _ hrelF
          (signedState_memo T nv published st request hmemo)
end Interaction
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell observedRun runWith_bind)
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_w9largeCouplingCertTable : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def verdictCert (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (st : RouterState) (value : Option ForgeryP × QueryLog Requests) (state : LazyPrivate.State) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker pk value) = true ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = false ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).calls ≤ q ∧
  CertGhost ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (routerEvent U) st)
theorem honestNonce_coherent {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell U → HashOutput} {a : AuxData} (hcoh : Coherent U T vals nv τ a) : nv = honestNonce T := by
  funext m
  exact (hcoh.privateNonce m).symm
theorem table_cert_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : Coherent (Wots.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => CertR adversary q rec T |
        Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[CertOut |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary := Wots.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  have hnv := honestNonce_coherent hcoh
  rw [hcoh.routerWith, Wots.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le' initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hpub
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictCert (Wots.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon st
      value state)
    (verdictCont (Wots.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) CertOut
    ?_ ?_ ?_ Monitor.initial RouterState.initial (keyState (Wots.referenceInputs adversary) q vals nv) _ rel_initial
    (fun _ _ h => by simp [RouterState.initial] at h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    obtain ⟨h1, h2, h3, h4⟩ := hc _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h2 h3 h4
    have hv : (Wots.Ref.verdictRecord T t.untag).value =
        evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) :=
      Wots.Ref.pureRecord_value _ _ _
    refine ⟨hv ▸ h1, h2, h3, ?_⟩
    unfold routerFold at h4
    rw [hnv]
    exact h4
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PaddedGame.verdict_public _ _) mon st ws state hrel
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.referenceInputs adversary) a q
        (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    obtain ⟨hval, hnc, hcalls, hcert⟩ := hf
    rcases hph with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · rw [hnc] at h2; cases h2
    · omega
    · rw [if_pos ⟨_, by rw [h1, hval], hcert⟩]
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    have := hf.2.2.1
    omega
  · intro ws' _
    right
    intro m s v σ hf
    by_contra hcon
    have hc : m.contact = true := by simpa using hcon
    have h := hf.2.1
    rw [events_frozen (Wots.referenceInputs adversary) T q m hc] at h
    rw [hc] at h
    cases h
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section



namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeCoupling (honestNonce honestNonce_short)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingCertShort : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem routerStep_world (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (e : FirstHit.QueryEvent) : routerStep U A nv published st (.world e) = routerEvent U st e := rfl
theorem routerStep_sign (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache)
    (st : RouterState) (request : Security.Request) (out : Option Signature) (events : List FirstHit.QueryEvent) :
    routerStep U A nv published st (.sign request out events) = signedState A nv published st request := rfl
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem routeOk_short : RouteOk A = RouteOk T := by
  funext index
  apply propext
  unfold RouteOk
  simp only [Wots.Ref.referenceSearch_short hAT]
theorem signedState_short (nv : Message → Digest) (published : SigGolfCandidate.T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState A nv published st request = signedState T nv published st request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  unfold signedState LargeResidual.signItems
  rw [signDigest_short hAT, hd, routeOk_short hAT]
theorem routerStep_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (st : RouterState) (s : TaggedStep) :
    routerStep U A (honestNonce A) published st s = routerStep U T (honestNonce T) published st s := by
  cases s with
  | world e => rw [routerStep_world, routerStep_world]
  | sign request out events =>
      rw [routerStep_sign, routerStep_sign, honestNonce_short hAT, signedState_short hAT]
theorem steps_router_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep) :
    ∀ st, steps.foldl (routerStep U A (honestNonce A) published) st =
      steps.foldl (routerStep U T (honestNonce T) published) st := by
  induction steps with
  | nil => intro st; rw [List.foldl_nil, List.foldl_nil]
  | cons s rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, routerStep_short hAT, ih]
theorem routerFold_short (U : Finset HashInput) (published : SigGolfCandidate.T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    routerFold U A published steps verdict = routerFold U T published steps verdict := by
  unfold routerFold
  rw [steps_router_short hAT]
end Short
theorem certR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : CertR adversary q result A ↔ CertR adversary q result T := by
  unfold CertR
  simp only [monitorRun_short hAT, routerFold_short hAT]
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section





namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell AuxQuery lazyRun finish observedRun run_posterior retain
  runWith_query_bind lazyImpl)
open SigGolfCandidate.T3.Security.LargeCoupling (pmf_probEvent_mono_support' probEvent_bind_mono_le probEvent_bind_le_of
  weight_self evalSPMF_uniform_inst probEvent_bind_congr_eq completeRows_none)
open ClaudeWCT.W9.T3.Security.CanonGraph
open ClaudeWCT.W9.T3.Security.CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section CertChain
attribute [local instance] Classical.propDecidable
open ClaudeWCT.W9.T3.Security.LargeCoupling.Samplers SigGolfCandidate.T3.Security.LargeCoupling.Samplers
def RealCert (adversary : AdversaryP) (q : Nat) (x : FirstHit.Recorded Bool × Answers) : Prop :=
  CertR adversary q x.1 x.2
theorem cert_real_side (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => CertR adversary q (QueryRecorded.recordedTrace z.1) z.2 | SeccLaw.completedExperiment adversary q hq] =
      Pr[RealCert adversary q |
        ($ᵗ FullGame.FullTable : ProbComp _) >>= fun priv =>
          ($ᵗ (Wots.referenceInputs adversary → HashOutput) : ProbComp _) >>= fun pub =>
            fixedNext adversary (Wots.eagerAnswers (Wots.referenceInputs adversary) priv pub)] := by
  have h1 := Wots.completed_eager_cut adversary q hq (CertR adversary q)
  rw [h1]
  have h2 : (fun x : FirstHit.Recorded Bool × Answers => CertR adversary q x.1 (Wots.Ref.cut x.1.state x.2)) =
      RealCert adversary q := by
    funext x
    exact propext (certR_short (Wots.Ref.cut_shortAgree _ _) adversary q x.1)
  rw [h2]
  unfold Wots.eagerRecorded
  rw [MonitoredPrivate.event_lift]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  rw [evalSPMF_bind, evalSPMF_bind, evalSPMF_uniform_inst _ samplerFull]
  congr 1
section Lazy
variable {U : Finset HashInput}
theorem finish_some_le {R : Type} (X : SPMF (Option R × LargeResidual.State WCoord (Cell U))) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | X >>= finish] ≤ Pr[fun r => ∃ v, r.1 = some v ∧ P v | X] := by
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro r
  rcases r with ⟨v, st⟩
  cases v with
  | none =>
      have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish ((none : Option R), st)] = 0 := by
        simp only [finish, probEvent_pure]
        rw [if_neg]
        rintro ⟨v, hv, -⟩
        cases hv
      rw [h0, mul_zero]
      exact zero_le
  | some v =>
      by_cases hP : P v
      · rw [if_pos ⟨v, rfl, hP⟩]
        exact mul_le_of_le_one_right zero_le probEvent_le_one
      · have h0 : Pr[fun r => ∃ v, r.1 = some v ∧ P v.2.2 | finish (some v, st)] = 0 := by
          rw [probEvent_eq_zero_iff]
          intro x hx hE
          unfold finish at hx
          simp only [mem_support_bind_iff, mem_support_pure_iff] at hx
          obtain ⟨labels, -, table, -, rfl⟩ := hx
          obtain ⟨v', hv', hP'⟩ := hE
          simp only [Option.some.injEq] at hv'
          subst hv'
          exact hP hP'
        rw [h0, mul_zero]
        exact zero_le
theorem observed_avg_le {R : Type} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
    (program : OracleComp (RWorld U) R) (P : R → Prop) :
    Pr[fun r => ∃ v, r.1 = some v ∧ P v | 𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun labels =>
        𝒮[($ᵗ (Cell U → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
          observedRun aux q labels τ program LargeResidual.initial] ≤
      Pr[fun r => ∃ v, r.1 = some v ∧ P v | lazyRun aux q program LargeResidual.initial] := by
  rw [← complete_univ, ← completeRows_none]
  have hpost := run_posterior aux q program (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
    (fun _ => Finset.univ_nonempty)
  refine le_trans (le_of_eq ?_) (finish_some_le (lazyRun aux q program LargeResidual.initial) P)
  rw [← hpost]
  apply probEvent_bind_congr_eq
  intro labels
  apply probEvent_bind_congr_eq
  intro τ
  rw [probEvent_map]
  congr 1
  funext r
  apply propext
  rcases r with ⟨_ | v, st⟩
  · simp [retain]
  · simp [retain]
theorem certOut_iff (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    CertOut r ↔ ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st := by
  constructor
  · rintro ⟨st, h1, h2⟩
    exact ⟨_, h1, st, rfl, h2⟩
  · rintro ⟨v, h1, st, rfl, h2⟩
    exact ⟨st, h1, h2⟩
theorem router_side_cert (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut |
        𝒮[($ᵗ LowLabels : ProbComp _)] >>= fun high =>
        𝒮[($ᵗ (EncLeaf → Fin (2 ^ 22) → HashOutput) : ProbComp _)] >>= fun rows =>
        𝒮[($ᵗ FullGame.FullTable : ProbComp _)] >>= fun priv =>
        𝒮[($ᵗ (WCoord → LargeResidual.Digest) : ProbComp _)] >>= fun lab =>
        𝒮[($ᵗ (Cell (Wots.referenceInputs adversary) → LargeResidual.HashOutput) : ProbComp _)] >>= fun τ =>
        observedRun (auxLaw initLaw) q lab τ (routerWith (Wots.referenceInputs adversary) adversary q ⟨high, rows, priv⟩)
          LargeResidual.initial] ≤
      Pr[CertOut |
        lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial] := by
  have hce : (@CertOut (Wots.referenceInputs adversary)) =
      fun r => ∃ v, r.1 = some v ∧ ∃ st, v = some (true, st) ∧ CertGhost st :=
    funext fun r => propext (certOut_iff r)
  rw [hce]
  unfold router initReq
  rw [lazy_aux]
  change _ ≤ Pr[_ | (liftM initLaw : SPMF AuxData) >>= _]
  rw [initLaw_spmf]
  unfold initComp
  simp only [evalSPMF_bind, evalSPMF_pure, bind_assoc, pure_bind]
  apply probEvent_bind_mono_le
  intro high
  apply probEvent_bind_mono_le
  intro rows
  apply probEvent_bind_mono_le
  intro priv
  exact observed_avg_le (auxLaw initLaw) q _ _
end Lazy
theorem cert_le_lazy (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
      Pr[CertOut | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
        LargeResidual.initial] := by
  have hU : canonInputs ⊆ Wots.referenceInputs adversary :=
    canonInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  have hE : encInputs ⊆ Wots.referenceInputs adversary :=
    encInputs_subset_publicUniverse.trans (Wots.Ref.referenceInputs_universe adversary)
  refine le_trans (pmf_probEvent_mono_support' _ fun z hz h => cert_of_clean adversary q hq z hz h.1 h.2) ?_
  rw [cert_real_side]
  refine le_trans ?_ (router_side_cert adversary q)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (law_target (Wots.referenceInputs adversary) hU hE (fixedNext adversary))]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun high => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun rows => ?_
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun priv => ?_
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (world_split _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun lab => ?_
  have hτ : ∀ (k : (Wots.referenceInputs adversary → HashOutput) → ProbComp (FirstHit.Recorded Bool × Answers)),
      𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerPublic _) : ProbComp _) >>= k] =
        𝒮[(@uniformSample (Wots.referenceInputs adversary → HashOutput) (samplerCell _) : ProbComp _) >>= k] := by
    intro k
    rw [evalSPMF_bind]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (hτ _)]
  refine probEvent_bind_le_of _ _ _ _ _ _ (weight_self _) fun τ => ?_
  · have hT : CanonGraph.eagerAnswers (privateEquiv.symm ((fun s => lab (.inl (.inr s))),
          nonceOver (privateEquiv priv).2 (fun m => lab (.inr m)))) (Wots.referenceInputs adversary)
          (programmed (Wots.referenceInputs adversary) hU (fun s => lab (.inl (.inr s)))
            (joinLabels (fun N => lab (.inl (.inl N))) high)
            (residualPsi (Wots.referenceInputs adversary) hE (joinLabels (fun N => lab (.inl (.inl N))) high) rows τ)) =
        tablePsi (Wots.referenceInputs adversary) hU hE (fun c => lab (.inl c)) (fun m => lab (.inr m)) τ
          ⟨high, rows, priv⟩ := by
      unfold tablePsi
      rw [eagerAnswers_eq]
      rfl
    rw [hT]
    unfold fixedNext RealCert
    rw [probEvent_map]
    have h := table_cert_le adversary q hq initLaw
      (coherent_psi (Wots.referenceInputs adversary) hU hE (fun c => lab (.inl c)) (fun m => lab (.inr m)) τ
        ⟨high, rows, priv⟩)
    have hlab : Sum.elim (fun c => lab (.inl c)) (fun m => lab (.inr m)) = lab := by
      funext c
      rcases c with c | m <;> rfl
    rw [hlab] at h
    exact h
end CertChain
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section

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
noncomputable local instance instDecidableEqCache_largeCouplingBankRun : DecidableEq T3.Cache := Classical.decEq _
noncomputable def bankPay {U : Finset HashInput} (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi q st
    | _ => 0) + slackT q r.2
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi q st + slackT q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi q st + slackT q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi q st + slackT q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi q st + slackT q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls
theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [RouterState.initial]),
    fun p hp => absurd hp (by simp [RouterState.initial]), fun X hX => absurd hX (by simp [RouterState.initial])⟩
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay q) ≤
      psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) = (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction (auxLaw initLaw) q hUpub a _ _ _ (bankPay q) ?_ ?_ ?_ RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict (auxLaw initLaw) q a _ (bankPay q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]
end Run
end SigGolfCandidate.T3.Security.LargeCoupling
end

section

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open LargeResidual
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev lazyRouter (adversary : AdversaryP) (q : Nat) :=
  lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial
noncomputable def routerMass (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' r, Pr[= r | lazyRouter adversary q] * (r.2.counters.mass : ENNReal)
def LargeCertBound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : Prop :=
  Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
    routerMass adversary q / 2 ^ 128 + (q : ENNReal) * excessRate / 2 ^ 128 + (q : ENNReal) * cacheRate / 2 ^ 128 +
      (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute
theorem large_route_of_cert (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcert : LargeCertBound adversary q hq) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  apply SeccClosing.largeBound_of_parts q _
    (Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q]) _ (routerMass adversary q)
  · refine (SeccClosing.probEvent_le_contact_add _ (fun z => QueryRecorded.CleanWin q z.1) (Contact adversary q)
      (fun _ => True) (fun _ _ => trivial)).trans ?_
    gcongr
    refine le_trans (probEvent_mono'' fun z hz => hz.2) ?_
    exact contact_le_lazy adversary q hq
  · exact residual_potential (auxLaw initLaw) q hq _
  · exact hcert
end SigGolfCandidate.T3.Security.LargeCoupling
end

section



namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section NoFail
variable {Coord Cell AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}
  [Fintype Coord] [DecidableEq Coord] [Fintype Cell] [DecidableEq Cell]
  (aux : (input : auxSpec.Domain) → PMF (auxSpec.Range input)) (q : Nat)
theorem observed_noFail (labels : Coord → LargeResidual.Digest) (table : Cell → LargeResidual.HashOutput) {R : Type}
    (P : OracleComp (World auxSpec Coord Cell) R) :
    ∀ s, Pr[⊥ | observedRun aux q labels table P s] = 0 := by
  induction P using OracleComp.inductionOn with
  | pure v =>
      intro s
      rw [observedRun, runWith_pure]
      simp
  | query_bind input next ih =>
      intro s
      rw [observedRun, runWith_query_bind, probFailure_bind_eq_add_tsum]
      have h1 : Pr[⊥ | (observedImpl aux q labels table input).run.run s] = 0 := by
        rcases input with i | req
        · simp [observedImpl]
        · cases req with
          | read row ch => simp [observedImpl]
          | probe row test =>
              simp only [observedImpl, OptionT.run_mk, StateT.run_mk]
              split
              · simp
              · split <;> simp
          | disclose c ch => simp [observedImpl]
          | tick ch => simp [observedImpl]
      rw [h1, zero_add]
      apply ENNReal.tsum_eq_zero.mpr
      intro r
      rcases r with ⟨o, s'⟩
      cases o with
      | none => simp
      | some v =>
          simp only [Option.elim_some]
          exact mul_eq_zero_of_right _ (ih v s')
theorem lazy_noFail {R : Type} (P : OracleComp (World auxSpec Coord Cell) R) :
    Pr[⊥ | lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)] = 0 := by
  have hpost := run_posterior aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)
    (fun _ => Finset.univ_nonempty)
  have h1 : Pr[⊥ | lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell) >>= finish] = 0 := by
    rw [← hpost]
    have hc : complete (LargeResidual.initial : LargeResidual.State Coord Cell).candidates =
        liftM (uniformTable (fun _ : Coord => (Finset.univ : Finset LargeResidual.Digest)) (fun _ => Finset.univ_nonempty)) :=
      complete_of_nonempty _ _
    have hr : completeRows (LargeResidual.initial : LargeResidual.State Coord Cell).rows =
        liftM (PMF.uniformOfFintype (Cell → LargeResidual.HashOutput)) := completeRows_empty
    rw [hc, hr, probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    apply ENNReal.tsum_eq_zero.mpr
    intro labels
    rw [probFailure_bind_eq_add_tsum, SPMF.probFailure_liftM, probFailure_eq_zero, zero_add]
    rw [ENNReal.tsum_eq_zero.mpr, mul_zero]
    intro table
    rw [probFailure_map, observed_noFail, mul_zero]
  have h2 := probFailure_bind_eq_add_tsum
    (lazyRun aux q P (LargeResidual.initial : LargeResidual.State Coord Cell)) finish
  rw [h1] at h2
  exact (add_eq_zero.mp h2.symm).1
end NoFail
section Bank
variable {U : Finset HashInput}
noncomputable def psiOut (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi q st
  | _ => 0
theorem bankPay_eq (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    bankPay q r = psiOut q r + slackT q r.2 := rfl
theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert q st hc
  · exact zero_le
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 +
        (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut q r + slackT q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi q)
  set S := expectedValue L (fun r => slackT q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : (q : ENNReal) / 2 ^ 128 ≤ S + Mass / 2 ^ 128 := by
    have hMass' : Mass / 2 ^ 128 = expectedValue L (fun r => (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv]
      rw [expectedValue_mul_const L (fun r => (r.2.counters.mass : ENNReal))]
      rfl
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail ((q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div]
    apply ENNReal.div_le_div_right
    rw [← Nat.cast_add]
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top q) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut q) + S ≤ (psi q RouterState.initial + Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi q RouterState.initial + (S + Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut q) := hcert
    _ ≤ psi q RouterState.initial + Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial q) le_rfl
end Bank
theorem large_cert_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : LargeCertBound adversary q hq := by
  unfold LargeCertBound
  refine (cert_le_lazy adversary q hq).trans ?_
  refine (bank_cert_le (Wots.Ref.referenceInputs_universe adversary) initLaw adversary q).trans ?_
  have hrm : (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
      LargeResidual.initial] * (r.2.counters.mass : ENNReal)) = routerMass adversary q := rfl
  rw [hrm, SeccClosing.excessRate_def]
  calc
    _ = routerMass adversary q / 2 ^ 128 + (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 := add_comm _ _
    _ ≤ _ := by
      simp only [add_assoc]
      exact add_le_add le_rfl le_self_add
theorem large_route (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  large_route_of_cert adversary q hq (large_cert_bound adversary q hq)
theorem large_route_hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  fun adversary q hq _ => large_route adversary q hq
end SigGolfCandidate.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (State Cell lazyRun)
open SigGolfCandidate.T3.Security.LargeCoupling (ev_bind_le lazy_pure ev_runWith_bind)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9largeCouplingBankRun : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def bankPay {U : Finset HashInput} (q : Nat)
    (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) : ENNReal :=
  (match r.1 with
    | some (some (_, st)) => psi q st
    | _ => 0) + slackT q r.2
section Run
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
theorem bank_interaction (hUpub : SeccLaw.publicUniverse ⊆ U) (a : AuxData) (published : SigGolfCandidate.T3.Cache) {α : Type}
    (program : OracleComp LazyPrivate.Interaction α) :
    ∀ {β : Type} (K : Option ((α × QueryLog Requests) × RouterState) → OracleComp (RWorld U) β)
      (pay : Option β × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (K (some (v, st))) ws) pay ≤ psi q st + slackT q ws) →
      (∀ ws, expectedValue (lazyRun aux q (K none) ws) pay ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeInteraction U a published q program st >>= K) ws) pay ≤
          psi q st + slackT q ws := by
  induction program using OracleComp.inductionOn with
  | pure v =>
      intro β K pay _ hleaf _ st ws hinv hcalls
      rw [routeInteraction_pure, pure_bind]
      exact hleaf _ st ws hinv hcalls
  | query_bind input next ih =>
      intro β K pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | request
      · rw [routeInteraction_coin, bind_assoc, lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c K pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeInteraction_hash]
        split_ifs with hb
        · rw [pure_bind]
          exact (hnone ws).trans le_add_self
        · rw [bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y K pay hstop hleaf hnone st' ws' hinv' hcalls'
      · rw [routeInteraction_request, bind_assoc, lazyRun, ev_runWith_bind, ← lazyRun]
        apply bank_routeSign aux q hUpub a published st ws request hinv
        intro sig st' ws' hinv' hcalls'
        simp only [Option.elim_some, bind_assoc, pure_bind]
        refine ih sig (fun rest => K (rest.map fun res => ((res.1.1, ⟨request, sig⟩ :: res.1.2), res.2))) pay hstop
          ?_ ?_ st' ws' hinv' (by omega)
        · intro v st ws hinv hc
          exact hleaf _ st ws hinv hc
        · intro ws
          exact hnone ws
theorem bank_verdict (a : AuxData) {β : Type} (V : M β) :
    ∀ (pay : Option (Option (β × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal),
      (∀ ws', pay (none, ws') ≤ slackT q ws') →
      (∀ v st ws, BankInv U ws st → st.calls ≤ q → pay (some (some (v, st)), ws) ≤ psi q st + slackT q ws) →
      (∀ ws, pay (some none, ws) ≤ slackT q ws) →
      ∀ st ws, BankInv U ws st → st.calls ≤ q →
        expectedValue (lazyRun aux q (routeVerdict U a q V st) ws) pay ≤ psi q st + slackT q ws := by
  induction V using OracleComp.inductionOn with
  | pure v =>
      intro pay _ hleaf _ st ws hinv hcalls
      rw [routeVerdict_pure, lazy_pure, expectedValue_pure]
      exact hleaf v st ws hinv hcalls
  | query_bind input next ih =>
      intro pay hstop hleaf hnone st ws hinv hcalls
      rcases input with (n | X) | c
      · change expectedValue (lazyRun aux q (coinReq U n >>= fun c => routeVerdict U a q (next c) st) ws) pay ≤ _
        rw [lazy_coinReq]
        apply ev_bind_le
        intro c
        exact ih c pay hstop hleaf hnone st ws hinv hcalls
      · rw [routeVerdict_public]
        split_ifs with hb
        · rw [lazy_pure, expectedValue_pure]
          exact (hnone ws).trans le_add_self
        · rw [lazyRun, ev_runWith_bind, ← lazyRun]
          apply bank_routeQuery aux q a st ws X hinv (by omega)
          · intro ws'
            exact hstop ws'
          · intro y st' ws' hinv' hcalls'
            exact ih y pay hstop hleaf hnone st' ws' hinv' hcalls'
      · change expectedValue (lazyRun aux q (routeVerdict U a q (next (a.priv c)) st) ws) pay ≤ _
        exact ih (a.priv c) pay hstop hleaf hnone st ws hinv hcalls
theorem bankInv_initial (s : LargeResidual.State WCoord (Cell U)) (hd : DiscFrame U LargeResidual.initial s) :
    BankInv U s RouterState.initial := by
  obtain ⟨hr, hc, hn⟩ := hd
  refine ⟨by rw [hc]; rfl, by rw [hc]; exact le_rfl, le_rfl, fun m _ => by rw [hn m]; rfl,
    fun X hX _ _ _ => by rw [hr]; rfl, fun X hX _ hs _ => absurd hs (by simp [RouterState.initial]),
    fun p hp => absurd hp (by simp [RouterState.initial]), fun X hX => absurd hX (by simp [RouterState.initial])⟩
theorem bank_router (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) :
    expectedValue (lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial) (bankPay q) ≤
      psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := by
  have hslack0 : slackT q (LargeResidual.initial : LargeResidual.State WCoord (Cell U)) = (q : ENNReal) / 2 ^ 128 := by
    unfold slackT; rfl
  rw [← hslack0]
  unfold router
  rw [lazy_initReq]
  apply ev_bind_le
  intro a
  unfold routerWith
  apply ev_discloseAll_le
  intro pairs s hd
  have hinv := bankInv_initial s hd
  refine (bank_interaction (auxLaw initLaw) q hUpub a _ _ _ (bankPay q) ?_ ?_ ?_ RouterState.initial s hinv
    (Nat.zero_le _)).trans ?_
  · intro ws'
    simp only [bankPay, zero_add]
    exact le_rfl
  · intro v st ws hinv' hc
    apply bank_verdict (auxLaw initLaw) q a _ (bankPay q)
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · intro v' st' ws' _ _
      simp only [bankPay]
      exact le_rfl
    · intro ws'
      simp only [bankPay, zero_add]
      exact le_rfl
    · exact hinv'
    · exact hc
  · intro ws
    rw [lazy_pure, expectedValue_pure]
    simp only [bankPay, zero_add]
    exact le_rfl
  · rw [slackT_eq_of_mass q (show s.counters.mass = (LargeResidual.initial : LargeResidual.State WCoord (Cell U)).counters.mass by
      rw [hd.2.1])]
end Run
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section


namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (residual_potential lazyRun)
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
noncomputable abbrev lazyRouter (adversary : AdversaryP) (q : Nat) :=
  lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q) LargeResidual.initial
noncomputable def routerMass (adversary : AdversaryP) (q : Nat) : ENNReal :=
  ∑' r, Pr[= r | lazyRouter adversary q] * (r.2.counters.mass : ENNReal)
def LargeCertBound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : Prop :=
  Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ ¬Contact adversary q z | SeccLaw.completedExperiment adversary q hq] ≤
    routerMass adversary q / 2 ^ 128 + (q : ENNReal) * excessRate / 2 ^ 128 + (q : ENNReal) * cacheRate / 2 ^ 128 +
      (q : ENNReal) * largeReserveRate / 2 ^ 128 + largeReserveAbsolute
theorem large_route_of_cert (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hcert : LargeCertBound adversary q hq) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q := by
  rw [← SeccLaw.completed_trace_event adversary q hq (QueryRecorded.CleanWin q)]
  apply SeccClosing.largeBound_of_parts q _
    (Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q | lazyRouter adversary q]) _ (routerMass adversary q)
  · refine (SeccClosing.probEvent_le_contact_add _ (fun z => QueryRecorded.CleanWin q z.1) (Contact adversary q)
      (fun _ => True) (fun _ _ => trivial)).trans ?_
    gcongr
    refine le_trans (probEvent_mono'' fun z hz => hz.2) ?_
    exact contact_le_lazy adversary q hq
  · exact residual_potential (auxLaw initLaw) q hq _
  · exact hcert
end ClaudeWCT.W9.T3.Security.LargeCoupling
end

section




namespace ClaudeWCT.W9.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.LargeResidual
open SigGolfCandidate.T3.Security.LargeResidual (Cell lazyRun)
open SigGolfCandidate.T3.Security.LargeCoupling (lazy_noFail)
open SphincsSecurity.Concrete UniformTableCompletion ResidualTableCompletion RetainedObservation
open SeccClosing (largeBound excessRate cacheRate largeReserveRate largeReserveAbsolute)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [local instance] Classical.propDecidable
section Bank
variable {U : Finset HashInput}
noncomputable def psiOut (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    ENNReal :=
  match r.1 with
  | some (some (_, st)) => psi q st
  | _ => 0
theorem bankPay_eq (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    bankPay q r = psiOut q r + slackT q r.2 := rfl
theorem certOut_le_psi (q : Nat) (r : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U)) :
    (if CertOut r then (1 : ENNReal) else 0) ≤ psiOut q r := by
  split_ifs with h
  · obtain ⟨st, hr, hc⟩ := h
    unfold psiOut
    rw [hr]
    exact psi_cert q st hc
  · exact zero_le
theorem bank_cert_le (hUpub : SeccLaw.publicUniverse ⊆ U) (initLaw : PMF AuxData) (adversary : AdversaryP) (q : Nat) :
    Pr[CertOut | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] ≤
      (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 +
        (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial] *
          (r.2.counters.mass : ENNReal)) / 2 ^ 128 := by
  set L := lazyRun (auxLaw initLaw) q (router U adversary q) LargeResidual.initial with hL
  have hfail : Pr[⊥ | L] = 0 := lazy_noFail (auxLaw initLaw) q _
  have hbank := bank_router q hUpub initLaw adversary
  rw [← hL] at hbank
  have hbp : (bankPay q : Option (Option (Bool × RouterState)) × LargeResidual.State WCoord (Cell U) → ENNReal) =
      fun r => psiOut q r + slackT q r.2 := rfl
  rw [hbp, expectedValue_add] at hbank
  have hcert : Pr[CertOut | L] ≤ expectedValue L (psiOut q) := by
    rw [← expectedValue_ite_one]
    exact expectedValue_mono _ (certOut_le_psi q)
  set S := expectedValue L (fun r => slackT q r.2) with hS
  set Mass := ∑' r, Pr[= r | L] * (r.2.counters.mass : ENNReal) with hMass
  have hmass : (q : ENNReal) / 2 ^ 128 ≤ S + Mass / 2 ^ 128 := by
    have hMass' : Mass / 2 ^ 128 = expectedValue L (fun r => (r.2.counters.mass : ENNReal) / 2 ^ 128) := by
      rw [hMass]
      simp only [div_eq_mul_inv]
      rw [expectedValue_mul_const L (fun r => (r.2.counters.mass : ENNReal))]
      rfl
    rw [hMass', hS, ← expectedValue_add, ← expectedValue_const hfail ((q : ENNReal) / 2 ^ 128)]
    apply expectedValue_mono
    intro r
    unfold slackT
    rw [← ENNReal.add_div]
    apply ENNReal.div_le_div_right
    rw [← Nat.cast_add]
    exact_mod_cast (show q ≤ q - r.2.counters.mass + r.2.counters.mass by omega)
  have hSfin : S ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := (q : ENNReal) / 2 ^ 128)
    · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top q) (by positivity)
    · apply expectedValue_le_of_le
      intro r
      unfold slackT
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.sub_le q _
  have hkey : expectedValue L (psiOut q) + S ≤ (psi q RouterState.initial + Mass / 2 ^ 128) + S := by
    calc
      _ ≤ psi q RouterState.initial + (q : ENNReal) / 2 ^ 128 := hbank
      _ ≤ psi q RouterState.initial + (S + Mass / 2 ^ 128) := add_le_add le_rfl hmass
      _ = _ := by ring
  have hpsi := (ENNReal.add_le_add_iff_right hSfin).mp hkey
  calc
    _ ≤ expectedValue L (psiOut q) := hcert
    _ ≤ psi q RouterState.initial + Mass / 2 ^ 128 := hpsi
    _ ≤ _ := add_le_add (psi_initial q) le_rfl
end Bank
theorem large_cert_bound (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) : LargeCertBound adversary q hq := by
  unfold LargeCertBound
  refine (cert_le_lazy adversary q hq).trans ?_
  refine (bank_cert_le (Wots.Ref.referenceInputs_universe adversary) initLaw adversary q).trans ?_
  have hrm : (∑' r, Pr[= r | lazyRun (auxLaw initLaw) q (router (Wots.referenceInputs adversary) adversary q)
      LargeResidual.initial] * (r.2.counters.mass : ENNReal)) = routerMass adversary q := rfl
  rw [hrm, SeccClosing.excessRate_def]
  calc
    _ = routerMass adversary q / 2 ^ 128 + (q : ENNReal) * (11324 / 100000000) / 2 ^ 128 := add_comm _ _
    _ ≤ _ := by
      simp only [add_assoc]
      exact add_le_add le_rfl le_self_add
theorem large_route (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) :
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  large_route_of_cert adversary q hq (large_cert_bound adversary q hq)
theorem large_route_hlarge : ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), SeccClosing.budgetSplit ≤ q →
    Pr[QueryRecorded.CleanWin q | PaddedGame.tracedExperiment adversary q hq] ≤ largeBound q :=
  fun adversary q hq _ => large_route adversary q hq
end ClaudeWCT.W9.T3.Security.LargeCoupling
end
