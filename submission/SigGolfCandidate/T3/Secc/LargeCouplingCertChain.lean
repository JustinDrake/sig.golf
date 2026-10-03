import SigGolfCandidate.T3.Secc.LargeCouplingInteraction
import SigGolfCandidate.T3.Secc.LargeCouplingTable
import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.T3.Secc.LargeCouplingCertShort
import SigGolfCandidate.T3.Secc.LargeContactCertClean
import SigGolfCandidate.T3.Secc.LargeCouplingContact

section

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
noncomputable local instance instDecidableEqCache_largeCouplingCertInteraction : DecidableEq T3.Cache := Classical.decEq _
section Interaction
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat} (initLaw : PMF AuxData)
theorem interaction_le' (hcoh : Coherent U T vals nv τ a) (hq : q ≤ 2 ^ 127) (hUpub : SeccLaw.publicUniverse ⊆ U)
    (published : T3.Cache) (hpub : published.region = Correctness.cacheRegion (Correctness.maskedTop T))
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
end SigGolfCandidate.T3.Security.LargeCoupling
end

section



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
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingCertTable : DecidableEq T3.Cache := Classical.decEq _
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
end SigGolfCandidate.T3.Security.LargeCoupling
end

section




namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section CertChain
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3.Security.LargeCoupling.Samplers
theorem pmf_probEvent_mono_support' {α : Type} (p : PMF α) {F G : α → Prop} (h : ∀ x ∈ p.support, F x → G x) :
    Pr[F | p] ≤ Pr[G | p] := by
  simp only [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ p.support
  · by_cases hF : F x
    · simp [hF, h x hx hF]
    · simp [hF]
  · have hp : p x = 0 := by
      rw [PMF.apply_eq_zero_iff]
      exact hx
    simp [hp]
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
theorem probEvent_bind_mono_le {α β γ : Type} (m : SPMF α) (f : α → SPMF β) (g : α → SPMF γ) (E : β → Prop)
    (E' : γ → Prop) (h : ∀ x, Pr[E | f x] ≤ Pr[E' | g x]) : Pr[E | m >>= f] ≤ Pr[E' | m >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x
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
end SigGolfCandidate.T3.Security.LargeCoupling
end
