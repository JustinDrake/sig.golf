import SigGolfCandidate.T3.Secc.CaseCLinkInv
import SigGolfCandidate.T3.Secc.CaseCCover
import SigGolfCandidate.T3.Secc.WotsTransportSplit

/-!
# Stream CC: the bank run is the actual run of the pinned case-(C) event

* `logged_ghost_log` / `public_ghost_log`: the ghost log is the logged program's log, and the final verifier adds
  nothing to it;
* `record_prefix_unique` (prefix determinism of the recorder), `split_unique`: every `GameSplit` of the recorded
  trace has the actual key generation and interaction records;
* `bank_actual`: a bank sample carries the actual key generation and interaction records, the invariant, and its
  ghost log is the actual signing log.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCLinkSplit : DecidableEq T3.Cache := Classical.decEq _

/-! ## The ghost log -/

theorem bank_step_log (published : T3.Cache) (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (st : BankState) (r : LazyPrivate.Interaction.Range input × BankState)
    (hr : r ∈ ((bankImpl published budget input).run st).support) :
    r.2.1.log = st.1.log ++ ProposalOverflow.logFragment input r.1 := by
  cases input with
  | inl input =>
      obtain ⟨q, _, rfl⟩ := bank_support_world published budget input st r hr
      obtain ⟨_, hL, _⟩ := ghostWorld_fields budget input st.1 st.2 q.1
      simp only [hL, ProposalOverflow.logFragment, List.append_nil]
  | inr request =>
      obtain ⟨q, _, rfl⟩ := bank_support_sign published budget request st r hr
      rw [ghostSign_log]
      rfl

theorem logged_ghost_log {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState)
    (i : (α × QueryLog Requests) × BankState)
    (hi : i ∈ ((simulateQ (bankImpl published budget) (ProposalOverflow.logged program)).run st).support) :
    i.2.1.log = st.1.log ++ i.1.2 := by
  induction program using OracleComp.inductionOn generalizing st i with
  | pure value =>
      rw [ProposalOverflow.logged_pure] at hi
      simp only [simulateQ_pure, StateT.run_pure] at hi
      change i ∈ (PMF.pure ((value, []), st)).support at hi
      rw [PMF.support_pure, Set.mem_singleton_iff] at hi
      subst hi
      simp
  | query_bind input next ih =>
      rw [ProposalOverflow.logged_query_bind] at hi
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure] at hi
      change i ∈ (PMF.bind _ _).support at hi
      rw [PMF.mem_support_bind_iff] at hi
      obtain ⟨middle, hm, hi⟩ := hi
      change i ∈ (PMF.bind _ _).support at hi
      rw [PMF.mem_support_bind_iff] at hi
      obtain ⟨res, hres, hi⟩ := hi
      change i ∈ (PMF.pure _).support at hi
      rw [PMF.support_pure, Set.mem_singleton_iff] at hi
      subst hi
      have h1 := ih middle.1 middle.2 res hres
      have h2 := bank_step_log published budget input st middle hm
      simp only
      rw [h1, h2, List.append_assoc]

theorem public_ghost_log {β : Type} (published : T3.Cache) (budget : Nat) (program : M β) (st : BankState)
    (v : β × BankState)
    (hv : v ∈ ((simulateQ (bankImpl published budget) (CreationGame.publicProgram program)).run st).support) :
    v.2.1.log = st.1.log := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      rw [CreationGame.publicProgram_pure] at hv
      simp only [simulateQ_pure, StateT.run_pure] at hv
      change v ∈ (PMF.pure (value, st)).support at hv
      rw [PMF.support_pure, Set.mem_singleton_iff] at hv
      subst hv
      rfl
  | query_bind input next ih =>
      unfold CreationGame.publicProgram at hv
      rw [simulateQ_bind, simulateQ_spec_query] at hv
      rcases input with (sample | x) | coordinate
      · simp only [CreationGame.publicHandler, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hv
        change v ∈ (PMF.bind _ _).support at hv
        rw [PMF.mem_support_bind_iff] at hv
        obtain ⟨middle, hm, hv⟩ := hv
        rw [ih middle.1 middle.2 hv]
        have := bank_step_log published budget (.inl (.inl sample)) st middle hm
        rw [this]
        simp [ProposalOverflow.logFragment]
      · simp only [CreationGame.publicHandler, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hv
        change v ∈ (PMF.bind _ _).support at hv
        rw [PMF.mem_support_bind_iff] at hv
        obtain ⟨middle, hm, hv⟩ := hv
        rw [ih middle.1 middle.2 hv]
        have := bank_step_log published budget (.inl (.inr x)) st middle hm
        rw [this]
        simp [ProposalOverflow.logFragment]
      · simp only [CreationGame.publicHandler, simulateQ_pure, pure_bind] at hv
        exact ih _ st hv

/-! ## Prefix determinism -/

theorem queryEvent_answer_eq {state : LazyPrivate.State} {input : T3.Spec.Domain} {a b : T3.Spec.Range input}
    (h : (⟨state, input, a⟩ : FirstHit.QueryEvent) = ⟨state, input, b⟩) : a = b := by
  simp only [FirstHit.QueryEvent.mk.injEq, heq_eq_eq, true_and] at h
  exact h

/-- **Prefix determinism of the recorder** (as LR-34's). -/
theorem record_prefix_unique {α : Type} (program : M α) (state : LazyPrivate.State)
    (r1 r2 : FirstHit.Recorded α) (h1 : r1 ∈ support (FirstHit.record program state))
    (h2 : r2 ∈ support (FirstHit.record program state)) (rest1 rest2 : List FirstHit.QueryEvent)
    (heq : r1.events ++ rest1 = r2.events ++ rest2) : r1 = r2 := by
  induction program using OracleComp.inductionOn generalizing state r1 r2 rest1 rest2 with
  | pure value =>
      rw [FirstHit.record_pure, mem_support_pure_iff] at h1 h2
      rw [h1, h2]
  | query_bind input next ih =>
      rw [FirstHit.record_query_bind, mem_support_bind_iff] at h1 h2
      obtain ⟨m1, hm1, h1⟩ := h1
      obtain ⟨m2, hm2, h2⟩ := h2
      rw [support_map] at h1 h2
      obtain ⟨l1, hl1, rfl⟩ := h1
      obtain ⟨l2, hl2, rfl⟩ := h2
      simp only [List.cons_append, List.cons.injEq] at heq
      have ha : m1.1 = m2.1 := queryEvent_answer_eq heq.1
      have hs1 := FirstHit.query_advance state input m1 hm1
      have hs2 := FirstHit.query_advance state input m2 hm2
      have hm : m1 = m2 := Prod.ext ha (by rw [hs1, hs2, ha])
      subst hm
      have hl := ih m1.1 m1.2 l1 l2 hl1 hl2 rest1 rest2 heq.2
      rw [hl]

/-- Any decomposition of a recorded trace whose events begin with an actual key generation and interaction
record has exactly those records. -/
theorem split_unique (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (gen0 : FirstHit.Recorded (Digest × T3.Cache)) (hg0 : gen0 ∈ support (FirstHit.record keygen (∅, ∅)))
    (int0 : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi0 : int0 ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign gen0.value.2)
      (adversary gen0.value.1 gen0.value.2)) gen0.state))
    (rest : List FirstHit.QueryEvent) (hev : result.events = gen0.events ++ (int0.events ++ rest))
    (generated : FirstHit.Recorded (Digest × T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool)
    (hsplit : Wots.GameSplit adversary result generated interaction checked) :
    generated = gen0 ∧ interaction = int0 := by
  obtain ⟨hg, hi, _, hres⟩ := hsplit
  have hev' : result.events = generated.events ++ (interaction.events ++ checked.events) := by rw [hres]
  have hgen : generated = gen0 :=
    record_prefix_unique keygen (∅, ∅) generated gen0 hg hg0 _ _ (hev'.symm.trans hev)
  subst hgen
  have hcut : interaction.events ++ checked.events = int0.events ++ rest :=
    List.append_cancel_left (hev'.symm.trans hev)
  exact ⟨rfl, record_prefix_unique _ _ interaction int0 hi hi0 _ _ hcut⟩

/-! ## The actual records of a bank sample -/

/-- The key generation record of the recorded key generation. -/
def genRecord (generated : (Digest × T3.Cache) × QueryRecorded.State) : FirstHit.Recorded (Digest × T3.Cache) :=
  ⟨generated.1, generated.2.events, lazyOf generated.2⟩

theorem genRecord_support (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    genRecord generated ∈ support (FirstHit.record keygen (∅, ∅)) := by
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := recorded_new_events keygen QueryRecorded.initial generated hg
  have : genRecord generated = rec := by
    cases rec
    simp only [genRecord] at *
    rw [← hstate, ← hvalue, hev]
    rfl
  rw [this]
  exact hrec

/-- **A bank sample carries the actual records.** -/
theorem bank_actual (adversary : AdversaryP) (budget : Nat) (b : Bool × BankState)
    (hb : b ∈ (bankExperiment adversary budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      ∃ int0 : FirstHit.Recorded (Option ForgeryP × QueryLog Requests),
        int0 ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2)
          (adversary generated.1.1 generated.1.2)) (lazyOf generated.2)) ∧
        (∃ rest, b.2.2.events = generated.2.events ++ (int0.events ++ rest)) ∧
        b.2.1.log = int0.value.2 ∧ BankInv generated.1.2 budget generated.2.events b.2 := by
  unfold bankExperiment at hb
  change b ∈ (PMF.bind _ _).support at hb
  rw [PMF.mem_support_bind_iff] at hb
  obtain ⟨generated, hg, hb⟩ := hb
  rw [MonitoredPrivate.pmf_support] at hg
  refine ⟨generated, hg, ?_⟩
  have hinv := bankInv_run generated.1.2 budget generated.2.events _ (Ghost.empty, generated.2)
    (bankInv_initial generated.1.2 budget generated hg) b hb
  unfold CreationGame.rest at hb
  rw [simulateQ_bind, StateT.run_bind] at hb
  change b ∈ (PMF.bind _ _).support at hb
  rw [PMF.mem_support_bind_iff] at hb
  obtain ⟨i, hi, hb⟩ := hb
  -- the interaction record
  have hproj := bank_project generated.1.2 budget (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))
    (Ghost.empty, generated.2)
  have hi' : (i.1, i.2.2) ∈ support (QueryRecorded.run (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2)
      (adversary generated.1.1 generated.1.2)) generated.2) := by
    have hm : Prod.map id Prod.snd i ∈ (Prod.map id Prod.snd <$>
        (simulateQ (bankImpl generated.1.2 budget) (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run
          (Ghost.empty, generated.2)).support := by
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff]
      exact ⟨i, hi, rfl⟩
    rw [hproj, MonitoredPrivate.pmf_support, MonitoredPrivate.logged_source] at hm
    exact hm
  obtain ⟨int0, hint0, hev0, hstate0, hvalue0⟩ := recorded_new_events _ generated.2 _ hi'
  -- the verdict part extends the events and leaves the log
  have hprojv := bank_project generated.1.2 budget
    (CreationGame.publicProgram (GameWith.verdict PaddedGame.checker generated.1.1 i.1)) i.2
  have hb' : (b.1, b.2.2) ∈ support (QueryRecorded.run (simulateQ (MonitoredPrivate.interactionSource generated.1.2)
      (CreationGame.publicProgram (GameWith.verdict PaddedGame.checker generated.1.1 i.1))) i.2.2) := by
    have hm : Prod.map id Prod.snd b ∈ (Prod.map id Prod.snd <$>
        (simulateQ (bankImpl generated.1.2 budget)
          (CreationGame.publicProgram (GameWith.verdict PaddedGame.checker generated.1.1 i.1))).run i.2).support := by
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff]
      exact ⟨b, hb, rfl⟩
    rw [hprojv, MonitoredPrivate.pmf_support] at hm
    exact hm
  obtain ⟨more, hmore⟩ := QueryRecorded.run_events_extend _ i.2.2 (b.1, b.2.2) hb'
  refine ⟨int0, hint0, ⟨more, ?_⟩, ?_, hinv⟩
  · rw [← hmore, hev0, List.append_assoc]
  · rw [public_ghost_log generated.1.2 budget _ i.2 b hb,
      logged_ghost_log generated.1.2 budget _ (Ghost.empty, generated.2) i hi, hvalue0]
    simp [Ghost.empty]

end SigGolfCandidate.T3.Security.CaseC
