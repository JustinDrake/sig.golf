import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCLinkInv
import SigGolfCandidate.ClaudeWCT.W9.New.G3a.PaddedWitness
import SigGolfCandidate.T3.Secc.CaseCLinkSplit
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Basic
import SigGolfCandidate.T3.Secc.CaseCFull

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SigGolfCandidate.T3M (wrho wdc)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def GameSplit (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool) :
    Prop :=
  generated ∈ support (FirstHit.record keygen (∅, ∅)) ∧
  interaction ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.value.2)
      (adversary generated.value.1 generated.value.2)) generated.state) ∧
  checked ∈ support (FirstHit.record (GameWith.verdict PaddedGame.checker generated.value.1 interaction.value)
      interaction.state) ∧
  result = ⟨checked.value, generated.events ++ (interaction.events ++ checked.events), checked.state⟩
theorem GameSplit.extends {adversary : AdversaryP} {result : FirstHit.Recorded Bool}
    {generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache)}
    {interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)} {checked : FirstHit.Recorded Bool}
    (h : GameSplit adversary result generated interaction checked) :
    SourceReplay.Extends interaction.state result.state := by
  obtain ⟨-, -, hc, rfl⟩ := h
  exact SourceReplay.run_extends _ interaction.state (checked.value, checked.state)
    (FirstHit.recorded_support _ _ _ hc)
def SignedDigest (log : QueryLog Requests) (message : Message) (witness : WBytes) : Prop :=
  ∃ entry ∈ log, entry.1.message = message ∧ ∃ signature, entry.2 = some signature ∧
    signature.rho = wrho witness
theorem traced_record_support (adversary : AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : PaddedGame.TraceResult)
    (hr : result ∈ (PaddedGame.tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.recordedTrace result ∈ support
      (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)) := by
  have hm : QueryRecorded.recordedTrace result ∈
      (QueryRecorded.recordedTrace <$> PaddedGame.tracedExperiment adversary budget hbudget).support := by
    rw [PMF.monad_map_eq_map, PMF.support_map]
    exact ⟨result, hr, rfl⟩
  rw [PaddedGame.traced_record_erasure, MonitoredPrivate.pmf_support] at hm
  exact hm
theorem logged_resolves {α : Type} (published : SigGolfCandidate.T3.Cache)
    (program : OracleComp LazyPrivate.Interaction α)
    (before : LazyPrivate.State) (result : (α × QueryLog Requests) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.loggedWith (FullGame.authenticatedSign published) program)
      before)) :
    ∀ entry ∈ result.1.2, SourceReplay.Resolves result.2 (FullGame.authenticatedSign published entry.1) entry.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      rw [FullGame.loggedWith_pure, LazyPrivate.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [FullGame.loggedWith_world, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, _, hr⟩ := hr
          exact ih middle.1 middle.2 result hr
      | inr request =>
          rw [FullGame.loggedWith_request, LazyPrivate.run_bind, mem_support_bind_iff] at hr
          obtain ⟨middle, hm, hr⟩ := hr
          rw [LazyPrivate.run_map, support_map] at hr
          obtain ⟨last, hl, rfl⟩ := hr
          intro entry he
          rcases List.mem_cons.mp he with he | he
          · subst entry
            exact (SourceReplay.resolves_of_run _ (CountedPrivate.authenticatedSign_hashOnly published request)
              before middle hm).mono (SourceReplay.run_extends _ middle.2 last hl)
          · exact ih middle.1 middle.2 last hl entry he
end ClaudeWCT.W9.T3.Security.CaseC
end

section


namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (countOf lazyOf genRecord genRecord_support record_prefix_unique
  recorded_new_events)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open ClaudeWCT.Bank (Ghost)
open ClaudeWCT.Bank.WCT (payAfterDigest)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9caseCLinkSplit : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
theorem bank_step_log (published : SigGolfCandidate.T3.Cache) (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (st : BankState) (r : LazyPrivate.Interaction.Range input × BankState)
    (hr : r ∈ ((bankImpl published budget input).run st).support) :
    r.2.1.log = st.1.log ++ ProposalOverflow.logFragment input r.1 := by
  cases input with
  | inl input =>
      obtain ⟨q, _, rfl⟩ := bankSpec.bank_support_world payAfterDigest published budget input st r hr
      obtain ⟨_, hL, _⟩ := ClaudeWCT.Bank.FtsBankSpec.ghostWorld_fields budget input st.1 st.2 q.1
      simp only [hL, ProposalOverflow.logFragment, List.append_nil]
  | inr request =>
      obtain ⟨q, _, rfl⟩ := bankSpec.bank_support_sign payAfterDigest published budget request st r hr
      rw [bankSpec.ghostSign_log]
      rfl
theorem logged_ghost_log {α : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat)
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
theorem public_ghost_log {β : Type} (published : SigGolfCandidate.T3.Cache) (budget : Nat) (program : M β)
    (st : BankState) (v : β × BankState)
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
      · simp only [CreationGame.publicHandler, pure_bind] at hv
        exact ih _ st hv
theorem split_unique (adversary : AdversaryP) (result : FirstHit.Recorded Bool)
    (gen0 : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (hg0 : gen0 ∈ support (FirstHit.record keygen (∅, ∅)))
    (int0 : FirstHit.Recorded (Option ForgeryP × QueryLog Requests))
    (hi0 : int0 ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign gen0.value.2)
      (adversary gen0.value.1 gen0.value.2)) gen0.state))
    (rest : List FirstHit.QueryEvent) (hev : result.events = gen0.events ++ (int0.events ++ rest))
    (generated : FirstHit.Recorded (Digest × SigGolfCandidate.T3.Cache))
    (interaction : FirstHit.Recorded (Option ForgeryP × QueryLog Requests)) (checked : FirstHit.Recorded Bool)
    (hsplit : GameSplit adversary result generated interaction checked) :
    generated = gen0 ∧ interaction = int0 := by
  obtain ⟨hg, hi, _, hres⟩ := hsplit
  have hev' : result.events = generated.events ++ (interaction.events ++ checked.events) := by rw [hres]
  have hgen : generated = gen0 :=
    record_prefix_unique keygen (∅, ∅) generated gen0 hg hg0 _ _ (hev'.symm.trans hev)
  subst hgen
  have hcut : interaction.events ++ checked.events = int0.events ++ rest :=
    List.append_cancel_left (hev'.symm.trans hev)
  exact ⟨rfl, record_prefix_unique _ _ interaction int0 hi hi0 _ _ hcut⟩
theorem bank_actual (adversary : AdversaryP) (budget : Nat) (b : Bool × BankState)
    (hb : b ∈ (bankExperiment adversary budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      ∃ int0 : FirstHit.Recorded (Option ForgeryP × QueryLog Requests),
        int0 ∈ support (FirstHit.record (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2)
          (adversary generated.1.1 generated.1.2)) (lazyOf generated.2)) ∧
        (∃ rest, b.2.2.events = generated.2.events ++ (int0.events ++ rest)) ∧
        b.2.1.log = int0.value.2 ∧ BankInv generated.1.2 budget generated.2.events b.2 := by
  rw [bankExperiment_eq] at hb
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
  have hproj := bank_project generated.1.2 budget (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))
    (Ghost.empty, generated.2)
  have hi' : (i.1, i.2.2) ∈ support (QueryRecorded.run (FullGame.loggedWith (FullGame.authenticatedSign generated.1.2)
      (adversary generated.1.1 generated.1.2)) generated.2) := by
    have hm : Prod.map id Prod.snd i ∈ (Prod.map id Prod.snd <$>
        (simulateQ (bankImpl generated.1.2 budget)
          (ProposalOverflow.logged (adversary generated.1.1 generated.1.2))).run (Ghost.empty, generated.2)).support := by
      rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff]
      exact ⟨i, hi, rfl⟩
    rw [hproj, MonitoredPrivate.pmf_support, MonitoredPrivate.logged_source] at hm
    exact hm
  obtain ⟨int0, hint0, hev0, hstate0, hvalue0⟩ := recorded_new_events _ generated.2 _ hi'
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
end ClaudeWCT.W9.T3.Security.CaseC
end

section



namespace ClaudeWCT.W9.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.CaseC (IsDigestInput countOf lazyOf genRecord genRecord_support Agrees)
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3M (WBytes)
open ClaudeWCT.W9.T3M.Final (AdversaryP ForgeryP)
open ClaudeWCT.Bank (Ghost)
open ClaudeWCT.Bank.WCT (payAfterDigest outIdx Covered)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_w9caseCFull : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def signedOutput (answers : Correctness.Answers) (message : Message) (signature : Signature) :
    Option HashOutput :=
  (evalWithAnswerFn answers (WCT9.digestSearch signature.rho message 0 WCT9.digestAttemptLimit)).map Prod.snd
def SlotDisclosed (answers : Correctness.Answers) (log : QueryLog Requests) (N : HashOutput) (k : WCT9.Coord)
    (t : Fin 7) : Prop :=
  ∃ entry ∈ log, ∃ signature output, entry.2 = some signature ∧
    signedOutput answers entry.1.message signature = some output ∧
    outIdx output = outIdx N ∧ WCT9.child output k = WCT9.child N k ∧
    WCT9.digit (WCT9.rank N k) t ≤ WCT9.digit (WCT9.rank output k) t
def FullQ (answers : Correctness.Answers) (log : QueryLog Requests) (message : Message) (witness : WBytes)
    (_events : List FirstHit.QueryEvent) : Prop :=
  ∀ k t, SlotDisclosed answers log (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) k t
structure CaseCExtraction where
  CaseCAt : Correctness.Answers → Message → WBytes → List FirstHit.QueryEvent → Prop
  digest_event : ∀ answers message witness events, CaseCAt answers message witness events →
    WCT9.admissible (evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))) = true ∧
    ∃ prior, (⟨prior, .inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))),
      evalWithAnswerFn answers (digest (wrho witness) message (wdc witness))⟩ : FirstHit.QueryEvent) ∈ events
  fresh_not_signer : ∀ (answers : Correctness.Answers) (published : SigGolfCandidate.T3.Cache)
    (log : QueryLog Requests) (state : LazyPrivate.State),
    (∀ entry ∈ log, SourceReplay.Resolves state (FullGame.authenticatedSign published entry.1) entry.2) →
    (∀ input answer, SourceReplay.known state input = some answer → answers input = answer) →
    ∀ message witness events, CaseCAt answers message witness events → ¬SignedDigest log message witness →
    ∀ entry ∈ log, (.inl (.inr (pad64 (digestInput (wrho witness) message (wdc witness)))) :
      SigGolfCandidate.T3.Spec.Domain) ∉
        SigGolfCandidate.T3M.SecurityExtraction.queried answers (FullGame.authenticatedSign published entry.1)
def PinnedC (X : CaseCExtraction) (adversary : AdversaryP)
    (Q : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop)
    (z : PaddedGame.TraceResult × Correctness.Answers) : Prop :=
  ∃ generated interaction checked, GameSplit adversary (QueryRecorded.recordedTrace z.1) generated interaction checked ∧
    generated.value.1 = ClaudeWCT.W9.T3M.Extract.honestRoot z.2 0 0 ∧ interaction.value.2.length ≤ 2 ^ 32 ∧
    ∃ forgery, interaction.value.1 = some forgery ∧ PaddedExtraction.Fresh interaction.value.2 forgery ∧
    ∃ message witness, PaddedExtraction.WitnessOf z.2 generated.value.1 forgery message witness ∧
      ¬SignedDigest interaction.value.2 message witness ∧
      X.CaseCAt z.2 message witness (QueryRecorded.recordedTrace z.1).events ∧
      Q z.2 interaction.value.2 message witness checked.events
theorem PinnedC.mono {X : CaseCExtraction} {adversary : AdversaryP}
    {Q Q' : Correctness.Answers → QueryLog Requests → Message → WBytes → List FirstHit.QueryEvent → Prop}
    (hQ : ∀ answers log message witness events, Q answers log message witness events →
      Q' answers log message witness events)
    {z : PaddedGame.TraceResult × Correctness.Answers} (h : PinnedC X adversary Q z) : PinnedC X adversary Q' z := by
  obtain ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC, hq⟩ := h
  exact ⟨g, i, c, hs, hpk, hlen, f, hf, hfr, m, w, hof, hsd, hC, hQ _ _ _ _ _ hq⟩
theorem bankSpec_search (rho : Digest) (m : Message) :
    bankSpec.search rho m 0 bankSpec.limit = WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit :=
  ClaudeWCT.Bank.WCT.wctL_search horizon ⊤ excessBound_top rho m
theorem full_potential (X : CaseCExtraction) (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127)
    (b : Bool × BankState) (hb : b ∈ (bankExperiment adversary q).support) (hist : MonitoredPrivate.History)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf b.2.2)) (hcount : countOf b.2.2 ≤ q)
    (hfull : PinnedC X adversary FullQ ((b.1, (hist, b.2.2)), A)) : 1 ≤ potential q b.2 := by
  obtain ⟨generated, hg, int0, hint0, ⟨rest, hrest⟩, hlog, hinv⟩ := bank_actual adversary q b hb
  have hinv' : bankSpec.BankInv payAfterDigest WCT9.Signature.rho generated.1.2 q generated.2.events b.2 := hinv
  obtain ⟨gen', int', chk', hsplit, -, hlen, forgery, -, -, m, w, -, hnsd, hCat, hQ⟩ := hfull
  have hR : QueryRecorded.recordedTrace (b.1, (hist, b.2.2)) = ⟨b.1, b.2.2.events, lazyOf b.2.2⟩ := rfl
  rw [hR] at hsplit hCat
  obtain ⟨hgen, hint⟩ := split_unique adversary _ (genRecord generated) (genRecord_support generated hg) int0
    hint0 rest hrest gen' int' chk' hsplit
  subst hgen hint
  have halive : b.2.1.dead = false := by
    cases hd : b.2.1.dead
    · rfl
    · exfalso
      have h1 := hinv'.dead hd
      rw [hlog] at h1
      have : bankSpec.horizon = 4294967296 := by rw [bankSpec_horizon, horizon_eq]
      omega
  obtain ⟨hadm, prior, hev⟩ := X.digest_event A m w _ hCat
  set N := evalWithAnswerFn A (digest (wrho w) m (wdc w)) with hN
  have hRsupp : (⟨b.1, b.2.2.events, lazyOf b.2.2⟩ : FirstHit.Recorded Bool) ∈
      support (FirstHit.record (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)) := by
    have hm : (b.1, b.2.2) ∈ ((fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$>
        PaddedGame.tracedExperiment adversary q hq).support := by
      rw [← bank_traced adversary q hq, PMF.monad_map_eq_map, PMF.mem_support_map_iff]
      exact ⟨b, hb, rfl⟩
    rw [PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hm
    obtain ⟨r, hr, hre⟩ := hm
    have := traced_record_support adversary q hq r hr
    have hrt : QueryRecorded.recordedTrace r = ⟨b.1, b.2.2.events, lazyOf b.2.2⟩ := by
      unfold QueryRecorded.recordedTrace QueryRecorded.recorded
      rw [hre]
      rfl
    rwa [hrt] at this
  obtain ⟨first, hfirst, hfresh⟩ := FirstHit.first_public_occurrence _ _ hRsupp prior _ N hev
  have hdig : IsDigestInput (pad64 (digestInput (wrho w) m (wdc w))) := ⟨wrho w, m, wdc w, rfl⟩
  have htarget : N ∈ b.2.1.targets := by
    rcases hinv'.events _ hfirst with hk | hp
    · exfalso
      have hkg := FirstHit.recorded_inputs keygen SourceReplay.keygen_hashOnly (∅, ∅) (genRecord generated)
        (genRecord_support generated hg) (SourceReplay.answers (genRecord generated).state)
        (fun input answer hk => SourceReplay.answers_known _ input answer hk)
      have hmem : (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : SigGolfCandidate.T3.Spec.Domain) ∈
          SourceReplay.queried (SourceReplay.answers (genRecord generated).state) keygen := by
        rw [← hkg]
        exact List.mem_map_of_mem hk
      have hnd := SigGolfCandidate.T3.Security.CaseC.queried_notDigest_keygen _ _ hmem
      exact hnd (BPB.hdrTag_digestInput (wrho w) m (wdc w))
    · rcases hp _ N rfl hdig hfresh with ht | hb' | hs
      · exact ht
      · exfalso
        change q < countOf b.2.2 at hb'
        omega
      · exfalso
        obtain ⟨entry, hentry, hq'⟩ := hs
        have hres := logged_resolves generated.1.2 (adversary generated.1.1 generated.1.2) (lazyOf generated.2)
          (int'.value, int'.state) (FirstHit.recorded_support _ _ _ hint0)
        have hext : SourceReplay.Extends int'.state (lazyOf b.2.2) := hsplit.extends
        have hagree : ∀ input answer, SourceReplay.known int'.state input = some answer → A input = answer :=
          (hA.mono hext)
        have hnot := X.fresh_not_signer A generated.1.2 int'.value.2 int'.state hres hagree m w _ hCat hnsd
        rw [hlog] at hentry
        have hqA := hq' A hA
        rw [source_eq] at hqA
        exact hnot entry hentry hqA
  have hcov : Covered b.2.1.exposures N := by
    intro k t
    obtain ⟨entry, hentry, σ, out, hσ, hout, h1, h2, h3⟩ := hQ k t
    rw [← hlog] at hentry
    unfold signedOutput at hout
    cases hs : evalWithAnswerFn A (WCT9.digestSearch σ.rho entry.1.message 0 WCT9.digestAttemptLimit) with
    | none => rw [hs] at hout; cases hout
    | some found =>
        rw [hs] at hout
        simp only [Option.map_some, Option.some.injEq] at hout
        rcases found with ⟨c', out'⟩
        simp only at hout
        subst hout
        have hs' : evalWithAnswerFn A (bankSpec.search (WCT9.Signature.rho σ) entry.1.message 0 bankSpec.limit) =
            some (c', out') := by
          rw [bankSpec_search]
          exact hs
        exact ⟨out', ClaudeWCT.Bank.FtsBankSpecL.BankInv.logged_exposed bankSpec payAfterDigest WCT9.Signature.rho
          hinv' halive entry hentry σ hσ A hA c' out' hs', h1, h2, h3⟩
  exact bankSpec.potential_win q b.2 halive hcount (Or.inr ⟨N, htarget, hadm, hcov⟩)
end ClaudeWCT.W9.T3.Security.CaseC
end
