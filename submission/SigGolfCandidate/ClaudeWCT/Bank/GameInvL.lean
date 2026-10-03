import SigGolfCandidate.ClaudeWCT.Bank.GameBankL
import SigGolfCandidate.ClaudeWCT.Bank.GameInv

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction (queried)
open CaseC (Agrees Birth FreshSigning countOf lazyOf IsDigestInput eventPublic nonceOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankInvL : DecidableEq T3.Cache := Classical.decEq _
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (sigRho : Sig → Digest)
theorem eval_recordForNonce_selected (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message) :
    (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).2 =
      (evalWithAnswerFn A (S.search rho m 0 S.limit)).map Prod.snd := by
  unfold recordForNonce
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn A (S.search rho m 0 S.limit) with
  | none => simp
  | some found =>
      rcases found with ⟨c, out⟩
      simp
theorem eval_recordForNonce_rho (hrho : PayRho pay sigRho) (A : Correctness.Answers) (cache : T3.Cache)
    (rho : Digest) (m : Message) (σ : Sig) (h : (evalWithAnswerFn A (S.recordForNonce pay cache rho m)).1 = some σ) :
    sigRho σ = rho := by
  unfold recordForNonce at h
  simp only [evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn A (S.search rho m 0 S.limit) with
  | none => simp [hd] at h
  | some found =>
      rcases found with ⟨c, out⟩
      simp only [hd, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      exact hrho A cache rho out σ h
theorem eval_authenticatedRecord (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.authenticatedRecord pay published request) =
      if request.cache = published then
        evalWithAnswerFn A (S.recordForNonce pay published (evalWithAnswerFn A (privateNonce request.message))
          request.message)
      else (none, none) := by
  unfold authenticatedRecord
  simp only [evalWithAnswerFn_bind]
  by_cases hc : request.cache = published
  · rw [if_pos hc, if_pos hc]
    unfold payloadRecord
    rw [evalWithAnswerFn_bind, hc]
  · rw [if_neg hc, if_neg hc]
    rfl
theorem eval_source_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (S.source pay published (.inr request)) =
      (evalWithAnswerFn A (S.authenticatedRecord pay published request)).1 := by
  change evalWithAnswerFn A (Prod.fst <$> S.authenticatedRecord pay published request) = _
  rw [SigGolfCandidate.T3M.eval_map]
theorem queried_record_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    SourceReplay.queried A (S.authenticatedRecord pay published request) =
      queried A (S.source pay published (.inr request)) := by
  change _ = queried A (Prod.fst <$> S.authenticatedRecord pay published request)
  rw [SigGolfCandidate.T3M.Extract.queried_map]
  rfl
theorem authenticatedRecord_hashOnly (hhash : PayHashOnly pay) (published : T3.Cache) (request : Request) :
    Security.SourceReplay.HashOnly (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · exact SourceQueries.privateMac_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · exact SourceQueries.privateNonce_allowed Security.SourceReplay.IsHash (fun _ => trivial) _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun _ _ => trivial) S.limit 0 (by simpa using S.limit_le))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · exact SourceQueries.bind_allowed _ (hhash _ _ _) fun _ => SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
def SignerQueried (published : T3.Cache) (log : QueryLog (Requests' Sig)) (lazy : LazyPrivate.State)
    (x : HashInput) : Prop :=
  ∃ entry ∈ log, ∀ A, Agrees A lazy →
    (.inl (.inr x) : T3.Spec.Domain) ∈ queried A (S.source pay published (.inr entry.1))
structure BankInv (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent) (st : BankState Sig) :
    Prop where
  len : st.1.exposures.length ≤ st.1.log.length
  dead : st.1.dead = true → S.horizon < st.1.log.length
  events : ∀ e ∈ st.2.events, e ∈ kg ∨ ∀ x a, eventPublic e = some (x, a) → IsDigestInput x →
    e.before.2 x = none → a ∈ st.1.targets ∨ budget < countOf st.2 ∨ S.SignerQueried pay published st.1.log (lazyOf st.2) x
  exposed : st.1.dead = false → ∀ m, (lazyOf st.2).1 (.inr (.inl m)) ≠ none → ∀ A, Agrees A (lazyOf st.2) →
    ∀ c out, evalWithAnswerFn A (S.search (nonceOf (lazyOf st.2) m) m 0 S.limit) = some (c, out) →
      out ∈ st.1.exposures
  logged : ∀ entry ∈ st.1.log, ∀ σ, entry.2 = some σ → entry.1.cache = published ∧
    (lazyOf st.2).1 (.inr (.inl entry.1.message)) ≠ none ∧ sigRho σ = nonceOf (lazyOf st.2) entry.1.message
theorem bank_support_world (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (forwardWorld input) st.2),
      r = (q.1, (ghostWorld budget input st.1 st.2 q.1, q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (forwardWorld input) st.2))).support at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bank_support_sign (published : T3.Cache) (budget : Nat) (request : Request)
    (st : BankState Sig) (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (S.authenticatedRecord pay published request) st.2),
      r = (q.1.1, (S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2), q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2))).support
    at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bankInv_world (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : SphincsSecurity.OracleWorld.Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : SphincsSecurity.OracleWorld.Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inl input)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_world pay published budget input st r hr
  obtain ⟨hev, hcount, hlazy⟩ := CaseC.world_query_support input st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hpriv : (lazyOf q.2).1 = (lazyOf st.2).1 :=
    CaseC.world_private_eq input (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  obtain ⟨hX, hL, hD, hR, hT⟩ := FtsBankSpec.ghostWorld_fields budget input st.1 st.2 q.1
  have hcle : countOf st.2 ≤ countOf q.2 := by rw [hcount]; exact Nat.le_add_right _ _
  constructor
  · simp only [hX, hL]; exact hinv.len
  · simp only [hD, hL]; exact hinv.dead
  · intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · exact Or.inl (hT _ ht)
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hL]; exact hentry, fun A hA => hq' A (hA.mono hext)⟩
    · rw [List.mem_singleton] at he
      subst he
      right
      intro x a hxa hdig hfresh
      cases input with
      | inl n => simp [eventPublic] at hxa
      | inr y =>
          simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          obtain ⟨hy, ha⟩ := hxa
          subst hy
          by_cases hlt : countOf st.2 < budget
          · left
            have hbirth : Birth budget y st.2 := ⟨hdig, hfresh, hlt⟩
            simp only [ghostWorld, hbirth, if_true]
            rw [← ha]
            exact List.mem_append_right _ (List.mem_singleton_self _)
          · right; left
            rw [hcount]
            change budget < countOf st.2 + 1
            omega
  · intro hdead m hm A hA c out hs
    rw [hD] at hdead
    have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hpriv]
    have hn : nonceOf (lazyOf q.2) m = nonceOf (lazyOf st.2) m := by simp [nonceOf, hpriv]
    rw [hn] at hs
    rw [hX]
    exact hinv.exposed hdead m hm0 A (hA.mono hext) c out hs
  · intro entry he σ hσ
    rw [hL] at he
    obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
    refine ⟨h1, by rwa [hpriv], ?_⟩
    rw [h3]
    simp [nonceOf, hpriv]
theorem bankInv_sign (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (request : Request) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : Option Sig × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget (.inr request)).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := S.bank_support_sign pay published budget request st r hr
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := CaseC.recorded_new_events _ st.2 q hq
  have hlazy := CaseC.recorded_lazy_support _ st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hres : SourceReplay.Resolves (lazyOf q.2) (S.authenticatedRecord pay published request) q.1 :=
    SourceReplay.resolves_of_run _ (S.authenticatedRecord_hashOnly pay hhash published request) _ _ hlazy
  have hcle := CaseC.recorded_count_le _ st.2 q hq
  have hlog := S.ghostSign_log published request st.1 st.2 (q.1, lazyOf q.2)
  have htar := S.ghostSign_targets published request st.1 st.2 (q.1, lazyOf q.2)
  have h1 := S.ghostSign_exposures_len published request st.1 st.2 (q.1, lazyOf q.2)
  set g' := S.ghostSign published request st.1 st.2 (q.1, lazyOf q.2) with hg'
  show S.BankInv pay sigRho published budget kg (g', q.2)
  constructor
  ·
    show g'.exposures.length ≤ g'.log.length
    rw [hlog, List.length_append, List.length_singleton]
    have := hinv.len
    omega
  ·
    intro hd
    rw [hlog, List.length_append, List.length_singleton]
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · have := hinv.len
        omega
      · have hd0 : st.1.dead = true := by
          simpa [hg', FtsBankSpec.ghostSign, hf, hh] using hd
        have := hinv.dead hd0
        omega
    · have hd0 : st.1.dead = true := by
        simpa [hg', FtsBankSpec.ghostSign, hf] using hd
      have := hinv.dead hd0
      omega
  ·
    intro e he
    rw [hev, List.mem_append] at he
    rcases he with he | he
    · rcases hinv.events e he with hk | hp
      · exact Or.inl hk
      · right
        intro x a hxa hdig hfresh
        rcases hp x a hxa hdig hfresh with ht | hb | hs
        · left; rw [htar]; exact ht
        · exact Or.inr (Or.inl (lt_of_lt_of_le hb hcle))
        · right; right
          obtain ⟨entry, hentry, hq'⟩ := hs
          exact ⟨entry, by rw [hlog]; exact List.mem_append_left _ hentry, fun A hA => hq' A (hA.mono hext)⟩
    · right
      intro x a hxa _ _
      right; right
      refine ⟨⟨request, q.1.1⟩, by rw [hlog]; exact List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      intro A hA
      have hinputs := FirstHit.recorded_inputs _ (S.authenticatedRecord_hashOnly pay hhash published request)
        (lazyOf st.2) rec hrec A (by rw [hstate]; exact hA)
      have hmem : e.input ∈ rec.events.map FirstHit.QueryEvent.input := List.mem_map_of_mem he
      rw [hinputs, S.queried_record_sign pay] at hmem
      have hin : e.input = .inl (.inr x) := by
        rcases e with ⟨before, input, answer⟩
        rcases input with (n | y) | coordinate
        · simp [eventPublic] at hxa
        · simp only [eventPublic, Option.some.injEq, Prod.mk.injEq] at hxa
          rw [hxa.1]
        · simp [eventPublic] at hxa
      rw [hin] at hmem
      exact hmem
  ·
    intro hdead m hm A hA c out hs
    by_cases hf : FreshSigning published request st.2
    · by_cases hh : S.horizon ≤ st.1.exposures.length
      · simp [hg', FtsBankSpec.ghostSign, hf, hh] at hdead
      · have hdead0 : st.1.dead = false := by simpa [hg', FtsBankSpec.ghostSign, hf, hh] using hdead
        have hX : g'.exposures = st.1.exposures ++ q.1.2.toList := by simp [hg', FtsBankSpec.ghostSign, hf, hh]
        rw [hX]
        by_cases hmm : m = request.message
        · subst hmm
          obtain ⟨hcache, hnonce⟩ := hf
          have heval := hres.eval A hA
          rw [S.eval_authenticatedRecord pay, if_pos hcache,
            CaseC.eval_privateNonce A (lazyOf q.2) hA request.message hm] at heval
          have hsel := S.eval_recordForNonce_selected pay A published (nonceOf (lazyOf q.2) request.message)
            request.message
          rw [heval, hs] at hsel
          apply List.mem_append_right
          rw [hsel]
          simp
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hn]
          obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
          rw [hno] at hs
          exact List.mem_append_left _ (hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs)
    · have hdead0 : st.1.dead = false := by simpa [hg', FtsBankSpec.ghostSign, hf] using hdead
      have hX : g'.exposures = st.1.exposures := by simp [hg', FtsBankSpec.ghostSign, hf]
      rw [hX]
      have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by
        by_cases hmm : m = request.message
        · subst hmm
          by_cases hc : request.cache = published
          · intro hnone
            exact hf ⟨hc, hnone⟩
          · have := (S.sign_unpublished pay published request hc (lazyOf st.2) (q.1, lazyOf q.2) hlazy).1
            rwa [← this]
        · have hn := S.sign_other_nonce pay hAvoids published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          rwa [← hn]
      obtain ⟨hno, _⟩ := CaseC.nonceOf_extends hext m hm0
      rw [hno] at hs
      exact hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs
  ·
    intro entry he σ hσ
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
      obtain ⟨hno, hc'⟩ := CaseC.nonceOf_extends hext entry.1.message h2
      exact ⟨h1, hc', by rw [hno]; exact h3⟩
    · rw [List.mem_singleton] at he
      subst he
      change q.1.1 = some σ at hσ
      have hA : Agrees (SourceReplay.answers (lazyOf q.2)) (lazyOf q.2) :=
        fun input answer hk => SourceReplay.answers_known _ input answer hk
      have heval := hres.eval _ hA
      rw [S.eval_authenticatedRecord pay] at heval
      by_cases hc : request.cache = published
      · rw [if_pos hc] at heval
        have hreq : request = ⟨request.message, published⟩ := by cases request; simp_all
        have hcached : (lazyOf q.2).1 (.inr (.inl request.message)) ≠ none := by
          have := S.sign_published_nonce pay published request.message (lazyOf st.2) (q.1, lazyOf q.2)
            (by rw [← hreq]; exact hlazy)
          exact this
        refine ⟨hc, hcached, ?_⟩
        have hsig : (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (S.recordForNonce pay published
            (evalWithAnswerFn (SourceReplay.answers (lazyOf q.2)) (privateNonce request.message))
            request.message)).1 = some σ := by rw [heval]; exact hσ
        have hrho' := S.eval_recordForNonce_rho pay sigRho hrho _ published _ request.message σ hsig
        rw [hrho', CaseC.eval_privateNonce _ (lazyOf q.2) hA request.message hcached]
      · rw [if_neg hc] at heval
        rw [← heval] at hσ
        cases hσ
theorem bankInv_step (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : (Interaction' Sig).Domain) (st : BankState Sig) (hinv : S.BankInv pay sigRho published budget kg st)
    (r : (Interaction' Sig).Range input × BankState Sig)
    (hr : r ∈ ((S.bankImpl pay published budget input).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  cases input with
  | inl input => exact S.bankInv_world pay sigRho published budget kg input st hinv r hr
  | inr request => exact S.bankInv_sign pay sigRho hhash hrho hAvoids published budget kg request st hinv r hr
theorem bankInv_run {α : Type} (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig)
    (hinv : S.BankInv pay sigRho published budget kg st)
    (r : α × BankState Sig) (hr : r ∈ ((simulateQ (S.bankImpl pay published budget) program).run st).support) :
    S.BankInv pay sigRho published budget kg r.2 := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure] at hr
      change r ∈ (PMF.pure (value, st)).support at hr
      rw [PMF.support_pure, Set.mem_singleton_iff] at hr
      subst hr
      exact hinv
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hr
      change r ∈ (PMF.bind _ _).support at hr
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2
        (S.bankInv_step pay sigRho hhash hrho hAvoids published budget kg input st hinv middle hm) hr
theorem bankInv_initial (published : T3.Cache) (budget : Nat)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.BankInv pay sigRho published budget generated.2.events ((Ghost.empty : Ghost Sig), generated.2) := by
  have hl := CaseC.recorded_lazy_support keygen QueryRecorded.initial generated hg
  constructor
  · simp [Ghost.empty]
  · simp [Ghost.empty]
  · intro e he
    exact Or.inl he
  · intro _ m hm
    exfalso
    apply hm
    exact NonceFreshness.keygen_nonce_fresh m (generated.1, lazyOf generated.2) hl
  · intro entry he
    simp [Ghost.empty] at he
theorem bankInv_experiment (hhash : PayHashOnly pay) (hrho : PayRho pay sigRho) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (b : Bool × BankState Sig)
    (hb : b ∈ (S.bankExperiment pay rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      S.BankInv pay sigRho generated.1.2 budget generated.2.events b.2 := by
  unfold bankExperiment at hb
  change b ∈ (PMF.bind _ _).support at hb
  rw [PMF.mem_support_bind_iff] at hb
  obtain ⟨generated, hg, hb⟩ := hb
  rw [MonitoredPrivate.pmf_support] at hg
  exact ⟨generated, hg, S.bankInv_run pay sigRho hhash hrho hAvoids generated.1.2 budget generated.2.events _
    (Ghost.empty, generated.2) (S.bankInv_initial pay sigRho generated.1.2 budget generated hg) b hb⟩
theorem BankInv.alive {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent} {st : BankState Sig}
    (hinv : S.BankInv pay sigRho published budget kg st) (hlog : st.1.log.length ≤ S.horizon) :
    st.1.dead = false := by
  cases hd : st.1.dead
  · rfl
  · have := hinv.dead hd
    omega
theorem BankInv.logged_exposed {published : T3.Cache} {budget : Nat} {kg : List FirstHit.QueryEvent}
    {st : BankState Sig} (hinv : S.BankInv pay sigRho published budget kg st) (halive : st.1.dead = false)
    (entry : (_ : Request) × Option Sig) (he : entry ∈ st.1.log) (σ : Sig) (hσ : entry.2 = some σ)
    (A : Correctness.Answers) (hA : Agrees A (lazyOf st.2)) (c : BitVec 32) (out : HashOutput)
    (hs : evalWithAnswerFn A (S.search (sigRho σ) entry.1.message 0 S.limit) = some (c, out)) :
    out ∈ st.1.exposures := by
  obtain ⟨-, hcached, hrho⟩ := hinv.logged entry he σ hσ
  rw [hrho] at hs
  exact hinv.exposed halive entry.1.message hcached A hA c out hs
end FtsBankSpecL
end ClaudeWCT.Bank
