import SigGolfCandidate.ClaudeWCT.Bank.GameBankL
import SigGolfCandidate.ClaudeWCT.Bank.GameInv
import SigGolfCandidate.ClaudeWCT.Bank.Kernel
import SigGolfCandidate.ClaudeWCT.Bank.WCTSpec
import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.ClaudeWCT.Bank.GameBank
import SigGolfCandidate.ClaudeWCT.Bank.WCTAccept
import SigGolfCandidate.ClaudeWCT.WCT9.Limits

section


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
end

section



namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (Coord Child Rank child rank digit Opening wctHeader buildChild buildCoordinate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem wct_digestSearch_public {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.admissible = WCT9.admissible) (rho : Digest) (message : Message) :
    ∀ fuel counter, WCT9.digestSearch rho message counter fuel = S.search rho message counter fuel := by
  intro fuel
  induction fuel with
  | zero => intro counter; rfl
  | succ fuel ih =>
      intro counter
      rw [WCT9.digestSearch, FtsBankSpec.search, searchLoop]
      simp only [Sampling.publicProgram, simulateQ_bind, simulateQ_spec_query,
        SphincsSecurity.Concrete.oracleHash, HasQuery.query, Sampling.publicHandler,
        digest, publicHash, Sampling.digestTrial, FtsBankSpec.decode, hadm]
      apply bind_congr
      intro answer
      split <;> simp only [simulateQ_pure, map_pure, ih, FtsBankSpec.search, Sampling.publicProgram]
def payAfterDigest (cache : T3.Cache) (rho : Digest) (output : HashOutput) : M (Option WCT9.Signature) := do
  let index := output.toNat % 2 ^ 31
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List Digest) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening], state.2 ++ [(levels.getD 7 []).getD 0 0])) ([], [])
  let root ← WCT9.forestPk index state.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
theorem signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 attemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayload
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem payloadRecord_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P)
    (hadm : S.admissible = WCT9.admissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayload cache message := by
  rw [signPayload_factor]
  unfold FtsBankSpec.payloadRecord FtsBankSpec.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
section avoids
variable (m : Message)
theorem avoids_chain (index coord selected i start count : Nat) (value : Digest) :
    NonceFreshness.Avoids m (WCT9.chain index coord selected i start count value) := by
  unfold WCT9.chain
  exact NonceFreshness.avoids_foldlM m _ _ (fun _ _ => NonceFreshness.avoids_shortHash m _) _
theorem avoids_leafHash (index coord selected : Nat) (ends : List Digest) :
    NonceFreshness.Avoids m (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_forestPk (index : Nat) (roots : List Digest) : NonceFreshness.Avoids m (WCT9.forestPk index roots) := by
  unfold WCT9.forestPk
  exact NonceFreshness.avoids_shortHash m _
theorem avoids_buildChild (index coord selected : Nat) (word : Rank) :
    NonceFreshness.Avoids m (buildChild index coord selected word) := by
  unfold buildChild
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state pair
    apply NonceFreshness.avoids_bind m (NonceFreshness.avoids_privatePair m _ _ _ _ _)
    intro seeds
    apply NonceFreshness.avoids_foldlM m
    intro state half
    split
    · apply NonceFreshness.avoids_bind m (avoids_chain m _ _ _ _ _ _ _)
      intro value
      apply NonceFreshness.avoids_bind m (avoids_chain m _ _ _ _ _ _ _)
      intro _
      exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
  · intro state
    exact NonceFreshness.avoids_bind m (avoids_leafHash m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
theorem avoids_buildCoordinate (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    NonceFreshness.Avoids m (buildCoordinate index coord selected word) := by
  unfold buildCoordinate
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state j
    exact NonceFreshness.avoids_bind m (avoids_buildChild m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m
    · apply NonceFreshness.avoids_foldlM m
      intro nodes heap
      exact NonceFreshness.avoids_bind m (NonceFreshness.avoids_nodeHash m _ _ _ _ _ _)
        fun _ => NonceFreshness.avoids_pure m _
    · intro _
      exact NonceFreshness.avoids_pure m _
end avoids
theorem wct_payAvoids : PayAvoids payAfterDigest := by
  intro m cache rho output
  unfold payAfterDigest
  apply NonceFreshness.avoids_bind m
  · apply NonceFreshness.avoids_foldlM m
    intro state coord
    exact NonceFreshness.avoids_bind m (avoids_buildCoordinate m _ _ _ _) fun _ => NonceFreshness.avoids_pure m _
  · intro state
    apply NonceFreshness.avoids_bind m (avoids_forestPk m _ _)
    intro root
    apply NonceFreshness.avoids_bind m (NonceFreshness.avoids_signLayers m _ _ _ _)
    intro layers
    split
    · exact NonceFreshness.avoids_pure m _
    · exact NonceFreshness.avoids_pure m _
theorem wctHeader_value_lt (tag lay tree position index : Nat) :
    1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
      position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 < 2 ^ 128 := by
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat =
      1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
        position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96 := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wctHeader_value_lt _ _ _ _ _)]
theorem wctHeader_byte1 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0).toNat = tag % 256 := by
  have h : (bytesLE 16 (wctHeader tag lay tree position index)).getD 1 0 =
      ⟨(wctHeader tag lay tree position index).extractLsb' 8 8⟩ := rfl
  rw [h]
  show ((wctHeader tag lay tree position index).extractLsb' 8 8).toNat = tag % 256
  rw [BitVec.extractLsb'_toNat, wctHeader_toNat, Nat.shiftRight_eq_div_pow]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a at *
  generalize lay % 256 = b at *
  generalize tree / 2 ^ 32 % 256 = c at *
  generalize position % 2 ^ 32 = d at *
  generalize tree % 2 ^ 32 = e at *
  generalize index % 2 ^ 32 = f at *
  norm_num at h4 h5 h6 ⊢
  omega
theorem wctHeader_byte0 (tag lay tree position index : Nat) :
    ((bytesLE 16 (wctHeader tag lay tree position index)).getD 0 0).toNat = 1 := by
  rw [bytesLE16_first_toNat, wctHeader_toNat]
  omega
theorem hdrBlock_pad64_prefix (a h rest : HashInput) (ha : a.length = 16) (hh : h.length = 16) :
    T3M.Extract.hdrBlock (pad64 (a ++ h ++ rest)) = h := by
  rw [T3M.Extract.hdrBlock_pad64 _ (by simp [ha, hh]; omega)]
  unfold T3M.Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hh]
theorem shortHash_wct_ok (a rest : HashInput) (tag lay tree position index : Nat) (ha : a.length = 16)
    (ht : tag % 256 ≠ 12) :
    AllQueriesSatisfy (shortHash (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) BPB.NotDigestQ := by
  unfold shortHash publicHash
  apply SourceQueries.bind_allowed
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    show BPB.hdrTag (pad64 (a ++ bytesLE 16 (wctHeader tag lay tree position index) ++ rest)) ≠ 12
    unfold BPB.hdrTag
    rw [hdrBlock_pad64_prefix _ _ _ ha (bytesLE_length _ _), wctHeader_byte0, if_neg (by decide),
      wctHeader_byte1]
    exact ht
  · intro _; exact SourceQueries.pure_allowed _ _
theorem chain_ok (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) BPB.NotDigestQ := by
  unfold WCT9.chain
  refine SourceQueries.foldlM_allowed BPB.NotDigestQ _ _ (fun v step => ?_) _
  unfold WCT9.chainInput
  rw [List.append_assoc (zero16 ++ _)]
  exact shortHash_wct_ok zero16 _ 5 _ _ _ _ (by simp [zero16]) (by decide)
theorem leafHash_ok (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) BPB.NotDigestQ := by
  unfold WCT9.leafHash
  exact shortHash_wct_ok _ _ 6 _ _ _ _ (bytesLE_length _ _) (by decide)
theorem forest_header_plain (index : Nat) : header 15 0 index 0 0 = wctHeader 15 0 index 0 0 := by
  unfold wctHeader header
  rw [if_neg (by decide)]
  simp only [Nat.add_assoc]
theorem forestPk_ok (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (WCT9.forestPk index roots) BPB.NotDigestQ := by
  unfold WCT9.forestPk
  rw [forest_header_plain]
  exact shortHash_wct_ok _ _ 15 _ _ _ _ (bytesLE_length _ _) (by decide)
theorem buildChild_ok (index coord selected : Nat) (word : Rank) :
    AllQueriesSatisfy (buildChild index coord selected word) BPB.NotDigestQ := by
  unfold buildChild
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state pair
    apply SourceQueries.bind_allowed _ (BPB.privatePair_ok _ _ _ _ _)
    intro seeds
    apply SourceQueries.foldlM_allowed
    intro state half
    split
    · apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
      intro value
      apply SourceQueries.bind_allowed _ (chain_ok _ _ _ _ _ _ _)
      intro _
      exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
  · intro state
    exact SourceQueries.bind_allowed _ (leafHash_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
theorem buildCoordinate_ok (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) BPB.NotDigestQ := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChild_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · apply SourceQueries.foldlM_allowed
      intro nodes heap
      exact SourceQueries.bind_allowed _ (BPB.nodeHash_ok 11 _ _ _ _ _ (by decide))
        fun _ => SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
theorem wct_payNotDigest : PayNotDigest payAfterDigest := by
  intro cache rho output
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinate_ok _ _ _ _) fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed _ (forestPk_ok _ _)
    intro root
    apply SourceQueries.bind_allowed _ (BPB.signLayers_ok _ _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end ClaudeWCT.Bank.WCT
end

section

namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_exists_admissible : ∃ x, digestAdmissible x = true := by
  obtain ⟨x, hx⟩ := CaseC.admissibleSet_nonempty
  exact ⟨x, (Finset.mem_filter.mp hx).2⟩
theorem bpors_acceptance_eq :
    Pr[fun x : HashOutput => digestAdmissible x = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput) CaseC.admInd := by
  unfold CaseC.admInd
  rw [expectedValue_ite_one]
theorem bpors_one_le_score (X : List HashOutput) (N : HashOutput) (hadm : digestAdmissible N = true)
    (hcov : ∀ c, CaseC.CoordCovered X N c) : 1 ≤ CaseC.score X N := by
  unfold digestAdmissible at hadm
  rw [Bool.and_eq_true] at hadm
  exact CaseC.one_le_score X N (CaseC.outLeaves_injective N hadm.1) hadm.2 hcov
noncomputable def bporsSpec : FtsBankSpec BPORS.History.Proposal where
  admissible := digestAdmissible
  exists_admissible := bpors_exists_admissible
  acceptance_le := bpors_acceptance_eq ▸ CaseC.expected_admInd_tight
  proposal := CaseC.label
  accepted_proposal g := by
    rw [Sampling.digest_acceptanceProbability]
    exact accepted_samplingData g
  score := CaseC.score
  covered X N := ∀ c, CaseC.CoordCovered X N c
  one_le_score := bpors_one_le_score
  score_append_mono := CaseC.score_append_mono
  price := BPORS.History.fullPrice
  average_score := CaseC.average_score
  horizon := BPORS.Numeric.proposalLength
  excessRate := 11324 / 100000000
  excess_le := CaseC.excess_three_quarters
theorem bpors_decode : bporsSpec.decode = Sampling.digestDecode := rfl
theorem bpors_acceptance : bporsSpec.acceptance = acceptanceProbability := Sampling.digest_acceptanceProbability
theorem bpors_freshPrice (w : HashOutput → ENNReal) :
    bporsSpec.freshPrice w = Sampling.WeightedSelection.freshPrice w := by
  unfold FtsBankSpec.freshPrice Sampling.WeightedSelection.freshPrice
  rw [bpors_acceptance]
  rfl
theorem bpors_search (rho : Digest) (m : Message) (counter fuel : Nat) :
    bporsSpec.search rho m counter fuel = digestSearch rho m counter fuel :=
  (Sampling.digestSearch_public rho m fuel counter).symm
theorem bpors_admissibleSet : bporsSpec.admissibleSet = CaseC.admissibleSet := by
  ext x
  simp [FtsBankSpec.admissibleSet, CaseC.admissibleSet, bporsSpec]
theorem bpors_accepted : bporsSpec.accepted = CaseC.accepted := by
  unfold FtsBankSpec.accepted CaseC.accepted
  congr 1
theorem bpors_forecast : bporsSpec.forecast = CaseC.forecast := by
  funext R X N
  unfold FtsBankSpec.forecast CaseC.forecast
  rw [bpors_accepted]
  rfl
theorem bpors_excessForecast : bporsSpec.excessForecast = CaseC.excessForecast := rfl
theorem bpors_ledger : bporsSpec.ledger = CaseC.ledger := by
  funext R targets X slack
  unfold FtsBankSpec.ledger CaseC.ledger
  rw [bpors_forecast, bpors_excessForecast]
theorem bpors_corePotential : bporsSpec.corePotential = CaseC.corePotential := by
  funext b
  unfold FtsBankSpec.corePotential CaseC.corePotential
  rw [bpors_ledger]
  rfl
theorem bpors_Reuse : bporsSpec.Reuse = CaseC.Reuse := rfl
theorem bpors_admissibleEntry : bporsSpec.admissibleEntry = CaseC.admissibleEntry := by
  funext cache input
  unfold FtsBankSpec.admissibleEntry CaseC.admissibleEntry
  cases cache input <;> simp [bporsSpec]
theorem bpors_reuseMass : bporsSpec.reuseMass = CaseC.reuseMass := by
  funext cache m
  unfold FtsBankSpec.reuseMass CaseC.reuseMass
  rw [bpors_admissibleEntry]
theorem bpors_admInd : bporsSpec.admInd = CaseC.admInd := by
  funext a
  simp [FtsBankSpec.admInd, CaseC.admInd, bporsSpec]
theorem bpors_recordForNonce (cache : T3.Cache) (rho : Digest) (m : Message) :
    bporsSpec.recordForNonce payloadAfterDigest cache rho m = payloadRecordForNonce cache rho m := by
  unfold FtsBankSpec.recordForNonce payloadRecordForNonce
  rw [bpors_search]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem bpors_record (published : T3.Cache) (request : Request) :
    bporsSpec.authenticatedRecord payloadAfterDigest published request =
      FullGame.authenticatedRecord published request := by
  unfold FtsBankSpec.authenticatedRecord FullGame.authenticatedRecord
  apply bind_congr
  intro tag
  by_cases h : request.cache = published
  · simp only [h, if_true]
    unfold FtsBankSpec.payloadRecord payloadRecord
    apply bind_congr
    intro rho
    exact bpors_recordForNonce _ rho _
  · simp only [h, if_false]
theorem t3_core_sign (b : CaseC.BankCore) (cache : Sampling.RCache) (m : Message) (C' : ENNReal)
    (hC : C' + CaseC.reuseMass cache m ≤ b.reuse) (secret : BitVec 256) (fuel : Nat) (hfuel : fuel ≤ 2 ^ 32) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
      if CaseC.Reuse cache rho m then CaseC.corePotential { b with reused := true, reuse := C' }
      else expectedValue (Sampling.roRun secret (digestSearch rho m 0 fuel) cache)
        (fun result => CaseC.corePotential (b.expose C' (result.1.map Prod.snd)))) ≤ CaseC.corePotential b := by
  have h := bporsSpec.core_sign b cache m C' (by rw [bpors_reuseMass]; exact hC) secret fuel hfuel
  simp only [bpors_corePotential, bpors_Reuse, bpors_search] at h
  exact h
theorem t3_core_birth (b : CaseC.BankCore) (s : Nat) (hs : b.slack = s + 1) (C' : HashOutput → ENNReal)
    (hC : ∀ N, C' N ≤ b.reuse + CaseC.admInd N / 2 ^ 128) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun N => CaseC.corePotential { b with targets := b.targets ++ [N], slack := s, reuse := C' N }) ≤
      CaseC.corePotential b + (CaseC.theta + 1 / 64) / 2 ^ 128 := by
  have h := bporsSpec.core_birth b s hs C' (by rw [bpors_admInd]; exact hC)
  simp only [bpors_corePotential] at h
  exact h
theorem t3_core_initial (budget : Nat) :
    CaseC.corePotential ⟨[], [], false, 0, budget⟩ ≤ (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  have h := bporsSpec.core_initial budget
  rw [bpors_corePotential] at h
  exact h
theorem t3_core_win (b : CaseC.BankCore) (halive : ¬BPORS.Numeric.proposalLength < b.exposures.length)
    (h : b.reused = true ∨ ∃ N ∈ b.targets, admissible (selections N) = true ∧ digestGate N = true ∧
      CaseC.CoveredBy b.exposures N) :
    1 ≤ CaseC.corePotential b := by
  rw [← bpors_corePotential]
  apply bporsSpec.core_win b halive
  rcases h with h | ⟨N, hN, hadm, hgate, hcov⟩
  · exact Or.inl h
  · refine Or.inr ⟨N, hN, ?_, ?_⟩
    · change digestAdmissible N = true
      unfold digestAdmissible
      rw [Bool.and_eq_true]
      exact ⟨hadm, hgate⟩
    · exact fun c => CaseC.coordCovered_of_opened b.exposures N c fun j => hcov _ (CaseC.opened_mem N c j)
theorem t3_fresh_signing_kernel (published : T3.Cache) (m : Message) (state : LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P : ENNReal) (hP : Sampling.WeightedSelection.freshPrice w ≤ P)
    (hF : ∀ result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state),
      F result ≤ if CaseC.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P w) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state) F ≤
      P + CaseC.reuseMass state.2 m := by
  have h := bporsSpec.fresh_signing_kernel payloadAfterDigest published m state hfresh F w P
    (by rw [bpors_freshPrice]; exact hP) (by rw [bpors_record]; exact hF)
  rw [bpors_record, bpors_reuseMass] at h
  exact h
theorem bpors_payNotDigest : PayNotDigest payloadAfterDigest := BPB.payloadAfterDigest_ok
theorem bpors_source (published : T3.Cache) :
    bporsSpec.source payloadAfterDigest published = MonitoredPrivate.interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request =>
      change Prod.fst <$> bporsSpec.authenticatedRecord payloadAfterDigest published request =
        FullGame.authenticatedSign published request
      rw [bpors_record, FullGame.authenticatedRecord_erasure]
end ClaudeWCT.Bank.BPORSRegression
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankRegression2 : DecidableEq T3.Cache := Classical.decEq _
theorem bpors_payAvoids : PayAvoids payloadAfterDigest := by
  intro m cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(NonceFreshness.avoids_pure m), (NonceFreshness.avoids_bind m), (NonceFreshness.avoids_map m),
      (NonceFreshness.avoids_foldlM m), (NonceFreshness.avoids_mapM m), (NonceFreshness.avoids_buildFts m),
      (NonceFreshness.avoids_forestPk m), (NonceFreshness.avoids_signLayers m)])
theorem bpors_recordedExperiment (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    (fun r : PaddedGame.TraceResult => (r.1, r.2.2)) <$> PaddedGame.tracedExperiment adversary budget hbudget =
      bporsSpec.recordedExperiment payloadAfterDigest (CreationGame.rest adversary) := by
  rw [CreationGame.padded_trace_eq, FtsBankSpec.recordedExperiment, map_bind]
  apply bind_congr
  intro generated
  have ht := (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_erasure
    (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [QueryRecorded.proposal_execution_erasure] at ht
  rw [bpors_source]
  exact ht
theorem bpors_birthWeight (budget : Nat) (input : LazyPrivate.Interaction.Domain)
    (state : MonitoredPrivate.History × QueryRecorded.State) :
    birthWeight (Sig := Signature) budget input state.2 =
      (CreationGame.classWeight CaseC.IsDigestInput budget input state : ENNReal) := by
  rcases input with (n | x) | request
  · simp [birthWeight, CreationGame.classWeight]
  · simp only [birthWeight, CreationGame.classWeight]
    by_cases h : CaseC.Birth budget x state.2
    · have h' : state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none :=
        ⟨h.2.2, h.1, h.2.1⟩
      rw [if_pos h, if_pos h', Nat.cast_one]
    · have h' : ¬(state.2.base.source.1 < budget ∧ CaseC.IsDigestInput x ∧ state.2.base.source.2.2 x = none) :=
        fun h' => h ⟨h'.2.1, h'.2.2, h'.1⟩
      rw [if_neg h, if_neg h', Nat.cast_zero]
  · simp [birthWeight, CreationGame.classWeight]
theorem bpors_expectedBirths (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    bporsSpec.expectedBirths payloadAfterDigest (CreationGame.rest adversary) budget =
      CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget := by
  unfold FtsBankSpec.expectedBirths CreationGame.expectedBirths
  congr 1
  funext generated
  have ht := BPORS.Adaptive.Creation.expectedCharges_project
    (QueryRecorded.proposalModel generated.1.2 budget hbudget).traced
    (bporsSpec.recordedImpl payloadAfterDigest generated.1.2) Prod.snd
    (fun input st => by
      rw [(QueryRecorded.proposalModel generated.1.2 budget hbudget).traced_query_erasure,
        QueryRecorded.proposal_query_erasure, ← bpors_source]
      rfl)
    (birthWeight budget) (CreationGame.rest adversary generated.1.1 generated.1.2) ([], generated.2)
  rw [← ht]
  congr 1
  funext input state
  exact bpors_birthWeight budget input state
theorem t3_bank_potential_le (adversary : SigGolfCandidate.T3M.Final.AdversaryP) (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    expectedValue (bporsSpec.bankExperiment payloadAfterDigest (CreationGame.rest adversary) budget)
        (fun r => bporsSpec.potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * CreationGame.expectedBirths CaseC.IsDigestInput adversary budget hbudget +
        (budget : ENNReal) * (11324 / 100000000) / 2 ^ 128 := by
  rw [← bpors_expectedBirths adversary budget hbudget]
  exact bporsSpec.bank_potential_le payloadAfterDigest bpors_payNotDigest bpors_payAvoids
    (CreationGame.rest adversary) budget
end ClaudeWCT.Bank.BPORSRegression
end

section


namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctBank : DecidableEq T3.Cache := Classical.decEq _
variable (hacc : AcceptedProposalUniform) (hle : AcceptanceBound) (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
noncomputable def authenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.signPayload request.cache request.message else pure none
theorem wct_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpec hacc hle horizon rate hexc).authenticatedRecord payAfterDigest published request =
      authenticatedSign published request := by
  unfold FtsBankSpec.authenticatedRecord authenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecord_erasure _ rfl _ _
  · rfl
theorem wct_source_sign (published : T3.Cache) (request : Request) :
    (wctSpec hacc hle horizon rate hexc).source payAfterDigest published (.inr request) =
      authenticatedSign published request :=
  wct_record_erasure hacc hle horizon rate hexc published request
noncomputable def interactionSource (published : T3.Cache) : QueryImpl (Interaction' WCT9.Signature) M
  | .inl input => forwardWorld input
  | .inr request => authenticatedSign published request
theorem wct_source (published : T3.Cache) :
    (wctSpec hacc hle horizon rate hexc).source payAfterDigest published = interactionSource published := by
  funext input
  cases input with
  | inl input => rfl
  | inr request => exact wct_source_sign hacc hle horizon rate hexc published request
theorem wct_recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) :
    (wctSpec hacc hle horizon rate hexc).recordedExperiment payAfterDigest rest = (do
      let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
      (liftM (QueryRecorded.run (simulateQ (interactionSource generated.1.2) (rest generated.1.1 generated.1.2))
        generated.2) : PMF _)) := by
  unfold FtsBankSpec.recordedExperiment
  simp only [wct_source]
theorem wct_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpec hacc hle horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec hacc hle horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec hacc hle horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wct_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpec hacc hle horizon rate hexc).potential budget st :=
  (wctSpec hacc hle horizon rate hexc).potential_win budget st halive hcount h
theorem wct_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpec hacc hle horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpec hacc hle horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpec hacc hle horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpec hacc hle horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
end ClaudeWCT.Bank.WCT
end

section



namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChild buildCoordinate)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section allowed
variable (Q : T3.Spec.Domain → Prop) (hpublic : ∀ input, Q (.inl (.inr input)))
  (hpair : ∀ tweak, Q (.inr (.inl tweak))) (hnonce : ∀ message, Q (.inr (.inr (.inl message))))
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) Q := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed Q _ _ (fun _ _ => SourceQueries.shortHash_allowed Q hpublic _) _
include hpublic hpair in
theorem buildChild_allowed (index coord selected : Nat) (word : Rank) :
    AllQueriesSatisfy (buildChild index coord selected word) Q := by
  unfold buildChild
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state pair
    apply SourceQueries.bind_allowed _ (SourceQueries.privatePair_allowed Q hpair _ _ _ _ _)
    intro seeds
    apply SourceQueries.foldlM_allowed
    intro state half
    split
    · apply SourceQueries.bind_allowed _ (chain_allowed Q hpublic _ _ _ _ _ _ _)
      intro value
      apply SourceQueries.bind_allowed _ (chain_allowed Q hpublic _ _ _ _ _ _ _)
      intro _
      exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
  · intro state
    unfold WCT9.leafHash
    exact SourceQueries.bind_allowed _ (SourceQueries.shortHash_allowed Q hpublic _)
      fun _ => SourceQueries.pure_allowed _ _
include hpublic hpair hnonce in
theorem buildCoordinate_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) Q := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state j
    exact SourceQueries.bind_allowed _ (buildChild_allowed Q hpublic hpair _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    apply SourceQueries.bind_allowed
    · apply SourceQueries.foldlM_allowed
      intro nodes heap
      exact SourceQueries.bind_allowed _ (SourceQueries.nodeHash_allowed Q hpublic hpair hnonce _ _ _ _ _ _)
        fun _ => SourceQueries.pure_allowed _ _
    · intro _
      exact SourceQueries.pure_allowed _ _
include hpublic hpair hnonce in
theorem payAfterDigest_allowed (cache : T3.Cache) (rho : Digest) (output : HashOutput) :
    AllQueriesSatisfy (payAfterDigest cache rho output) Q := by
  unfold payAfterDigest
  apply SourceQueries.bind_allowed
  · apply SourceQueries.foldlM_allowed
    intro state coord
    exact SourceQueries.bind_allowed _ (buildCoordinate_allowed Q hpublic hpair hnonce _ _ _ _)
      fun _ => SourceQueries.pure_allowed _ _
  · intro state
    unfold WCT9.forestPk
    apply SourceQueries.bind_allowed _ (SourceQueries.shortHash_allowed Q hpublic _)
    intro root
    apply SourceQueries.bind_allowed _ (SourceQueries.signLayers_allowed Q hpublic hpair hnonce _ _ _ _)
    intro layers
    split
    · exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
end allowed
theorem wct_payHashOnly : PayHashOnly payAfterDigest :=
  payAfterDigest_allowed _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
theorem wct_payRho : PayRho payAfterDigest WCT9.Signature.rho := by
  intro A cache rho output σ h
  unfold payAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
variable (hacc : AcceptedProposalUniform) (hle : AcceptanceBound) (horizon : Nat) (rate : ENNReal)
  (hexc : ExcessBound horizon rate)
theorem wct_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpec hacc hle horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpec hacc hle horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpec hacc hle horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
end ClaudeWCT.Bank.WCT
namespace ClaudeWCT.Bank.BPORSRegression
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem bpors_payHashOnly : PayHashOnly payloadAfterDigest := by
  intro cache rho output
  unfold payloadAfterDigest
  aesop (config := { maxRuleApplications := 1000 })
    (add safe apply [(SourceQueries.pure_allowed Security.SourceReplay.IsHash),
      (SourceQueries.bind_allowed Security.SourceReplay.IsHash),
      (SourceQueries.foldlM_allowed Security.SourceReplay.IsHash),
      (SourceQueries.map_allowed Security.SourceReplay.IsHash),
      (SourceQueries.buildFts_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.forestPk_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial)),
      (SourceQueries.signLayers_allowed Security.SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial))])
theorem bpors_payRho : PayRho payloadAfterDigest Signature.rho :=
  CaseC.eval_payloadAfterDigest_rho
end ClaudeWCT.Bank.BPORSRegression
end

section




namespace ClaudeWCT.Bank.WCT
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Concrete (uniformWordAverage)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_wctRev3 : DecidableEq T3.Cache := Classical.decEq _
theorem signPayloadWith_factor (limit : Nat) (cache : T3.Cache) (message : Message) :
    WCT9.signPayloadWith limit cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 limit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) := by
  unfold WCT9.signPayloadWith
  apply bind_congr
  intro rho
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩ <;> rfl
theorem rev3_signPayload_factor (cache : T3.Cache) (message : Message) :
    WCT9.Rev3.signPayload cache message = (do
      let rho ← privateNonce message
      let found ← WCT9.digestSearch rho message 0 WCT9.digestAttemptLimit
      match found with
      | none => pure none
      | some (_, output) => payAfterDigest cache rho output) :=
  signPayloadWith_factor WCT9.digestAttemptLimit cache message
theorem payloadRecordL_erasure {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
    (hadm : S.admissible = WCT9.admissible) (cache : T3.Cache) (message : Message) :
    Prod.fst <$> S.payloadRecord payAfterDigest cache message = WCT9.signPayloadWith S.limit cache message := by
  rw [signPayloadWith_factor]
  unfold FtsBankSpecL.payloadRecord FtsBankSpecL.recordForNonce
  simp only [map_bind]
  apply bind_congr
  intro rho
  rw [wct_digestSearch_public S.toFtsBankSpec hadm]
  apply bind_congr
  intro found
  rcases found with _ | ⟨_, output⟩
  · simp
  · simp only [map_bind, map_pure]
    exact bind_pure _
noncomputable def wctSpecL (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate) :
    FtsBankSpecL WProposal :=
  (wctSpec' horizon rate hexc).atLimit WCT9.digestAttemptLimit WCT9.digestAttemptLimit_le
variable (horizon : Nat) (rate : ENNReal) (hexc : ExcessBound horizon rate)
@[simp] theorem wctSpecL_limit : (wctSpecL horizon rate hexc).limit = WCT9.digestAttemptLimit := rfl
theorem wctSpecL_admissible : (wctSpecL horizon rate hexc).admissible = WCT9.admissible := rfl
@[simp] theorem wctSpecL_horizon : (wctSpecL horizon rate hexc).horizon = horizon := rfl
noncomputable def rev3AuthenticatedSign (published : T3.Cache) (request : Request) : M (Option WCT9.Signature) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then WCT9.Rev3.signPayload request.cache request.message else pure none
theorem wctL_record_erasure (published : T3.Cache) (request : Request) :
    Prod.fst <$> (wctSpecL horizon rate hexc).authenticatedRecord payAfterDigest published request =
      rev3AuthenticatedSign published request := by
  unfold FtsBankSpecL.authenticatedRecord rev3AuthenticatedSign
  rw [map_bind]
  apply bind_congr
  intro tag
  split_ifs
  · exact payloadRecordL_erasure _ rfl _ _
  · rfl
theorem excess_of_excessBound (h : ExcessBound horizon rate) :
    uniformWordAverage (wctSpecL horizon rate hexc).horizon
      (fun W : List WProposal => (wctSpecL horizon rate hexc).price W - CaseC.theta) ≤ rate := h
theorem wctL_bank_potential_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) :
    expectedValue ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget)
        (fun r => (wctSpecL horizon rate hexc).potential budget r.2) ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_potential_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
theorem wctL_potential_win (budget : Nat) (st : BankState WCT9.Signature) (halive : st.1.dead = false)
    (hcount : CaseC.countOf st.2 ≤ budget)
    (h : st.1.reused = true ∨ ∃ N ∈ st.1.targets, WCT9.admissible N = true ∧ Covered st.1.exposures N) :
    1 ≤ (wctSpecL horizon rate hexc).potential budget st :=
  (wctSpecL horizon rate hexc).potential_win budget st halive hcount h
theorem wctL_event_le (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hw : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support,
      weight (b.1, b.2.2) ≠ 0 → 1 ≤ (wctSpecL horizon rate hexc).potential budget b.2) :
    expectedValue ((wctSpecL horizon rate hexc).recordedExperiment payAfterDigest rest) weight ≤
      (CaseC.theta + 1 / 64) / 2 ^ 128 * (wctSpecL horizon rate hexc).expectedBirths payAfterDigest rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 :=
  (wctSpecL horizon rate hexc).bank_event_le payAfterDigest wct_payNotDigest wct_payAvoids rest budget
    weight hw hwin
theorem wctL_bankInv_experiment (rest : Digest → T3.Cache → OracleComp (Interaction' WCT9.Signature) Bool)
    (budget : Nat) (b : Bool × BankState WCT9.Signature)
    (hb : b ∈ ((wctSpecL horizon rate hexc).bankExperiment payAfterDigest rest budget).support) :
    ∃ generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial),
      (wctSpecL horizon rate hexc).BankInv payAfterDigest WCT9.Signature.rho generated.1.2 budget
        generated.2.events b.2 :=
  (wctSpecL horizon rate hexc).bankInv_experiment payAfterDigest WCT9.Signature.rho wct_payHashOnly
    wct_payRho wct_payAvoids rest budget b hb
theorem wctL_search (rho : Digest) (m : Message) :
    (wctSpecL horizon rate hexc).search rho m 0 (wctSpecL horizon rate hexc).limit =
      WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit :=
  (wct_digestSearch_public (wctSpecL horizon rate hexc).toFtsBankSpec rfl rho m _ 0).symm
end ClaudeWCT.Bank.WCT
end
