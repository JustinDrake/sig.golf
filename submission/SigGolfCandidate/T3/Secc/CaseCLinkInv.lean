import SigGolfCandidate.T3.Secc.CaseCBankMain

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityExtraction (queried)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCLinkInv : DecidableEq T3.Cache := Classical.decEq _
def Agrees (A : Correctness.Answers) (lazy : LazyPrivate.State) : Prop :=
  ∀ input answer, SourceReplay.known lazy input = some answer → A input = answer
theorem Agrees.mono {A : Correctness.Answers} {lazy lazy' : LazyPrivate.State} (h : Agrees A lazy')
    (hext : SourceReplay.Extends lazy lazy') : Agrees A lazy :=
  fun input answer hk => h input answer (SourceReplay.known_mono lazy lazy' hext hk)
def eventPublic : FirstHit.QueryEvent → Option (HashInput × HashOutput)
  | ⟨_, .inl (.inr x), a⟩ => some (x, a)
  | _ => none
def SignerQueried (published : T3.Cache) (log : QueryLog Requests) (lazy : LazyPrivate.State) (x : HashInput) :
    Prop :=
  ∃ entry ∈ log, ∀ A, Agrees A lazy →
    (.inl (.inr x) : T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published entry.1)
structure BankInv (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent) (st : BankState) : Prop where
  len : st.1.exposures.length ≤ st.1.log.length
  dead : st.1.dead = true → horizon < st.1.log.length
  events : ∀ e ∈ st.2.events, e ∈ kg ∨ ∀ x a, eventPublic e = some (x, a) → IsDigestInput x →
    e.before.2 x = none → a ∈ st.1.targets ∨ budget < countOf st.2 ∨ SignerQueried published st.1.log (lazyOf st.2) x
  exposed : st.1.dead = false → ∀ m, (lazyOf st.2).1 (.inr (.inl m)) ≠ none → ∀ A, Agrees A (lazyOf st.2) →
    ∀ c out, evalWithAnswerFn A (digestSearch (nonceOf (lazyOf st.2) m) m 0 attemptLimit) = some (c, out) →
      out ∈ st.1.exposures
  logged : ∀ entry ∈ st.1.log, ∀ σ, entry.2 = some σ → entry.1.cache = published ∧
    (lazyOf st.2).1 (.inr (.inl entry.1.message)) ≠ none ∧ σ.rho = nonceOf (lazyOf st.2) entry.1.message
theorem nonceOf_extends {lazy lazy' : LazyPrivate.State} (hext : SourceReplay.Extends lazy lazy') (m : Message)
    (h : lazy.1 (.inr (.inl m)) ≠ none) : nonceOf lazy' m = nonceOf lazy m ∧ lazy'.1 (.inr (.inl m)) ≠ none := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp h
  have h' := hext.1 ho
  simp [nonceOf, ho, h']
theorem eval_privateNonce (A : Correctness.Answers) (lazy : LazyPrivate.State) (hA : Agrees A lazy) (m : Message)
    (h : lazy.1 (.inr (.inl m)) ≠ none) : evalWithAnswerFn A (privateNonce m) = nonceOf lazy m := by
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.mp h
  have hk : A (.inr (.inr (.inl m))) = o := hA (.inr (.inr (.inl m))) o ho
  unfold privateNonce privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, nonceOf, ho, Option.getD_some]
  rw [← hk]
  rfl
theorem eval_payload_selected (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message) :
    (evalWithAnswerFn A (payloadRecordForNonce cache rho m)).2 =
      (evalWithAnswerFn A (digestSearch rho m 0 attemptLimit)).map Prod.snd := by
  unfold payloadRecordForNonce
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn A (digestSearch rho m 0 attemptLimit) with
  | none => simp
  | some found =>
      rcases found with ⟨c, out⟩
      simp [evalWithAnswerFn_bind]
theorem eval_payloadAfterDigest_rho (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest)
    (output : HashOutput) (σ : Signature) (h : evalWithAnswerFn A (payloadAfterDigest cache rho output) = some σ) :
    σ.rho = rho := by
  unfold payloadAfterDigest at h
  simp only [evalWithAnswerFn_bind] at h
  split at h
  all_goals (rw [evalWithAnswerFn_pure] at h; cases h)
  all_goals rfl
theorem eval_payload_rho (A : Correctness.Answers) (cache : T3.Cache) (rho : Digest) (m : Message)
    (σ : Signature) (h : (evalWithAnswerFn A (payloadRecordForNonce cache rho m)).1 = some σ) : σ.rho = rho := by
  unfold payloadRecordForNonce at h
  simp only [evalWithAnswerFn_bind] at h
  cases hd : evalWithAnswerFn A (digestSearch rho m 0 attemptLimit) with
  | none => simp [hd] at h
  | some found =>
      rcases found with ⟨c, out⟩
      simp only [hd, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h
      exact eval_payloadAfterDigest_rho A cache rho out σ h
theorem recorded_new_events {α : Type} (program : M α) (s : QueryRecorded.State) (r : α × QueryRecorded.State)
    (hr : r ∈ support (QueryRecorded.run program s)) :
    ∃ rec ∈ support (FirstHit.record program (lazyOf s)),
      r.2.events = s.events ++ rec.events ∧ rec.state = lazyOf r.2 ∧ rec.value = r.1 := by
  have hm : QueryRecorded.recorded r ∈ support (QueryRecorded.recorded <$> QueryRecorded.run program s) := by
    rw [support_map]; exact ⟨r, hr, rfl⟩
  rw [QueryRecorded.run_recorded, support_map] at hm
  obtain ⟨rec, hrec, he⟩ := hm
  refine ⟨rec, hrec, ?_, ?_, ?_⟩
  · have := congrArg FirstHit.Recorded.events he
    exact this.symm
  · have := congrArg FirstHit.Recorded.state he
    exact this
  · have := congrArg FirstHit.Recorded.value he
    exact this
theorem bank_support_world (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState) (r : SphincsSecurity.OracleWorld.Range input × BankState)
    (hr : r ∈ ((bankImpl published budget (.inl input)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (forwardWorld input) st.2), r = (q.1, (ghostWorld budget input st.1 st.2 q.1, q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (forwardWorld input) st.2))).support at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem bank_support_sign (published : T3.Cache) (budget : Nat) (request : Request)
    (st : BankState) (r : Option Signature × BankState)
    (hr : r ∈ ((bankImpl published budget (.inr request)).run st).support) :
    ∃ q ∈ support (QueryRecorded.run (FullGame.authenticatedRecord published request) st.2),
      r = (q.1.1, (ghostSign published request st.1 st.2 q, q.2)) := by
  change r ∈ (PMF.map _ (liftM (QueryRecorded.run (FullGame.authenticatedRecord published request) st.2))).support
    at hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨q, ?_, rfl⟩
  rw [MonitoredPrivate.pmf_support] at hq
  exact hq
theorem world_query_support (input : SphincsSecurity.OracleWorld.Domain) (s : QueryRecorded.State)
    (q : SphincsSecurity.OracleWorld.Range input × QueryRecorded.State)
    (hq : q ∈ support (QueryRecorded.run (forwardWorld input) s)) :
    q.2.events = s.events ++ [⟨lazyOf s, .inl input, q.1⟩] ∧
      countOf q.2 = countOf s + FullGame.queryCharge (.inl input) ∧
      (q.1, lazyOf q.2) ∈ support (LazyPrivate.run (forwardWorld input) (lazyOf s)) := by
  change q ∈ support (QueryRecorded.run (liftM (T3.Spec.query (.inl input))) s) at hq
  rw [QueryRecorded.run_query_explicit, support_map] at hq
  obtain ⟨res, hres, rfl⟩ := hq
  exact ⟨rfl, rfl, hres⟩
theorem world_private_eq (input : SphincsSecurity.OracleWorld.Domain) (lazy : LazyPrivate.State)
    (res : SphincsSecurity.OracleWorld.Range input × LazyPrivate.State)
    (hres : res ∈ support (LazyPrivate.run (forwardWorld input) lazy)) : res.2.1 = lazy.1 := by
  cases input with
  | inl n => rw [lazy_world_coin n lazy res hres]
  | inr x =>
      change res ∈ support (LazyPrivate.run (Sampling.publicHandler x) lazy) at hres
      rw [LazyPrivate.run_publicQuery, mem_support_bind_iff] at hres
      obtain ⟨step, _, hres⟩ := hres
      rw [mem_support_pure_iff] at hres
      subst hres
      rfl
theorem ghostWorld_fields (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain) (g : Ghost)
    (s : QueryRecorded.State) (a : SphincsSecurity.OracleWorld.Range input) :
    (ghostWorld budget input g s a).exposures = g.exposures ∧ (ghostWorld budget input g s a).log = g.log ∧
      (ghostWorld budget input g s a).dead = g.dead ∧ (ghostWorld budget input g s a).reused = g.reused ∧
      ∀ N ∈ g.targets, N ∈ (ghostWorld budget input g s a).targets := by
  cases input with
  | inl n => exact ⟨rfl, rfl, rfl, rfl, fun _ h => h⟩
  | inr x =>
      by_cases hb : Birth budget x s
      · simp only [ghostWorld, hb, if_true, true_and]
        exact fun _ h => List.mem_append_left _ h
      · simp only [ghostWorld, hb, if_false, true_and]
        exact fun _ h => h
theorem bankInv_world (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : SphincsSecurity.OracleWorld.Domain) (st : BankState) (hinv : BankInv published budget kg st)
    (r : SphincsSecurity.OracleWorld.Range input × BankState)
    (hr : r ∈ ((bankImpl published budget (.inl input)).run st).support) : BankInv published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := bank_support_world published budget input st r hr
  obtain ⟨hev, hcount, hlazy⟩ := world_query_support input st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hpriv : (lazyOf q.2).1 = (lazyOf st.2).1 := world_private_eq input (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  obtain ⟨hX, hL, hD, hR, hT⟩ := ghostWorld_fields budget input st.1 st.2 q.1
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
theorem queried_record_sign (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    SourceReplay.queried A (FullGame.authenticatedRecord published request) =
      queried A (FullGame.authenticatedSign published request) := by
  rw [← FullGame.authenticatedRecord_erasure, SigGolfCandidate.T3M.Extract.queried_map]
  rfl
theorem eval_sign_of_record (A : Correctness.Answers) (published : T3.Cache) (request : Request) :
    evalWithAnswerFn A (FullGame.authenticatedSign published request) =
      (evalWithAnswerFn A (FullGame.authenticatedRecord published request)).1 := by
  rw [← FullGame.authenticatedRecord_erasure, SigGolfCandidate.T3M.eval_map]
theorem ghostSign_log (published : T3.Cache) (request : Request) (g : Ghost) (s : QueryRecorded.State)
    (q : (Option Signature × Option HashOutput) × QueryRecorded.State) :
    (ghostSign published request g s q).log = g.log ++ [⟨request, q.1.1⟩] := by
  unfold ghostSign; split_ifs <;> rfl
theorem ghostSign_targets (published : T3.Cache) (request : Request) (g : Ghost) (s : QueryRecorded.State)
    (q : (Option Signature × Option HashOutput) × QueryRecorded.State) :
    (ghostSign published request g s q).targets = g.targets := by
  unfold ghostSign; split_ifs <;> rfl
theorem ghostSign_exposures_len (published : T3.Cache) (request : Request) (g : Ghost) (s : QueryRecorded.State)
    (q : (Option Signature × Option HashOutput) × QueryRecorded.State) :
    (ghostSign published request g s q).exposures.length ≤ g.exposures.length + 1 := by
  unfold ghostSign
  split_ifs
  · simp
  · cases q.1.2 <;> simp
  · simp
theorem bankInv_sign (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (request : Request) (st : BankState) (hinv : BankInv published budget kg st)
    (r : Option Signature × BankState)
    (hr : r ∈ ((bankImpl published budget (.inr request)).run st).support) : BankInv published budget kg r.2 := by
  obtain ⟨q, hq, rfl⟩ := bank_support_sign published budget request st r hr
  obtain ⟨rec, hrec, hev, hstate, hvalue⟩ := recorded_new_events _ st.2 q hq
  have hlazy := recorded_lazy_support _ st.2 q hq
  have hext : SourceReplay.Extends (lazyOf st.2) (lazyOf q.2) :=
    SourceReplay.run_extends _ (lazyOf st.2) (q.1, lazyOf q.2) hlazy
  have hres : SourceReplay.Resolves (lazyOf q.2) (FullGame.authenticatedRecord published request) q.1 :=
    SourceReplay.resolves_of_run _ (CountedPrivate.authenticatedRecord_hashOnly published request) _ _ hlazy
  have hcle := recorded_count_le _ st.2 q hq
  have hlog := ghostSign_log published request st.1 st.2 q
  have htar := ghostSign_targets published request st.1 st.2 q
  have h1 := ghostSign_exposures_len published request st.1 st.2 q
  set g' := ghostSign published request st.1 st.2 q with hg'
  show BankInv published budget kg (g', q.2)
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
    · by_cases hh : horizon ≤ st.1.exposures.length
      · have := hinv.len
        omega
      · have hd0 : st.1.dead = true := by
          simpa [hg', ghostSign, hf, hh] using hd
        have := hinv.dead hd0
        omega
    · have hd0 : st.1.dead = true := by
        simpa [hg', ghostSign, hf] using hd
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
      have hinputs := FirstHit.recorded_inputs _ (CountedPrivate.authenticatedRecord_hashOnly published request)
        (lazyOf st.2) rec hrec A (by rw [hstate]; exact hA)
      have hmem : e.input ∈ rec.events.map FirstHit.QueryEvent.input := List.mem_map_of_mem he
      rw [hinputs, queried_record_sign] at hmem
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
    · by_cases hh : horizon ≤ st.1.exposures.length
      · simp [hg', ghostSign, hf, hh] at hdead
      · have hdead0 : st.1.dead = false := by simpa [hg', ghostSign, hf, hh] using hdead
        have hX : g'.exposures = st.1.exposures ++ q.1.2.toList := by simp [hg', ghostSign, hf, hh]
        rw [hX]
        by_cases hmm : m = request.message
        · subst hmm
          obtain ⟨hcache, hnonce⟩ := hf
          have hreq : request = ⟨request.message, published⟩ := by cases request; simp_all
          have heval := hres.eval A hA
          rw [hreq, BPB.eval_authenticatedRecord_published,
            eval_privateNonce A (lazyOf q.2) hA request.message hm] at heval
          have hsel := eval_payload_selected A published (nonceOf (lazyOf q.2) request.message) request.message
          rw [heval, hs] at hsel
          apply List.mem_append_right
          rw [hsel]
          simp
        · have hn := sign_other_nonce published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by rwa [← hn]
          obtain ⟨hno, _⟩ := nonceOf_extends hext m hm0
          rw [hno] at hs
          exact List.mem_append_left _ (hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs)
    · have hdead0 : st.1.dead = false := by simpa [hg', ghostSign, hf] using hdead
      have hX : g'.exposures = st.1.exposures := by simp [hg', ghostSign, hf]
      rw [hX]
      have hm0 : (lazyOf st.2).1 (.inr (.inl m)) ≠ none := by
        by_cases hmm : m = request.message
        · subst hmm
          by_cases hc : request.cache = published
          · intro hnone
            exact hf ⟨hc, hnone⟩
          · have := (sign_unpublished published request hc (lazyOf st.2) (q.1, lazyOf q.2) hlazy).1
            rwa [← this]
        · have hn := sign_other_nonce published request (lazyOf st.2) (q.1, lazyOf q.2) hlazy m hmm
          rwa [← hn]
      obtain ⟨hno, _⟩ := nonceOf_extends hext m hm0
      rw [hno] at hs
      exact hinv.exposed hdead0 m hm0 A (hA.mono hext) c out hs
  ·
    intro entry he σ hσ
    rw [hlog, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨h1, h2, h3⟩ := hinv.logged entry he σ hσ
      obtain ⟨hno, hc'⟩ := nonceOf_extends hext entry.1.message h2
      exact ⟨h1, hc', by rw [hno]; exact h3⟩
    · rw [List.mem_singleton] at he
      subst he
      change q.1.1 = some σ at hσ
      have hA : Agrees (SourceReplay.answers (lazyOf q.2)) (lazyOf q.2) :=
        fun input answer hk => SourceReplay.answers_known _ input answer hk
      have heval := hres.eval _ hA
      have hsign := eval_sign_of_record (SourceReplay.answers (lazyOf q.2)) published request
      rw [heval, hσ, BPB.eval_authenticatedSign] at hsign
      by_cases hc : request.cache = published
      · rw [if_pos hc] at hsign
        have hreq : request = ⟨request.message, published⟩ := by cases request; simp_all
        have hcached : (lazyOf q.2).1 (.inr (.inl request.message)) ≠ none := by
          have := sign_published_nonce published request.message (lazyOf st.2) (q.1, lazyOf q.2)
            (by rw [← hreq]; exact hlazy)
          exact this
        refine ⟨hc, hcached, ?_⟩
        have hrho := eval_payload_rho _ published _ request.message σ hsign
        rw [hrho, eval_privateNonce _ (lazyOf q.2) hA request.message hcached]
      · rw [if_neg hc] at hsign
        cases hsign
theorem bankInv_step (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (input : LazyPrivate.Interaction.Domain) (st : BankState) (hinv : BankInv published budget kg st)
    (r : LazyPrivate.Interaction.Range input × BankState)
    (hr : r ∈ ((bankImpl published budget input).run st).support) : BankInv published budget kg r.2 := by
  cases input with
  | inl input => exact bankInv_world published budget kg input st hinv r hr
  | inr request => exact bankInv_sign published budget kg request st hinv r hr
theorem bankInv_run {α : Type} (published : T3.Cache) (budget : Nat) (kg : List FirstHit.QueryEvent)
    (program : OracleComp LazyPrivate.Interaction α) (st : BankState) (hinv : BankInv published budget kg st)
    (r : α × BankState) (hr : r ∈ ((simulateQ (bankImpl published budget) program).run st).support) :
    BankInv published budget kg r.2 := by
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
      exact ih middle.1 middle.2 (bankInv_step published budget kg input st hinv middle hm) hr
theorem bankInv_initial (published : T3.Cache) (budget : Nat)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    BankInv published budget generated.2.events (Ghost.empty, generated.2) := by
  have hl := recorded_lazy_support keygen QueryRecorded.initial generated hg
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
end SigGolfCandidate.T3.Security.CaseC
