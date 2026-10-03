import SigGolfCandidate.ClaudeWCT.Bank.Kernel
import SigGolfCandidate.ClaudeWCT.Bank.GameBank

section

namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankKernelL : DecidableEq T3.Cache := Classical.decEq _
structure FtsBankSpecL (P : Type) [Fintype P] [SampleableType P] extends FtsBankSpec P where
  limit : Nat
  limit_le : limit ≤ 2 ^ 32
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P]
def atLimit (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) : FtsBankSpecL P :=
  { toFtsBankSpec := S, limit := limit, limit_le := h }
def toL (S : FtsBankSpec P) : FtsBankSpecL P := S.atLimit attemptLimit (by decide)
@[simp] theorem atLimit_toFtsBankSpec (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) :
    (S.atLimit limit h).toFtsBankSpec = S := rfl
@[simp] theorem atLimit_limit (S : FtsBankSpec P) (limit : Nat) (h : limit ≤ 2 ^ 32) :
    (S.atLimit limit h).limit = limit := rfl
end FtsBankSpec
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type}
def recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (rho : Digest)
    (message : Message) : M (Option Sig × Option HashOutput) := do
  let found ← S.search rho message 0 S.limit
  match found with
  | none => pure (none, none)
  | some (_, output) => do
      let signature ← pay cache rho output
      pure (signature, some output)
def payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache) (message : Message) :
    M (Option Sig × Option HashOutput) := do
  let rho ← privateNonce message
  S.recordForNonce pay cache rho message
noncomputable def authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) : M (Option Sig × Option HashOutput) := do
  let _ ← privateMac request.cache.region
  if request.cache = published then S.payloadRecord pay request.cache request.message else pure (none, none)
theorem recordForNonce_le_search (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (cache : T3.Cache)
    (rho : Digest) (message : Message) (state : LazyPrivate.State) (w : HashOutput → ENNReal) (base : ENNReal) :
    expectedValue (LazyPrivate.run (S.recordForNonce pay cache rho message) state)
      (fun result => result.1.2.elim base w) ≤
    expectedValue (Sampling.roRun 0 (S.search rho message 0 S.limit) state.2)
      (fun result => result.1.elim base (fun found => w found.2)) := by
  rw [recordForNonce, LazyPrivate.run_bind, expectedValue_bind, S.run_search, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [LazyPrivate.run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [LazyPrivate.run_bind, expectedValue_bind, LazyPrivate.run_pure, expectedValue_pure,
        Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl
theorem fresh_signing_kernel (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (state : LazyPrivate.State) (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P' : ENNReal) (hP : S.freshPrice w ≤ P')
    (hF : ∀ result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state),
      F result ≤ if S.Reuse state.2 (CaseC.nonceOf result.2 m) m then 1 else result.1.2.elim P' w) :
    expectedValue (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state) F ≤
      P' + S.reuseMass state.2 m := by
  have hrun : LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) state =
      LazyPrivate.run (privateMac published.region) state >>= fun mac =>
        LazyPrivate.run (S.payloadRecord pay published m) mac.2 := by
    rw [authenticatedRecord, LazyPrivate.run_bind]
    simp only [if_true]
  rw [hrun, expectedValue_bind]
  have hmac : ∀ mac ∈ support (LazyPrivate.run (privateMac published.region) state),
      expectedValue (LazyPrivate.run (S.payloadRecord pay published m) mac.2) F ≤ P' + S.reuseMass state.2 m := by
    intro mac hmac
    have hp := LazyPrivate.privateMac_preserves_nonce published.region m state mac hmac
    have hfresh1 : mac.2.1 (.inr (.inl m)) = none := hp.1.trans hfresh
    rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
    simp only [bind_assoc, pure_bind, expectedValue_bind]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
          (if S.Reuse state.2 (output.extractLsb' 0 128) m then 1 else 0) + P') := by
        apply expectedValue_mono
        intro output
        set s2 : LazyPrivate.State := (mac.2.1.cacheQuery (.inr (.inl m)) output, mac.2.2) with hs2
        have hsupp : ∀ result ∈ support (LazyPrivate.run
            (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2),
            F result ≤ if S.Reuse state.2 (output.extractLsb' 0 128) m then 1
              else result.1.2.elim P' w := by
          intro result hr
          have hmem : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩)
              state) := by
            rw [hrun, mem_support_bind_iff]
            refine ⟨mac, hmac, ?_⟩
            rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
            simp only [bind_assoc, pure_bind, mem_support_bind_iff]
            exact ⟨output, by simp, hr⟩
          have hn := CaseC.nonceOf_cacheQuery mac.2 m output result.2
            (SourceReplay.run_extends _ s2 result hr)
          have := hF result hmem
          rwa [hn] at this
        by_cases hreuse : S.Reuse state.2 (output.extractLsb' 0 128) m
        · refine le_trans (expectedValue_le_of_support (c := 1) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          · simp [hreuse]
        · refine le_trans (expectedValue_mono_of_support (h := fun result => result.1.2.elim P' w) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          calc
            expectedValue (LazyPrivate.run (S.recordForNonce pay published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P' w) ≤
                expectedValue (Sampling.roRun 0 (S.search (output.extractLsb' 0 128) m 0 S.limit) s2.2)
                (fun result => result.1.elim P' (fun found => w found.2)) :=
              S.recordForNonce_le_search pay published _ m s2 w P'
            _ ≤ P' := by
              apply S.search_le_price 0 _ m S.limit S.limit_le s2.2 _ w P' P' le_rfl hP
              have hc : s2.2 = state.2 := by rw [hs2]; exact hp.2
              rw [hc]
              exact not_not.mp hreuse
            _ ≤ _ := by simp [hreuse]
      _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if S.Reuse state.2 rho m then 1 else 0) + P' := by
        rw [expectedValue_add, expectedValue_const (by simp)]
        congr 1
        exact LazyPrivate.uniform_hash_low_expectation (fun rho => if S.Reuse state.2 rho m then 1 else 0)
      _ ≤ S.reuseMass state.2 m + P' := add_le_add (S.reuse_probability_le state.2 m) le_rfl
      _ = P' + S.reuseMass state.2 m := add_comm _ _
  exact expectedValue_le_of_support hmac
theorem authenticatedRecord_signerQ (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) :
    AllQueriesSatisfy (S.authenticatedRecord pay published request) (CaseC.SignerQ request.message) := by
  unfold authenticatedRecord
  apply SourceQueries.bind_allowed
  · apply SourceQueries.privateMac_allowed (CaseC.SignerQ request.message)
    intro tweak x hx
    cases hx
  · intro tag
    split
    · unfold payloadRecord recordForNonce
      apply SourceQueries.bind_allowed
      · unfold privateNonce
        apply SourceQueries.bind_allowed
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          intro x hx
          cases hx
        · intro _; exact SourceQueries.pure_allowed _ _
      · intro rho
        apply SourceQueries.bind_allowed _
          (S.search_allowed rho request.message _ (fun c hc x hx _ => by
            simp only [Sum.inl.injEq, Sum.inr.injEq] at hx
            rw [← hx]
            exact CaseC.digestTrial_rowOf rho request.message c hc) S.limit 0 (by simpa using S.limit_le))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · apply SourceQueries.bind_allowed
          · exact CaseC.allQueriesSatisfy_mono _ _ _ (CaseC.notDigestQ_signerQ request.message) (hpay _ _ _)
          · intro _; exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _
theorem signer_new_rows (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (before : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) before))
    (x : HashInput) (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) (hdig : CaseC.IsDigestInput x) :
    CaseC.DigestRowOf x request.message :=
  CaseC.run_new_public _ (fun x => CaseC.IsDigestInput x → CaseC.DigestRowOf x request.message)
    (CaseC.allQueriesSatisfy_mono _ _ _ (fun _ hq x hx => hq x hx)
      (S.authenticatedRecord_signerQ pay hpay published request))
    before result hr x hx hnew hdig
theorem authenticatedRecord_avoids (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (message : Message) (published : T3.Cache) (request : Request)
    (hrequest : request.cache ≠ published ∨ request.message ≠ message) :
    NonceFreshness.Avoids message (S.authenticatedRecord pay published request) := by
  unfold authenticatedRecord
  apply NonceFreshness.avoids_bind message (FtsBankSpec.privateMac_avoids _ message)
  intro tag
  split
  · rename_i hc
    have hm : request.message ≠ message := hrequest.resolve_left (fun h => h hc)
    unfold payloadRecord recordForNonce
    apply NonceFreshness.avoids_bind message
    · unfold privateNonce
      apply NonceFreshness.avoids_bind message
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        intro he
        apply hm
        unfold NonceFreshness.nonceQuery at he
        simp only [Sum.inr.injEq, Sum.inl.injEq] at he
        exact he
      · intro _; exact NonceFreshness.avoids_pure _ _
    · intro rho
      apply NonceFreshness.avoids_bind message
        (S.search_allowed rho request.message _ (fun c _ h => by cases h) S.limit 0 (by simpa using S.limit_le))
      intro found
      split
      · exact NonceFreshness.avoids_pure _ _
      · exact NonceFreshness.avoids_bind message (hpay _ _ _ _) fun _ => NonceFreshness.avoids_pure _ _
  · exact NonceFreshness.avoids_pure _ _
theorem sign_other_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayAvoids pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    result.2.1 (.inr (.inl m')) = lz.1 (.inr (.inl m')) :=
  NonceFreshness.run_preserves m' _
    (S.authenticatedRecord_avoids pay hpay m' published request (Or.inr (Ne.symm hm'))) lz result hr
theorem sign_other_reuseMass (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (hpay : PayNotDigest pay)
    (published : T3.Cache) (request : Request) (lz : LazyPrivate.State)
    (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz))
    (m' : Message) (hm' : m' ≠ request.message) :
    S.reuseMass result.2.2 m' = S.reuseMass lz.2 m' := by
  have hext := SourceReplay.run_extends _ lz result hr
  unfold FtsBankSpec.reuseMass
  congr 1
  apply tsum_congr
  intro p
  unfold FtsBankSpec.admissibleEntry
  cases hc : lz.2 (Sampling.digestTrial p.1 m' p.2.val) with
  | some a =>
      rw [hext.2 hc]
  | none =>
      have hn : result.2.2 (Sampling.digestTrial p.1 m' p.2.val) = none := by
        by_contra hne
        have hrow := S.signer_new_rows pay hpay published request lz result hr _ hc hne
          (CaseC.digestRowOf_isDigest ⟨p, rfl⟩)
        exact hm' (CaseC.digestRowOf_unique ⟨p, rfl⟩ hrow)
      rw [hn]
theorem sign_published_nonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (m : Message) (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published ⟨m, published⟩) lz)) :
    result.2.1 (.inr (.inl m)) ≠ none := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, _, hr⟩ := hr
  simp only [if_true] at hr
  rw [payloadRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨nonce, hnonce, hr⟩ := hr
  have hext := SourceReplay.run_extends _ nonce.2 result hr
  unfold privateNonce at hnonce
  rw [LazyPrivate.run_bind, mem_support_bind_iff] at hnonce
  obtain ⟨hashed, hhashed, hn⟩ := hnonce
  rw [LazyPrivate.run_pure, mem_support_pure_iff] at hn
  have hc := SourceReplay.hash_query_caches (.inr (.inr (.inl m))) trivial mac.2 hashed hhashed
  have hc' : nonce.2.1 (.inr (.inl m)) = some hashed.1 := by rw [hn]; exact hc
  rw [hext.1 hc']
  simp
theorem sign_unpublished (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) (published : T3.Cache)
    (request : Request) (hc : request.cache ≠ published)
    (lz : LazyPrivate.State) (result : (Option Sig × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (S.authenticatedRecord pay published request) lz)) :
    result.2.1 (.inr (.inl request.message)) = lz.1 (.inr (.inl request.message)) ∧ result.2.2 = lz.2 := by
  rw [authenticatedRecord, LazyPrivate.run_bind, mem_support_bind_iff] at hr
  obtain ⟨mac, hmac, hr⟩ := hr
  simp only [hc, if_false, LazyPrivate.run_pure, mem_support_pure_iff] at hr
  subst hr
  exact LazyPrivate.privateMac_preserves_nonce request.cache.region request.message lz mac hmac
end FtsBankSpecL
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P) {Sig : Type}
theorem toL_recordForNonce (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.recordForNonce pay = S.recordForNonce pay := rfl
theorem toL_payloadRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.payloadRecord pay = S.payloadRecord pay := rfl
theorem toL_authenticatedRecord (pay : T3.Cache → Digest → HashOutput → M (Option Sig)) :
    S.toL.authenticatedRecord pay = S.authenticatedRecord pay := rfl
end FtsBankSpec
end ClaudeWCT.Bank
end

section


namespace ClaudeWCT.Bank
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete (uniformWordAverage)
open CaseC (theta IsDigestInput Birth FreshSigning countOf lazyOf)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_bankGameL : DecidableEq T3.Cache := Classical.decEq _
namespace FtsBankSpec
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpec P) {Sig : Type}
theorem potential_initial_le_rate (budget : Nat) (rate : ENNReal)
    (hrate : uniformWordAverage S.horizon (fun W : List P => S.price W - theta) ≤ rate)
    (generated : (Digest × T3.Cache) × QueryRecorded.State)
    (hg : generated ∈ support (QueryRecorded.run keygen QueryRecorded.initial)) :
    S.potential budget ((Ghost.empty : Ghost Sig), generated.2) ≤ (budget : ENNReal) * rate / 2 ^ 128 := by
  have hreuse : S.reusePotential (lazyOf generated.2) = 0 :=
    S.reusePotential_of_noDigest _ (CaseC.keygen_noDigest generated hg)
  unfold potential livePotential
  split_ifs with h1 h2
  · exact bot_le
  · simp [Ghost.empty] at h2
  · simp only [hreuse, add_zero]
    have hbank : S.bankValue (Ghost.empty : Ghost Sig) = 0 := by simp [bankValue, Ghost.empty]
    rw [hbank, zero_add]
    unfold excessTerm
    apply ENNReal.div_le_div_right
    apply mul_le_mul'
    · exact_mod_cast Nat.sub_le budget _
    · have he : S.excessForecast S.horizon [] ≤ rate := by
        unfold excessForecast
        simpa [proposals] using hrate
      simpa [Ghost.empty] using he
end FtsBankSpec
namespace FtsBankSpecL
variable {P : Type} [Fintype P] [SampleableType P] (S : FtsBankSpecL P)
variable {Sig : Type} (pay : T3.Cache → Digest → HashOutput → M (Option Sig))
noncomputable def source (published : T3.Cache) : QueryImpl (Interaction' Sig) M
  | .inl input => forwardWorld input
  | .inr request => Prod.fst <$> S.authenticatedRecord pay published request
noncomputable def bankImpl (published : T3.Cache) (budget : Nat) :
    QueryImpl (Interaction' Sig) (StateT (BankState Sig) PMF)
  | .inl input => StateT.mk fun st =>
      (liftM (QueryRecorded.run (forwardWorld input) st.2) : PMF _).map fun r =>
        (r.1, (ghostWorld budget input st.1 st.2 r.1, r.2))
  | .inr request => StateT.mk fun st =>
      (liftM (QueryRecorded.run (S.authenticatedRecord pay published request) st.2) : PMF _).map fun r =>
        (r.1.1, (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2))
noncomputable def recordedImpl (published : T3.Cache) : QueryImpl (Interaction' Sig) (StateT QueryRecorded.State PMF) :=
  fun input => StateT.mk fun s => (liftM (QueryRecorded.run (S.source pay published input) s) : PMF _)
theorem bank_query_project (published : T3.Cache) (budget : Nat) (input : (Interaction' Sig).Domain)
    (st : BankState Sig) :
    Prod.map id Prod.snd <$> (S.bankImpl pay published budget input).run st =
      (liftM (QueryRecorded.run (S.source pay published input) st.2) : PMF _) := by
  cases input with
  | inl input =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change PMF.map id _ = _
      rw [PMF.map_id]
      rfl
  | inr request =>
      change (PMF.map _ (PMF.map _ _)) = _
      rw [PMF.map_comp]
      change _ = (liftM (QueryRecorded.run (Prod.fst <$> S.authenticatedRecord pay published request) st.2) : PMF _)
      rw [QueryRecorded.run_map, liftM_map, ← PMF.monad_map_eq_map]
      rfl
theorem bank_project {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    Prod.map id Prod.snd <$> (simulateQ (S.bankImpl pay published budget) program).run st =
      (liftM (QueryRecorded.run (simulateQ (S.source pay published) program) st.2) :
        PMF (α × QueryRecorded.State)) := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, QueryRecorded.run_pure, liftM_pure, map_pure]
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [simulateQ_bind, simulateQ_spec_query, QueryRecorded.run_bind, liftM_bind]
      rw [← S.bank_query_project pay published budget input st, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2
theorem world_unfold (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) (f : BankState Sig → ENNReal) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => f r.2) =
      expectedValue (QueryRecorded.run (forwardWorld input) st.2)
        (fun r => f (ghostWorld budget input st.1 st.2 r.1, r.2)) := by
  change expectedValue (PMF.map _ (liftM _)) _ = _
  rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
theorem world_step (published : T3.Cache) (budget : Nat) (input : SphincsSecurity.OracleWorld.Domain)
    (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inl input)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget (.inl input) st := by
  rw [S.world_unfold pay published budget input st (S.potential budget)]
  cases input with
  | inl n =>
      have hb : birthCharge (Sig := Sig) budget (.inl (.inl n)) st = 0 := rfl
      rw [hb, add_zero]
      apply expectedValue_le_of_support
      intro r hr
      have hl := CaseC.lazy_world_coin n (lazyOf st.2) (r.1, lazyOf r.2) (CaseC.recorded_lazy_support _ _ r hr)
      have hc := CaseC.recorded_count_le _ _ r hr
      change S.livePotential budget (countOf r.2) st.1 (lazyOf r.2) ≤
        S.livePotential budget (countOf st.2) st.1 (lazyOf st.2)
      rw [show lazyOf r.2 = lazyOf st.2 from hl]
      exact S.livePotential_count_anti budget hc st.1 _
  | inr x =>
      have hcount : ∀ r ∈ support (QueryRecorded.run (forwardWorld (.inr x)) st.2),
          countOf r.2 = countOf st.2 + 1 :=
        fun r hr => CreationGame.recorded_world_hash_count x st.2 r hr
      set g := st.1 with hg
      set c := countOf st.2 with hc
      set lz := lazyOf st.2 with hlz
      calc
        _ ≤ expectedValue (QueryRecorded.run (forwardWorld (.inr x)) st.2)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) (lazyOf r.2)) := by
          apply expectedValue_mono_of_support
          intro r hr
          change S.livePotential budget (countOf r.2) _ _ ≤ _
          rw [hcount r hr]
        _ = expectedValue (LazyPrivate.run (forwardWorld (.inr x)) lz)
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2) :=
          CaseC.expected_recorded _ _
            (fun r => S.livePotential budget (c + 1) (ghostWorld budget (.inr x) g st.2 r.1) r.2)
        _ ≤ _ := ?_
      cases hx : lz.2 x with
      | some a0 =>
          rw [CaseC.lazy_world_cached x lz a0 hx, expectedValue_pure]
          have hnb : ¬Birth budget x st.2 := fun h => by
            have h2 := h.2.1
            rw [← hlz, hx] at h2
            cases h2
          have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hnb]
          simp only [ghostWorld, hnb, if_false, hcb, add_zero]
          exact S.livePotential_count_anti budget (Nat.le_succ _) g _
      | none =>
          rw [CaseC.lazy_world_fresh x lz hx]
          by_cases hbirth : Birth budget x st.2
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = (theta + 1 / 64) / 2 ^ 128 := by
              simp [birthCharge, hbirth]
            rw [hcb]
            have hlt : c < budget := hbirth.2.2
            have hnot : ¬budget < c + 1 := by omega
            have hnot0 : ¬budget < c := by omega
            simp only [ghostWorld, hbirth, if_true]
            by_cases hd : g.dead = true
            · simp only [FtsBankSpec.livePotential, hd, true_or, if_true, expectedValue_const (by simp : Pr[⊥ |
                ($ᵗ HashOutput : ProbComp HashOutput)] = 0), zero_le]
            have hd' : g.dead = false := by simpa using hd
            by_cases hr : g.reused = true
            · have hpt : S.potential budget st = 1 + S.reusePotential lz :=
                S.livePotential_reused budget c g lz hd' hnot0 hr
              rw [hpt]
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                    (fun a => 1 + S.reusePotential lz + S.admInd a / 2 ^ 128) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_reused budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr,
                    add_assoc]
                  exact add_le_add le_rfl (S.reusePotential_public_le lz x a hx)
                _ = 1 + S.reusePotential lz +
                    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128 := by
                  rw [expectedValue_add, expectedValue_const (by simp)]
                  congr 1
                  simp only [div_eq_mul_inv]
                  rw [expectedValue_mul_const]
                _ ≤ 1 + S.reusePotential lz + (1 / 64) / 2 ^ 128 :=
                  add_le_add le_rfl (ENNReal.div_le_div_right S.expected_admInd_tight _)
                _ ≤ _ := by
                  apply add_le_add le_rfl
                  apply ENNReal.div_le_div_right
                  exact le_add_self
            · have hr' : g.reused = false := by simpa using hr
              have hpt : S.potential budget st = S.bankValue g + S.reusePotential lz + S.excessTerm budget c g :=
                S.livePotential_alive budget c g lz hd' hnot0 hr'
              rw [hpt]
              set R := S.horizon - g.exposures.length
              have hfa : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                  (fun a => S.forecast R g.exposures a) ≤ (theta + S.excessForecast R g.exposures) / 2 ^ 128 := by
                rw [BPORS.expected_uniform_eq_finiteAverage]
                exact S.average_forecast_le R g.exposures
              calc
                _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a =>
                    S.bankValue g + S.forecast R g.exposures a + (S.reusePotential lz + S.admInd a / 2 ^ 128) +
                      S.excessTerm budget (c + 1) g) := by
                  apply expectedValue_mono
                  intro a
                  rw [S.livePotential_alive budget (c + 1) { g with targets := g.targets ++ [a] } _ hd' hnot hr',
                    S.bankValue_birth]
                  exact add_le_add (add_le_add le_rfl (S.reusePotential_public_le lz x a hx)) le_rfl
                _ = S.bankValue g + expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                      (fun a => S.forecast R g.exposures a) +
                    (S.reusePotential lz + expectedValue ($ᵗ HashOutput : ProbComp HashOutput) S.admInd / 2 ^ 128) +
                    S.excessTerm budget (c + 1) g := by
                  simp only [expectedValue_add, expectedValue_const (by simp : Pr[⊥ |
                    ($ᵗ HashOutput : ProbComp HashOutput)] = 0), div_eq_mul_inv, expectedValue_mul_const]
                _ ≤ S.bankValue g + (theta + S.excessForecast R g.exposures) / 2 ^ 128 +
                    (S.reusePotential lz + (1 / 64) / 2 ^ 128) + S.excessTerm budget (c + 1) g := by
                  gcongr
                  exact S.expected_admInd_tight
                _ = S.bankValue g + S.reusePotential lz +
                    (S.excessTerm budget (c + 1) g + S.excessForecast R g.exposures / 2 ^ 128) +
                    (theta + 1 / 64) / 2 ^ 128 := by
                  rw [ENNReal.add_div, ENNReal.add_div]
                  ring
                _ = _ := by rw [← S.excessTerm_succ budget c g hlt]
          · have hcb : birthCharge (Sig := Sig) budget (.inl (.inr x)) st = 0 := by simp [birthCharge, hbirth]
            simp only [ghostWorld, hbirth, if_false, hcb, add_zero]
            apply expectedValue_le_of_le
            intro a
            by_cases hlt : c < budget
            · have hnd : ¬IsDigestInput x := fun hd => hbirth ⟨hd, by rw [← hlz]; exact hx, hlt⟩
              calc
                _ ≤ S.livePotential budget (c + 1) g lz :=
                  S.livePotential_reuse_mono budget (c + 1) g (S.reusePotential_public_nondigest lz x a hx hnd)
                _ ≤ S.livePotential budget c g lz := S.livePotential_count_anti budget (Nat.le_succ _) g lz
                _ = _ := rfl
            · have hover : budget < c + 1 := by omega
              simp [FtsBankSpec.livePotential, hover]
theorem sign_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache) (budget : Nat)
    (request : Request) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget (.inr request)).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st := by
  set g := st.1 with hg
  set c := countOf st.2 with hc
  set lz := lazyOf st.2 with hlz
  have hunfold : expectedValue ((S.bankImpl pay published budget (.inr request)).run st)
      (fun r => S.potential budget r.2) =
      expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.potential budget (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2), r.2)) := by
    change expectedValue (PMF.map _ (liftM _)) _ = _
    rw [CaseC.expectedValue_pmf_map, CaseC.expectedValue_liftM]
  rw [hunfold]
  calc
    _ ≤ expectedValue (QueryRecorded.run (S.authenticatedRecord pay published request) st.2)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 (r.1, lazyOf r.2)) (lazyOf r.2)) := by
      apply expectedValue_mono_of_support
      intro r hr
      change S.livePotential budget (countOf r.2) (S.ghostSign published request st.1 st.2 (r.1, lazyOf r.2))
        (lazyOf r.2) ≤ _
      exact S.livePotential_count_anti budget (CaseC.recorded_count_le _ _ r hr) _ _
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay published request) lz)
        (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2) :=
      CaseC.expected_recorded _ _ (fun r => S.livePotential budget c (S.ghostSign published request g st.2 r) r.2)
    _ ≤ S.potential budget st := ?_
  change _ ≤ S.livePotential budget c g lz
  by_cases hfresh : FreshSigning published request st.2
  swap
  ·
    apply expectedValue_le_of_support
    intro r hr
    simp only [FtsBankSpec.ghostSign, hfresh, if_false, FtsBankSpec.livePotential_log]
    apply S.livePotential_reuse_mono
    apply S.reusePotential_sign_stale_le lz r.2 request.message
    · intro hcached hnone
      apply hcached
      cases hcz : lz.1 (.inr (.inl request.message)) with
      | none => rfl
      | some a =>
          have := (SourceReplay.run_extends _ lz r hr).1 hcz
          rw [hnone] at this
          cases this
    · intro hnone
      have hcp : request.cache ≠ published := fun h => hfresh ⟨h, hnone⟩
      obtain ⟨h1, h2⟩ := S.sign_unpublished pay published request hcp lz r hr
      exact ⟨h1.trans hnone, by rw [h2]⟩
    · exact fun m' hm' => S.sign_other_nonce pay hAvoids published request lz r hr m' hm'
    · exact fun m' hm' => S.sign_other_reuseMass pay hNotDigest published request lz r hr m' hm'
  by_cases hhor : S.horizon ≤ g.exposures.length
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential]
  have hlen : g.exposures.length < S.horizon := by omega
  by_cases hd : g.dead = true
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential, hd]
  have hd' : g.dead = false := by simpa using hd
  by_cases hb : budget < c
  · apply expectedValue_le_of_le
    intro r
    simp [FtsBankSpec.ghostSign, hfresh, hhor, FtsBankSpec.livePotential, hb]
  obtain ⟨m, cache⟩ := request
  obtain ⟨hcache, hnonce⟩ := hfresh
  change cache = published at hcache
  subst hcache
  change lz.1 (.inr (.inl m)) = none at hnonce
  have hsign : ∀ r ∈ support (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz),
      S.reusePotential r.2 + S.reuseMass lz.2 m ≤ S.reusePotential lz := fun r hr =>
    S.reusePotential_sign_le lz r.2 m hnonce (S.sign_published_nonce pay cache m lz r hr)
      (fun m' hm' => S.sign_other_nonce pay hAvoids cache ⟨m, cache⟩ lz r hr m' hm')
      (fun m' hm' => S.sign_other_reuseMass pay hNotDigest cache ⟨m, cache⟩ lz r hr m' hm')
  have hfr : FreshSigning cache ⟨m, cache⟩ st.2 := ⟨rfl, hnonce⟩
  have hdead : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).dead = false := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor, hd']
  have hreu : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused =
      (g.reused || decide (S.Reuse (lazyOf st.2).2 (CaseC.nonceOf r.2 m) m)) := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have hexp : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).exposures = g.exposures ++ r.1.2.toList := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  have htar : ∀ r, (S.ghostSign cache ⟨m, cache⟩ g st.2 r).targets = g.targets := by
    intro r; simp [FtsBankSpec.ghostSign, hfr, hhor]
  by_cases hr : g.reused = true
  · apply expectedValue_le_of_support
    intro r hrs
    rw [S.livePotential_reused budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 (hdead r) hb
        (by rw [hreu r, hr, Bool.true_or]),
      S.livePotential_reused budget c g lz hd' hb hr]
    exact add_le_add le_rfl (le_trans le_self_add (hsign r hrs))
  have hr' : g.reused = false := by simpa using hr
  set P' := S.bankValue g + S.excessTerm budget c g with hP
  let Fmain : (Option Sig × Option HashOutput) × LazyPrivate.State → ENNReal := fun r =>
    if S.Reuse lz.2 (CaseC.nonceOf r.2 m) m then 1 else r.1.2.elim P' (S.signWeight budget c g)
  have hpoint : ∀ r, S.livePotential budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) r.2 ≤
      Fmain r + S.reusePotential r.2 := by
    intro r
    by_cases hre : S.Reuse lz.2 (CaseC.nonceOf r.2 m) m
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = true := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_true hre
      rw [S.livePotential_reused budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_true, le_refl]
    · have hru : (S.ghostSign cache ⟨m, cache⟩ g st.2 r).reused = false := by
        rw [hreu r, hr', Bool.false_or]
        exact decide_eq_false hre
      rw [S.livePotential_alive budget c _ r.2 (hdead r) hb hru]
      simp only [Fmain, hre, if_false]
      have hbv : S.bankValue (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.bankValue { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.bankValue; rw [htar r, hexp r]
      have het : S.excessTerm budget c (S.ghostSign cache ⟨m, cache⟩ g st.2 r) =
          S.excessTerm budget c { g with exposures := g.exposures ++ r.1.2.toList } := by
        unfold FtsBankSpec.excessTerm; rw [hexp r]
      rw [hbv, het]
      cases hsel : r.1.2 with
      | none =>
          simp only [Option.toList_none, List.append_nil, Option.elim_none, hP]
          apply le_of_eq
          ring
      | some A =>
          simp only [Option.toList_some, Option.elim_some, FtsBankSpec.signWeight]
          apply le_of_eq
          ring
  calc
    _ ≤ expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
        (fun r => Fmain r + S.reusePotential r.2) := expectedValue_mono _ hpoint
    _ = expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz) Fmain +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := expectedValue_add _ _ _
    _ ≤ (P' + S.reuseMass lz.2 m) +
        expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2) := by
      apply add_le_add _ le_rfl
      apply S.fresh_signing_kernel pay cache m lz hnonce Fmain (S.signWeight budget c g) P'
        (le_of_eq (S.freshPrice_signWeight budget c g hlen))
      intro r _
      exact le_rfl
    _ = P' + (expectedValue (LazyPrivate.run (S.authenticatedRecord pay cache ⟨m, cache⟩) lz)
          (fun r => S.reusePotential r.2 + S.reuseMass lz.2 m)) := by
      rw [expectedValue_add, expectedValue_const (by simp)]
      ring
    _ ≤ P' + S.reusePotential lz := add_le_add le_rfl (expectedValue_le_of_support hsign)
    _ = S.livePotential budget c g lz := by
      rw [S.livePotential_alive budget c g lz hd' hb hr', hP]
      ring
theorem potential_step (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (input : (Interaction' Sig).Domain) (st : BankState Sig) :
    expectedValue ((S.bankImpl pay published budget input).run st) (fun r => S.potential budget r.2) ≤
      S.potential budget st + birthCharge budget input st := by
  cases input with
  | inl input => exact S.world_step pay published budget input st
  | inr request => exact (S.sign_step pay hNotDigest hAvoids published budget request st).trans le_self_add
theorem potential_run {α : Type} (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay) (published : T3.Cache)
    (budget : Nat) (program : OracleComp (Interaction' Sig) α) (st : BankState Sig) :
    expectedValue ((simulateQ (S.bankImpl pay published budget) program).run st)
        (fun r => S.potential budget r.2) ≤
      S.potential budget st + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (birthCharge budget) program st := by
  induction program using OracleComp.inductionOn generalizing st with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, BPORS.Adaptive.Creation.expectedCharges_pure, add_zero]
      rw [expectedValue_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, expectedValue_bind,
        BPORS.Adaptive.Creation.expectedCharges_query_bind]
      calc
        _ ≤ expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
            S.potential budget result.2 + BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
              (birthCharge budget) (next result.1) result.2) :=
          expectedValue_mono _ fun result => ih result.1 result.2
        _ = expectedValue ((S.bankImpl pay published budget input).run st)
              (fun result => S.potential budget result.2) +
            expectedValue ((S.bankImpl pay published budget input).run st) (fun result =>
              BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
                (birthCharge budget) (next result.1) result.2) := expectedValue_add _ _ _
        _ ≤ (S.potential budget st + birthCharge budget input st) + _ :=
          add_le_add (S.potential_step pay hNotDigest hAvoids published budget input st) le_rfl
        _ = _ := by ring
theorem bank_charges_eq_births {α : Type} (published : T3.Cache) (budget : Nat)
    (program : OracleComp (Interaction' Sig) α) (s : QueryRecorded.State) (g : Ghost Sig) :
    BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget) program (g, s) =
      (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay published)
        (birthWeight budget) program s := by
  have h1 : BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget) (birthCharge budget)
      program (g, s) =
      BPORS.Adaptive.Creation.expectedCharges (S.bankImpl pay published budget)
        (fun input st => (theta + 1 / 64) / 2 ^ 128 * birthWeight budget input st.2) program (g, s) := by
    congr 1
    funext input st
    exact birthCharge_eq budget input st
  rw [h1, BPORS.Adaptive.Creation.expectedCharges_scale]
  congr 1
  exact BPORS.Adaptive.Creation.expectedCharges_project (S.bankImpl pay published budget)
    (S.recordedImpl pay published) Prod.snd
    (fun input st => S.bank_query_project pay published budget input st)
    (birthWeight budget) program (g, s)
noncomputable def bankExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    PMF (Bool × BankState Sig) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (simulateQ (S.bankImpl pay generated.1.2 budget) (rest generated.1.1 generated.1.2)).run (Ghost.empty, generated.2)
noncomputable def recordedExperiment (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) :
    PMF (Bool × QueryRecorded.State) := do
  let generated ← (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _)
  (liftM (QueryRecorded.run (simulateQ (S.source pay generated.1.2) (rest generated.1.1 generated.1.2))
    generated.2) : PMF _)
theorem bank_experiment_project (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    (fun r : Bool × BankState Sig => (r.1, r.2.2)) <$> S.bankExperiment pay rest budget =
      S.recordedExperiment pay rest := by
  unfold bankExperiment recordedExperiment
  rw [map_bind]
  apply bind_congr
  intro generated
  exact S.bank_project pay generated.1.2 budget (rest generated.1.1 generated.1.2) (Ghost.empty, generated.2)
noncomputable def expectedBirths (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    ENNReal :=
  expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
    BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2) (birthWeight budget)
      (rest generated.1.1 generated.1.2) generated.2)
theorem bank_potential_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * S.excessRate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.potential_initial_le budget generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem bank_event_le (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * S.excessRate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le pay hNotDigest hAvoids rest budget)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
theorem bank_potential_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : uniformWordAverage S.horizon (fun W : List P => S.price W - theta) ≤ rate) :
    expectedValue (S.bankExperiment pay rest budget) (fun r => S.potential budget r.2) ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  unfold bankExperiment
  rw [expectedValue_bind]
  calc
    _ ≤ expectedValue (liftM (QueryRecorded.run keygen QueryRecorded.initial) : PMF _) (fun generated =>
        (budget : ENNReal) * rate / 2 ^ 128 +
          (theta + 1 / 64) / 2 ^ 128 * BPORS.Adaptive.Creation.expectedCharges (S.recordedImpl pay generated.1.2)
            (birthWeight budget) (rest generated.1.1 generated.1.2) generated.2) := by
      apply CaseC.pmf_expectedValue_mono
      intro generated hg
      rw [MonitoredPrivate.pmf_support] at hg
      refine (S.potential_run pay hNotDigest hAvoids generated.1.2 budget _ _).trans ?_
      rw [S.bank_charges_eq_births pay generated.1.2 budget]
      exact add_le_add (S.toFtsBankSpec.potential_initial_le_rate budget rate hrate generated hg) le_rfl
    _ = _ := by
      rw [expectedValue_add, expectedValue_const (by simp), CaseC.pmf_expectedValue_left_mul]
      unfold expectedBirths
      ring
theorem bank_event_le_rate (hNotDigest : PayNotDigest pay) (hAvoids : PayAvoids pay)
    (rest : Digest → T3.Cache → OracleComp (Interaction' Sig) Bool) (budget : Nat) (rate : ENNReal)
    (hrate : uniformWordAverage S.horizon (fun W : List P => S.price W - theta) ≤ rate)
    (weight : Bool × QueryRecorded.State → ENNReal) (hle : ∀ y, weight y ≤ 1)
    (hwin : ∀ b ∈ (S.bankExperiment pay rest budget).support, weight (b.1, b.2.2) ≠ 0 → 1 ≤ S.potential budget b.2) :
    expectedValue (S.recordedExperiment pay rest) weight ≤
      (theta + 1 / 64) / 2 ^ 128 * S.expectedBirths pay rest budget +
        (budget : ENNReal) * rate / 2 ^ 128 := by
  rw [← S.bank_experiment_project pay rest budget, PMF.monad_map_eq_map, CaseC.expectedValue_pmf_map]
  refine le_trans ?_ (S.bank_potential_le_rate pay hNotDigest hAvoids rest budget rate hrate)
  apply CaseC.pmf_expectedValue_mono
  intro b hb
  by_cases h0 : weight (b.1, b.2.2) = 0
  · rw [h0]; exact bot_le
  · exact (hle _).trans (hwin b hb h0)
end FtsBankSpecL
end ClaudeWCT.Bank
end
