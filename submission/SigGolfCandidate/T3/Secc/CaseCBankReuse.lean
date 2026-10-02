import SigGolfCandidate.T3.Secc.CaseCBankDefs
import SigGolfCandidate.T3.Secc.CaseCCore
import SigGolfCandidate.T3.Secc.SeccSufRoute

/-!
# Stream CC: the reuse potential (cached admissible digest rows of unsigned messages)

`reusePotential s = Σ_m [nonce of m uncached] · reuseMass s.cache m`. It pays the cache-reuse exception:

* a fresh public row adds at most its admissibility indicator over `2^128` (`reusePotential_public_le`);
* a fresh signing of `m` removes exactly `reuseMass s m`, the bound on its reuse probability
  (`reusePotential_sign_le`), because the signer's new public rows are rows of `m` (`signer_new_rows`) and it
  touches no other nonce.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M.Final
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_caseCBankReuse : DecidableEq T3.Cache := Classical.decEq _

/-! ## New public rows of a run -/

theorem query_new_public (input : T3.Spec.Domain) (before : LazyPrivate.State)
    (result : T3.Spec.Range input × LazyPrivate.State)
    (h : result ∈ support (LazyPrivate.run (liftM (T3.Spec.query input)) before)) (x : HashInput)
    (hx : before.2 x = none) (hr : result.2.2 x ≠ none) : input = .inl (.inr x) := by
  rw [LazyPrivate.run_query] at h
  cases input with
  | inl input =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, hstep, rfl⟩ := h
      cases input with
      | inl n =>
          change step ∈ support ((fun answer => (answer, before.2)) <$>
            ($ᵗ (SphincsSecurity.OracleWorld.Range (.inl n)) : ProbComp _)) at hstep
          rw [support_map] at hstep
          obtain ⟨_, _, rfl⟩ := hstep
          exact absurd hx hr
      | inr y =>
          by_cases hxy : y = x
          · rw [hxy]
          · exfalso
            apply hr
            change step ∈ support ((randomOracle (spec := SphincsSecurity.HashSpec) y).run before.2) at hstep
            rw [OracleSpec.randomOracle] at hstep
            cases hc : before.2 y with
            | some u =>
                rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hstep
                subst step
                exact hx
            | none =>
                rw [QueryImpl.withCaching_run_none _ hc, support_map] at hstep
                obtain ⟨v, _, rfl⟩ := hstep
                change (before.2.cacheQuery y v) x = none
                rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hxy)]
                exact hx
  | inr coordinate =>
      simp only [PrivateTable.lazyImpl, StateT.run_mk, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at h
      obtain ⟨step, _, rfl⟩ := h
      exact absurd hx hr

/-- A program all of whose public queries satisfy `Q` caches only new public rows satisfying `Q`. -/
theorem run_new_public {α : Type} (program : M α) (Q : HashInput → Prop)
    (hQ : AllQueriesSatisfy program (fun q => ∀ x, q = .inl (.inr x) → Q x))
    (before : LazyPrivate.State) (result : α × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run program before)) (x : HashInput)
    (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) : Q x := by
  induction program using OracleComp.inductionOn generalizing before with
  | pure value =>
      rw [LazyPrivate.run_pure, mem_support_pure_iff] at hr
      subst result
      exact absurd hx hnew
  | query_bind input next ih =>
      obtain ⟨hinput, htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp hQ
      rw [LazyPrivate.run_bind, mem_support_bind_iff] at hr
      obtain ⟨step, hstep, htailResult⟩ := hr
      by_cases hs : step.2.2 x = none
      · exact ih step.1 (htail step.1) step.2 htailResult hs
      · exact hinput x (query_new_public input before step hstep x hx hs)

theorem allQueriesSatisfy_mono {α : Type} (program : M α) (P Q : T3.Spec.Domain → Prop)
    (hPQ : ∀ q, P q → Q q) (h : AllQueriesSatisfy program P) : AllQueriesSatisfy program Q := by
  induction program using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind input next ih =>
      obtain ⟨hi, hn⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hi, fun u => ih u (hn u)⟩

/-! ## The signer's digest rows -/

/-- A digest row of message `m` (counter below `2^32`). -/
def DigestRowOf (x : HashInput) (m : Message) : Prop :=
  ∃ p : Digest × Fin (2 ^ 32), x = Sampling.digestTrial p.1 m p.2.val

/-- The signer's public queries: non-digest, or digest rows of the request's message. -/
def SignerQ (m : Message) : T3.Spec.Domain → Prop :=
  fun q => ∀ x, q = .inl (.inr x) → IsDigestInput x → DigestRowOf x m

theorem notDigestQ_signerQ (m : Message) (q : T3.Spec.Domain) (h : BPB.NotDigestQ q) : SignerQ m q := by
  intro x hq ⟨rho, m', c, hx⟩
  subst hq
  exfalso
  have := BPB.hdrTag_digestInput rho m' c
  rw [← hx] at this
  exact h this

theorem digestTrial_rowOf (rho : Digest) (m : Message) (c : Nat) (hc : c < 2 ^ 32) :
    DigestRowOf (Sampling.digestTrial rho m c) m := ⟨(rho, ⟨c, hc⟩), rfl⟩

theorem digestSearch_signerQ (rho : Digest) (m : Message) :
    ∀ fuel counter, counter + fuel ≤ 2 ^ 32 → AllQueriesSatisfy (digestSearch rho m counter fuel) (SignerQ m) := by
  intro fuel
  induction fuel with
  | zero => intro counter _; exact SourceQueries.pure_allowed _ _
  | succ fuel ih =>
      intro counter hlimit
      rw [BPB.digestSearch_succ]
      apply SourceQueries.bind_allowed
      · apply (allQueriesSatisfy_query_iff _ _).mpr
        intro x hx _
        simp only [Sum.inl.injEq, Sum.inr.injEq] at hx
        rw [← hx]
        exact digestTrial_rowOf rho m counter (by omega)
      · intro answer
        split
        · exact SourceQueries.pure_allowed _ _
        · exact ih (counter + 1) (by omega)

theorem authenticatedRecord_signerQ (published : T3.Cache) (request : Request) :
    AllQueriesSatisfy (FullGame.authenticatedRecord published request) (SignerQ request.message) := by
  unfold FullGame.authenticatedRecord
  apply SourceQueries.bind_allowed
  · apply SourceQueries.privateMac_allowed (SignerQ request.message)
    intro tweak x hx
    cases hx
  · intro tag
    split
    · unfold payloadRecord payloadRecordForNonce
      apply SourceQueries.bind_allowed
      · unfold privateNonce
        apply SourceQueries.bind_allowed
        · apply (allQueriesSatisfy_query_iff _ _).mpr
          intro x hx
          cases hx
        · intro _; exact SourceQueries.pure_allowed _ _
      · intro rho
        apply SourceQueries.bind_allowed _ (digestSearch_signerQ rho request.message attemptLimit 0 (by decide))
        intro found
        split
        · exact SourceQueries.pure_allowed _ _
        · apply SourceQueries.bind_allowed
          · exact allQueriesSatisfy_mono _ _ _ (notDigestQ_signerQ request.message)
              (BPB.payloadAfterDigest_ok _ _ _)
          · intro _; exact SourceQueries.pure_allowed _ _
    · exact SourceQueries.pure_allowed _ _

/-- New digest rows created by a signing request are rows of its message. -/
theorem signer_new_rows (published : T3.Cache) (request : Request) (before : LazyPrivate.State)
    (result : (Option Signature × Option HashOutput) × LazyPrivate.State)
    (hr : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published request) before))
    (x : HashInput) (hx : before.2 x = none) (hnew : result.2.2 x ≠ none) (hdig : IsDigestInput x) :
    DigestRowOf x request.message :=
  run_new_public _ (fun x => IsDigestInput x → DigestRowOf x request.message)
    (allQueriesSatisfy_mono _ _ _ (fun q hq x hx => hq x hx) (authenticatedRecord_signerQ published request))
    before result hr x hx hnew hdig

/-! ## The reuse potential -/


theorem digestRowOf_unique {x : HashInput} {m m' : Message} (h : DigestRowOf x m) (h' : DigestRowOf x m') :
    m = m' := by
  obtain ⟨p, rfl⟩ := h
  obtain ⟨p', hp'⟩ := h'
  have he := Sampling.pad64_inj_of_length (by simp [digestInput, SphincsSecurity.bytesLE_length]) hp'
  exact (digestInput_injective he).2.1

theorem tsum_indicator_le_of_subsingleton {β : Type} (P : β → Prop) [DecidablePred P]
    (hP : ∀ a b, P a → P b → a = b)
    (c : ENNReal) : (∑' b, if P b then c else 0) ≤ c := by
  by_cases h : ∃ b, P b
  · obtain ⟨b0, hb0⟩ := h
    rw [tsum_eq_single b0 (fun b hb => if_neg (fun hP' => hb (hP b b0 hP' hb0)))]
    simp [hb0]
  · push Not at h
    simp [h]

theorem admissibleEntry_cacheQuery (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (y : HashInput) :
    admissibleEntry (cache.cacheQuery x a) y = admissibleEntry cache y + if y = x then admInd a else 0 := by
  by_cases hy : y = x
  · subst hy
    simp [admissibleEntry, hx, admInd]
  · simp [admissibleEntry, hy]

theorem reuseMass_cacheQuery_le (cache : Sampling.RCache) (x : HashInput) (a : HashOutput)
    (hx : cache x = none) (m : Message) :
    reuseMass (cache.cacheQuery x a) m ≤ reuseMass cache m + (if DigestRowOf x m then admInd a else 0) / 2 ^ 128 := by
  unfold reuseMass
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  simp_rw [admissibleEntry_cacheQuery cache x a hx]
  rw [ENNReal.tsum_add]
  apply add_le_add le_rfl
  by_cases hrow : DigestRowOf x m
  · rw [if_pos hrow]
    apply tsum_indicator_le_of_subsingleton
    intro p q hp hq
    exact Sampling.WeightedSelection.digest_nonce_trials_injective m (2 ^ 32) le_rfl (hp.trans hq.symm)
  · rw [if_neg hrow]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    rw [if_neg]
    intro he
    exact hrow ⟨p, he.symm⟩

/-- **The reuse potential**: cached admissible digest rows of messages whose nonce is still uncached. -/
noncomputable def reusePotential (s : LazyPrivate.State) : ENNReal :=
  ∑' m : Message, if s.1 (.inr (.inl m)) = none then reuseMass s.2 m else 0

/-- A fresh public row adds at most its admissibility indicator. -/
theorem reusePotential_public_le (s : LazyPrivate.State) (x : HashInput) (a : HashOutput) (hx : s.2 x = none) :
    reusePotential (s.1, s.2.cacheQuery x a) ≤ reusePotential s + admInd a / 2 ^ 128 := by
  unfold reusePotential
  calc
    (∑' m : Message, if s.1 (.inr (.inl m)) = none then reuseMass (s.2.cacheQuery x a) m else 0) ≤
        ∑' m : Message, ((if s.1 (.inr (.inl m)) = none then reuseMass s.2 m else 0) +
          (if DigestRowOf x m then admInd a / 2 ^ 128 else 0)) := by
      apply ENNReal.tsum_le_tsum
      intro m
      split_ifs with h1 h2
      · simpa [ENNReal.div_eq_inv_mul, h2] using reuseMass_cacheQuery_le s.2 x a hx m
      · simpa [h2] using reuseMass_cacheQuery_le s.2 x a hx m
      · exact bot_le
      · exact bot_le
    _ = _ + _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl (tsum_indicator_le_of_subsingleton _ (fun _ _ h h' => digestRowOf_unique h h') _)

/-- A fresh signing of `m` removes the reuse mass of `m` and changes nothing else. -/
theorem reusePotential_sign_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) = none) (hm' : s'.1 (.inr (.inl m)) ≠ none)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → reuseMass s'.2 m' = reuseMass s.2 m') :
    reusePotential s' + reuseMass s.2 m ≤ reusePotential s := by
  unfold reusePotential
  rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite m (f := fun m' =>
    if s.1 (.inr (.inl m')) = none then reuseMass s.2 m' else 0)]
  simp only [hm', if_false, zero_add, hm, if_true]
  rw [add_comm]
  apply add_le_add le_rfl
  apply le_of_eq
  apply tsum_congr
  intro m'
  by_cases he : m' = m
  · simp [he]
  · simp only [he, if_false, hother m' he, hrows m' he]

/-- A non-fresh signing does not raise the reuse potential (`m`'s nonce is cached throughout, or nothing public
is added). -/
theorem reusePotential_sign_stale_le (s s' : LazyPrivate.State) (m : Message)
    (hm : s.1 (.inr (.inl m)) ≠ none → s'.1 (.inr (.inl m)) ≠ none)
    (hnone : s.1 (.inr (.inl m)) = none → s'.1 (.inr (.inl m)) = none ∧ reuseMass s'.2 m = reuseMass s.2 m)
    (hother : ∀ m', m' ≠ m → s'.1 (.inr (.inl m')) = s.1 (.inr (.inl m')))
    (hrows : ∀ m', m' ≠ m → reuseMass s'.2 m' = reuseMass s.2 m') :
    reusePotential s' ≤ reusePotential s := by
  unfold reusePotential
  apply ENNReal.tsum_le_tsum
  intro m'
  by_cases he : m' = m
  · subst he
    by_cases hc : s.1 (.inr (.inl m')) = none
    · obtain ⟨h1, h2⟩ := hnone hc
      simp [h1, h2, hc]
    · simp [hm hc, hc]
  · simp only [hother m' he, hrows m' he, le_refl]

end SigGolfCandidate.T3.Security.CaseC
