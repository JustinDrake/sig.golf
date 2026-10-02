import SigGolfCandidate.T3.Secc.CaseCForecast

/-!
# Stream CC: the fresh signing kernel (selection law of an actual signing request)

For a fresh-nonce published signing request, the selected digest is the first admissible fresh trial of the
digest search from the actual nonce. For any weight `w` of the selection whose fresh accepted price
(`freshPrice w = E_{accepted}[w]`) is at most `P`, and any exhaustion payoff `≤ P`:

* `search_le_price` / `digestSearch_le_price`: the search alone (previously cached *rejected* trials are skipped);
* `payloadForNonce_le_price`: the payload after the selection does not change the selected digest;
* `Reuse` / `reuseMass`: the cache-reuse exception (an admissible cached trial of the request's message under the
  sampled nonce) has probability at most `reuseMass`, the cached admissible digest rows of the message / 2^128;
* `fresh_signing_kernel`: the whole authenticated signing record (MAC query, fresh nonce, search, payload) obeys
  `E[F] ≤ P + reuseMass` for every payoff `F` dominated by `1` on reuse and by `sel.elim P w` otherwise.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
open SphincsSecurity.Completeness (searchLoop failMass)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-! ## The rejection search with an exhaustion payoff -/

theorem search_le_price {β γ : Type} (secret : BitVec 256) (inputs : Nat → HashInput)
    (decoder : HashOutput → Option β) (result : Nat → β → γ) (payoff : γ → ENNReal) (weight : β → ENNReal)
    (hweight : ∀ counter value, payoff (result counter value) = weight value)
    (base price : ENNReal) (hbase : base ≤ price)
    (hstep : Sampling.acceptedWeight decoder weight + failMass decoder * price ≤ price) (bound : Nat)
    (hinj : ∀ left right, left < bound → right < bound → inputs left = inputs right → left = right) :
    ∀ fuel counter, counter + fuel ≤ bound → ∀ cache : Sampling.RCache,
      Sampling.CachedTrialsReject inputs decoder counter bound cache →
      expectedValue (Sampling.roRun secret
        (Sampling.publicProgram (searchLoop inputs decoder (fun c v => pure (result c v)) fuel counter)) cache)
        (fun output => output.1.elim base payoff) ≤ price := by
  intro fuel
  induction fuel with
  | zero =>
      intro counter _ cache _
      simpa [searchLoop, Sampling.publicProgram] using hbase
  | succ fuel ih =>
      intro counter hlimit cache hcache
      rw [Sampling.publicSearch_succ, Sampling.roRun_bind, Sampling.roRun_publicQuery, expectedValue_bind]
      cases hc : cache (inputs counter) with
      | some answer =>
          have hd := hcache counter le_rfl (by omega) answer hc
          rw [randomOracle.run_eq, hc]
          simp only [expectedValue_pure, hd]
          exact ih (counter + 1) (by omega) cache
            (fun c hstart hbound answer ha => hcache c (by omega) hbound answer ha)
      | none =>
          rw [Sampling.expectedValue_fresh _ _ hc]
          calc
            _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
                (fun answer => (decoder answer).elim price weight) := by
              apply expectedValue_mono
              intro answer
              cases hd : decoder answer with
              | some value => simp [hweight]
              | none =>
                  apply ih (counter + 1) (by omega) _
                  intro c hstart hbound output ho
                  have hne : inputs c ≠ inputs counter := by
                    intro he
                    have hh := hinj c counter hbound (by omega) he
                    omega
                  have hh : cache (inputs c) = some output :=
                    (QueryCache.cacheQuery_of_ne cache answer hne).symm.trans ho
                  exact hcache c (by omega) hbound output hh
            _ = Sampling.acceptedWeight decoder weight + failMass decoder * price :=
              Sampling.uniform_decoder_weight decoder weight price
            _ ≤ price := hstep

/-- The fresh-price fixed point of the digest decoder. -/
theorem digest_step_le (w : HashOutput → ENNReal) (P : ENNReal)
    (hP : Sampling.WeightedSelection.freshPrice w ≤ P) :
    Sampling.acceptedWeight Sampling.digestDecode w + failMass Sampling.digestDecode * P ≤ P := by
  have hfix := Sampling.WeightedSelection.freshPrice_step w
  calc
    _ ≤ Sampling.acceptedWeight Sampling.digestDecode w + failMass Sampling.digestDecode * P := le_rfl
    _ = acceptanceProbability * Sampling.WeightedSelection.freshPrice w +
        (1 - acceptanceProbability) * P := by
      have hw : Sampling.acceptedWeight Sampling.digestDecode w =
          acceptanceProbability * Sampling.WeightedSelection.freshPrice w := by
        unfold Sampling.WeightedSelection.freshPrice
        rw [div_eq_mul_inv, mul_comm, mul_assoc,
          ENNReal.inv_mul_cancel Sampling.WeightedSelection.acceptanceProbability_ne_zero
            Sampling.WeightedSelection.acceptanceProbability_ne_top, mul_one]
      rw [Sampling.digest_failMass, hw]
    _ ≤ acceptanceProbability * P + (1 - acceptanceProbability) * P :=
      add_le_add (mul_le_mul' le_rfl hP) le_rfl
    _ = P := by
      rw [← add_mul, add_tsub_cancel_of_le Sampling.digest_acceptanceProbability_le_one, one_mul]

theorem digestSearch_le_price (secret : BitVec 256) (rho : Digest) (message : Message)
    (fuel : Nat) (hlimit : fuel ≤ 2 ^ 32) (cache : Sampling.RCache)
    (hreject : Sampling.CachedTrialsReject (Sampling.digestTrial rho message) Sampling.digestDecode 0 (2 ^ 32) cache)
    (w : HashOutput → ENNReal) (base P : ENNReal) (hbase : base ≤ P)
    (hP : Sampling.WeightedSelection.freshPrice w ≤ P) :
    expectedValue (Sampling.roRun secret (digestSearch rho message 0 fuel) cache)
      (fun result => result.1.elim base (fun found => w found.2)) ≤ P := by
  rw [Sampling.digestSearch_public]
  exact search_le_price secret (Sampling.digestTrial rho message) Sampling.digestDecode
    (fun c output => (BitVec.ofNat 32 c, output)) (fun found => w found.2) w (fun _ _ => rfl) base P hbase
    (digest_step_le w P hP) (2 ^ 32)
    (fun _ _ hl hr he => Sampling.digestTrial_injective rho message hl hr he) fuel 0 (by omega) cache hreject

/-- The payload after the digest selection leaves the selected digest unchanged. -/
theorem payloadForNonce_le_search (cache : T3.Cache) (rho : Digest) (message : Message)
    (state : LazyPrivate.State) (w : HashOutput → ENNReal) (base : ENNReal) :
    expectedValue (LazyPrivate.run (payloadRecordForNonce cache rho message) state)
      (fun result => result.1.2.elim base w) ≤
    expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
      (fun result => result.1.elim base (fun found => w found.2)) := by
  rw [payloadRecordForNonce, LazyPrivate.run_bind, expectedValue_bind, LazyPrivate.run_digestSearch,
    expectedValue_map]
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

/-! ## The cache-reuse exception -/

/-- Some cached trial of `(rho, m)` below `2^32` is admissible: the signer would reuse a cached row. -/
def Reuse (cache : Sampling.RCache) (rho : Digest) (m : Message) : Prop :=
  ¬Sampling.CachedTrialsReject (Sampling.digestTrial rho m) Sampling.digestDecode 0 (2 ^ 32) cache

/-- An admissible cached answer at an input (0/1). -/
noncomputable def admissibleEntry (cache : Sampling.RCache) (input : HashInput) : ENNReal :=
  (cache input).elim 0 (fun answer => if admissible (selections answer) = true then 1 else 0)

/-- Cached admissible digest rows of message `m` (all nonces, counters below `2^32`), over `2^128`. -/
noncomputable def reuseMass (cache : Sampling.RCache) (m : Message) : ENNReal :=
  (∑' p : Digest × Fin (2 ^ 32), admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val)) / 2 ^ 128

theorem reuse_indicator_le (cache : Sampling.RCache) (rho : Digest) (m : Message) :
    (if Reuse cache rho m then (1 : ENNReal) else 0) ≤
      ∑ c : Fin (2 ^ 32), admissibleEntry cache (Sampling.digestTrial rho m c.val) := by
  split_ifs with h
  · unfold Reuse Sampling.CachedTrialsReject at h
    push Not at h
    obtain ⟨c, -, hc, answer, ha, hd⟩ := h
    have hadm : admissible (selections answer) = true := by
      unfold Sampling.digestDecode at hd
      by_contra hn
      exact hd (by simp [hn])
    calc
      (1 : ENNReal) = admissibleEntry cache (Sampling.digestTrial rho m (⟨c, hc⟩ : Fin (2 ^ 32)).val) := by
        simp [admissibleEntry, ha, hadm]
      _ ≤ _ := Finset.single_le_sum (f := fun c : Fin (2 ^ 32) =>
          admissibleEntry cache (Sampling.digestTrial rho m c.val)) (fun _ _ => bot_le) (Finset.mem_univ _)
  · exact bot_le

/-- **The reuse exception is rare**: a uniform nonce hits a cached admissible row with probability ≤ `reuseMass`. -/
theorem reuse_probability_le (cache : Sampling.RCache) (m : Message) :
    expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if Reuse cache rho m then 1 else 0) ≤
      reuseMass cache m := by
  rw [BPORS.expected_uniform_eq_finiteAverage]
  unfold BPORS.finiteAverage reuseMass
  simp only [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  calc
    _ ≤ ∑ rho : Digest, ∑ c : Fin (2 ^ 32), admissibleEntry cache (Sampling.digestTrial rho m c.val) :=
      Finset.sum_le_sum fun rho _ => reuse_indicator_le cache rho m
    _ = ∑' p : Digest × Fin (2 ^ 32), admissibleEntry cache (Sampling.digestTrial p.1 m p.2.val) := by
      rw [tsum_fintype, Fintype.sum_prod_type]

/-! ## The fresh signing kernel -/

/-- The nonce of `m` recorded in a private cache (low 128 bits of its answer; `0` if absent). -/
def nonceOf (state : LazyPrivate.State) (m : Message) : Digest :=
  ((state.1 (.inr (.inl m))).getD 0).extractLsb' 0 128

theorem nonceOf_cacheQuery (state : LazyPrivate.State) (m : Message) (output : HashOutput)
    (after : LazyPrivate.State)
    (hext : SourceReplay.Extends (state.1.cacheQuery (.inr (.inl m)) output, state.2) after) :
    nonceOf after m = output.extractLsb' 0 128 := by
  have h : after.1 (.inr (.inl m)) = some output := hext.1 (QueryCache.cacheQuery_self _ _ _)
  simp only [nonceOf, h, Option.getD_some]

/-- **The fresh signing kernel.** A published, fresh-nonce authenticated signing record pays at most the fresh
accepted price `P` of its selection plus the reuse mass of its message. -/
theorem fresh_signing_kernel (published : T3.Cache) (m : Message) (state : LazyPrivate.State)
    (hfresh : state.1 (.inr (.inl m)) = none)
    (F : (Option Signature × Option HashOutput) × LazyPrivate.State → ENNReal)
    (w : HashOutput → ENNReal) (P : ENNReal) (hP : Sampling.WeightedSelection.freshPrice w ≤ P)
    (hF : ∀ result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state),
      F result ≤ if Reuse state.2 (nonceOf result.2 m) m then 1 else result.1.2.elim P w) :
    expectedValue (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state) F ≤
      P + reuseMass state.2 m := by
  have hrun : LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩) state =
      LazyPrivate.run (privateMac published.region) state >>= fun mac =>
        LazyPrivate.run (payloadRecord published m) mac.2 := by
    rw [FullGame.authenticatedRecord, LazyPrivate.run_bind]
    simp only [if_true]
  rw [hrun, expectedValue_bind]
  have hmac : ∀ mac ∈ support (LazyPrivate.run (privateMac published.region) state),
      expectedValue (LazyPrivate.run (payloadRecord published m) mac.2) F ≤ P + reuseMass state.2 m := by
    intro mac hmac
    have hp := LazyPrivate.privateHash_preserves_other (.inr (.inr published.region)) (.inr (.inl m))
      (by simp) state mac hmac
    have hfresh1 : mac.2.1 (.inr (.inl m)) = none := hp.1.trans hfresh
    rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
    simp only [bind_assoc, pure_bind, expectedValue_bind]
    calc
      _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
          (if Reuse state.2 (output.extractLsb' 0 128) m then 1 else 0) + P) := by
        apply expectedValue_mono
        intro output
        set s2 : LazyPrivate.State := (mac.2.1.cacheQuery (.inr (.inl m)) output, mac.2.2) with hs2
        have hsupp : ∀ result ∈ support (LazyPrivate.run
            (payloadRecordForNonce published (output.extractLsb' 0 128) m) s2),
            F result ≤ if Reuse state.2 (output.extractLsb' 0 128) m then 1
              else result.1.2.elim P w := by
          intro result hr
          have hmem : result ∈ support (LazyPrivate.run (FullGame.authenticatedRecord published ⟨m, published⟩)
              state) := by
            rw [hrun, mem_support_bind_iff]
            refine ⟨mac, hmac, ?_⟩
            rw [payloadRecord, LazyPrivate.run_bind, LazyPrivate.run_privateNonce_fresh m mac.2 hfresh1]
            simp only [bind_assoc, pure_bind, mem_support_bind_iff]
            exact ⟨output, by simp, hr⟩
          have hn := nonceOf_cacheQuery mac.2 m output result.2
            (SourceReplay.run_extends _ s2 result hr)
          have := hF result hmem
          rwa [hn] at this
        by_cases hreuse : Reuse state.2 (output.extractLsb' 0 128) m
        · refine le_trans (expectedValue_le_of_support (c := 1) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          · simp [hreuse]
        · refine le_trans (expectedValue_mono_of_support (h := fun result => result.1.2.elim P w) ?_) ?_
          · intro result hr
            simpa [hreuse] using hsupp result hr
          calc
            expectedValue (LazyPrivate.run (payloadRecordForNonce published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P w) ≤
                expectedValue (LazyPrivate.run (payloadRecordForNonce published (output.extractLsb' 0 128) m) s2)
                (fun result => result.1.2.elim P w) := le_rfl
            _ ≤ expectedValue (Sampling.roRun 0 (digestSearch (output.extractLsb' 0 128) m 0 attemptLimit) s2.2)
                (fun result => result.1.elim P (fun found => w found.2)) :=
              payloadForNonce_le_search published _ m s2 w P
            _ ≤ P := by
              apply digestSearch_le_price 0 _ m attemptLimit (by decide) s2.2 _ w P P le_rfl hP
              have hc : s2.2 = state.2 := by rw [hs2]; exact hp.2
              rw [hc]
              exact not_not.mp hreuse
            _ ≤ _ := by simp [hreuse]
      _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho => if Reuse state.2 rho m then 1 else 0) + P := by
        rw [expectedValue_add, expectedValue_const (by simp)]
        congr 1
        exact LazyPrivate.uniform_hash_low_expectation (fun rho => if Reuse state.2 rho m then 1 else 0)
      _ ≤ reuseMass state.2 m + P := add_le_add (reuse_probability_le state.2 m) le_rfl
      _ = P + reuseMass state.2 m := add_comm _ _
  exact expectedValue_le_of_support hmac

end SigGolfCandidate.T3.Security.CaseC
