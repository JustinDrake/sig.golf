import SigGolfCandidate.T3.Secc.WeightedSelection

namespace SigGolfCandidate.T3.Security.LazyPrivate
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open Sampling.WeightedSelection
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- Preserve every selected-leaf payoff through the real payload continuation;
later payload failure can only decrease its expected contribution. -/
theorem payloadForNonce_weight_le (cache : T3.Cache) (rho : Digest) (message : Message)
    (state : State) (weight : HashOutput → ENNReal) :
    expectedValue (run (payloadRecordForNonce cache rho message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
        (fun result => result.1.elim 0 (fun found => weight found.2)) := by
  rw [payloadRecordForNonce, run_bind, expectedValue_bind, run_digestSearch, expectedValue_map]
  apply expectedValue_mono
  intro result
  cases result.1 with
  | none => simp only [run_pure, expectedValue_pure, Option.elim_none, le_refl]
  | some found =>
      rcases found with ⟨counter, output⟩
      simp only [run_bind, expectedValue_bind, run_pure, expectedValue_pure, Option.elim_some]
      apply expectedValue_le_of_le
      intro signature
      exact le_rfl

/-- Freshness is a property of the actual private cache. The nonce is sampled
by the source program, rather than assumed as independent external input. -/
theorem payload_weight_le (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message)) = none) (weight : HashOutput → ENNReal) :
    expectedValue (run (payloadRecord cache message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      freshPrice weight + cacheWeight Sampling.digestDecode weight state.2 / (2 : ENNReal)^128 := by
  rw [payloadRecord, run_bind, run_privateNonce_fresh message state hfresh]
  simp only [bind_assoc, pure_bind, expectedValue_bind]
  calc
    _ ≤ expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output =>
        expectedValue (Sampling.roRun 0
          (digestSearch (output.extractLsb' 0 128) message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2))) :=
      expectedValue_mono _ fun output => payloadForNonce_weight_le cache _ message
        (state.1.cacheQuery (.inr (.inl message)) output, state.2) weight
    _ = expectedValue ($ᵗ Digest : ProbComp Digest) (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2))) :=
      uniform_hash_low_expectation (fun rho =>
        expectedValue (Sampling.roRun 0 (digestSearch rho message 0 attemptLimit) state.2)
          (fun result => result.1.elim 0 (fun found => weight found.2)))
    _ ≤ _ := by
      rw [← expectedValue_bind]
      exact uniform_nonce_digest_weight_le 0 message attemptLimit (by decide) state.2 weight

/-- Leaf-dependent selection bound for the real authenticated signer, including
the MAC gate and later payload failure. Cached nonce requests are handled by
the separate reuse/journal case; this lemma is the fresh-request kernel. -/
theorem signing_weight_le (cache : T3.Cache) (message : Message) (state : State)
    (hfresh : state.1 (.inr (.inl message)) = none) (weight : HashOutput → ENNReal) :
    expectedValue (run (signingRecord cache message) state)
      (fun result => result.1.2.elim 0 weight) ≤
      freshPrice weight + cacheWeight Sampling.digestDecode weight state.2 / (2 : ENNReal)^128 := by
  rw [signingRecord, run_bind, expectedValue_bind]
  apply expectedValue_le_of_support
  intro result hresult
  have hp := privateMac_preserves_nonce cache.region message state result hresult
  split_ifs with htag
  · simp only [run_pure, expectedValue_pure, Option.elim_none]
    exact bot_le
  · have h := payload_weight_le cache message result.2 (hp.1.trans hfresh) weight
    rw [hp.2] at h
    exact h

end SigGolfCandidate.T3.Security.LazyPrivate
