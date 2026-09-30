import SigGolfCandidate.SphincsSecurity.Completeness.Game
import SigGolfCandidate.SphincsSecurity.Completeness.Signing
import SigGolfCandidate.SphincsSecurity.Completeness.Keygen
import SigGolfCandidate.SphincsSecurity.Completeness.Decay

/-!
# Completeness

The proofs of the claims of `Completeness.lean`. Correctness is `Game.correct`, which reads
`verify_of_sign` of `Recovery.lean` off key generation. For completeness:

`Game.lean` pulls the seed out of the experiment and, through recovery, charges failure to signing
returning `none`. `Keygen.lean` shows key generation leaves every input a later search hashes
uncached, and caches its MAC query with the tag it returns, so the signer's MAC check is a cache hit
that passes. `Signing.lean` charges a signing failure to its six searches: the randomizer search
(`Digest.lean`) and the five counter searches (`Counter.lean`, with the code's size from `Code.lean`
and `Encoding.lean`). Each search is long enough that its failure decays exponentially
(`Decay.lean`), which is what closes the bound below. Nothing in the bound depends on the seed, so it
holds for every seed (`complete_seeded`), and averaging over the seed gives `complete`.

The numbers: digest admissibility has probability at least `1/2142`; after the collision allowance
`2²⁰/2¹²⁸`, a randomizer trial still succeeds with probability at least `1/2143`. Each block of
`1500` trials halves the failure probability, and `2²⁰ ≥ 1500 · 699` gives failure at most
`2⁻⁶⁹⁹`. A counter trial accepts at least one in `codeShare = 2397` of the `2¹²⁸` digests, so
`2²² ≥ 2397 · 1749` counters all fail with probability at most `2⁻¹⁷⁴⁹`. Over `2²⁵⁶` messages,
`2²⁵⁶ · (2⁻⁶⁹⁹ + 5 · 2⁻¹⁷⁴⁹) ≤ 2⁻²⁵⁶`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

theorem digestFactor_pow_le : digestFactor ^ digestAttemptLimit ≤ (2⁻¹ : ℝ≥0∞) ^ 699 := by
  have hroom : digestFactor + ((2143 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 :=
    digest_room digestReject digestReject_add
  have hhalf := pow_le_half_2143_1500 digestFactor hroom
  have hone : digestFactor ≤ 1 := le_trans le_self_add hroom
  calc digestFactor ^ digestAttemptLimit ≤ digestFactor ^ (1500 * 699) :=
        pow_le_pow_right_of_le_one' hone (by rw [digestAttemptLimit]; norm_num)
    _ = (digestFactor ^ 1500) ^ 699 := pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 699 := pow_le_pow_left₀ (by positivity) hhalf _

theorem encoding_pow_le : encodingBound ≤ (2⁻¹ : ℝ≥0∞) ^ 1749 := by
  have hroom := failMass_encoding_add_le
  have hhalf := pow_le_half_ennreal codeShare (by decide) _ hroom
  have hone : failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ≤ 1 :=
    le_trans le_self_add hroom
  rw [encodingBound]
  calc failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit
        ≤ failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ (codeShare * 1749) :=
          pow_le_pow_right_of_le_one' hone (by rw [encodingAttemptLimit, codeShare]; norm_num)
    _ = (failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ codeShare) ^ 1749 :=
          pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 1749 := pow_le_pow_left₀ (by positivity) hhalf _

/-- Key generation then signing fails only if one of signing's six searches does. -/
theorem probEvent_signedWithKeys_none (seed : MasterSeed) (message : Message) :
    Pr[fun r => r.1.2 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signedWithKeys seed message)).run ∅]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * encodingBound := by
  rw [signedWithKeys]
  refine probEvent_bind_le _ _ _ ∅ _ (fun r hr => ?_)
  obtain ⟨hrand, hmsg, henc⟩ := keygen_fresh seed r hr message
  have hmac := keygen_mac_cached seed r hr
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ r.2 0 ?_) ?_
  · rintro ⟨result, c⟩ _ hsome
    obtain ⟨signature, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp
  · rw [add_zero]
    exact probEvent_sign_none r.1.2.2 r.1.2.1 message r.2 hmac hrand hmsg henc

/-- One message fails from a fixed seed with probability at most `2⁻¹⁰²³ + 5 · 2⁻¹⁷⁴⁹`. -/
theorem seeded_failure_le (seed : MasterSeed) (message : Message) :
    Pr[= false | seededExperiment seed message]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 699 + 5 * (2⁻¹ : ℝ≥0∞) ^ 1749 := by
  rw [seededExperiment_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
  refine ((probEvent_honest_false_le seed message).trans
    (probEvent_signedWithKeys_none seed message)).trans ?_
  refine add_le_add digestFactor_pow_le ?_
  rw [show ((numLayers : Nat) : ℝ≥0∞) = 5 by norm_num [numLayers]]
  exact mul_le_mul_right encoding_pow_le _

/-- **Per-seed completeness.** From every master seed, the scheme is `2⁻²⁵⁶`-complete. -/
theorem complete_seeded : SphincsSeededCompletenessStatement := by
  intro seed
  calc
    ∑' message : Message, Pr[= false | seededExperiment seed message]
        ≤ ∑' _message : Message, ((2⁻¹ : ℝ≥0∞) ^ 699 + 5 * (2⁻¹ : ℝ≥0∞) ^ 1749) :=
          ENNReal.tsum_le_tsum fun message => seeded_failure_le seed message
    _ = (2 : ℝ≥0∞) ^ 256 * ((2⁻¹ : ℝ≥0∞) ^ 699 + 5 * (2⁻¹ : ℝ≥0∞) ^ 1749) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := closing_sum

/-- **Completeness.** Averaging the per-seed bound over the sampled seed: the scheme is
`2⁻²⁵⁶`-complete. -/
theorem complete : SphincsCompletenessStatement := by
  calc
    ∑' message : Message, Pr[= false | experiment message]
        = ∑' message : Message, ∑' seed : MasterSeed,
            Pr[= seed | sampleMasterSeed] * Pr[= false | seededExperiment seed message] := by
          refine tsum_congr fun message => ?_
          rw [experiment_eq, probOutput_bind_eq_tsum]
    _ = ∑' seed : MasterSeed, Pr[= seed | sampleMasterSeed]
          * ∑' message : Message, Pr[= false | seededExperiment seed message] := by
          rw [ENNReal.tsum_comm]
          exact tsum_congr fun seed => ENNReal.tsum_mul_left
    _ ≤ ∑' seed : MasterSeed, Pr[= seed | sampleMasterSeed] * ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun seed => mul_le_mul' le_rfl (complete_seeded seed)
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Completeness
