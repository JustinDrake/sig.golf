import SigGolfCandidate.SphincsSecurity.Completeness.Game
import SigGolfCandidate.SphincsSecurity.Completeness.Signing
import SigGolfCandidate.SphincsSecurity.Completeness.Keygen
import SigGolfCandidate.SphincsSecurity.Completeness.PairedDigest

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

Paired randomizer trials give digest failure at most `2⁻⁴¹⁹`. The mixed counter targets
give failure at most `2⁻⁵²⁹`. Their union over all `2²⁵⁶` messages is at most `2⁻¹²⁸`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

theorem digestFactor_pow_le : pairedDigestFactor ^ digestPairLimit ≤ (2⁻¹ : ℝ≥0∞) ^ 419 := by
  have hp : digestReject + (3410 : ℝ≥0∞)⁻¹ ≤ 1 :=
    (add_le_add (le_refl digestReject) (show (3410 : ℝ≥0∞)⁻¹ ≤ (2142 : ℝ≥0∞)⁻¹ by norm_num)).trans digestReject_add
  have hroom : pairedDigestFactor + ((1706 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 :=
    paired_digest_room digestReject hp
  have hhalf := pow_le_half_1706_1250 pairedDigestFactor hroom
  have hone : pairedDigestFactor ≤ 1 := le_trans le_self_add hroom
  calc pairedDigestFactor ^ digestPairLimit ≤ pairedDigestFactor ^ (1250 * 419) :=
        pow_le_pow_right_of_le_one' hone (by rw [digestPairLimit]; norm_num)
    _ = (pairedDigestFactor ^ 1250) ^ 419 := pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 419 := pow_le_pow_left₀ (by positivity) hhalf _

theorem encoding_pow_le : encodingBound ≤ (2⁻¹ : ℝ≥0∞) ^ 529 := by
  have hroom : encodingFactor + (codeShare : ℝ≥0∞)⁻¹ ≤ 1 := encodingFactor_room.le
  have hhalf := pow_le_half_2822_1980 encodingFactor hroom
  have hone : encodingFactor ≤ 1 :=
    le_trans le_self_add hroom
  rw [encodingBound]
  calc encodingFactor ^ encodingAttemptLimit
        ≤ encodingFactor ^ (1980 * 529) :=
          pow_le_pow_right_of_le_one' hone (by rw [encodingAttemptLimit]; norm_num)
    _ = (encodingFactor ^ 1980) ^ 529 :=
          pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 529 := pow_le_pow_left₀ (by positivity) hhalf _

/-- Key generation then signing fails only if one of signing's six searches does. -/
theorem probEvent_signedWithKeys_none (seed : MasterSeed) (message : Message) :
    Pr[fun r => r.1.2 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signedWithKeys seed message)).run ∅]
      ≤ pairedDigestFactor ^ digestPairLimit + (numLayers : ℝ≥0∞) * encodingBound := by
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

/-- One message fails from a fixed seed with probability at most `2⁻⁴¹⁹ + 5 · 2⁻⁵²⁹`. -/
theorem seeded_failure_le (seed : MasterSeed) (message : Message) :
    Pr[= false | seededExperiment seed message]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 419 + 5 * (2⁻¹ : ℝ≥0∞) ^ 529 := by
  rw [seededExperiment_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
  refine ((probEvent_honest_false_le seed message).trans
    (probEvent_signedWithKeys_none seed message)).trans ?_
  refine add_le_add digestFactor_pow_le ?_
  rw [show ((numLayers : Nat) : ℝ≥0∞) = 5 by norm_num [numLayers]]
  exact mul_le_mul_right encoding_pow_le _

/-- **Per-seed completeness.** From every master seed, the scheme is `2⁻¹²⁸`-complete. -/
theorem complete_seeded : SphincsSeededCompletenessStatement := by
  intro seed
  calc
    ∑' message : Message, Pr[= false | seededExperiment seed message]
        ≤ ∑' _message : Message, ((2⁻¹ : ℝ≥0∞) ^ 419 + 5 * (2⁻¹ : ℝ≥0∞) ^ 529) :=
          ENNReal.tsum_le_tsum fun message => seeded_failure_le seed message
    _ = (2 : ℝ≥0∞) ^ 256 * ((2⁻¹ : ℝ≥0∞) ^ 419 + 5 * (2⁻¹ : ℝ≥0∞) ^ 529) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := paired_closing_sum

/-- **Completeness.** Averaging the per-seed bound over the sampled seed: the scheme is
`2⁻¹²⁸`-complete. -/
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
    _ ≤ ∑' seed : MasterSeed, Pr[= seed | sampleMasterSeed] * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun seed => mul_le_mul' le_rfl (complete_seeded seed)
    _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Completeness
