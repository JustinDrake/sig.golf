import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.KeyDerivation

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
theorem prefix_bound (input : HashInput) :
    Pr[fun seed : MasterSeed => input.take 28 = [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208) |
      sampleMasterSeed] ≤ 1 / ((2 ^ 208 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ low : BitVec 208, input.take 28 = [1, 7] ++ bytesLE 26 low
  · obtain ⟨low, hlow⟩ := hexists
    have hevent : (fun seed : MasterSeed =>
        input.take 28 = [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208)) =
        (fun seed => seed.extractLsb' 0 208 = low) := by
      funext seed
      apply propext
      constructor
      · intro h
        have hp : [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208) = [1, 7] ++ bytesLE 26 low :=
          h.symm.trans hlow
        exact bytesLE_injective (by simpa using hp)
      · intro h
        rw [h]
        exact hlow
    rw [hevent]
    have hsample : sampleMasterSeed = ($ᵗ HashOutput : ProbComp HashOutput) := rfl
    have hdistr : 𝒮[(fun seed : MasterSeed => seed.extractLsb' 0 208) <$> sampleMasterSeed] =
        𝒮[($ᵗ BitVec 208 : ProbComp (BitVec 208))] := by
      rw [hsample]
      exact evalDist_hashOutput_extract_uniform (by decide : 208 ≤ hashOutputBits)
    change Pr[(fun output => output = low) ∘ (fun seed : MasterSeed => seed.extractLsb' 0 208) |
      sampleMasterSeed] ≤ _
    rw [← probEvent_map]
    rw [probEvent_congr' (fun _ _ => Iff.rfl) hdistr]
    rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]
    simp [Fintype.card_bitVec]
  · have hempty : (fun seed : MasterSeed =>
        input.take 28 = [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208)) =
        (fun _ => False) := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed.extractLsb' 0 208, h⟩, False.elim⟩
    rw [hempty]
    simp
theorem full_bound (input : HashInput) :
    Pr[fun seed : MasterSeed => (input.drop 32).take 32 = bytesLE 32 seed |
      sampleMasterSeed] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ seed, (input.drop 32).take 32 = bytesLE 32 seed
  · obtain ⟨seed, hseed⟩ := hexists
    have hevent : (fun other : MasterSeed => (input.drop 32).take 32 = bytesLE 32 other) =
        (fun other => other = seed) := by
      funext other
      exact propext ⟨fun h => bytesLE_injective (h.symm.trans hseed), fun h => h ▸ hseed⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed]
  · have hempty : (fun seed : MasterSeed => (input.drop 32).take 32 = bytesLE 32 seed) =
        (fun _ => False) := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed, h⟩, False.elim⟩
    rw [hempty]
    simp
theorem numeric_bound :
    1 / ((2 ^ 256 : Nat) : ℝ≥0∞) + 1 / ((2 ^ 208 : Nat) : ℝ≥0∞) ≤
      1 / ((2 ^ 207 : Nat) : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add, ENNReal.toReal_div]
end SphincsSecurity
