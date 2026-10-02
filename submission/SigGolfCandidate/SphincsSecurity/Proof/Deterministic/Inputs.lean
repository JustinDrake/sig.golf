import SigGolfCandidate.SphincsSecurity.Proof.Seeded.KeyDerivation
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.SeedHitProbability

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem randomizerHashInput_injective {p₁ p₂ : PublicParameter} {s : MasterSeed}
    {m₁ m₂ : Message} {a₁ a₂ : BitVec 32}
    (h : randomizerHashInput p₁ s m₁ a₁ = randomizerHashInput p₂ s m₂ a₂) :
    m₁ = m₂ ∧ a₁ = a₂ := by
  unfold randomizerHashInput at h
  obtain ⟨hprefix, ha⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨_, hm⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hm, bytesLE_injective ha⟩

private theorem tag_append (left right : HashInput) (h : 2 ≤ left.length) :
    (left ++ right).getD 1 0 = left.getD 1 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega : 1 < left.length)]

private theorem tag_fieldBytes (fields : TweakFields) :
    (fieldBytes fields).getD 1 0 = UInt8.ofBitVec fields.tag := by
  simp only [fieldBytes, bytesLE, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

private theorem tag_randomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    (randomizerHashInput parameter seed message trial).getD 1 0 = 7 := by
  simp [randomizerHashInput, List.getD_eq_getElem?_getD]

private theorem tag_keygen (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    (keygenHashInput parameter domain seed).getD 1 0 =
      UInt8.ofBitVec (keygenDomainFields domain).tag := by
  simp only [keygenHashInput]
  rw [tag_append _ _ (by simp [fieldBytes, bytesLE_length])]
  rw [tag_append _ _ (by simp [fieldBytes, bytesLE_length])]
  exact tag_fieldBytes _

theorem tag_tweakable (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).getD 1 0 =
      UInt8.ofBitVec (hashDomainFields domain).tag := by
  simp only [tweakableHashInput, tweakBytes]
  rw [tag_append _ _ (by simp [fieldBytes, bytesLE_length])]
  rw [tag_append _ _ (by simp [fieldBytes, bytesLE_length])]
  exact tag_fieldBytes _

theorem randomizerHashInput_ne_keygenHashInput (p₁ p₂ : PublicParameter)
    (s₁ s₂ : MasterSeed) (message : Message) (trial : BitVec 32) (domain : KeygenDomain) :
    randomizerHashInput p₁ s₁ message trial ≠ keygenHashInput p₂ domain s₂ := by
  intro h
  have htag := congrArg (fun x : HashInput => x.getD 1 0) h
  rw [tag_randomizer, tag_keygen] at htag
  have hne : UInt8.ofBitVec (keygenDomainFields domain).tag ≠ 7 := by
    cases domain <;> dsimp [keygenDomainFields, tweakFields] <;> decide
  exact hne htag.symm

theorem randomizerHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter)
    (seed : MasterSeed) (message : Message) (trial : BitVec 32)
    (domain : HashDomain) (payload : HashInput) :
    randomizerHashInput p₁ seed message trial ≠ tweakableHashInput p₂ domain payload := by
  intro h
  have htag := congrArg (fun x : HashInput => x.getD 1 0) h
  rw [tag_randomizer, tag_tweakable] at htag
  have hne : UInt8.ofBitVec (hashDomainFields domain).tag ≠ 7 := by
    cases domain <;> dsimp [hashDomainFields, tweakFields] <;> decide
  exact hne htag.symm

/-- A seed-derived query contains either the whole seed at the legacy position, or the
26-byte seed prefix used by the one-block randomizer domain. -/
def DerivationSeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (input.drop 32).take 32 = bytesLE 32 seed ∨
    input.take 28 = [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208)

theorem derivationSeedHit_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    DerivationSeedHit (keygenHashInput parameter domain seed) seed := by
  apply Or.inl
  simp [keygenHashInput, fieldBytes, bytesLE]

theorem derivationSeedHit_randomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    DerivationSeedHit (randomizerHashInput parameter seed message trial) seed := by
  apply Or.inr
  simp [randomizerHashInput, bytesLE_length]

theorem probEvent_derivationSeedHit_le (input : HashInput) :
    Pr[DerivationSeedHit input | sampleMasterSeed] ≤ 1 / ((2 ^ 207 : Nat) : ℝ≥0∞) := by
  change Pr[(fun seed => (input.drop 32).take 32 = bytesLE 32 seed ∨
    input.take 28 = [1, 7] ++ bytesLE 26 (seed.extractLsb' 0 208)) | sampleMasterSeed] ≤ _
  exact (probEvent_or_le _ _ _).trans
    ((add_le_add (full_bound input) (prefix_bound input)).trans numeric_bound)

end SphincsSecurity
