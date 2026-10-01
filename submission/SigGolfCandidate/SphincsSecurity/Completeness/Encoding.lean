import SigGolfCandidate.SphincsSecurity.Completeness.Code
import SigGolfCandidate.SphincsSecurity.Completeness.Search
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform

/-!
# What one encoding trial rejects

A trial keeps the low `128` bits of a uniform answer, and that truncation is uniform on digests
(`probEvent_truncateHash_mem`). So one trial accepts exactly as often as a uniform digest decodes,
which by `Code.lean` is at least one trial in `codeShare`.
-/

open Finset ENNReal OracleComp

namespace SphincsSecurity.Completeness

open TargetSum

variable {lay : Layer}

/-- The accepted share is the code's size over the digest space. -/
theorem probEvent_accept :
    Pr[fun u : HashOutput => (decodeDigest lay (truncateHash u)).isSome |
        ($ᵗ HashOutput : ProbComp HashOutput)]
      = ((univ.filter fun d : Digest => (decodeDigest lay d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show Fintype.card Digest = 2 ^ digestBits by simp, Nat.cast_pow, Nat.cast_ofNat,
    ← probEvent_truncateHash_mem (univ.filter fun d : Digest => (decodeDigest lay d).isSome)]
  apply probEvent_congr'
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rfl

/-- One trial rejects at most `1 - 1 / codeShare` of the answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest lay (truncateHash out)) + (codeShare : ℝ≥0∞)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest lay d).isSome).card = n := ⟨_, rfl⟩
  have hnat : (2 : Nat) ^ 128 ≤ codeShare * accepted :=
    haccepted ▸ digests_le_codeShare_mul_card_accepting
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcompl := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (decodeDigest lay (truncateHash u)).isSome)
  have hreject : Pr[fun u : HashOutput => ¬ (decodeDigest lay (truncateHash u)).isSome = true |
      ($ᵗ HashOutput : ProbComp HashOutput)]
      = failMass (fun out => decodeDigest lay (truncateHash out)) := by
    rw [failMass_eq_probEvent]
    apply probEvent_congr'
    · intro u _
      cases decodeDigest lay (truncateHash u) <;> simp
    · rfl
  have hfail : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by simp
  rw [hreject, probEvent_accept, hfail, tsub_zero, hcard, haccepted] at hcompl
  have hshare : (codeShare : ℝ≥0∞)⁻¹ ≤ (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)),
      ENNReal.inv_mul_le_iff (by simp [codeShare]) (by simp)]
    exact_mod_cast hnat
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

/-- A common rejection envelope for both admitted layer targets. -/
noncomputable def encodingFactor : ℝ≥0∞ := 2821 / 2822

theorem encodingFactor_room : encodingFactor + (codeShare : ℝ≥0∞)⁻¹ = 1 := by
  change (2821 : ℝ≥0∞) / 2822 + (2822 : ℝ≥0∞)⁻¹ = 1
  have hq : (2821 : ℝ≥0∞) / 2822 ≠ ⊤ := ENNReal.div_ne_top (by simp) (by norm_num)
  have hi : (2822 : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hq, hi⟩) (by simp),
    ENNReal.toReal_add hq hi, ENNReal.toReal_div, ENNReal.toReal_inv]
  norm_num

theorem failMass_encoding_le :
    failMass (fun out => decodeDigest lay (truncateHash out)) ≤ encodingFactor := by
  apply (ENNReal.add_le_add_iff_right (a := (codeShare : ℝ≥0∞)⁻¹) (by simp [codeShare])).mp
  rw [encodingFactor_room]
  exact failMass_encoding_add_le

end SphincsSecurity.Completeness
