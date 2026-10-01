import SigGolfCandidate.SphincsSecurity.Completeness.Code
import SigGolfCandidate.SphincsSecurity.Completeness.Search
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingSelection

/-!
# What one encoding trial rejects

Conditional-half selection gives every accepted digest exactly `63/32` times its
ordinary truncation mass. Together with the target-186 count, this preserves the
conservative success lower bound `1 / codeShare` used by the completeness tail.
-/

open Finset ENNReal OracleComp

namespace SphincsSecurity.Completeness

open TargetSum

variable {lay : Layer}

/-- The ordinary low-half share, retained as a digest-counting helper only. -/
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

/-- The actual raw-query decoder has exactly the `63/32` selected acceptance share. -/
theorem probEvent_selected_accept :
    Pr[fun u : HashOutput => (decodeDigest lay (selectEncodingDigest u)).isSome |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (63 / 32 : ℝ≥0∞) *
        (((univ.filter fun d : Digest => (decodeDigest lay d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞)) := by
  have hpad : ∀ d ∈ (univ.filter fun d : Digest => (decodeDigest lay d).isSome),
      (d.getLsbD 63 || d.getLsbD 127) = false := by
    intro d hd
    have hd' := (mem_filter.mp hd).2
    unfold decodeDigest at hd'
    split at hd'
    · rename_i hp
      exact Bool.or_eq_false_iff.mpr ⟨hp.1, hp.2.1⟩
    · simp at hd'
  simpa only [mem_filter, mem_univ, true_and] using
    EncodingSelection.prob_select_mem_of_padding
      (univ.filter fun d : Digest => (decodeDigest lay d).isSome) hpad

/-- One selected trial rejects at most `1 - 1 / codeShare` of raw answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest lay (selectEncodingDigest out)) + (codeShare : ℝ≥0∞)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest lay d).isSome).card = n := ⟨_, rfl⟩
  have hnat : 32 * (2 : Nat) ^ 128 ≤ (63 * codeShare) * accepted :=
    haccepted ▸ digests_le_codeShare_mul_card_accepting
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcompl := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (decodeDigest lay (selectEncodingDigest u)).isSome)
  have hreject : Pr[fun u : HashOutput => ¬ (decodeDigest lay (selectEncodingDigest u)).isSome = true |
      ($ᵗ HashOutput : ProbComp HashOutput)]
      = failMass (fun out => decodeDigest lay (selectEncodingDigest out)) := by
    rw [failMass_eq_probEvent]
    apply probEvent_congr'
    · intro u _
      cases decodeDigest lay (selectEncodingDigest u) <;> simp
    · rfl
  have hfail : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by simp
  rw [hreject, probEvent_selected_accept, hfail, tsub_zero, hcard, haccepted] at hcompl
  have hshare : (codeShare : ℝ≥0∞)⁻¹ ≤
      (63 / 32 : ℝ≥0∞) * ((accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) := by
    apply (ENNReal.toReal_le_toReal (by norm_num [codeShare]) (by finiteness)).mp
    have hnatR : (32 : ℝ) * 2 ^ 128 ≤ (63 * (codeShare : ℝ)) * accepted := by
      exact_mod_cast hnat
    simp only [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    norm_num [codeShare] at hnatR ⊢
    linarith
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

/-- A common rejection envelope for both admitted layer targets. -/
noncomputable def encodingFactor : ℝ≥0∞ := 2407 / 2408

theorem encodingFactor_room : encodingFactor + (codeShare : ℝ≥0∞)⁻¹ = 1 := by
  change (2407 : ℝ≥0∞) / 2408 + (2408 : ℝ≥0∞)⁻¹ = 1
  have hq : (2407 : ℝ≥0∞) / 2408 ≠ ⊤ := ENNReal.div_ne_top (by simp) (by norm_num)
  have hi : (2408 : ℝ≥0∞)⁻¹ ≠ ⊤ := by simp
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hq, hi⟩) (by simp),
    ENNReal.toReal_add hq hi, ENNReal.toReal_div, ENNReal.toReal_inv]
  norm_num

theorem failMass_encoding_le :
    failMass (fun out => decodeDigest lay (selectEncodingDigest out)) ≤ encodingFactor := by
  apply (ENNReal.add_le_add_iff_right (a := (codeShare : ℝ≥0∞)⁻¹) (by simp [codeShare])).mp
  rw [encodingFactor_room]
  exact failMass_encoding_add_le

end SphincsSecurity.Completeness
