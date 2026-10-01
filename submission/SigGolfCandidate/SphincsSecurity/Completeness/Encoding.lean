import SigGolfCandidate.SphincsSecurity.Completeness.Code
import SigGolfCandidate.SphincsSecurity.Completeness.Search
import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingSelection

/-!
# What one encoding trial rejects

Conditional-half selection gives every accepted digest exactly `3/2` times its
ordinary truncation mass. Together with the target-183 count, this preserves the
conservative success lower bound `1 / codeShare` used by the completeness tail.
-/

open Finset ENNReal OracleComp

namespace SphincsSecurity.Completeness

open TargetSum

/-- The ordinary low-half share, retained as a digest-counting helper only. -/
theorem probEvent_accept :
    Pr[fun u : HashOutput => (decodeDigest (truncateHash u)).isSome |
        ($ᵗ HashOutput : ProbComp HashOutput)]
      = ((univ.filter fun d : Digest => (decodeDigest d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show Fintype.card Digest = 2 ^ digestBits by simp, Nat.cast_pow, Nat.cast_ofNat,
    ← probEvent_truncateHash_mem (univ.filter fun d : Digest => (decodeDigest d).isSome)]
  apply probEvent_congr'
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rfl

/-- The actual raw-query decoder has exactly the `3/2` selected acceptance share. -/
theorem probEvent_selected_accept :
    Pr[fun u : HashOutput => (decodeDigest (selectEncodingDigest u)).isSome |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (3 / 2 : ℝ≥0∞) *
        (((univ.filter fun d : Digest => (decodeDigest d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞)) := by
  have hpad : ∀ d ∈ (univ.filter fun d : Digest => (decodeDigest d).isSome),
      d.getLsbD 63 = false := by
    intro d hd
    have hd' := (mem_filter.mp hd).2
    unfold decodeDigest at hd'
    split at hd'
    · rename_i hp
      exact hp.1
    · simp at hd'
  simpa only [mem_filter, mem_univ, true_and] using
    EncodingSelection.prob_select_mem_of_padding
      (univ.filter fun d : Digest => (decodeDigest d).isSome) hpad

/-- One selected trial rejects at most `1 - 1 / codeShare` of raw answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest (selectEncodingDigest out)) + (codeShare : ℝ≥0∞)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest d).isSome).card = n := ⟨_, rfl⟩
  have hnat : 2 * (2 : Nat) ^ 128 ≤ (3 * codeShare) * accepted :=
    haccepted ▸ digests_le_codeShare_mul_card_accepting
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcompl := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => (decodeDigest (selectEncodingDigest u)).isSome)
  have hreject : Pr[fun u : HashOutput => ¬ (decodeDigest (selectEncodingDigest u)).isSome = true |
      ($ᵗ HashOutput : ProbComp HashOutput)]
      = failMass (fun out => decodeDigest (selectEncodingDigest out)) := by
    rw [failMass_eq_probEvent]
    apply probEvent_congr'
    · intro u _
      cases decodeDigest (selectEncodingDigest u) <;> simp
    · rfl
  have hfail : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by simp
  rw [hreject, probEvent_selected_accept, hfail, tsub_zero, hcard, haccepted] at hcompl
  have hshare : (codeShare : ℝ≥0∞)⁻¹ ≤
      (3 / 2 : ℝ≥0∞) * ((accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) := by
    apply (ENNReal.toReal_le_toReal (by norm_num [codeShare]) (by finiteness)).mp
    have hnatR : (2 : ℝ) * 2 ^ 128 ≤ (3 * (codeShare : ℝ)) * accepted := by
      exact_mod_cast hnat
    simp only [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    norm_num [codeShare] at hnatR ⊢
    linarith
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

end SphincsSecurity.Completeness
