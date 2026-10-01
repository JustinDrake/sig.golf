import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability

/-!
# Encoding-only conditional half selection

Bit 63 of the low half selects the high half when set. The two contributions are
counted before decoding: every padding-clear digest has `2^128 + 2^127` preimages,
and no digest has more. Nothing here changes the ordinary hash truncation law.
-/

namespace SphincsSecurity

open OracleComp ENNReal Finset
open Completeness

set_option allowUnsafeReducibility true in
attribute [local reducible] hashOutputBits digestBits

set_option maxRecDepth 4096

@[simp] theorem truncateHash_getLsbD_63 (a : HashOutput) :
    (truncateHash a).getLsbD 63 = a.getLsbD 63 := by
  simp [truncateHash, BitVec.getLsbD_extractLsb', digestBits]

theorem truncateHash_shiftRight_128 (a : HashOutput) :
    truncateHash (a >>> 128) = a.extractLsb' 128 digestBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiRaw : i < hashOutputBits := lt_trans hi (by decide)
  simp [truncateHash, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    hi, hiRaw, Nat.add_comm]

theorem selectEncodingDigest_eq (a : HashOutput) :
    selectEncodingDigest a =
      if (truncateHash a).getLsbD 63 then a.extractLsb' 128 digestBits else truncateHash a := by
  simp only [selectEncodingDigest, selectEncodingAnswer, truncateHash_getLsbD_63]
  split <;> simp only [truncateHash_shiftRight_128]

namespace EncodingSelection

/-- Exactly half of the low digests select the upper half. -/
theorem card_selector_set :
    (univ.filter fun d : Digest => d.getLsbD 63 = true).card = 2 ^ 127 := by
  have hbit : (univ.filter fun b : BitVec 1 => b.getLsbD 0 = true).card = 1 := by decide
  have h64 := card_filter_high (n := 64) (w := 63) (by decide)
    (fun b : BitVec (64 - 63) => b.getLsbD 0 = true)
  simp only [BitVec.getLsbD_extractLsb', show (0 : Nat) < 64 - 63 by decide,
    decide_true, Bool.true_and, Nat.add_zero, hbit, mul_one] at h64
  have h128 := card_filter_low' (n := 128) (w := 64) (by decide)
    (fun d : BitVec 128 => d.getLsbD 63 = true)
    (fun d : BitVec 64 => d.getLsbD 63 = true) (by
      intro d
      simp [BitVec.getLsbD_extractLsb'])
  rw [h64] at h128
  norm_num at h128 ⊢
  exact h128

set_option linter.constructorNameAsVariable false in
/-- The two disjoint branches of the selector, counted for an arbitrary target set. -/
theorem card_select_mem (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (targets.filter fun d => d.getLsbD 63 = false).card * 2 ^ 128 +
        2 ^ 127 * targets.card := by
  classical
  let B : Finset Digest := univ.filter fun d => d.getLsbD 63 = true
  let A : Finset Digest := targets.filter fun d => d.getLsbD 63 = false
  have hsplit := card_filter_splitBits (n := 256) (w := 128) (by decide)
    (fun p => (if p.1.getLsbD 63 then p.2 else p.1) ∈ targets)
  have hpre :
      (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets) =
        (univ.filter fun a : BitVec 256 =>
          (if (splitBits 256 128 a).1.getLsbD 63 then
            (splitBits 256 128 a).2 else (splitBits 256 128 a).1) ∈ targets) := by
    ext a
    simp only [mem_filter, mem_univ, true_and]
    change selectEncodingDigest a ∈ targets ↔
      (if (splitBits 256 128 a).1.getLsbD 63 then
        (splitBits 256 128 a).2 else (splitBits 256 128 a).1) ∈ targets
    rw [selectEncodingDigest_eq]
    rfl
  have hpairs :
      (univ.filter fun p : Digest × Digest =>
        (if p.1.getLsbD 63 then p.2 else p.1) ∈ targets) =
          (A ×ˢ univ) ∪ (B ×ˢ targets) := by
    ext p
    cases hb : p.1.getLsbD 63 <;> simp [A, B, hb]
  have hdisj : Disjoint (A ×ˢ (univ : Finset Digest)) (B ×ˢ targets) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [A, B, mem_product, mem_filter, mem_univ, true_and, and_true] at hp hq
    have hf : p.1.getLsbD 63 = false := hp.2
    have ht : p.1.getLsbD 63 = true := hq.1
    exact Bool.noConfusion (hf.symm.trans ht)
  rw [hpre, hsplit, hpairs, card_union_of_disjoint hdisj, card_product, card_product]
  simp only [A, B, card_univ, Fintype.card_bitVec, card_selector_set, digestBits]

/-- Padding-clear sets get precisely the `3/2` acceptance multiplier. -/
theorem card_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, d.getLsbD 63 = false) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (2 ^ 128 + 2 ^ 127) * targets.card := by
  rw [card_select_mem, filter_eq_self.mpr hpad]
  ring

theorem prob_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, d.getLsbD 63 = false) :
    Pr[fun a : HashOutput => selectEncodingDigest a ∈ targets |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
        (3 / 2 : ENNReal) * ((targets.card : ENNReal) / (Fintype.card Digest : ENNReal)) := by
  rw [probEvent_uniform, card_select_mem_of_padding targets hpad]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_ofNat, Fintype.card_bitVec]
  norm_num [hashOutputBits, digestBits]
  <;> ring

/-- The largest selector fiber has three half-digest spaces. -/
theorem card_select_eq_le (target : Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a = target).card ≤
      2 ^ 128 + 2 ^ 127 := by
  have h := card_select_mem ({target} : Finset Digest)
  simp only [mem_singleton, card_singleton, mul_one] at h
  rw [h]
  have hc : (({target} : Finset Digest).filter fun d => d.getLsbD 63 = false).card ≤ 1 :=
    (card_filter_le _ _).trans_eq (card_singleton _)
  nlinarith

theorem prob_select_eq_le (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
        (3 / 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [probEvent_uniform]
  calc
    _ ≤ ((2 ^ 128 + 2 ^ 127 : Nat) : ENNReal) / 2 ^ hashOutputBits :=
      ENNReal.div_le_div_right (by exact_mod_cast card_select_eq_le target) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [hashOutputBits, digestBits, ENNReal.toReal_mul, ENNReal.toReal_div,
        ENNReal.toReal_inv, ENNReal.toReal_pow]

theorem prob_select_eq_le_pmf (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target | PMF.uniformOfFintype HashOutput] ≤
      (3 / 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply] using prob_select_eq_le target

end EncodingSelection
end SphincsSecurity
