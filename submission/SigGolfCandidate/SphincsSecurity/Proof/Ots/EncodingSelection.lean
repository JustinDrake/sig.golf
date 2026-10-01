import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingProbability

/-!
# Encoding-only conditional half selection

Either padding bit (63 or 127) of the low half selects the high half when set. The
two contributions are counted before decoding: every padding-clear digest has
`2^128 + 3 * 2^126` preimages,
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

@[simp] theorem truncateHash_getLsbD_127 (a : HashOutput) :
    (truncateHash a).getLsbD 127 = a.getLsbD 127 := by
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
      if ((truncateHash a).getLsbD 63 || (truncateHash a).getLsbD 127) then
        a.extractLsb' 128 digestBits else truncateHash a := by
  simp only [selectEncodingDigest, selectEncodingAnswer, truncateHash_getLsbD_63,
    truncateHash_getLsbD_127]
  split <;> simp only [truncateHash_shiftRight_128]

namespace EncodingSelection

/-- Each value of the top bit occurs in half of the 64-bit words. -/
theorem card_half_padding_set (b : Bool) :
    (univ.filter fun d : BitVec 64 => d.getLsbD 63 = b).card = 2 ^ 63 := by
  have hbit : (univ.filter fun d : BitVec 1 => d.getLsbD 0 = b).card = 1 := by
    cases b <;> decide
  have h64 := card_filter_high (n := 64) (w := 63) (by decide)
    (fun d : BitVec (64 - 63) => d.getLsbD 0 = b)
  simpa only [BitVec.getLsbD_extractLsb', show (0 : Nat) < 64 - 63 by decide,
    decide_true, Bool.true_and, Nat.add_zero, hbit, mul_one] using h64

set_option linter.constructorNameAsVariable false in
/-- Exactly three quarters of the low digests select the upper half. -/
theorem card_selector_set :
    (univ.filter fun d : Digest => (d.getLsbD 63 || d.getLsbD 127) = true).card =
      3 * 2 ^ 126 := by
  classical
  let A : Finset (BitVec 64) := univ.filter fun d => d.getLsbD 63 = false
  let B : Finset (BitVec 64) := univ.filter fun d => d.getLsbD 63 = true
  have hsplit := card_filter_splitBits (n := 128) (w := 64) (by decide)
    (fun p => (p.1.getLsbD 63 || p.2.getLsbD 63) = true)
  have hpre :
      (univ.filter fun d : Digest => (d.getLsbD 63 || d.getLsbD 127) = true) =
        (univ.filter fun d : BitVec 128 =>
          ((splitBits 128 64 d).1.getLsbD 63 ||
            (splitBits 128 64 d).2.getLsbD 63) = true) := by
    ext d
    simp only [mem_filter, mem_univ, true_and, splitBits, BitVec.getLsbD_extractLsb']
    norm_num only
    simp only [decide_true, Bool.true_and]
  have hpairs :
      (univ.filter fun p : BitVec 64 × BitVec 64 =>
        (p.1.getLsbD 63 || p.2.getLsbD 63) = true) =
          (B ×ˢ univ) ∪ (A ×ˢ B) := by
    ext p
    cases hl : p.1.getLsbD 63 <;> cases hh : p.2.getLsbD 63 <;>
      simp only [A, B, mem_filter, mem_univ, true_and, mem_union, mem_product, hl, hh] <;>
      simp
  have hdisj : Disjoint (B ×ˢ (univ : Finset (BitVec 64))) (A ×ˢ B) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [A, B, mem_product, mem_filter, mem_univ, true_and, and_true] at hp hq
    have ht : p.1.getLsbD 63 = true := hp
    have hf : p.1.getLsbD 63 = false := hq.1
    exact Bool.noConfusion (hf.symm.trans ht)
  rw [hpre, hsplit, hpairs, card_union_of_disjoint hdisj, card_product, card_product]
  simp only [A, B, card_univ, Fintype.card_bitVec, card_half_padding_set]
  norm_num

set_option linter.constructorNameAsVariable false in
/-- The two disjoint branches of the selector, counted for an arbitrary target set. -/
theorem card_select_mem (targets : Finset Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (targets.filter fun d => (d.getLsbD 63 || d.getLsbD 127) = false).card * 2 ^ 128 +
        (3 * 2 ^ 126) * targets.card := by
  classical
  let B : Finset Digest := univ.filter fun d => (d.getLsbD 63 || d.getLsbD 127) = true
  let A : Finset Digest := targets.filter fun d => (d.getLsbD 63 || d.getLsbD 127) = false
  have hsplit := card_filter_splitBits (n := 256) (w := 128) (by decide)
    (fun p => (if (p.1.getLsbD 63 || p.1.getLsbD 127) then p.2 else p.1) ∈ targets)
  have hpre :
      (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets) =
        (univ.filter fun a : BitVec 256 =>
          (if ((splitBits 256 128 a).1.getLsbD 63 ||
              (splitBits 256 128 a).1.getLsbD 127) then
            (splitBits 256 128 a).2 else (splitBits 256 128 a).1) ∈ targets) := by
    ext a
    simp only [mem_filter, mem_univ, true_and]
    change selectEncodingDigest a ∈ targets ↔
      (if ((splitBits 256 128 a).1.getLsbD 63 ||
          (splitBits 256 128 a).1.getLsbD 127) then
        (splitBits 256 128 a).2 else (splitBits 256 128 a).1) ∈ targets
    rw [selectEncodingDigest_eq]
    rfl
  have hpairs :
      (univ.filter fun p : Digest × Digest =>
        (if (p.1.getLsbD 63 || p.1.getLsbD 127) then p.2 else p.1) ∈ targets) =
          (A ×ˢ univ) ∪ (B ×ˢ targets) := by
    ext p
    cases hb : (p.1.getLsbD 63 || p.1.getLsbD 127) <;>
      simp only [A, B, mem_filter, mem_univ, true_and, mem_union, mem_product, hb] <;>
      simp
  have hdisj : Disjoint (A ×ˢ (univ : Finset Digest)) (B ×ˢ targets) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [A, B, mem_product, mem_filter, mem_univ, true_and, and_true] at hp hq
    have hf : (p.1.getLsbD 63 || p.1.getLsbD 127) = false := hp.2
    have ht : (p.1.getLsbD 63 || p.1.getLsbD 127) = true := hq.1
    exact Bool.noConfusion (hf.symm.trans ht)
  rw [hpre, hsplit, hpairs, card_union_of_disjoint hdisj, card_product, card_product]
  simp only [A, B, card_univ, Fintype.card_bitVec, card_selector_set, digestBits]

/-- Padding-clear sets get precisely the `7/4` acceptance multiplier. -/
theorem card_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, d.getLsbD 63 = false ∧ d.getLsbD 127 = false) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a ∈ targets).card =
      (2 ^ 128 + 3 * 2 ^ 126) * targets.card := by
  rw [card_select_mem, filter_eq_self.mpr (by
    intro d hd
    obtain ⟨hl, hh⟩ := hpad d hd
    simp only [hl, hh, Bool.false_or])]
  ring

theorem prob_select_mem_of_padding (targets : Finset Digest)
    (hpad : ∀ d ∈ targets, d.getLsbD 63 = false ∧ d.getLsbD 127 = false) :
    Pr[fun a : HashOutput => selectEncodingDigest a ∈ targets |
      ($ᵗ HashOutput : ProbComp HashOutput)] =
        (7 / 4 : ENNReal) * ((targets.card : ENNReal) / (Fintype.card Digest : ENNReal)) := by
  rw [probEvent_uniform, card_select_mem_of_padding targets hpad]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_ofNat, Fintype.card_bitVec]
  norm_num [hashOutputBits, digestBits]
  <;> ring

/-- The largest selector fiber has seven quarter-digest spaces. -/
theorem card_select_eq_le (target : Digest) :
    (univ.filter fun a : HashOutput => selectEncodingDigest a = target).card ≤
      2 ^ 128 + 3 * 2 ^ 126 := by
  have h := card_select_mem ({target} : Finset Digest)
  simp only [mem_singleton, card_singleton, mul_one] at h
  rw [h]
  have hc : (({target} : Finset Digest).filter fun d =>
      (d.getLsbD 63 || d.getLsbD 127) = false).card ≤ 1 :=
    (card_filter_le _ _).trans_eq (card_singleton _)
  nlinarith

theorem prob_select_eq_le (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤
        (7 / 4 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [probEvent_uniform]
  calc
    _ ≤ ((2 ^ 128 + 3 * 2 ^ 126 : Nat) : ENNReal) / 2 ^ hashOutputBits :=
      ENNReal.div_le_div_right (by exact_mod_cast card_select_eq_le target) _
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [hashOutputBits, digestBits, ENNReal.toReal_mul, ENNReal.toReal_div,
        ENNReal.toReal_inv, ENNReal.toReal_pow]

theorem prob_select_eq_le_pmf (target : Digest) :
    Pr[fun a : HashOutput => selectEncodingDigest a = target | PMF.uniformOfFintype HashOutput] ≤
      (7 / 4 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [probEvent_eq_tsum_ite, probOutput_uniformSample, PMF.probOutput_eq_apply,
    PMF.uniformOfFintype_apply] using prob_select_eq_le target

end EncodingSelection
end SphincsSecurity
