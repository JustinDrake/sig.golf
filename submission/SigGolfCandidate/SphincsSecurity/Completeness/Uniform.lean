import VCVio.OracleComp.Constructions.SampleableType
import SigGolfCandidate.SphincsSecurity.Completeness.Octopus.Tuples
import SigGolfCandidate.SphincsSecurity.Scheme

section


namespace SphincsSecurity.Completeness.Octopus
open OracleComp Finset ENNReal
theorem card_bitVec_filter' (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]
theorem probEvent_uniform_toNat' (P : ℕ → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter', Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]
theorem admissibleTuples_eq :
    Nat.factorial 15 * Nadm = 768394439706066703645522769421343549971302651574651715584000 := by
  unfold Nadm; norm_num [Nat.factorial]
theorem admissibleTuples_bounds :
    2 ^ 210 ≤ 2142 * (Nat.factorial 15 * Nadm) ∧ 2141 * (Nat.factorial 15 * Nadm) ≤ 2 ^ 210 ∧
      2 ^ 198 ≤ Nat.factorial 15 * Nadm := by
  rw [admissibleTuples_eq]; norm_num
theorem probEvent_admissibleDigest :
    Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [probEvent_uniform_toNat' (fun N => admissible N = true), card_admissibleDigests]
  have e : (2 : ℝ≥0∞) ^ 256 = 2 ^ 46 * 2 ^ 210 := by rw [← pow_add]
  rw [e, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]
theorem probEvent_not_admissibleDigest :
    Pr[fun u : BitVec 256 => ¬ admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => admissible u.toNat = true)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_admissibleDigest]
theorem admissibleProb_ge :
    (1 : ℝ≥0∞) / 2142 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_div,
    ← ENNReal.div_eq_inv_mul]
  apply ENNReal.div_le_of_le_mul
  have h := admissibleTuples_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProb_le :
    ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 ≤ (1 : ℝ≥0∞) / 2141 := by
  rw [ENNReal.div_le_iff (by simp) (by simp), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleTuples_bounds.2.1
  rw [mul_comm] at h
  exact_mod_cast h
theorem admissibleProb_ge_two_pow :
    (1 : ℝ≥0∞) / 2 ^ 12 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 :=
  le_trans (ENNReal.div_le_div_left (by norm_num) 1) admissibleProb_ge
theorem probEvent_admissibleDigest_ge :
    (1 : ℝ≥0∞) / 2 ^ 12 ≤ Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  rw [probEvent_admissibleDigest]; exact admissibleProb_ge_two_pow
end SphincsSecurity.Completeness.Octopus
end

section


open OracleComp ENNReal Finset
namespace SphincsSecurity.Completeness
def splitBits (n w : Nat) (x : BitVec n) : BitVec w × BitVec (n - w) :=
  (x.extractLsb' 0 w, x.extractLsb' w (n - w))
theorem splitBits_injective {n w : Nat} (hw : w ≤ n) : Function.Injective (splitBits n w) := by
  intro x y h
  simp only [splitBits, Prod.mk.injEq] at h
  obtain ⟨hlow, hhigh⟩ := h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hiw : i < w
  · have := congrArg (fun b : BitVec w => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hiw] using this
  · have := congrArg (fun b : BitVec (n - w) => b.getLsbD (i - w)) hhigh
    simpa [BitVec.getLsbD_extractLsb', show i - w < n - w by omega,
      show w + (i - w) = i by omega] using this
theorem splitBits_bijective {n w : Nat} (hw : w ≤ n) : Function.Bijective (splitBits n w) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨splitBits_injective hw, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr 1
  omega
theorem card_filter_splitBits {n w : Nat} (hw : w ≤ n) (P : BitVec w × BitVec (n - w) → Prop)
    [DecidablePred P] :
    (univ.filter fun x : BitVec n => P (splitBits n w x)).card = (univ.filter P).card := by
  refine Finset.card_bij (fun x _ => splitBits n w x) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact splitBits_injective hw h
  · intro p hp
    obtain ⟨x, hx⟩ := (splitBits_bijective hw).2 p
    exact ⟨x, by simpa [hx] using hp, hx⟩
theorem card_filter_low {n w : Nat} (hw : w ≤ n) (Q : BitVec w → Prop) [DecidablePred Q] :
    (univ.filter fun x : BitVec n => Q (x.extractLsb' 0 w)).card
      = (univ.filter Q).card * 2 ^ (n - w) := by
  have h := card_filter_splitBits hw (fun p => Q p.1)
  rw [show (univ.filter fun p : BitVec w × BitVec (n - w) => Q p.1) = (univ.filter Q) ×ˢ univ by
      ext p; simp, Finset.card_product, Finset.card_univ, Fintype.card_bitVec] at h
  exact h
theorem card_filter_low' {n w : Nat} (hw : w ≤ n) (P : BitVec n → Prop) [DecidablePred P]
    (Q : BitVec w → Prop) [DecidablePred Q] (hPQ : ∀ x, P x ↔ Q (x.extractLsb' 0 w)) :
    (univ.filter P).card = (univ.filter Q).card * 2 ^ (n - w) := by
  rw [Finset.filter_congr (fun x _ => hPQ x)]
  exact card_filter_low hw Q
theorem card_filter_high {n w : Nat} (hw : w ≤ n) (Q : BitVec (n - w) → Prop) [DecidablePred Q] :
    (univ.filter fun x : BitVec n => Q (x.extractLsb' w (n - w))).card
      = 2 ^ w * (univ.filter Q).card := by
  have h := card_filter_splitBits hw (fun p => Q p.2)
  rw [show (univ.filter fun p : BitVec w × BitVec (n - w) => Q p.2) = univ ×ˢ (univ.filter Q) by
      ext p; simp, Finset.card_product, Finset.card_univ, Fintype.card_bitVec] at h
  exact h
theorem probEvent_uniform (P : HashOutput → Prop) [DecidablePred P] :
    Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]
      = ((univ.filter P).card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ hashOutputBits := by
  rw [probEvent_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]
theorem probEvent_truncateHash_mem (targets : Finset Digest) :
    Pr[fun u : HashOutput => truncateHash u ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)]
      = (targets.card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ digestBits := by
  rw [probEvent_uniform]
  have hcard := card_filter_low' (n := hashOutputBits) (w := digestBits) (by decide)
    (fun u : HashOutput => truncateHash u ∈ targets) (fun d => d ∈ targets) (fun _ => Iff.rfl)
  rw [Finset.filter_univ_mem] at hcard
  have hsplit : (2 : ℝ≥0∞) ^ hashOutputBits = 2 ^ digestBits * 2 ^ (hashOutputBits - digestBits) := by
    rw [← pow_add]; congr 1
  rw [hcard, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hsplit,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]
theorem sortedLeaves_eq_sortLeaves (leaves : IndexGroup → FtsLeaf) :
    Concrete.sortedLeaves leaves = Octopus.sortLeaves (Octopus.valList leaves) := by
  unfold Concrete.sortedLeaves Concrete.sortedSlots Octopus.sortLeaves Octopus.valList
  rw [List.ofFn_eq_map]
  exact List.map_insertionSort (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val)
    (fun a b : Nat => a ≤ b) _ _ (fun _ _ _ _ => Iff.rfl)
theorem valList_digestLeaves (d : MessageDigest) :
    Octopus.valList (Concrete.digestLeaves d) = Octopus.leavesOf d.toNat := by
  unfold Octopus.valList Octopus.leavesOf Octopus.leafOf Concrete.digestLeaves
  apply List.ext_getElem (by simp [ftsOpenings])
  intro r h1 _
  simp [Nat.shiftRight_eq_div_pow, totalHeight, ftsTreeHeight]
theorem admissible_iff (u : HashOutput) :
    Concrete.Admissible (truncateMessageDigest u) ↔ Octopus.admissible u.toNat = true := by
  have htrunc : (truncateMessageDigest u).toNat = u.toNat := by
    simp [truncateMessageDigest, messageDigestBits, hashOutputBits]
    exact Nat.mod_eq_of_lt u.isLt
  unfold Concrete.Admissible Concrete.AdmissibleLeaves Octopus.admissible
  rw [sortedLeaves_eq_sortLeaves, valList_digestLeaves, htrunc, ← Octopus.valList_nodup,
    valList_digestLeaves, htrunc]
  simp [ftsAuthCapacity]
theorem probEvent_admissible_ge :
    (2142 : ℝ≥0∞)⁻¹ ≤ Pr[fun u : HashOutput => Concrete.Admissible (truncateMessageDigest u) |
      ($ᵗ HashOutput : ProbComp HashOutput)] := by
  calc
    _ ≤ ((Nat.factorial 15 * Octopus.Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
      simpa only [one_div] using Octopus.admissibleProb_ge
    _ = Pr[fun u : BitVec 256 => Octopus.admissible u.toNat = true |
        ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := Octopus.probEvent_admissibleDigest.symm
    _ = _ := probEvent_congr' (fun u _ => (admissible_iff u).symm) rfl
end SphincsSecurity.Completeness
end
