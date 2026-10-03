import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Search.TopTail

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option Elab.async false
set_option linter.unusedSimpArgs false

def pairWeight (a b : Nat) : Nat := if a < 125 ∧ b < 125 then rankWeight a + rankWeight b else 255

def pairLookup (r : Nat) : Nat := pairWeight (r % 128) (r / 128)

theorem pairLookup_components (a b : Nat) (ha : a < 128) :
    pairLookup (a + 128 * b) = pairWeight a b := by
  unfold pairLookup
  congr 1 <;> omega

theorem pairWeight_le (a b : Nat) : pairWeight a b ≤ 255 := by
  unfold pairWeight
  split_ifs
  · have := rankWeight_le a; have := rankWeight_le b; omega
  · omega

theorem pairWeight_eq (a b : Nat) (ha : a < 125) (hb : b < 125) :
    pairWeight a b = rankLookup a + rankLookup b := by simp [pairWeight,rankLookup,ha,hb]

theorem pairWeight_bad_left (a b : Nat) (ha : 125 ≤ a) : pairWeight a b = 255 := by
  simp [pairWeight,show ¬ a < 125 by omega]

theorem pairWeight_bad_right (a b : Nat) (hb : 125 ≤ b) : pairWeight a b = 255 := by
  simp [pairWeight,show ¬ b < 125 by omega]

def compressedSum (f : Nat → Nat) : Nat :=
  pairWeight (f 0) (f 1) + pairWeight (f 2) (f 3) +
  pairWeight (f 4) (f 5) + pairWeight (f 6) (f 7) + rankLookup (f 8) +
  pairWeight (f 9) (f 10) + pairWeight (f 11) (f 12) +
  pairWeight (f 13) (f 14) + pairWeight (f 15) (f 16)

def fullSum (f : Nat → Nat) : Nat := ((List.range 17).map fun i => rankLookup (f i)).sum

theorem compressedSum_good (f : Nat → Nat) (h : ∀ i, i < 17 → f i < 125) :
    compressedSum f = fullSum f := by
  unfold compressedSum
  rw [pairWeight_eq _ _ (h 0 (by decide)) (h 1 (by decide)),
      pairWeight_eq _ _ (h 2 (by decide)) (h 3 (by decide)),
      pairWeight_eq _ _ (h 4 (by decide)) (h 5 (by decide)),
      pairWeight_eq _ _ (h 6 (by decide)) (h 7 (by decide)),
      pairWeight_eq _ _ (h 9 (by decide)) (h 10 (by decide)),
      pairWeight_eq _ _ (h 11 (by decide)) (h 12 (by decide)),
      pairWeight_eq _ _ (h 13 (by decide)) (h 14 (by decide)),
      pairWeight_eq _ _ (h 15 (by decide)) (h 16 (by decide))]
  simp only [fullSum,List.range_succ,List.range_zero,List.nil_append,List.map_append,
    List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  omega

theorem compressedSum_bad (f : Nat → Nat) (i : Nat) (hi : i < 17) (hb : 125 ≤ f i) :
    255 ≤ compressedSum f := by
  unfold compressedSum
  interval_cases i
  all_goals first
    | rw [pairWeight_bad_left _ _ hb]; omega
    | rw [pairWeight_bad_right _ _ hb]; omega
    | rw [rankLookup_bad _ (by omega)]; omega

theorem fullSum_bad (f : Nat → Nat) (i : Nat) (hi : i < 17) (hb : 125 ≤ f i) :
    255 ≤ fullSum f := by
  have hx : rankLookup (f i) ≤ fullSum f := by
    unfold fullSum
    exact List.single_le_sum (by intro x hx; omega) _ (List.mem_map.mpr ⟨i, by simp [hi], rfl⟩)
  rw [rankLookup_bad _ (by omega)] at hx
  exact hx

/-- Poisoning an invalid pair once preserves every sum target below255. -/
theorem compressedSum_target (f : Nat → Nat) (tail target : Nat) (ht : target < 255) :
    compressedSum f + tail = target ↔ fullSum f + tail = target := by
  by_cases h : ∀ i, i < 17 → f i < 125
  · rw [compressedSum_good f h]
  · push_neg at h
    obtain ⟨i,hi,hb⟩ := h
    have h1 := compressedSum_bad f i hi hb
    have h2 := fullSum_bad f i hi hb
    omega

def pairedLookupSum (v : Digest) : Nat := compressedSum (topRank v) + tailWeight v

theorem pairedLookupSum_eq_iff (v : Digest) : pairedLookupSum v = 126 ↔ topLookupSum v = 126 := by
  change compressedSum (topRank v) + tailWeight v = 126 ↔ _
  rw [compressedSum_target _ _ _ (by decide)]
  rfl

/-- The optimized LUT uses the exact same strong source decoder. -/
theorem decode_top_paired (v : Digest) :
    SigGolfCandidate.T3.decode 0 v =
      if v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 then some (topDigits v) else none := by
  simp only [decode_top_lookup,pairedLookupSum_eq_iff]

end SigGolfCandidate.T3M.Verify.Nonbinary
