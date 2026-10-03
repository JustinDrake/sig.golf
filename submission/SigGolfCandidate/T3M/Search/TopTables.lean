import SigGolfCandidate.T3M.Search.Decode

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
abbrev TOP_DATA : Nat := 16773120
def rankDigit (r i : Nat) : Nat := r / 5 ^ i % 5
def rankWeight (r : Nat) : Nat := r % 5 + r / 5 % 5 + r / 25 % 5
def rankLookup (r : Nat) : Nat := if r < 125 then rankWeight r else 255
def topRank (v : Digest) (j : Nat) : Nat := v.toNat / 2 ^ (7 * j) % 128
def rankDigits (v : Digest) : List Nat := (List.range 17).map (topRank v)
def tailWeight (v : Digest) : Nat := v.toNat / 2 ^ 119 % 4 + v.toNat / 2 ^ 121 % 4 + v.toNat / 2 ^ 123 % 4
def topLookupSum (v : Digest) : Nat := ((rankDigits v).map rankLookup).sum + tailWeight v
def tableByte (i : Nat) : BitVec 8 := BitVec.ofNat 8 <|
  if i < 128 then rankLookup i
  else if i < 628 then if (i - 128) % 4 < 3 then rankDigit ((i - 128) / 4) ((i - 128) % 4) else 0
  else 0
def SumTableOK (s : MachineState) : Prop :=
  ∀ i, i < 128 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = BitVec.ofNat 8 (rankLookup i)
def TableOK (s : MachineState) : Prop :=
  ∀ i, i < 628 → s.getByte (BitVec.ofNat 64 (TOP_DATA + i)) = tableByte i
theorem TableOK.sum {s : MachineState} (h : TableOK s) : SumTableOK s := by
  intro i hi
  rw [h i (by omega)]
  simp [tableByte, hi]
theorem TableOK.frame {s t : MachineState} {W : Nat → Prop} (h : TableOK s)
    (hf : Frame s t W) (hd : ∀ i, i < 628 → ¬ W ((TOP_DATA + i) / 8 * 8)) : TableOK t := by
  intro i hi
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi)).trans (h i hi)
theorem SumTableOK.frame {s t : MachineState} {W : Nat → Prop} (h : SumTableOK s)
    (hf : Frame s t W) (hd : ∀ i, i < 128 → ¬ W ((TOP_DATA + i) / 8 * 8)) : SumTableOK t := by
  intro i hi
  exact (hf.getByte (by unfold TOP_DATA; omega) (hd i hi)).trans (h i hi)
theorem rankWeight_le (r : Nat) : rankWeight r ≤ 12 := by unfold rankWeight; omega
theorem rankLookup_le (r : Nat) : rankLookup r ≤ 255 := by
  unfold rankLookup
  split_ifs
  · have := rankWeight_le r; omega
  · omega
theorem rankLookup_bad (r : Nat) (h : ¬ r < 125) : rankLookup r = 255 := by simp [rankLookup, h]
theorem topDigits_grouped (v : Digest) :
    (topDigits v).sum = ((rankDigits v).map rankWeight).sum + tailWeight v := by
  simp only [topDigits, rankDigits, List.map_map, Function.comp_def, rankWeight, topRank, tailWeight,
    List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  norm_num [T3.coreDigit]
  omega
theorem topRanksValid_iff (v : Digest) :
    T3.topRanksValid v = true ↔ ∀ r ∈ rankDigits v, r < 125 := by
  simp [T3.topRanksValid, rankDigits, topRank]
private theorem map_sum_entry_le {xs : List Nat} (f : Nat → Nat) {r : Nat} (h : r ∈ xs) :
    f r ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega
theorem topLookupSum_good (v : Digest) (h : T3.topRanksValid v = true) :
    topLookupSum v = (topDigits v).sum := by
  rw [topDigits_grouped]
  unfold topLookupSum
  apply congrArg (fun x : Nat => x + tailWeight v)
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  simp [rankLookup, (topRanksValid_iff v).mp h r hr]
theorem topLookupSum_eq_iff (v : Digest) :
    topLookupSum v = 126 ↔ T3.topRanksValid v = true ∧ (topDigits v).sum = 126 := by
  constructor
  · intro h
    have hv : T3.topRanksValid v = true := by
      rw [topRanksValid_iff]
      intro r hr
      have hb := map_sum_entry_le rankLookup hr
      by_contra hn
      rw [rankLookup_bad r hn] at hb
      unfold topLookupSum at h
      omega
    exact ⟨hv, (topLookupSum_good v hv).symm.trans h⟩
  · rintro ⟨hv, hsum⟩
    exact (topLookupSum_good v hv).trans hsum
theorem decode_top_lookup (v : Digest) :
    T3.decode 0 v = if v.toNat < 2 ^ 125 ∧ topLookupSum v = 126
      then some (topDigits v) else none := by
  rw [decode_top]
  simp only [topLookupSum_eq_iff]
end SigGolfCandidate.T3M.Search
