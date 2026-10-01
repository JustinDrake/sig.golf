import SigGolfCandidate.Legacy.Oracle
import Mathlib.Tactic.NormNum

/-! A reversible relabelling of the WOTS header.  The address identifies the layer and chain;
the original tree-high byte and step byte remain in the upper half of the header. -/

namespace SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 1024

def oldValid (w : Nat) : Prop :=
  w % 65536 = 257 ∧ w / 65536 % 256 < 7 ∧ w / 16777216 % 256 < 4 ∧
    w / 4294967296 % 256 < 8 ∧ w / 1099511627776 < 42

def newValid (w : Nat) : Prop :=
  4992 ≤ w % 4294967296 ∧ w % 4294967296 < 23808 ∧
    (w % 4294967296 - 4992) % 64 = 0 ∧ w / 4294967296 % 256 < 8 ∧
    w / 1099511627776 < 4

instance (w : Nat) : Decidable (oldValid w) := inferInstanceAs (Decidable (_ ∧ _))
instance (w : Nat) : Decidable (newValid w) := inferInstanceAs (Decidable (_ ∧ _))

def oldToNew (w : Nat) : Nat :=
  4992 + 2688 * (w / 65536 % 256) + 64 * (w / 1099511627776) +
    4294967296 * (w / 4294967296 % 256) + 1099511627776 * (w / 16777216 % 256)

def newToOld (w : Nat) : Nat :=
  let rank := (w % 4294967296 - 4992) / 64
  257 + 65536 * (rank / 42) + 16777216 * (w / 1099511627776) +
    4294967296 * (w / 4294967296 % 256) + 1099511627776 * (rank % 42)

theorem disjoint (w : Nat) : ¬ (oldValid w ∧ newValid w) := by
  simp only [oldValid, newValid]
  omega

def oldHeader (l h i m : Nat) : Nat :=
  257 + 65536 * l + 16777216 * h + 4294967296 * m + 1099511627776 * i

def newHeader (l h i m : Nat) : Nat :=
  4992 + 2688 * l + 64 * i + 4294967296 * m + 1099511627776 * h

theorem old_fields (l h i m : Nat) (hl : l < 7) (hh : h < 4) (hi : i < 42) (hm : m < 8) :
    oldValid (oldHeader l h i m) ∧ oldToNew (oldHeader l h i m) = newHeader l h i m := by
  have e1 : oldHeader l h i m = 257 + 65536 * (l + 256 * (h + 256 * (m + 256 * i))) := by
    unfold oldHeader; omega
  have e2 : oldHeader l h i m = (257 + 65536 * l) + 16777216 * (h + 256 * (m + 256 * i)) := by
    unfold oldHeader; omega
  have e3 : oldHeader l h i m = (257 + 65536 * l + 16777216 * h) + 4294967296 * (m + 256 * i) := by
    unfold oldHeader; omega
  have e4 : oldHeader l h i m = (257 + 65536 * l + 16777216 * h + 4294967296 * m) + 1099511627776 * i := rfl
  have d1 : oldHeader l h i m / 65536 % 256 = l := by
    rw [e1, Nat.add_mul_div_left _ _ (by decide)]
    simp only [Nat.reduceDiv, Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d2 : oldHeader l h i m / 16777216 % 256 = h := by
    rw [e2, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d3 : oldHeader l h i m / 4294967296 % 256 = m := by
    rw [e3, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d4 : oldHeader l h i m / 1099511627776 = i := by
    rw [e4, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have d0 : oldHeader l h i m % 65536 = 257 := by rw [e1, Nat.add_mul_mod_self_left]
  constructor
  · refine ⟨d0, ?_, ?_, ?_, ?_⟩ <;> simp only [d1, d2, d3, d4] <;> assumption
  · simp only [oldToNew, d1, d2, d3, d4, newHeader]

theorem new_fields (l h i m : Nat) (hl : l < 7) (hh : h < 4) (hi : i < 42) (hm : m < 8) :
    newValid (newHeader l h i m) ∧ newToOld (newHeader l h i m) = oldHeader l h i m := by
  have e1 : newHeader l h i m = (4992 + 2688 * l + 64 * i) + 4294967296 * (m + 256 * h) := by
    unfold newHeader; omega
  have e2 : newHeader l h i m = (4992 + 2688 * l + 64 * i + 4294967296 * m) + 1099511627776 * h := rfl
  have d0 : newHeader l h i m % 4294967296 = 4992 + 2688 * l + 64 * i := by
    rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have d1 : newHeader l h i m / 4294967296 % 256 = m := by
    rw [e1, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m < 256)]
  have d2 : newHeader l h i m / 1099511627776 = h := by
    rw [e2, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have rank : (newHeader l h i m % 4294967296 - 4992) / 64 = 42 * l + i := by rw [d0]; omega
  constructor
  · simp only [newValid, d0, d1, d2]; omega
  · dsimp only [newToOld]
    rw [rank]
    have r1 : (42 * l + i) / 42 = l := by omega
    have r2 : (42 * l + i) % 42 = i := by omega
    rw [r1, r2, d1, d2]
    rfl

theorem old_roundtrip (w : Nat) (h : oldValid w) :
    newValid (oldToNew w) ∧ newToOld (oldToNew w) = w := by
  obtain ⟨h0, hl, hh, hm, hi⟩ := h
  have d1 : w / 65536 / 256 = w / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have d2 : w / 16777216 / 256 = w / 4294967296 := by rw [Nat.div_div_eq_div_mul]
  have d3 : w / 4294967296 / 256 = w / 1099511627776 := by rw [Nat.div_div_eq_div_mul]
  have e : w = oldHeader (w / 65536 % 256) (w / 16777216 % 256) (w / 1099511627776) (w / 4294967296 % 256) := by
    unfold oldHeader; omega
  have ho := (old_fields _ _ _ _ hl hh hi hm).2
  have hn := new_fields _ _ _ _ hl hh hi hm
  rw [e, ho]
  exact hn

theorem new_roundtrip (w : Nat) (h : newValid w) :
    oldValid (newToOld w) ∧ oldToNew (newToOld w) = w := by
  obtain ⟨h0, h1, h2, hm, hh⟩ := h
  have d3 : w / 4294967296 / 256 = w / 1099511627776 := by rw [Nat.div_div_eq_div_mul]
  let rank := (w % 4294967296 - 4992) / 64
  have hl : rank / 42 < 7 := by dsimp [rank]; omega
  have hi : rank % 42 < 42 := Nat.mod_lt _ (by decide)
  have e : w = newHeader (rank / 42) (w / 1099511627776) (rank % 42) (w / 4294967296 % 256) := by
    dsimp [newHeader, rank]; omega
  have hn := (new_fields _ _ _ _ hl hh hi hm).2
  have ho := old_fields _ _ _ _ hl hh hi hm
  rw [e, hn]
  exact ho

def wordPerm (w : Nat) : Nat :=
  if oldValid w then oldToNew w else if newValid w then newToOld w else w

theorem wordPerm_involutive : Function.Involutive wordPerm := by
  intro w
  by_cases ho : oldValid w
  · obtain ⟨hn, he⟩ := old_roundtrip w ho
    have hno : ¬ oldValid (oldToNew w) := fun h => disjoint _ ⟨h, hn⟩
    simp only [wordPerm, if_pos ho, if_neg hno, if_pos hn, he]
  · by_cases hn : newValid w
    · obtain ⟨ho', he⟩ := new_roundtrip w hn
      simp only [wordPerm, if_neg ho, if_pos hn, if_pos ho', he]
    · simp only [wordPerm, if_neg ho, if_neg hn]

theorem wordPerm_lt (w : Nat) (h : w < 18446744073709551616) :
    wordPerm w < 18446744073709551616 := by
  unfold wordPerm
  split_ifs with ho hn
  · simp only [oldValid] at ho
    unfold oldToNew
    omega
  · simp only [newValid] at hn
    dsimp only [newToOld]
    omega
  · exact h

def payloadPerm (w : Nat) : Nat :=
  wordPerm (w % 18446744073709551616) + 18446744073709551616 * (w / 18446744073709551616)

theorem payloadPerm_mod (w : Nat) :
    payloadPerm w % 18446744073709551616 = wordPerm (w % 18446744073709551616) := by
  have h := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  omega

theorem payloadPerm_div (w : Nat) :
    payloadPerm w / 18446744073709551616 = w / 18446744073709551616 := by
  have h := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  omega

theorem payloadPerm_involutive : Function.Involutive payloadPerm := by
  intro w
  change wordPerm (payloadPerm w % 18446744073709551616) +
    18446744073709551616 * (payloadPerm w / 18446744073709551616) = w
  rw [payloadPerm_mod, payloadPerm_div, wordPerm_involutive]
  omega

theorem payloadPerm_lt (w : Nat) (h : w < 2 ^ 512) : payloadPerm w < 2 ^ 512 := by
  have h' := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  norm_num only [Nat.reducePow] at h ⊢
  omega

def queryPerm : Query → Query
  | ⟨0, w⟩ => ⟨0, BitVec.ofNat 512 (payloadPerm w.toNat)⟩
  | ⟨n + 1, w⟩ => ⟨n + 1, w⟩

theorem queryPerm_involutive : Function.Involutive queryPerm := by
  rintro ⟨n, w⟩
  cases n with
  | zero =>
    simp only [queryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (payloadPerm_lt _ w.isLt), payloadPerm_involutive,
      Nat.mod_eq_of_lt w.isLt]
  | succ n => rfl

theorem queryPerm_injective : Function.Injective queryPerm :=
  queryPerm_involutive.injective

theorem queryPerm_blocks (q : Query) : (queryPerm q).blocks = q.blocks := by
  rcases q with ⟨n, w⟩
  cases n <;> rfl

theorem wordPerm_fixed (w : Nat) (h0 : w % 64 ≠ 0) (h1 : w % 65536 ≠ 257) :
    wordPerm w = w := by
  have ho : ¬ oldValid w := fun h => h1 h.1
  have hn : ¬ newValid w := by
    intro h
    unfold newValid at h
    omega
  simp only [wordPerm, if_neg ho, if_neg hn]

theorem queryPerm_fixed (q : Query) (h0 : q.2.toNat % 64 ≠ 0)
    (h1 : q.2.toNat % 65536 ≠ 257) : queryPerm q = q := by
  rcases q with ⟨n, w⟩
  cases n with
  | zero =>
    have h0' : w.toNat % 18446744073709551616 % 64 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 64 ∣ 18446744073709551616)]
      exact h0
    have h1' : w.toNat % 18446744073709551616 % 65536 ≠ 257 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 65536 ∣ 18446744073709551616)]
      exact h1
    simp only [queryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, payloadPerm, wordPerm_fixed _ h0' h1']
    have e : w.toNat % 18446744073709551616 +
        18446744073709551616 * (w.toNat / 18446744073709551616) = w.toNat := by omega
    rw [e, Nat.mod_eq_of_lt w.isLt]
  | succ n => rfl

theorem old_header (lay treeHigh i mu : Nat) (hl : lay < 7) (ht : treeHigh < 4)
    (hi : i < 42) (hm : mu < 8) :
    wordPerm (257 + 65536 * lay + 16777216 * treeHigh + 4294967296 * mu + 1099511627776 * i) =
      4992 + 2688 * lay + 64 * i + 4294967296 * mu + 1099511627776 * treeHigh := by
  have h : oldValid (257 + 65536 * lay + 16777216 * treeHigh +
      4294967296 * mu + 1099511627776 * i) := by
    unfold oldValid
    omega
  rw [wordPerm, if_pos h]
  exact (old_fields lay treeHigh i mu hl ht hi hm).2

end SigGolfCandidate.Ref.AddressFormat

/-! The alternate four-layer, 62-chain witness uses the same global involution
construction, with its own protocol tag and physical block interval. Keeping the
permutation global is essential: arbitrary adversarial queries are relabelled too. -/

namespace SigGolfCandidate.Base4Candidate.AddressFormat
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 1024

def oldValid (w : Nat) : Prop :=
  w % 65536 = 258 ∧ w / 65536 % 256 < 4 ∧ w / 16777216 % 256 < 4 ∧
    w / 4294967296 % 256 < 4 ∧ w / 1099511627776 < 62

def newValid (w : Nat) : Prop :=
  5376 ≤ w % 4294967296 ∧ w % 4294967296 < 21248 ∧
    (w % 4294967296 - 5376) % 64 = 0 ∧ w / 4294967296 % 256 < 4 ∧
    w / 1099511627776 < 4

instance (w : Nat) : Decidable (oldValid w) := inferInstanceAs (Decidable (_ ∧ _))
instance (w : Nat) : Decidable (newValid w) := inferInstanceAs (Decidable (_ ∧ _))

def oldToNew (w : Nat) : Nat :=
  5376 + 3968 * (w / 65536 % 256) + 64 * (w / 1099511627776) +
    4294967296 * (w / 4294967296 % 256) + 1099511627776 * (w / 16777216 % 256)

def newToOld (w : Nat) : Nat :=
  let rank := (w % 4294967296 - 5376) / 64
  258 + 65536 * (rank / 62) + 16777216 * (w / 1099511627776) +
    4294967296 * (w / 4294967296 % 256) + 1099511627776 * (rank % 62)

theorem disjoint (w : Nat) : ¬ (oldValid w ∧ newValid w) := by
  simp only [oldValid, newValid]
  omega

def oldHeader (l h i m : Nat) : Nat :=
  258 + 65536 * l + 16777216 * h + 4294967296 * m + 1099511627776 * i

def newHeader (l h i m : Nat) : Nat :=
  5376 + 3968 * l + 64 * i + 4294967296 * m + 1099511627776 * h

theorem old_fields (l h i m : Nat) (hl : l < 4) (hh : h < 4) (hi : i < 62) (hm : m < 4) :
    oldValid (oldHeader l h i m) ∧ oldToNew (oldHeader l h i m) = newHeader l h i m := by
  have e1 : oldHeader l h i m = 258 + 65536 * (l + 256 * (h + 256 * (m + 256 * i))) := by
    unfold oldHeader; omega
  have e2 : oldHeader l h i m = (258 + 65536 * l) + 16777216 * (h + 256 * (m + 256 * i)) := by
    unfold oldHeader; omega
  have e3 : oldHeader l h i m = (258 + 65536 * l + 16777216 * h) + 4294967296 * (m + 256 * i) := by
    unfold oldHeader; omega
  have e4 : oldHeader l h i m = (258 + 65536 * l + 16777216 * h + 4294967296 * m) + 1099511627776 * i := rfl
  have d1 : oldHeader l h i m / 65536 % 256 = l := by
    rw [e1, Nat.add_mul_div_left _ _ (by decide)]
    simp only [Nat.reduceDiv, Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d2 : oldHeader l h i m / 16777216 % 256 = h := by
    rw [e2, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d3 : oldHeader l h i m / 4294967296 % 256 = m := by
    rw [e3, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add, Nat.add_mul_mod_self_left]
    omega
  have d4 : oldHeader l h i m / 1099511627776 = i := by
    rw [e4, Nat.add_mul_div_left _ _ (by decide)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have d0 : oldHeader l h i m % 65536 = 258 := by rw [e1, Nat.add_mul_mod_self_left]
  constructor
  · refine ⟨d0, ?_, ?_, ?_, ?_⟩ <;> simp only [d1, d2, d3, d4] <;> assumption
  · simp only [oldToNew, d1, d2, d3, d4, newHeader]

theorem new_fields (l h i m : Nat) (hl : l < 4) (hh : h < 4) (hi : i < 62) (hm : m < 4) :
    newValid (newHeader l h i m) ∧ newToOld (newHeader l h i m) = oldHeader l h i m := by
  have e1 : newHeader l h i m = (5376 + 3968 * l + 64 * i) + 4294967296 * (m + 256 * h) := by
    unfold newHeader; omega
  have e2 : newHeader l h i m = (5376 + 3968 * l + 64 * i + 4294967296 * m) + 1099511627776 * h := rfl
  have d0 : newHeader l h i m % 4294967296 = 5376 + 3968 * l + 64 * i := by
    rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have d1 : newHeader l h i m / 4294967296 % 256 = m := by
    rw [e1, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : m < 256)]
  have d2 : newHeader l h i m / 1099511627776 = h := by
    rw [e2, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have rank : (newHeader l h i m % 4294967296 - 5376) / 64 = 62 * l + i := by rw [d0]; omega
  constructor
  · simp only [newValid, d0, d1, d2]; omega
  · dsimp only [newToOld]
    rw [rank]
    have r1 : (62 * l + i) / 62 = l := by omega
    have r2 : (62 * l + i) % 62 = i := by omega
    rw [r1, r2, d1, d2]
    rfl

theorem old_roundtrip (w : Nat) (h : oldValid w) :
    newValid (oldToNew w) ∧ newToOld (oldToNew w) = w := by
  obtain ⟨h0, hl, hh, hm, hi⟩ := h
  have d1 : w / 65536 / 256 = w / 16777216 := by rw [Nat.div_div_eq_div_mul]
  have d2 : w / 16777216 / 256 = w / 4294967296 := by rw [Nat.div_div_eq_div_mul]
  have d3 : w / 4294967296 / 256 = w / 1099511627776 := by rw [Nat.div_div_eq_div_mul]
  have e : w = oldHeader (w / 65536 % 256) (w / 16777216 % 256) (w / 1099511627776) (w / 4294967296 % 256) := by
    unfold oldHeader; omega
  have ho := (old_fields _ _ _ _ hl hh hi hm).2
  have hn := new_fields _ _ _ _ hl hh hi hm
  rw [e, ho]
  exact hn

theorem new_roundtrip (w : Nat) (h : newValid w) :
    oldValid (newToOld w) ∧ oldToNew (newToOld w) = w := by
  obtain ⟨h0, h1, h2, hm, hh⟩ := h
  have d3 : w / 4294967296 / 256 = w / 1099511627776 := by rw [Nat.div_div_eq_div_mul]
  let rank := (w % 4294967296 - 5376) / 64
  have hl : rank / 62 < 4 := by dsimp [rank]; omega
  have hi : rank % 62 < 62 := Nat.mod_lt _ (by decide)
  have e : w = newHeader (rank / 62) (w / 1099511627776) (rank % 62) (w / 4294967296 % 256) := by
    dsimp [newHeader, rank]; omega
  have hn := (new_fields _ _ _ _ hl hh hi hm).2
  have ho := old_fields _ _ _ _ hl hh hi hm
  rw [e, hn]
  exact ho

def wordPerm (w : Nat) : Nat :=
  if oldValid w then oldToNew w else if newValid w then newToOld w else w

theorem wordPerm_involutive : Function.Involutive wordPerm := by
  intro w
  by_cases ho : oldValid w
  · obtain ⟨hn, he⟩ := old_roundtrip w ho
    have hno : ¬ oldValid (oldToNew w) := fun h => disjoint _ ⟨h, hn⟩
    simp only [wordPerm, if_pos ho, if_neg hno, if_pos hn, he]
  · by_cases hn : newValid w
    · obtain ⟨ho', he⟩ := new_roundtrip w hn
      simp only [wordPerm, if_neg ho, if_pos hn, if_pos ho', he]
    · simp only [wordPerm, if_neg ho, if_neg hn]

theorem wordPerm_lt (w : Nat) (h : w < 18446744073709551616) :
    wordPerm w < 18446744073709551616 := by
  unfold wordPerm
  split_ifs with ho hn
  · simp only [oldValid] at ho
    unfold oldToNew
    omega
  · simp only [newValid] at hn
    dsimp only [newToOld]
    omega
  · exact h

def payloadPerm (w : Nat) : Nat :=
  wordPerm (w % 18446744073709551616) + 18446744073709551616 * (w / 18446744073709551616)

theorem payloadPerm_mod (w : Nat) :
    payloadPerm w % 18446744073709551616 = wordPerm (w % 18446744073709551616) := by
  have h := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  omega

theorem payloadPerm_div (w : Nat) :
    payloadPerm w / 18446744073709551616 = w / 18446744073709551616 := by
  have h := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  omega

theorem payloadPerm_involutive : Function.Involutive payloadPerm := by
  intro w
  change wordPerm (payloadPerm w % 18446744073709551616) +
    18446744073709551616 * (payloadPerm w / 18446744073709551616) = w
  rw [payloadPerm_mod, payloadPerm_div, wordPerm_involutive]
  omega

theorem payloadPerm_lt (w : Nat) (h : w < 2 ^ 512) : payloadPerm w < 2 ^ 512 := by
  have h' := wordPerm_lt (w % 18446744073709551616) (Nat.mod_lt w (by decide))
  unfold payloadPerm
  norm_num only [Nat.reducePow] at h ⊢
  omega

def queryPerm : Query → Query
  | ⟨0, w⟩ => ⟨0, BitVec.ofNat 512 (payloadPerm w.toNat)⟩
  | ⟨n + 1, w⟩ => ⟨n + 1, w⟩

theorem queryPerm_involutive : Function.Involutive queryPerm := by
  rintro ⟨n, w⟩
  cases n with
  | zero =>
    simp only [queryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (payloadPerm_lt _ w.isLt), payloadPerm_involutive,
      Nat.mod_eq_of_lt w.isLt]
  | succ n => rfl

theorem queryPerm_injective : Function.Injective queryPerm :=
  queryPerm_involutive.injective

theorem queryPerm_blocks (q : Query) : (queryPerm q).blocks = q.blocks := by
  rcases q with ⟨n, w⟩
  cases n <;> rfl

theorem wordPerm_fixed (w : Nat) (h0 : w % 64 ≠ 0) (h1 : w % 65536 ≠ 258) :
    wordPerm w = w := by
  have ho : ¬ oldValid w := fun h => h1 h.1
  have hn : ¬ newValid w := by
    intro h
    unfold newValid at h
    omega
  simp only [wordPerm, if_neg ho, if_neg hn]

theorem queryPerm_fixed (q : Query) (h0 : q.2.toNat % 64 ≠ 0)
    (h1 : q.2.toNat % 65536 ≠ 258) : queryPerm q = q := by
  rcases q with ⟨n, w⟩
  cases n with
  | zero =>
    have h0' : w.toNat % 18446744073709551616 % 64 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 64 ∣ 18446744073709551616)]
      exact h0
    have h1' : w.toNat % 18446744073709551616 % 65536 ≠ 258 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 65536 ∣ 18446744073709551616)]
      exact h1
    simp only [queryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, payloadPerm, wordPerm_fixed _ h0' h1']
    have e : w.toNat % 18446744073709551616 +
        18446744073709551616 * (w.toNat / 18446744073709551616) = w.toNat := by omega
    rw [e, Nat.mod_eq_of_lt w.isLt]
  | succ n => rfl

theorem old_header (lay treeHigh i mu : Nat) (hl : lay < 4) (ht : treeHigh < 4)
    (hi : i < 62) (hm : mu < 4) :
    wordPerm (258 + 65536 * lay + 16777216 * treeHigh + 4294967296 * mu + 1099511627776 * i) =
      5376 + 3968 * lay + 64 * i + 4294967296 * mu + 1099511627776 * treeHigh := by
  have h : oldValid (258 + 65536 * lay + 16777216 * treeHigh +
      4294967296 * mu + 1099511627776 * i) := by
    unfold oldValid
    omega
  rw [wordPerm, if_pos h]
  exact (old_fields lay treeHigh i mu hl ht hi hm).2

end SigGolfCandidate.Base4Candidate.AddressFormat
