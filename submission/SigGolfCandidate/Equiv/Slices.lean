import SigGolfCandidate.Equiv.Basic

/-!
# Byte-list slices

Generic lemmas on `Ref.slice` of concatenations, used by the cache, witness and signature layouts.
-/

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes)
open SphincsSecurity (Digest)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

section slices


theorem slice_append_left (A B : List Byte) (off len : Nat) (h : off + len ≤ A.length) :
    Ref.slice (A ++ B) off len = Ref.slice A off len := by
  unfold Ref.slice
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem slice_append_right (A B : List Byte) (off off' len : Nat) (h : off = A.length + off') :
    Ref.slice (A ++ B) off len = Ref.slice B off' len := by
  unfold Ref.slice
  subst h
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

theorem slice_full (A : List Byte) (len : Nat) (h : A.length = len) : Ref.slice A 0 len = A := by
  unfold Ref.slice; subst h; simp

theorem slice_split (l : List Byte) (a b c : Nat) :
    Ref.slice l a (b + c) = Ref.slice l a b ++ Ref.slice l (a + b) c := by
  simp [Ref.slice, List.take_add, List.drop_drop, Nat.add_comm]

theorem slice_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (i : Fin n) (r len off : Nat)
    (hf : ∀ j : Fin n, j.val < i.val → (f j).length = k) (hr : r + len ≤ (f i).length)
    (hoff : off = k * i.val + r) :
    Ref.slice (List.ofFn f).flatten off len = Ref.slice (f i) r len := by
  induction n generalizing off with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at hoff
      subst hoff
      exact slice_append_left _ _ _ _ hr
    | succ i =>
      have h0 := hf 0 (by simp)
      rw [slice_append_right _ _ _ (k * i.val + r) _ (by simp [Fin.val_succ] at hoff; rw [h0, hoff]; ring)]
      exact ih (f := fun j => f j.succ) (i := i) (off := k * i.val + r)
        (hf := fun j hj => hf j.succ (by simp; omega)) (hr := hr) (hoff := rfl)

theorem flatten_ofFn_slices (l : List Byte) (a k n : Nat) :
    (List.ofFn fun i : Fin n => Ref.slice l (a + k * i.val) k).flatten = Ref.slice l a (k * n) := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, Nat.mul_succ]

theorem length_slice (l : List Byte) (a len : Nat) (h : a + len ≤ l.length) :
    (Ref.slice l a len).length = len := by
  simp [Ref.slice]; omega

end slices

theorem length_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (hf : ∀ j, (f j).length = k) :
    (List.ofFn f).flatten.length = k * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
      ih (fun j => f j.succ) (fun j => hf j.succ), Nat.mul_succ]; ring

theorem slice_flatten_take (L : List (List Byte)) (i r len : Nat) (hi : i < L.length)
    (h : r + len ≤ (L.getD i []).length) :
    Ref.slice L.flatten ((L.take i).flatten.length + r) len = Ref.slice (L.getD i []) r len := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.zero_add, List.flatten_cons,
        List.getD_cons_zero] at h ⊢
      exact slice_append_left _ _ _ _ h
    | succ i =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append, List.getD_cons_succ] at h ⊢
      rw [slice_append_right _ _ _ ((L.take i).flatten.length + r) _ (by omega)]
      exact ih i (by simp at hi; omega) h

theorem dv_ofList_slice (l : List Byte) (a : Nat) (h : a + 16 ≤ l.length) :
    dv (Ref.ofList 16 (Ref.slice l a 16)) = Ref.slice l a 16 :=
  Ref.toList_ofList 16 _ (length_slice l a 16 h)

theorem flatten_ofFn_slices_var (l : List Byte) (a : Nat) {n : Nat} (w : Nat → Nat) :
    (List.ofFn fun j : Fin n => Ref.slice l (a + ((List.range j).map w).sum) (w j)).flatten =
      Ref.slice l a ((List.range n).map w).sum := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, List.range_succ, List.map_append, List.sum_append]
    simp

/-! ### The W1a witness counters (`Ref.withCounters`)

`c4` at `Ref.wC4 = 2688`, `c0 .. c3` at `Ref.wChains = 2944` (the tweak slot of chain block `(0, 0)`). -/

/-- A slice of `LE32`s at a multiple of 4 is one of them. -/
theorem slice_le32s (L : List Nat) (j : Nat) (hj : j < L.length) :
    Ref.slice (L.map Ref.le32).flatten (4 * j) 4 = Ref.le32 (L.getD j 0) := by
  induction L generalizing j with
  | nil => simp at hj
  | cons x L ih =>
    cases j with
    | zero =>
      simp only [List.map_cons, List.flatten_cons, List.getD_cons_zero, Nat.mul_zero]
      rw [slice_append_left _ _ _ _ (by simp), slice_full _ _ (by simp)]
    | succ j =>
      simp only [List.map_cons, List.flatten_cons, List.getD_cons_succ]
      rw [slice_append_right _ _ _ (4 * j) _ (by simp; ring)]
      exact ih j (by simpa using hj)

/-- The layout of `Ref.withCounters`: prefix, `c4`, the paths etc., `c0 .. c3`, the rest. -/
theorem withCounters_eq (w0 : List Byte) (cs : List Nat) :
    Ref.withCounters w0 cs = w0.take 2688 ++ Ref.le32 (cs.getD 4 0) ++ Ref.slice w0 2692 252 ++
      (((List.range 4).map (cs.getD · 0)).map Ref.le32).flatten ++ w0.drop 2960 := by
  unfold Ref.withCounters
  rw [Ref.wC4_eq, Ref.wChains_eq, List.map_map]
  rfl

theorem length_le32s (L : List Nat) : ((L.map Ref.le32).flatten).length = 4 * L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.flatten_cons, List.length_append, Ref.length_le32, ih,
      List.length_cons]; ring

/-- `Ref.withCounters` keeps the length of a witness that holds the counters. -/
theorem length_withCounters (w0 : List Byte) (cs : List Nat) (h : 2960 ≤ w0.length) :
    (Ref.withCounters w0 cs).length = w0.length := by
  rw [withCounters_eq]
  simp only [List.length_append, List.length_take, Ref.length_le32, length_le32s, List.length_map,
    List.length_range, List.length_drop, Ref.slice]
  omega

/-- The counter bytes of `Ref.withCounters w0 cs` (layer `lay < 5`) are the `LE32` of `cs[lay]`. -/
theorem slice_withCounters_ctrOff (w0 : List Byte) (cs : List Nat) (h : 2960 ≤ w0.length)
    (lay : Nat) (hlay : lay < 5) :
    Ref.slice (Ref.withCounters w0 cs) (Ref.ctrOff lay) 4 = Ref.le32 (cs.getD lay 0) := by
  have ht : (w0.take 2688).length = 2688 := by rw [List.length_take]; omega
  have hs : (Ref.slice w0 2692 252).length = 252 := by
    simp only [Ref.slice, List.length_take, List.length_drop]; omega
  rw [withCounters_eq]
  unfold Ref.ctrOff
  split
  · rw [Ref.wChains_eq, slice_append_left _ _ _ _ (by
        simp only [List.length_append, ht, Ref.length_le32, hs, length_le32s, List.length_map,
          List.length_range]; omega),
      slice_append_right _ _ _ (4 * lay) _ (by simp only [List.length_append, ht, Ref.length_le32, hs]),
      slice_le32s _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_range (show lay < 4 by omega)]
  · rw [Ref.wC4_eq, show lay = 4 by omega, List.append_assoc, List.append_assoc, List.append_assoc,
      slice_append_right _ _ _ 0 _ (by rw [ht]),
      slice_append_left _ _ _ _ (by simp), slice_full _ _ (by simp)]

/-- The counters of `Ref.withCounters w0 cs`. -/
theorem witCounter_withCounters (w0 : List Byte) (cs : List Nat) (h : 2960 ≤ w0.length)
    (lay : Nat) (hlay : lay < 5) :
    Ref.witCounter (Ref.withCounters w0 cs) lay = cs.getD lay 0 % 2 ^ 32 := by
  rw [Ref.witCounter, slice_withCounters_ctrOff w0 cs h lay hlay, Ref.leNat_le32]

end SigGolfCandidate.Equiv
