import SigGolfCandidate.Expand.CopyRun
import SigGolfCandidate.Expand.RefFacts

/-!
# `expand`: the witness bytes

`witness_bytes` : the byte view left by the copy phase is `witnessList sig v vs segs`
(`ref.expand`'s partial witness, zero counters) on the 6348 witness bytes and zero above them up to
the signature (`0x800 + i` for `i < 0x2B00`), given the byte view before the phase (signature
bytes, the segment stream, zero at the unused pi byte and above the layer bodies).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem getD_app (l1 l2 : List Byte) (i : Nat) :
    (l1 ++ l2).getD i 0 = if i < l1.length then l1.getD i 0 else l2.getD (i - l1.length) 0 := by
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_slice' (l : List Byte) (off len j : Nat) (hj : j < len) :
    (slice l off len).getD j 0 = l.getD (off + j) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj]

theorem length_slice' (l : List Byte) (off len : Nat) (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp [slice]; omega

/-- The copies read the signature and write the witness only. -/
theorem copyRest_pairwise : copyRest.Pairwise (fun c c' => Disj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) := by
  decide

theorem copyRest_srcdst : ∀ c ∈ copyRest, ∀ c' ∈ copyRest, Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by
  decide

theorem copy_hit (g : Nat → Byte) (c : Nat × Nat × Nat) (hc : c ∈ copyRest) (x : Nat)
    (h1 : c.2.1 ≤ x) (h2 : x < c.2.1 + 4 * c.2.2) :
    applyCopies copyRest g x = g (x - c.2.1 + c.1) :=
  applyCopies_hit copyRest g copyRest_pairwise copyRest_srcdst c hc x h1 h2

theorem copy_miss (g : Nat → Byte) (x : Nat) (hx : x < 0x820 ∨ (0x910 ≤ x ∧ x < 0x1178) ∨ 0x20B8 ≤ x) :
    applyCopies copyRest g x = g x :=
  applyCopies_frame copyRest g x (by
    intro c hc; simp only [copyRest, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp <;> omega)

theorem slice_append_slice (l : List Byte) (a n m : Nat) :
    slice l a n ++ slice l (a + n) m = slice l a (n + m) := by
  unfold slice; rw [List.take_add, List.drop_drop]

theorem flatten_slices (l : List Byte) (off len : Nat) :
    ∀ n, ((List.range n).map (fun k => slice l (off + len * k) len)).flatten = slice l off (len * n) := by
  intro n
  induction n with
  | zero => simp [slice]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, slice]
    rw [show len * (n + 1) = len * n + len by ring, List.take_add, List.drop_drop]

theorem getD_take' (l : List Byte) (n i : Nat) (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]; rw [if_pos hi]

theorem witness_bytes (sig : List Byte) (hsig : sig.length = 6048) (N : Nat) (A : Nat → Nat)
    (hSK : SortedKeys N A) (hn : (leavesOf N).Nodup) (segs : List Nat) (f0 : Nat → Byte)
    (h1 : ∀ j < 6048, f0 (0x3300 + j) = sig.getD j 0)
    (h2 : ∀ i < 2152, f0 (0x910 + i) = (curStream sig segs 0).getD i 0) (h3 : f0 0x81F = 0)
    (h4 : ∀ a, 0x800 + 6328 ≤ a → a < 0x3300 → f0 a = 0) :
    ∀ i < 0x2B00, applyCopies copyRest (piF A 15 (applyCopy (0x3300, 0x800, 4) f0)) (0x800 + i) =
      (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0 := by
  intro i hi
  set g := piF A 15 (applyCopy (0x3300, 0x800, 4) f0) with hg
  -- the signature under the copies
  have hgs : ∀ j < 6048, g (0x3300 + j) = sig.getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h1 j hj
  -- the witness as one concatenation with explicit lengths
  have eS : ((List.range porsK).map (sigItem sig)).flatten = slice sig 16 240 := by
    have := flatten_slices sig 16 16 15
    simp only [show 16 * 15 = 240 from rfl] at this
    rw [← this]; unfold porsK sigItem; rfl
  have eB : ((List.range nLayers).map (sigLayerBody sig)).flatten = slice sig 2144 3904 := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
    unfold sigLayerBody
    rw [show sigLayerOff 0 = 2144 by decide, show sigLayerOff 1 = 2144 + 848 by decide,
      show sigLayerOff 2 = 2144 + 848 + 768 by decide, show sigLayerOff 3 = 2144 + 848 + 768 + 768 by decide,
      show sigLayerOff 4 = 2144 + 848 + 768 + 768 + 768 by decide, show bodyBytes 0 = 848 by decide,
      show bodyBytes 1 = 768 by decide, show bodyBytes 2 = 768 by decide,
      show bodyBytes 3 = 768 by decide, show bodyBytes 4 = 752 by decide,
      slice_append_slice, slice_append_slice, slice_append_slice, slice_append_slice]
  have lr : (sigRho sig).length = 16 := length_slice' _ _ _ (by omega)
  have lp : ((vsOf A).map (fun x => byte (8 * (leavesOf N).idxOf x))).length = 15 := by simp [vsOf]
  have lz : (zeros (wSec - wPi - porsK)).length = 1 := by simp [zeros, wSec, wPi, porsK]
  have ls : (slice sig 16 240).length = 240 := length_slice' _ _ _ (by omega)
  have lt : ((segStream sig segs ++ zeros streamBytes).take streamBytes).length = 2152 := by
    rw [List.length_take, List.length_append, streamBytes_eq]; simp only [zeros, List.length_replicate]; omega
  have lb : (slice sig 2144 3904).length = 3904 := length_slice' _ _ _ (by omega)
  have lc : (zeros (4 * nLayers)).length = 20 := by simp [zeros, nLayers]
  unfold witnessList witnessBody
  rw [eS, eB]
  simp only [List.append_assoc]
  simp only [getD_app, lr, lp, lz, ls, lt, lb, lc, List.length_nil]
  by_cases r0 : i < 16
  · rw [if_pos r0, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_pos (by omega)]
    rw [show 0x800 + i - 0x800 + 0x3300 = 0x3300 + i by omega, h1 i (by omega), sigRho, getD_slice' _ _ _ _ r0,
      Nat.zero_add]
  rw [if_neg r0]
  by_cases r1 : i - 16 < 15
  · rw [if_pos r1, copy_miss g _ (by omega)]
    simp only [hg, piF]; rw [if_pos (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    simp only [vsOf, List.getElem?_map, List.getElem?_range r1, Option.map_some, Option.getD_some]
    rw [← idxOf_lv hSK hn (i - 16) r1, show 0x800 + i - 0x810 = i - 16 by omega]
    unfold byte; apply BitVec.eq_of_toNat_eq; simp
  rw [if_neg r1]
  by_cases r2 : i - 16 - 15 < 1
  · rw [if_pos r2, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega), show 0x800 + i = 0x81F by omega, h3]
    simp [zeros, List.getD_eq_getElem?_getD]
  rw [if_neg r2]
  by_cases r3 : i - 16 - 15 - 1 < 240
  · rw [if_pos r3, copy_hit g (0x3310, 0x820, 60) (by decide) _ (by simp; omega) (by simp; omega),
      getD_slice' _ _ _ _ r3]
    simp only
    rw [show 0x800 + i - 0x820 + 0x3310 = 0x3300 + (16 + (i - 16 - 15 - 1)) by omega, hgs _ (by omega)]
  rw [if_neg r3]
  by_cases r4 : i - 16 - 15 - 1 - 240 < 2152
  · rw [if_pos r4, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]
    rw [show 0x800 + i = 0x910 + (i - 16 - 15 - 1 - 240) by omega, h2 _ r4, getD_take' _ _ _ (by rw [streamBytes_eq]; exact r4)]
    unfold curStream items
    simp only [List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [getD_app, getD_app]
    split
    · rfl
    · rw [getD_zeros, getD_zeros]
  rw [if_neg r4]
  by_cases q0 : i - 16 - 15 - 1 - 240 - 2152 < 3904
  · rw [if_pos q0, copy_hit g (0x3B60, 0x1178, 976) (by decide) _ (by simp; omega) (by simp; omega),
      getD_slice' _ _ _ _ q0]
    simp only
    rw [show 0x800 + i - 0x1178 + 0x3B60 = 0x3300 + (2144 + (i - 16 - 15 - 1 - 240 - 2152)) by omega,
      hgs _ (by omega)]
  rw [if_neg q0]
  -- the zero counters and the zeros above the witness
  rw [copy_miss g _ (by omega)]
  simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega), h4 _ (by omega) (by omega)]
  rw [getD_zeros]

end SigGolfCandidate.Expand
