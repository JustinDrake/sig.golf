import SigGolfCandidate.Expand.CopyRun
import SigGolfCandidate.Expand.RefFacts

/-!
# `expand`: the witness bytes

`witness_bytes` : the byte view left by the copy phase is `witnessList sig v vs segs`
(`ref.expand`'s W1a partial witness: zero counters, pads and tweak slots) on the 16384 witness bytes
(`0x800 + i` for `i < 0x4000`), given the byte view before the phase (signature bytes, the segment
stream of at most 2120 bytes, zero at the unused pi byte and above the scheduler's region).
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
  decide +kernel

theorem copyRest_srcdst : ∀ c ∈ copyRest, ∀ c' ∈ copyRest, Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by
  decide +kernel

theorem copy_hit (g : Nat → Byte) (c : Nat × Nat × Nat) (hc : c ∈ copyRest) (x : Nat)
    (h1 : c.2.1 ≤ x) (h2 : x < c.2.1 + 4 * c.2.2) :
    applyCopies copyRest g x = g (x - c.2.1 + c.1) :=
  applyCopies_hit copyRest g copyRest_pairwise copyRest_srcdst c hc x h1 h2

theorem mem_layCp (lay : Nat) (hl : lay < 5) (c : Nat × Nat × Nat) (hc : c ∈ layCp lay) : c ∈ copyRest := by
  unfold copyRest
  apply List.mem_cons_of_mem
  simp only [List.mem_append]
  interval_cases lay <;> simp [hc]

theorem chain_mem (lay k : Nat) (hl : lay < 5) (hk : k < 42) :
    (0x24B00 + sgOff lay + 16 * k, 0x800 + 2992 + 2688 * lay + 64 * k, 4) ∈ copyRest :=
  mem_layCp lay hl _ (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

theorem path_mem (lay : Nat) (hl : lay < 5) : pathCp lay ∈ copyRest :=
  mem_layCp lay hl _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem copyRest_cases (c : Nat × Nat × Nat) (hc : c ∈ copyRest) :
    c = (0x24B10, 0x820, 60) ∨ (∃ lay < 5, ∃ k < 42, c = (0x24B00 + sgOff lay + 16 * k, 0x800 + 2992 + 2688 * lay + 64 * k, 4)) ∨
      (∃ lay < 5, c = pathCp lay) := by
  unfold copyRest at hc
  rcases List.mem_cons.mp hc with h | h
  · exact Or.inl h
  right
  have key : ∀ lay < 5, c ∈ layCp lay →
      (∃ lay < 5, ∃ k < 42, c = (0x24B00 + sgOff lay + 16 * k, 0x800 + 2992 + 2688 * lay + 64 * k, 4)) ∨
      (∃ lay < 5, c = pathCp lay) := by
    intro lay hl h'
    rcases List.mem_append.mp h' with h' | h'
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h'
      exact Or.inl ⟨lay, hl, k, List.mem_range.mp hk, rfl⟩
    · exact Or.inr ⟨lay, hl, List.mem_singleton.mp h'⟩
  simp only [List.mem_append] at h
  rcases h with (((h | h) | h) | h) | h
  · exact key 0 (by norm_num) h
  · exact key 1 (by norm_num) h
  · exact key 2 (by norm_num) h
  · exact key 3 (by norm_num) h
  · exact key 4 (by norm_num) h

theorem copy_miss (g : Nat → Byte) (x : Nat)
    (hx : x < 0x820 ∨ (0x910 ≤ x ∧ x < 0x800 + 2400) ∨
      (0x800 + 2944 ≤ x ∧ (x - (0x800 + 2944)) % 64 < 48) ∨ 0x800 + 16384 ≤ x) :
    applyCopies copyRest g x = g x :=
  applyCopies_frame copyRest g x (by
    intro c hc
    rcases copyRest_cases c hc with rfl | ⟨lay, hl, k, hk, rfl⟩ | ⟨lay, hl, rfl⟩
    · simp; omega
    · simp only; omega
    · interval_cases lay <;> simp [pathCp, pOff, pWords, sgOff] <;> omega)

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

/-- `getD` in a flatten of `n` lists of length `L`. -/
theorem getD_flatten_range (f : Nat → List Byte) (L : Nat) (hL : 0 < L) :
    ∀ n, (∀ k < n, (f k).length = L) → ∀ i, ((List.range n).map f).flatten.getD i 0 =
      if i < n * L then (f (i / L)).getD (i % L) 0 else 0 := by
  intro n
  induction n with
  | zero => intro _ i; simp
  | succ n ih =>
    intro hf i
    rw [List.range_succ, List.map_append, List.flatten_append, getD_app]
    have hlen : ((List.range n).map f).flatten.length = n * L := by
      clear ih; induction n with
      | zero => simp
      | succ m ihm =>
        rw [List.range_succ, List.map_append, List.flatten_append, List.length_append,
          ihm (fun k hk => hf k (by omega))]
        simp [hf m (by omega)]; ring
    rw [hlen]
    by_cases h1 : i < n * L
    · rw [if_pos h1, ih (fun k hk => hf k (by omega)) i, if_pos h1, if_pos (by nlinarith)]
    · rw [if_neg h1]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      by_cases h2 : i < (n + 1) * L
      · have hd : i / L = n := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
        have hm : i % L = i - n * L := by
          have := Nat.mod_add_div i L; rw [hd] at this; rw [Nat.mul_comm] at this; omega
        rw [if_pos h2, hd, hm]
      · have e : (n + 1) * L = n * L + L := by ring
        rw [if_neg h2, List.getD_eq_default _ _ (by rw [hf n (by omega)]; omega)]

theorem sgOff_eq (lay : Nat) (hl : lay < 5) : sigLayerOff lay = sgOff lay := by
  interval_cases lay <;> decide

set_option maxRecDepth 20000 in
theorem witness_bytes (sig : List Byte) (hsig : sig.length = 6048) (N : Nat) (A : Nat → Nat)
    (hSK : SortedKeys N A) (hn : (leavesOf N).Nodup) (segs : List Nat) (f0 : Nat → Byte)
    (h1 : ∀ j < 6048, f0 (0x24B00 + j) = sig.getD j 0)
    (h2 : ∀ i < 2152, f0 (0x910 + i) = (curStream sig segs 0).getD i 0) (h3 : f0 0x81F = 0)
    (hlen : (segStream sig segs).length ≤ 2120)
    (h4 : ∀ a, 0x800 + 2424 ≤ a → a < 0x24B00 → f0 a = 0) :
    ∀ i < 0x4000, applyCopies copyRest (piF A 15 (applyCopy (0x24B00, 0x800, 4) f0)) (0x800 + i) =
      (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0 := by
  intro i hi
  set g := piF A 15 (applyCopy (0x24B00, 0x800, 4) f0) with hg
  -- the signature under the copies
  have hgs : ∀ j < 6048, g (0x24B00 + j) = sig.getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h1 j hj
  have hg0 : ∀ a, 0x800 + 2424 ≤ a → a < 0x24B00 → g a = 0 := by
    intro a ha1 ha2; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h4 a ha1 ha2
  -- the witness as one concatenation with explicit lengths
  have eS : ((List.range porsK).map (sigItem sig)).flatten = slice sig 16 240 := by
    have := flatten_slices sig 16 16 15
    simp only [show 16 * 15 = 240 from rfl] at this
    rw [← this]; unfold porsK sigItem; rfl
  have eP : ((List.range nLayers).map (sigPath sig)).flatten =
      sigPath sig 0 ++ (sigPath sig 1 ++ (sigPath sig 2 ++ (sigPath sig 3 ++ sigPath sig 4))) := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
  have lpath : ∀ lay < 5, (sigPath sig lay).length = 16 * height lay := by
    intro lay hl; unfold sigPath; apply length_slice'
    rw [hsig]; interval_cases lay <;> decide
  have lchain : ∀ lay < 5, (chainRegion sig lay).length = 2688 := by
    intro lay hl
    unfold chainRegion
    have := getD_flatten_range (fun i => zeros 48 ++ sigChain sig lay i) 64 (by norm_num)
    rw [show (2688 : Nat) = 42 * 64 from rfl]
    clear this
    have : ∀ n ≤ 42, ((List.range n).map fun i => zeros 48 ++ sigChain sig lay i).flatten.length = n * 64 := by
      intro n hn
      induction n with
      | zero => simp
      | succ m ihm =>
        rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ihm (by omega)]
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, length_zeros]
        rw [sigChain, length_slice' _ _ _ (by rw [hsig, sgOff_eq lay hl]; interval_cases lay <;> simp [sgOff] <;> omega)]
        ring
    exact this 42 le_rfl
  have lr : (sigRho sig).length = 16 := length_slice' _ _ _ (by omega)
  have lp : ((vsOf A).map (fun x => byte (8 * (leavesOf N).idxOf x))).length = 15 := by simp [vsOf]
  have lz : (zeros (wSec - wPi - porsK)).length = 1 := by simp [zeros, wSec, wPi, porsK]
  have ls : (slice sig 16 240).length = 240 := length_slice' _ _ _ (by omega)
  have lt : ((segStream sig segs ++ zeros streamBytes).take streamBytes).length = 2120 := by
    rw [List.length_take, List.length_append, streamBytes_eq]; simp only [zeros, List.length_replicate]; omega
  have l8 : (zeros 8).length = 8 := by simp [zeros]
  have lP : (sigPath sig 0 ++ (sigPath sig 1 ++ (sigPath sig 2 ++ (sigPath sig 3 ++ sigPath sig 4)))).length = 544 := by
    simp only [List.length_append, lpath 0 (by norm_num), lpath 1 (by norm_num), lpath 2 (by norm_num),
      lpath 3 (by norm_num), lpath 4 (by norm_num)]; decide
  unfold witnessList witnessBody
  rw [eS, eP]
  simp only [List.append_assoc]
  simp only [getD_app, lr, lp, lz, ls, lt, l8, lP, List.length_nil]
  by_cases r0 : i < 16
  · rw [if_pos r0, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_pos (by omega)]
    rw [show 0x800 + i - 0x800 + 0x24B00 = 0x24B00 + i by omega, h1 i (by omega), sigRho, getD_slice' _ _ _ _ r0,
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
  · rw [if_pos r3, copy_hit g (0x24B10, 0x820, 60) List.mem_cons_self _ (by simp; omega) (by simp; omega),
      getD_slice' _ _ _ _ r3]
    simp only
    rw [show 0x800 + i - 0x820 + 0x24B10 = 0x24B00 + (16 + (i - 16 - 15 - 1)) by omega, hgs _ (by omega)]
  rw [if_neg r3]
  -- the stream and the c4 / zero bytes (the scheduler's region)
  have hstr : ∀ j < 2128, g (0x910 + j) = (curStream sig segs 0).getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h2 j (by omega)
  by_cases r4 : i - 16 - 15 - 1 - 240 < 2120
  · rw [if_pos r4, copy_miss g _ (by omega)]
    rw [show 0x800 + i = 0x910 + (i - 16 - 15 - 1 - 240) by omega, hstr _ (by omega),
      getD_take' _ _ _ (by rw [streamBytes_eq]; exact r4)]
    unfold curStream items
    simp only [List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [getD_app, getD_app]
    split
    · rfl
    · rw [getD_zeros, getD_zeros]
  rw [if_neg r4]
  by_cases r5 : i - 16 - 15 - 1 - 240 - 2120 < 8
  · rw [if_pos r5, copy_miss g _ (by omega), getD_zeros]
    have e := hstr (i - 16 - 15 - 1 - 240) (by omega)
    rw [show 0x910 + (i - 16 - 15 - 1 - 240) = 0x800 + i by omega] at e
    rw [e]
    unfold curStream items
    simp only [List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [getD_append_zeros]
    exact List.getD_eq_default _ _ (by omega)
  rw [if_neg r5]
  -- the paths
  have hpath : ∀ lay < 5, ∀ j < 16 * height lay,
      applyCopies copyRest g (0x800 + pOff lay + j) = (sigPath sig lay).getD j 0 := by
    intro lay hl j hj
    have hw : 4 * pWords lay = 16 * height lay := by interval_cases lay <;> decide
    have hj' : j < 4 * pWords lay := by omega
    rw [copy_hit g (pathCp lay) (path_mem lay hl) _ (by simp [pathCp]) (by simp only [pathCp]; omega)]
    simp only [pathCp]
    rw [show 0x800 + pOff lay + j - (0x800 + pOff lay) + (0x24B00 + sgOff lay + 672) =
      0x24B00 + (sgOff lay + 672 + j) by omega, hgs _ (by interval_cases lay <;> simp [sgOff, pWords] at hj' ⊢ <;> omega),
      sigPath, getD_slice' _ _ _ _ hj, sgOff_eq lay hl]
    rfl
  have lq : ∀ lay < 5, (sigPath sig lay).length = [176, 96, 96, 96, 80].getD lay 0 := by
    intro lay hl; rw [lpath lay hl]; interval_cases lay <;> rfl
  simp only [lq 0 (by norm_num), lq 1 (by norm_num), lq 2 (by norm_num), lq 3 (by norm_num), lq 4 (by norm_num),
    List.getD_cons_zero, List.getD_cons_succ, show nLayers = 5 from rfl] at *
  set i' := i - 16 - 15 - 1 - 240 - 2120 - 8 with hi'
  by_cases q0 : i' < 176
  · rw [if_pos q0]
    have := hpath 0 (by norm_num) i' q0
    rwa [show 0x800 + pOff 0 + i' = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q0]
  by_cases q1 : i' - 176 < 96
  · rw [if_pos q1]
    have := hpath 1 (by norm_num) (i' - 176) q1
    rwa [show 0x800 + pOff 1 + (i' - 176) = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q1]
  by_cases q2 : i' - 176 - 96 < 96
  · rw [if_pos q2]
    have := hpath 2 (by norm_num) (i' - 176 - 96) q2
    rwa [show 0x800 + pOff 2 + (i' - 176 - 96) = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q2]
  by_cases q3 : i' - 176 - 96 - 96 < 96
  · rw [if_pos q3]
    have := hpath 3 (by norm_num) (i' - 176 - 96 - 96) q3
    rwa [show 0x800 + pOff 3 + (i' - 176 - 96 - 96) = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q3]
  by_cases q4 : i' - 176 - 96 - 96 - 96 < 80
  · rw [if_pos q4]
    have := hpath 4 (by norm_num) (i' - 176 - 96 - 96 - 96) q4
    rwa [show 0x800 + pOff 4 + (i' - 176 - 96 - 96 - 96) = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q4]
  -- the chain array
  set c := i' - 176 - 96 - 96 - 96 - 80 with hc
  have hi2 : i = 2944 + c := by omega
  rw [getD_flatten_range (chainRegion sig) 2688 (by norm_num) 5 lchain c, if_pos (by omega)]
  set lay := c / 2688 with hlay
  have hl : lay < 5 := by omega
  unfold chainRegion
  rw [show nChains = 42 from rfl, getD_flatten_range _ 64 (by norm_num) 42 (fun k hk => by
    simp only [List.length_append, length_zeros]
    rw [sigChain, length_slice' _ _ _ (by rw [hsig, sgOff_eq lay hl]; interval_cases lay <;> simp [sgOff] <;> omega)]),
    if_pos (by omega)]
  set k := c % 2688 / 64 with hk
  set r := c % 2688 % 64 with hr
  have hc' : c = 2688 * lay + 64 * k + r := by omega
  rw [getD_app, length_zeros]
  by_cases h48 : r < 48
  · rw [if_pos h48, getD_zeros, copy_miss g _ (by omega), hg0 _ (by omega) (by omega)]
  · rw [if_neg h48]
    rw [copy_hit g _ (chain_mem lay k hl (by omega)) _ (by simp only; omega) (by simp only; omega)]
    simp only
    rw [show 0x800 + i - (0x800 + 2992 + 2688 * lay + 64 * k) + (0x24B00 + sgOff lay + 16 * k) =
      0x24B00 + (sgOff lay + 16 * k + (r - 48)) by omega,
      hgs _ (by interval_cases lay <;> simp [sgOff] <;> omega),
      sigChain, getD_slice' _ _ _ _ (by omega), sgOff_eq lay hl]

/-- The bytes `2396 .. 2399` of the partial witness (after the `c4` slot) are zero. -/
theorem witnessList_c4 (sig : List Byte) (hsig : sig.length = 6048) (v vs segs : List Nat) (hvs : vs.length = 15) :
    ∀ j < 4, (witnessList sig v vs segs).getD (2396 + j) 0 = 0 := by
  intro j hj
  have eS : ((List.range porsK).map (sigItem sig)).flatten = slice sig 16 240 := by
    have := flatten_slices sig 16 16 15
    simp only [show 16 * 15 = 240 from rfl] at this
    rw [← this]; unfold porsK sigItem; rfl
  have lr : (sigRho sig).length = 16 := length_slice' _ _ _ (by omega)
  have lp : (vs.map (fun x => byte (8 * v.idxOf x))).length = 15 := by simp [hvs]
  have lz : (zeros (wSec - wPi - porsK)).length = 1 := by simp [zeros, wSec, wPi, porsK]
  have ls : (slice sig 16 240).length = 240 := length_slice' _ _ _ (by omega)
  have lt : ((segStream sig segs ++ zeros streamBytes).take streamBytes).length = 2120 := by
    rw [List.length_take, List.length_append, streamBytes_eq]; simp only [zeros, List.length_replicate]; omega
  have l8 : (zeros 8).length = 8 := by simp [zeros]
  unfold witnessList witnessBody
  rw [eS]
  simp only [List.append_assoc]
  rw [getD_app, lr, if_neg (by omega), getD_app, lp, if_neg (by omega), getD_app, lz, if_neg (by omega),
    getD_app, ls, if_neg (by omega), getD_app, lt, if_neg (by omega), getD_app, l8, if_pos (by omega), getD_zeros]

end SigGolfCandidate.Expand
