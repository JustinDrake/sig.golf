import SigGolfCandidate.Expand.CopyRun
import SigGolfCandidate.Expand.RefFacts
import SigGolfCandidate.Expand.Stream

/-!
# `expand`: the witness bytes

`witness_bytes` : the byte view left by the copy phase is `witnessList sig v vs segs`
(`ref.expand`'s W1a partial witness: zero counters and pads; W1: `rho` and the secrets in the tweak
slots of layer 0's blocks 1 .. 16, the other tweak slots zero) on the 16384 bytes of the view
`0x800 .. 0x4800` (`0x800 + i` for `i < 0x4000`, the zero lead `0x800 .. 0x1270` included), given the
byte view before the phase (signature bytes, the segment stream of at most 2120 bytes, zero below the
stream and above the scheduler's region).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

/-- Only the first sixteen bytes of each sparse stream cell may be nonzero. -/
def Sparse (l : List Byte) : Prop := ∀ i, 16 ≤ i % 64 → l.getD i 0 = 0

theorem sparse_zeros (n : Nat) : Sparse (zeros n) := by
  intro i hi; exact getD_zeros n i

theorem Sparse.block (l : List Byte) (hl : l.length ≤ 16) : Sparse (l ++ zeros (64 - l.length)) := by
  intro i hi
  rw [List.getD_append_right _ _ _ _ (by omega), getD_zeros]

theorem Sparse.append {l r : List Byte} (hl : Sparse l) (hr : Sparse r)
    (hlen : l.length % 64 = 0) : Sparse (l ++ r) := by
  intro i hi
  by_cases h : i < l.length
  · rw [List.getD_append _ _ _ _ h]; exact hl i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    exact hr _ (by omega)

theorem sparse_items (sig : List Byte) (hsig : sig.length = 6032) (r n : Nat) (hn : r + n ≤ 117) :
    Sparse (items sig r n) := by
  induction n with
  | zero => simpa [items, zeros] using sparse_zeros 0
  | succ n ih =>
    rw [items_succ]
    apply (ih (by omega)).append
    · have ha := length_sigAuth sig hsig (r + n) (by omega)
      simpa [ha] using Sparse.block (sigAuth sig (r + n)) (by omega)
    · rw [length_items sig hsig r n (by omega)]; omega

theorem sparse_segStream (sig : List Byte) (hsig : sig.length = 6032) :
    ∀ segs, nsum segs ≤ 117 → Sparse (segStream sig segs) := by
  intro segs
  induction segs using List.reverseRecOn with
  | nil => intro _; simpa [segStream, zeros] using sparse_zeros 0
  | append_singleton segs b ih =>
    intro hn
    rw [nsum_snoc] at hn
    rw [segStream_snoc]
    simp only [List.append_assoc]
    apply (ih (by omega)).append
    · rw [← List.append_assoc]
      apply (show Sparse ([byte b] ++ zeros 63) from by
        simpa using Sparse.block [byte b] (by simp)).append
      · exact sparse_items sig hsig (nsum segs) (b % 16) hn
      · simp [zeros]
    · rw [length_segStream sig hsig segs (by omega)]; omega

theorem getD_curStream_zero (sig : List Byte) (segs : List Nat) (i : Nat) :
    (curStream sig segs 0).getD i 0 = (segStream sig segs).getD i 0 := by
  simp only [curStream, items, List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
  exact getD_append_zeros _ _ _


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
  apply List.mem_append_right
  simp only [List.mem_append]
  interval_cases lay <;> simp [hc]

/-- W1: the copy of secret `s` into the tweak slot of chain block `(0, 2 + s)`. -/
theorem sec_mem (s : Nat) (hs : s < 15) : (0x24B10 + 16 * s, 0x1400 + 64 * s, 4) ∈ copyRest :=
  List.mem_append_left _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)

theorem chain_mem (lay k : Nat) (hl : lay < 5) (hk : k < 42) :
    (0x24B00 + sgOff lay + 16 * k, 0x800 + 2992 + 2688 * lay + 64 * k, 4) ∈ copyRest :=
  mem_layCp lay hl _ (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))

theorem top_path_mem : pathCp 0 ∈ copyRest := by decide +kernel

theorem path_mem (lay k : Nat) (hl : lay < 5) (hpos : 0 < lay) (hk : k < pWords lay / 4) :
    (0x24B00 + sgOff lay + 672 + 16 * k, 0x800 + pOff lay + 64 * k, 4) ∈ copyRest := by
  apply mem_layCp lay hl
  apply List.mem_append_right
  simp only [pathCps, if_neg (by omega : lay ≠ 0)]
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

/-- Every copy destination is a top path, a packed tweak slot, or a chain value. -/
theorem copyRest_dest : ∀ c ∈ copyRest,
    (4752 ≤ c.2.1 ∧ c.2.1 + 4 * c.2.2 ≤ 4928) ∨
    (5120 ≤ c.2.1 ∧ c.2.1 < 7552 ∧ c.2.1 % 64 = 0 ∧ c.2.2 = 4) ∨
    (5040 ≤ c.2.1 ∧ c.2.1 + 16 ≤ 18432 ∧ c.2.1 % 64 = 48 ∧ c.2.2 = 4) := by
  decide +kernel

theorem copy_miss (g : Nat → Byte) (x : Nat)
    (hx : x < 0x800 + 2704 ∨ (0x800 + 2880 ≤ x ∧ x < 0x800 + 2944) ∨
      (0x800 + 2944 ≤ x ∧ (x - (0x800 + 2944)) % 64 < 48 ∧
        ¬ (0x1400 ≤ x ∧ x < 0x1D80 ∧ (x - 0x1400) % 64 < 16)) ∨ 0x800 + 16384 ≤ x) :
    applyCopies copyRest g x = g x :=
  applyCopies_frame copyRest g x (by
    intro c hc
    rcases copyRest_dest c hc with h | h | h <;> omega)

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
theorem witness_bytes (sig : List Byte) (hsig : sig.length = 6032) (N : Nat) (A : Nat → Nat)
    (hSK : SortedKeys N A) (hn : (leavesOf N).Nodup) (segs : List Nat) (f0 : Nat → Byte) (hns : nsum segs ≤ 117)
    (h1 : ∀ j < 6032, f0 (0x24B00 + j) = sig.getD j 0)
    (h2 : ∀ i < 9408, f0 (0x1D80 + i) = (curStream sig segs 0).getD i 0)
    (h3 : ∀ a, 0x800 ≤ a → a < 0x1D80 → f0 a = 0)
    (hlen : (segStream sig segs).length ≤ 9344)
    (h4 : ∀ a, 0x4240 ≤ a → a < 0x24B00 → f0 a = 0) :
    ∀ i < 0x10000, applyCopies copyRest (piF A 15 (applyCopy (0x24B00, 0x13C0, 4) f0)) (0x800 + i) =
      (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0 := by
  intro i hi
  set g := piF A 15 (applyCopy (0x24B00, 0x13C0, 4) f0) with hg
  -- the signature under the copies
  have hgs : ∀ j < 6032, g (0x24B00 + j) = sig.getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h1 j hj
  have hg0 : ∀ a, 0x4240 ≤ a → a < 0x24B00 → ¬ (0x13C0 ≤ a ∧ a < 0x13D0) → g a = 0 := by
    intro a ha1 ha2 ha3; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h4 a ha1 ha2
  -- the witness as one concatenation with explicit lengths
  have lpath : ∀ lay < 5, (sigPath sig lay).length = 16 * height lay := by
    intro lay hl; unfold sigPath; apply length_slice'
    rw [hsig]; interval_cases lay <;> decide
  have lslot : ∀ lay k, (slotOf sig segs lay k).length = 16 := length_slotOf sig hsig segs
  have lchain : ∀ lay < 5, (chainRegion sig segs lay).length = 2688 := by
    intro lay hl
    unfold chainRegion
    rw [show (2688 : Nat) = 42 * 64 from rfl]
    have : ∀ n ≤ 42, ((List.range n).map fun i => slotOf sig segs lay i ++ zeros 32 ++ sigChain sig lay i).flatten.length =
        n * 64 := by
      intro n hn
      induction n with
      | zero => simp
      | succ m ihm =>
        rw [List.range_succ, List.map_append, List.flatten_append, List.length_append, ihm (by omega)]
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.length_append, length_zeros, lslot]
        rw [sigChain, length_slice' _ _ _ (by rw [hsig, sgOff_eq lay hl]; interval_cases lay <;> simp [sgOff] <;> omega)]
        ring
    exact this 42 le_rfl
  have lw : (zeros wPi).length = 2672 := by rw [length_zeros]; rfl
  have lp : ((vsOf A).map (fun x => byte (8 * (leavesOf N).idxOf x))).length = 15 := by simp [vsOf]
  have lz : (zeros 1).length = 1 := by rw [length_zeros]
  have l16 : (zeros 16).length = 16 := by simp [zeros]
  have l64 : (zeros 64).length = 64 := by simp [zeros]
  have lP : (sigPath sig 0).length = 176 := by simpa [height, heights] using lpath 0 (by omega)
  by_cases hitail : 16384 ≤ i
  · rw [copy_miss g _ (Or.inr (Or.inr (Or.inr (by omega)))),
      List.getD_eq_default _ _ (by rw [length_witnessList sig hsig _ _ segs (by simp [vsOf, porsK])]; exact hitail)]
    exact hg0 _ (by omega) (by omega) (by omega)
  unfold witnessList witnessBody
  simp only [List.append_assoc]
  simp only [getD_app, lw, lp, lz, l16, l64, lP, List.length_nil]
  -- W1: the view's zero lead `0x800 .. 0x1270` (no copy writes there)
  by_cases r0 : i < 2672
  · rw [if_pos r0, copy_miss g _ (by omega), getD_zeros]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]
    exact h3 _ (by omega) (by omega)
  rw [if_neg r0]
  by_cases r1 : i - 2672 < 15
  · rw [if_pos r1, copy_miss g _ (by omega)]
    simp only [hg, piF]; rw [if_pos (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    simp only [vsOf, List.getElem?_map, List.getElem?_range r1, Option.map_some, Option.getD_some]
    rw [← idxOf_lv hSK hn (i - 2672) r1, show 0x800 + i - 0x1270 = i - 2672 by omega]
    unfold byte; apply BitVec.eq_of_toNat_eq; simp
  rw [if_neg r1]
  by_cases r2 : i - 2672 - 15 < 1
  · rw [if_pos r2, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega), h3 _ (by omega) (by omega)]
    simp [zeros, List.getD_eq_getElem?_getD]
  rw [if_neg r2]
  -- c4, its zero pad, and the contiguous path area.
  by_cases r3 : i - 2672 - 15 - 1 < 16
  · rw [if_pos r3, copy_miss g _ (by omega), getD_zeros]
    simp only [hg, piF, applyCopy]
    rw [if_neg (by omega), if_neg (by omega)]
    exact h3 _ (by omega) (by omega)
  rw [if_neg r3]
  -- The top path remains contiguous; lower paths are packed into tweak slots.
  have hpath0 : ∀ j < 176,
      applyCopies copyRest g (0x800 + pOff 0 + j) = (sigPath sig 0).getD j 0 := by
    intro j hj
    rw [copy_hit g (pathCp 0) top_path_mem _ (by simp [pathCp]) (by simp [pathCp, pWords]; omega)]
    simp only [pathCp]
    rw [show 0x800 + pOff 0 + j - (0x800 + pOff 0) + (0x24B00 + sgOff 0 + 672) =
      0x24B00 + (sgOff 0 + 672 + j) by omega, hgs _ (by simp [sgOff]; omega),
      sigPath, getD_slice' _ _ _ _ (by simpa [height, heights] using hj), sgOff_eq 0 (by omega)]
    rfl
  have hpath : ∀ lay < 5, 0 < lay → ∀ k < height lay, ∀ r < 16,
      applyCopies copyRest g (0x800 + pOff lay + 64 * k + r) = (sigPath sig lay).getD (16 * k + r) 0 := by
    intro lay hl hp k hk r hr
    have hk' : k < pWords lay / 4 := by interval_cases lay <;> simp [pWords, height, heights] at * <;> omega
    rw [copy_hit g _ (path_mem lay k hl hp hk') _ (by simp only; omega) (by simp only; omega)]
    simp only
    rw [show 0x800 + pOff lay + 64 * k + r - (0x800 + pOff lay + 64 * k) +
      (0x24B00 + sgOff lay + 672 + 16 * k) = 0x24B00 + (sgOff lay + 672 + (16 * k + r)) by omega,
      hgs _ (by interval_cases lay <;> simp [sgOff, height, heights] at hk ⊢ <;> omega),
      sigPath, getD_slice' _ _ _ _ (by omega), sgOff_eq lay hl]
    rfl
  set i' := i - 2672 - 15 - 1 - 16 with hi'
  by_cases q0 : i' < 176
  · rw [if_pos q0]
    have := hpath0 i' q0
    rwa [show 0x800 + pOff 0 + i' = 0x800 + i by simp [pOff]; omega] at this
  rw [if_neg q0]
  by_cases q5 : i' - 176 < 64
  · rw [if_pos q5, getD_zeros, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]
    rw [if_neg (by omega), if_neg (by omega)]
    exact h3 _ (by omega) (by omega)
  rw [if_neg q5]
  -- the chain array
  set c := i' - 176 - 64 with hc
  have hi2 : i = 2944 + c := by omega
  rw [show nLayers = 5 from rfl]
  rw [getD_flatten_range (chainRegion sig segs) 2688 (by norm_num) 5 lchain c, if_pos (by omega)]
  set lay := c / 2688 with hlay
  have hl : lay < 5 := by omega
  unfold chainRegion
  rw [show nChains = 42 from rfl, getD_flatten_range _ 64 (by norm_num) 42 (fun k hk => by
    simp only [List.length_append, length_zeros, lslot]
    rw [sigChain, length_slice' _ _ _ (by rw [hsig, sgOff_eq lay hl]; interval_cases lay <;> simp [sgOff] <;> omega)]),
    if_pos (by omega)]
  set k := c % 2688 / 64 with hk
  set r := c % 2688 % 64 with hr
  have hc' : c = 2688 * lay + 64 * k + r := by omega
  have hk42 : k < 42 := by omega
  have hstr : ∀ j < 9408, g (0x1D80 + j) = (segStream sig segs).getD j 0 := by
    intro j hj
    simp only [hg, piF, applyCopy]
    rw [if_neg (by omega), if_neg (by omega), h2 j hj, getD_curStream_zero]
  have hgzero : ∀ a, 0x1380 ≤ a → a < 0x4800 →
      ¬ (0x13C0 ≤ a ∧ a < 0x13D0) → (a < 0x1D80 ∨ 0x1D80 + 9344 ≤ a) → g a = 0 := by
    intro a ha1 ha2 hnr hsparse
    by_cases hlow : a < 0x1D80
    · simp only [hg, piF, applyCopy]
      rw [if_neg (by omega), if_neg (by omega)]
      exact h3 a (by omega) hlow
    · by_cases hhi : a < 0x4240
      · rw [show a = 0x1D80 + (a - 0x1D80) by omega, hstr _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
      · exact hg0 a (by omega) (by omega) hnr
  rw [getD_app, List.length_append, lslot, length_zeros, show (16 + 32 : Nat) = 48 from rfl]
  by_cases h48 : r < 48
  · rw [if_pos h48, getD_app, lslot]
    by_cases h16 : r < 16
    · -- W1: the tweak slot (`rho` in block `(0, 1)`, secret `s` in block `(0, 2 + s)`, else zero)
      rw [if_pos h16]
      unfold slotOf
      split_ifs with hrho hsec hauth hstream
      · rw [copy_miss g _ (by omega)]
        simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_pos (by omega)]
        rw [show 0x800 + i - 0x13C0 + 0x24B00 = 0x24B00 + r by omega, h1 r (by omega), sigRho,
          getD_slice' _ _ _ _ h16, Nat.zero_add]
      · have hs' : lay = 0 ∧ 2 ≤ k ∧ k < 17 := by unfold porsK at hsec; omega
        rw [copy_hit g _ (sec_mem (k - 2) (by omega)) _ (by simp only; omega) (by simp only; omega)]
        simp only
        rw [show 0x800 + i - (0x1400 + 64 * (k - 2)) + (0x24B10 + 16 * (k - 2)) =
          0x24B00 + (16 + 16 * (k - 2) + r) by omega, hgs _ (by omega), sigItem, getD_slice' _ _ _ _ h16]
      · have hpors : porsK = 15 := rfl
        obtain ⟨hlay0, hk17, hk40⟩ := hauth
        subst lay
        rw [getD_slice' _ _ _ _ h16]
        have lp1 := lpath 1 (by omega)
        have lp2 := lpath 2 (by omega)
        have lp3 := lpath 3 (by omega)
        have lp4 := lpath 4 (by omega)
        simp [height, heights] at lp1 lp2 lp3 lp4
        unfold lowerPaths
        simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons,
          List.map_nil, List.nil_append, List.flatten_append, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.append_assoc, Nat.reduceAdd]
        simp only [getD_app, lp1, lp2, lp3, lp4]
        by_cases h23 : k < 23
        · rw [if_pos (by omega)]
          have hh := hpath 1 (by omega) (by omega) (k - 17) (by simp [height, heights]; omega) r h16
          convert hh using 1 <;> first
          | exact congrArg (applyCopies copyRest g) (by simp [pOff]; omega)
          | exact congrArg (fun j => (sigPath sig 1).getD j 0) (by omega)
        · rw [if_neg (by omega)]
          by_cases h29 : k < 29
          · rw [if_pos (by omega)]
            have hh := hpath 2 (by omega) (by omega) (k - 23) (by simp [height, heights]; omega) r h16
            convert hh using 1 <;> first
            | exact congrArg (applyCopies copyRest g) (by simp [pOff]; omega)
            | exact congrArg (fun j => (sigPath sig 2).getD j 0) (by omega)
          · rw [if_neg (by omega)]
            by_cases h35 : k < 35
            · rw [if_pos (by omega)]
              have hh := hpath 3 (by omega) (by omega) (k - 29) (by simp [height, heights]; omega) r h16
              convert hh using 1 <;> first
              | exact congrArg (applyCopies copyRest g) (by simp [pOff]; omega)
              | exact congrArg (fun j => (sigPath sig 3).getD j 0) (by omega)
            · rw [if_neg (by omega)]
              have hh := hpath 4 (by omega) (by omega) (k - 35) (by simp [height, heights]; omega) r h16
              convert hh using 1 <;> first
              | exact congrArg (applyCopies copyRest g) (by simp [pOff]; omega)
              | exact congrArg (fun j => (sigPath sig 4).getD j 0) (by omega)
      · have hs' : ¬ (lay = 0 ∧ 2 ≤ k ∧ k < 17) := by unfold porsK at hsec; omega
        have hp' : 40 ≤ 42 * lay + k ∧ 42 * lay + k < 186 := hstream
        rw [copy_miss g _ (by omega)]
        rw [show 0x800 + i = 0x1D80 + (64 * (42 * lay + k - 40) + r) by omega,
          hstr _ (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h16, nChains]
      · have hs' : ¬ (lay = 0 ∧ 2 ≤ k ∧ k < 17) := by unfold porsK at hsec; omega
        have hp' : ¬ (40 ≤ 42 * lay + k ∧ 42 * lay + k < 186) := hstream
        rw [getD_zeros, copy_miss g _ (by omega)]
        exact hgzero _ (by omega) (by omega) (by omega) (by omega)
    · rw [if_neg h16, getD_zeros, copy_miss g _ (by omega)]
      by_cases hp' : 40 ≤ 42 * lay + k ∧ 42 * lay + k < 186
      · rw [show 0x800 + i = 0x1D80 + (64 * (42 * lay + k - 40) + r) by omega,
          hstr _ (by omega)]
        exact sparse_segStream sig hsig segs hns _ (by omega)
      · exact hgzero _ (by omega) (by omega) (by omega) (by omega)
  · rw [if_neg h48]
    rw [copy_hit g _ (chain_mem lay k hl (by omega)) _ (by simp only; omega) (by simp only; omega)]
    simp only
    rw [show 0x800 + i - (0x800 + 2992 + 2688 * lay + 64 * k) + (0x24B00 + sgOff lay + 16 * k) =
      0x24B00 + (sgOff lay + 16 * k + (r - 48)) by omega,
      hgs _ (by interval_cases lay <;> simp [sgOff] <;> omega),
      sigChain, getD_slice' _ _ _ _ (by omega), sgOff_eq lay hl]

/-- Four reserved bytes following the fourth counter stay zero before counter insertion. -/
theorem witnessList_c4 (sig : List Byte) (hsig : sig.length = 6032) (v vs segs : List Nat) (hvs : vs.length = 15) :
    ∀ j < 4, (witnessList sig v vs segs).getD (2692 + j) 0 = 0 := by
  intro j hj
  have lw : (zeros wPi).length = 2672 := by rw [length_zeros]; rfl
  have lp : (vs.map (fun x => byte (8 * v.idxOf x))).length = 15 := by simp [hvs]
  unfold witnessList witnessBody
  simp only [List.append_assoc]
  rw [getD_app, lw, if_neg (by omega), getD_app, lp, if_neg (by omega), getD_app,
    length_zeros, if_neg (by omega), getD_app, length_zeros, if_pos (by omega), getD_zeros]

end SigGolfCandidate.Expand
