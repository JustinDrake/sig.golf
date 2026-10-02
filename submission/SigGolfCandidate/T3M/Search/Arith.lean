import SigGolfCandidate.T3M.Search.Basic

/-!
# Shared search kernels: pure lemmas (stream E)

Word-level facts the kernel block specifications normalize to (`ofNat` masks, xor, unsigned
compares, the 27-bit selection window read from two doublewords), the branch-free bit length of
`select_ok`, its three-element sorting network (`sort3` = Core's `mergeSort`), and the
selection model: `selections N` and `admissible` restated through `selWin`.
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-! ## Word arithmetic -/

theorem ofNat_and_mask (a m : Nat) (_hm : m ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a % 2 ^ m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : i < m <;> simp [h]

@[simp] theorem ofNat_and7 (a : Nat) : BitVec.ofNat 64 a &&& 7#64 = BitVec.ofNat 64 (a % 8) :=
  ofNat_and_mask a 3 (by decide)
@[simp] theorem ofNat_and3 (a : Nat) : BitVec.ofNat 64 a &&& 3#64 = BitVec.ofNat 64 (a % 4) :=
  ofNat_and_mask a 2 (by decide)
@[simp] theorem ofNat_and255 (a : Nat) : BitVec.ofNat 64 a &&& 255#64 = BitVec.ofNat 64 (a % 256) :=
  ofNat_and_mask a 8 (by decide)

theorem ofNat_xor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

theorem ofNat_ult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

@[simp] theorem ofNat_and15 (a : Nat) : BitVec.ofNat 64 a &&& 15#64 = BitVec.ofNat 64 (a % 16) :=
  ofNat_and_mask a 4 (by decide)
@[simp] theorem ofNat_and127 (a : Nat) : BitVec.ofNat 64 a &&& 127#64 = BitVec.ofNat 64 (a % 128) :=
  ofNat_and_mask a 7 (by decide)

/-! ## The branch-free bit length -/

/-- `select_ok`'s bit length of a byte `x`: `8 - #{k ∈ 1..7 | x < 2^k}` (`sltiu` / `sub`). -/
theorem bitlen_word (X : Nat) (hX : X < 256) :
    (((((((8#64 - if (BitVec.ofNat 64 X).ult 2#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 4#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 8#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 16#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 32#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 64#64 = true then 1#64 else 0#64) -
      if (BitVec.ofNat 64 X).ult 128#64 = true then 1#64 else 0#64) =
      BitVec.ofNat 64 (X.log2 + 1) := by
  interval_cases X <;> decide

/-! ## The selection window -/

/-- `N` (the digest output) at `NBUF`, as four doublewords. -/
def NAt (s : MachineState) (N : BitVec 256) : Prop :=
  ∀ j < 4, s.getMem (BitVec.ofNat 64 (NBUF + 8 * j)) = N.extractLsb' (64 * j) 64

/-- The 25-bit window of coordinate `c`: bucket (3 bits) and three 8-bit leaves. -/
def selWin (N : BitVec 256) (c : Nat) : Nat := N.toNat / 2 ^ (31 + 25 * c) % 2 ^ 25

theorem window_bits (N : BitVec 256) (p j sh : Nat) (hp : p = 64 * j + sh) (w0 w1 : BitVec 64)
    (h0 : w0 = N.extractLsb' (64 * j) 64) (h1 : 64 < sh + 25 → w1 = N.extractLsb' (64 * (j + 1)) 64)
    (hsh : sh < 64) :
    (w0 >>> sh ||| w1 <<< (64 - sh)) &&& 33554431#64 =
      BitVec.ofNat 64 (N.toNat / 2 ^ p % 2 ^ 25) := by
  subst hp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (33554431#64).getLsbD i = decide (i < 25) := by
    rw [BitVec.getLsbD_ofNat, show (33554431 : Nat) = 2 ^ 25 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [BitVec.getLsbD_and, hm, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h25 : i < 25
  · simp only [h25, decide_true, Bool.and_true, Bool.true_and, hi]
    rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, h0, BitVec.getLsbD_extractLsb']
    by_cases hc : sh + i < 64
    · have hz : (w1 <<< (64 - sh)).getLsbD i = false := by
        simp only [BitVec.getLsbD_shiftLeft, show i < 64 - sh by omega]; simp
      simp only [hz, Bool.or_false, hc, decide_true, Bool.true_and]
      rw [BitVec.testBit_toNat]; congr 1; omega
    · have hw : 64 < sh + 25 := by omega
      rw [h1 hw]
      simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb']
      have a1 : ¬ i < 64 - sh := by omega
      have a2 : i - (64 - sh) < 64 := by omega
      simp only [hc, hi, a1, a2, decide_false, decide_true, Bool.false_and, Bool.false_or,
        Bool.not_false, Bool.true_and, BitVec.testBit_toNat]
      congr 1; omega
  · simp [h25]

/-- The window of coordinate `c < 7` as `select_ok` extracts it from the doublewords at `NBUF`. -/
theorem window_mem (s : MachineState) (N : BitVec 256) (hN : NAt s N) (c : Nat) (hc : c < 7) :
    (s.getMem (BitVec.ofNat 64 (NBUF + 8 * ((31 + 25 * c) / 64))) >>> ((31 + 25 * c) % 64) |||
      s.getMem (BitVec.ofNat 64 (NBUF + 8 * ((31 + 25 * c) / 64 + 1))) <<< (64 - (31 + 25 * c) % 64)) &&&
        33554431#64 = BitVec.ofNat 64 (selWin N c) := by
  exact window_bits N _ _ _ (by omega) _ _ (hN ((31 + 25 * c) / 64) (by omega))
    (fun _ => hN ((31 + 25 * c) / 64 + 1) (by omega)) (Nat.mod_lt _ (by omega))

/-! ## The sorting network -/

/-- `select_ok`'s network on `(x0, x1, x2)`: compare-exchange (0,1), (1,2), (0,1) (`bge hi, lo`
keeps the pair, else swap: each exchange yields `(min, max)`). -/
def sort3 (x0 x1 x2 : Nat) : List Nat :=
  [min (min x0 x1) (min (max x0 x1) x2), max (min x0 x1) (min (max x0 x1) x2), max (max x0 x1) x2]

theorem sort3_eq (x0 x1 x2 : Nat) : sort3 x0 x1 x2 = [x0, x1, x2].mergeSort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => (decide (a ≤ b)) = true)
  · intro a b _ _ h1 h2; simp at h1 h2; omega
  · simp [sort3]; omega
  · exact List.pairwise_mergeSort (fun a b c h1 h2 => by simp at *; omega)
      (fun a b => by simp; omega) _
  · refine List.Perm.trans ?_ (List.mergeSort_perm _ _).symm
    rw [List.perm_iff_count]
    intro a
    simp only [sort3, List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega

theorem sort3_length (x0 x1 x2 : Nat) : (sort3 x0 x1 x2).length = 3 := rfl

/-! ## The selection model -/

theorem mod_two_pow_div_mod (n k m p : Nat) (h : k + m ≤ p) :
    n % 2 ^ p / 2 ^ k % 2 ^ m = n / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp [hi, show i + k < p by omega]
  · simp [hi]

/-- The bucket of coordinate `c`. -/
def selBucket (N : BitVec 256) (c : Nat) : Nat := selWin N c % 16

/-- The sorted leaves of coordinate `c`. -/
def selRow (N : BitVec 256) (c : Nat) : List Nat :=
  sort3 (selWin N c / 16 % 128) (selWin N c / 2 ^ 11 % 128) (selWin N c / 2 ^ 18 % 128)

/-- `select_ok`'s repeated-leaf test on a sorted row. -/
def rowOk (l : List Nat) : Bool := decide (l.getD 0 0 ≠ l.getD 1 0) && decide (l.getD 1 0 ≠ l.getD 2 0)

/-- `select_ok`'s cost of a sorted row: `4 + bitlen (l0 ⊕ l1) + bitlen (l1 ⊕ l2)`. -/
def rowCost (l : List Nat) : Nat :=
  4 + ((l.getD 0 0 ^^^ l.getD 1 0).log2 + 1) + ((l.getD 1 0 ^^^ l.getD 2 0).log2 + 1)

/-- The accumulated cost of the first `n` coordinates. -/
def selCost (N : BitVec 256) (n : Nat) : Nat := ((List.range n).map fun c => rowCost (selRow N c)).sum

theorem selCost_zero (N : BitVec 256) : selCost N 0 = 0 := rfl

theorem selCost_succ (N : BitVec 256) (n : Nat) : selCost N (n + 1) = selCost N n + rowCost (selRow N n) := by
  simp [selCost, List.range_succ]

theorem selWin_lt (N : BitVec 256) (c : Nat) : selWin N c < 2 ^ 25 := Nat.mod_lt _ (by decide)

theorem selRow_lt (N : BitVec 256) (c j : Nat) : (selRow N c).getD j 0 < 128 := by
  have h1 := Nat.mod_lt (selWin N c / 16) (show 0 < 128 by decide)
  have h2 := Nat.mod_lt (selWin N c / 2 ^ 11) (show 0 < 128 by decide)
  have h3 := Nat.mod_lt (selWin N c / 2 ^ 18) (show 0 < 128 by decide)
  simp only [selRow, sort3]
  rcases j with _ | _ | _ | j <;> simp <;> omega

theorem rowCost_le (N : BitVec 256) (c : Nat) : rowCost (selRow N c) ≤ 20 := by
  have hl : ∀ x < 128, x.log2 < 7 := fun x hx => by
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · exact (Nat.log2_lt (by omega)).2 hx
  have := hl _ (Nat.xor_lt_two_pow (n := 7) (selRow_lt N c 0) (selRow_lt N c 1))
  have := hl _ (Nat.xor_lt_two_pow (n := 7) (selRow_lt N c 1) (selRow_lt N c 2))
  unfold rowCost; omega

theorem selCost_le (N : BitVec 256) (n : Nat) : selCost N n ≤ 20 * n := by
  induction n with
  | zero => simp [selCost_zero]
  | succ n ih => rw [selCost_succ]; have := rowCost_le N n; omega

theorem selections_eq (N : BitVec 256) :
    T3.selections N = (List.range 7).map fun c => ⟨selBucket N c, selRow N c⟩ := by
  unfold T3.selections
  apply List.map_congr_left
  intro c _
  simp only [selBucket, selRow, selWin]
  congr 1
  · rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.mod_mod_of_dvd _ (by decide)]
  · have hk : ∀ n k, k + 7 ≤ 25 → n % 2 ^ 25 / 2 ^ k % 128 = n / 2 ^ k % 128 :=
      fun n k h => mod_two_pow_div_mod n k 7 25 h
    rw [sort3_eq, show (16 : Nat) = 2 ^ 4 from rfl, hk _ 4 (by decide), hk _ 11 (by decide),
      hk _ 18 (by decide)]
    rfl

theorem sort3_nodup (x0 x1 x2 : Nat) : (sort3 x0 x1 x2).Nodup ↔ rowOk (sort3 x0 x1 x2) = true := by
  simp [sort3, rowOk]
  omega

theorem authCount_sort3 (x0 x1 x2 : Nat) : T3.authCount (sort3 x0 x1 x2) + 1 = rowCost (sort3 x0 x1 x2) := by
  simp [T3.authCount, sort3, rowCost]
  omega

/-- `admissible` of the selections of `N`, as `select_ok` computes it. -/
theorem admissible_selections (N : BitVec 256) :
    T3.admissible (T3.selections N) =
      ((List.range 7).all (fun c => rowOk (selRow N c)) && decide (21 + selCost N 7 ≤ 121)) := by
  rw [selections_eq, T3.admissible]
  congr 1
  · simp only [List.all_map, Function.comp_def]
    apply List.all_congr rfl
    intro c
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact sort3_nodup _ _ _
  · have eqCost : 28 + ((List.range 7).map fun c => T3.authCount (selRow N c)).sum =
        21 + selCost N 7 := by
      simp only [selCost, List.range_succ, List.range_zero, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
      have h0 := authCount_sort3 (selWin N 0 / 16 % 128) (selWin N 0 / 2 ^ 11 % 128) (selWin N 0 / 2 ^ 18 % 128)
      have h1 := authCount_sort3 (selWin N 1 / 16 % 128) (selWin N 1 / 2 ^ 11 % 128) (selWin N 1 / 2 ^ 18 % 128)
      have h2 := authCount_sort3 (selWin N 2 / 16 % 128) (selWin N 2 / 2 ^ 11 % 128) (selWin N 2 / 2 ^ 18 % 128)
      have h3 := authCount_sort3 (selWin N 3 / 16 % 128) (selWin N 3 / 2 ^ 11 % 128) (selWin N 3 / 2 ^ 18 % 128)
      have h4 := authCount_sort3 (selWin N 4 / 16 % 128) (selWin N 4 / 2 ^ 11 % 128) (selWin N 4 / 2 ^ 18 % 128)
      have h5 := authCount_sort3 (selWin N 5 / 16 % 128) (selWin N 5 / 2 ^ 11 % 128) (selWin N 5 / 2 ^ 18 % 128)
      have h6 := authCount_sort3 (selWin N 6 / 16 % 128) (selWin N 6 / 2 ^ 11 % 128) (selWin N 6 / 2 ^ 18 % 128)
      simp only [selRow] at *
      omega
    simpa only [List.map_map, Function.comp_def] using congrArg (fun n => decide (n ≤ 121)) eqCost

end SigGolfCandidate.T3M.Search
