import SigGolfCandidate.Rv
import SigGolfCandidate.T3.Core

/-!
# Arithmetic of the selection code (no image import)

* `BinOp` evaluation on 64-bit words: `srl_toNat`, `sll_toNat`, `andMask_toNat`, `or_toNat`;
* the 25-bit number of coordinate `c` from one or two words of `N` (`gp_single`, `gp_double`);
* the heap index `(gp >> (3 + 8 j)) & 255 | ((gp & 7 | 8) << 8)` (`xval_eq`);
* `mergeSort3` : the sorted triple from a permutation and the order;
* `selections_getD` : Core's selection `c` as `⟨b, [x0, x1, x2].mergeSort⟩`.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Words -/

theorem srl_toNat (x : Word) (k : Nat) (hk : k < 64) :
    (BinOp.eval .srl x (BitVec.ofNat 64 k)).toNat = x.toNat / 2 ^ k := by
  simp only [BinOp.eval, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]

theorem sll_toNat (x : Word) (k : Nat) (hk : k < 64) :
    (BinOp.eval .sll x (BitVec.ofNat 64 k)).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  simp only [BinOp.eval, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk]

theorem andMask_toNat (x : Word) (k : Nat) (hk : k ≤ 64) :
    (BinOp.eval .and x (BitVec.ofNat 64 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
  simp only [BinOp.eval, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
    omega
  rw [Nat.mod_eq_of_lt this, Nat.and_two_pow_sub_one_eq_mod]

theorem or_toNat (x y : Word) : (BinOp.eval .or x y).toNat = x.toNat ||| y.toNat := by
  simp only [BinOp.eval, BitVec.toNat_or]

/-- `x % 2^n / 2^k % 2^m = x / 2^k % 2^m` when `k + m ≤ n`. -/
theorem mod_div_mod (x n k m : Nat) (h : k + m ≤ n) : x % 2 ^ n / 2 ^ k % 2 ^ m = x / 2 ^ k % 2 ^ m := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self x, ← Nat.pow_add,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]

theorem or_add_shift (X y k : Nat) (hX : X < 2 ^ k) : X ||| 2 ^ k * y = X + 2 ^ k * y := by
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hX]; ring

/-! ## The 25-bit numbers -/

/-- A word of `N`: `W.toNat = N / 2^(64 w) % 2^64`. -/
theorem gp_single (N : Nat) (W : Word) (w o : Nat) (hW : W.toNat = N / 2 ^ (64 * w) % 2 ^ 64)
    (ho : o + 25 ≤ 64) :
    (BinOp.eval .srl W (BitVec.ofNat 64 o)).toNat % 2 ^ 25 = N / 2 ^ (64 * w + o) % 2 ^ 25 := by
  rw [srl_toNat W o (by omega), hW, mod_div_mod _ 64 o 25 ho, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem gp_double (N : Nat) (W W' : Word) (w o : Nat) (hW : W.toNat = N / 2 ^ (64 * w) % 2 ^ 64)
    (hW' : W'.toNat = N / 2 ^ (64 * (w + 1)) % 2 ^ 64) (ho : 0 < o) (ho' : o < 64) :
    (BinOp.eval .or (BinOp.eval .srl W (BitVec.ofNat 64 o))
        (BinOp.eval .sll W' (BitVec.ofNat 64 (64 - o)))).toNat % 2 ^ 25 =
      N / 2 ^ (64 * w + o) % 2 ^ 25 := by
  rw [or_toNat, srl_toNat W o ho', sll_toNat W' (64 - o) (by omega), hW, hW']
  have hN : N / 2 ^ (64 * w + o) = N / 2 ^ (64 * w) / 2 ^ o := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  have hN' : N / 2 ^ (64 * (w + 1)) = N / 2 ^ (64 * w) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]; congr 2
  rw [hN, hN']
  generalize N / 2 ^ (64 * w) = A
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - o) * 2 ^ o := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hlo : A % 2 ^ 64 / 2 ^ o < 2 ^ (64 - o) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e]
    exact Nat.mod_lt _ (by positivity)
  have hhi : A / 2 ^ 64 % 2 ^ 64 * 2 ^ (64 - o) % 2 ^ 64 = 2 ^ (64 - o) * (A / 2 ^ 64 % 2 ^ o) := by
    generalize A / 2 ^ 64 = B
    rw [e, Nat.mul_comm (B % _), Nat.mul_mod_mul_left,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left _ _)]
  rw [hhi, or_add_shift _ _ _ hlo]
  have h1 : A / 2 ^ o % 2 ^ (64 - o) = A % 2 ^ 64 / 2 ^ o := by
    rw [e, Nat.mul_comm (2 ^ (64 - o)), Nat.mod_mul_right_div_self]
  have h2 : A / 2 ^ o / 2 ^ (64 - o) = A / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  have hsum : A % 2 ^ 64 / 2 ^ o + 2 ^ (64 - o) * (A / 2 ^ 64 % 2 ^ o) = A / 2 ^ o % 2 ^ 64 := by
    conv_rhs => rw [e, Nat.mod_mul]
    rw [h1, h2]
  rw [hsum, Nat.mod_mod_of_dvd _ (by norm_num)]

/-! ## Heap indices -/

theorem andMask_toNat' (x : Word) (m k : Nat) (hm : m = 2 ^ k - 1) (hk : k ≤ 64) :
    (BinOp.eval .and x (BitVec.ofNat 64 m)).toNat = x.toNat % 2 ^ k := by
  subst hm; exact andMask_toNat x k hk

/-- `(g >> (3 + 8 j)) & 127 | ((g & 7 | 8) << 8)` for a `g` agreeing with `G` on its low 25 bits. -/
theorem xval_eq (g : Word) (G j : Nat) (hj : j < 3) (hg : g.toNat % 2 ^ 25 = G % 2 ^ 25) :
    BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl g (BitVec.ofNat 64 (4 + 7 * j))) (BitVec.ofNat 64 127))
        (BinOp.eval .sll (BinOp.eval .or (BinOp.eval .and g (BitVec.ofNat 64 15)) (BitVec.ofNat 64 16))
          (BitVec.ofNat 64 7)) =
      BitVec.ofNat 64 (2048 + 128 * (G % 16) + G / 2 ^ (4 + 7 * j) % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [or_toNat, andMask_toNat' _ 127 7 rfl (by decide), srl_toNat _ _ (by omega),
    sll_toNat _ 7 (by decide), or_toNat, andMask_toNat' _ 15 4 rfl (by decide)]
  have h8 : (BitVec.ofNat 64 16).toNat = 2 ^ 4 * 1 := rfl
  rw [h8, or_add_shift _ _ _ (Nat.mod_lt _ (by decide))]
  have hlt : (g.toNat % 2 ^ 4 + 2 ^ 4 * 1) * 2 ^ 7 < 2 ^ 64 := by
    have := Nat.mod_lt g.toNat (show 0 < 2 ^ 4 by decide); omega
  rw [Nat.mod_eq_of_lt hlt, show (g.toNat % 2 ^ 4 + 2 ^ 4 * 1) * 2 ^ 7 = 2 ^ 7 * (g.toNat % 2 ^ 4 + 2 ^ 4 * 1)
    by ring, or_add_shift _ _ _ (Nat.mod_lt _ (by decide))]
  have e1 : g.toNat % 2 ^ 4 = G % 16 := by
    rw [← Nat.mod_mod_of_dvd g.toNat (show 2 ^ 4 ∣ 2 ^ 25 by norm_num), hg,
      Nat.mod_mod_of_dvd _ (show 2 ^ 4 ∣ 2 ^ 25 by norm_num)]; rfl
  have e2 : g.toNat / 2 ^ (4 + 7 * j) % 2 ^ 7 = G / 2 ^ (4 + 7 * j) % 128 := by
    rw [← mod_div_mod g.toNat 25 (4 + 7 * j) 7 (by omega), hg, mod_div_mod G 25 (4 + 7 * j) 7 (by omega)]; rfl
  rw [e1, e2, BitVec.toNat_ofNat]
  have hb : 2048 + 128 * (G % 16) + G / 2 ^ (4 + 7 * j) % 128 < 2 ^ 64 := by
    have := Nat.mod_lt G (show 0 < 16 by decide)
    have := Nat.mod_lt (G / 2 ^ (4 + 7 * j)) (show 0 < 128 by decide)
    omega
  rw [Nat.mod_eq_of_lt hb]
  omega

/-! ## Sorting three numbers -/

theorem mergeSort3 (x0 x1 x2 a b c : Nat) (hp : [a, b, c].Perm [x0, x1, x2]) (hab : a ≤ b) (hbc : b ≤ c) :
    [x0, x1, x2].mergeSort (fun x y => decide (x ≤ y)) = [a, b, c] := by
  apply List.Perm.eq_of_sortedLE
  · rw [List.sortedLE_iff_pairwise]
    exact (List.pairwise_mergeSort (le := fun x y => decide (x ≤ y))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      (fun h => by simpa using h)
  · rw [List.sortedLE_iff_pairwise]
    simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, forall_eq_or_imp,
      forall_eq, or_false, List.Pairwise.nil, and_true, forall_const, IsEmpty.forall_iff, implies_true]
    omega
  · exact (List.mergeSort_perm _ _).trans hp.symm

theorem perm3_0 (x0 x1 x2 : Nat) : [x0, x1, x2].Perm [x0, x1, x2] := List.Perm.refl _
theorem perm3_1 (x0 x1 x2 : Nat) : [x0, x2, x1].Perm [x0, x1, x2] := List.Perm.cons x0 (List.Perm.swap x1 x2 [])
theorem perm3_2 (x0 x1 x2 : Nat) : [x2, x0, x1].Perm [x0, x1, x2] :=
  (List.Perm.swap x0 x2 [x1]).trans (perm3_1 x0 x1 x2)
theorem perm3_3 (x0 x1 x2 : Nat) : [x1, x0, x2].Perm [x0, x1, x2] := List.Perm.swap x0 x1 [x2]
theorem perm3_4 (x0 x1 x2 : Nat) : [x1, x2, x0].Perm [x0, x1, x2] :=
  (List.Perm.cons x1 (List.Perm.swap x0 x2 [])).trans (perm3_3 x0 x1 x2)
theorem perm3_5 (x0 x1 x2 : Nat) : [x2, x1, x0].Perm [x0, x1, x2] :=
  (List.Perm.swap x1 x2 [x0]).trans (perm3_4 x0 x1 x2)

/-! ## Core's selections -/

def selNum (N : Nat) (c : Nat) : Nat := N / 2 ^ (31 + 25 * c)
def selX (N c j : Nat) : Nat := selNum N c / 2 ^ (4 + 7 * j) % 128

theorem selections_getD (N : T3.HashOutput) (c : Nat) (hc : c < 7) :
    (T3.selections N).getD c ⟨0, []⟩ =
      ⟨selNum N.toNat c % 16, [selX N.toNat c 0, selX N.toNat c 1, selX N.toNat c 2].mergeSort
        (fun x y => decide (x ≤ y))⟩ := by
  simp only [T3.selections, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some, selNum, selX]
  rfl

theorem selections_length (N : T3.HashOutput) : (T3.selections N).length = 7 := by
  simp [T3.selections]

end SigGolfCandidate.T3M.Verify
