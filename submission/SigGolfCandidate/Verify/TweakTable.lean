import SigGolfCandidate.Verify.Words
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem flat_length8 (xs : List Nat) (f : Nat → List Byte) (hf : ∀ j, (f j).length = 8) :
    (xs.flatMap f).length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, hf, Nat.mul_add, Nat.add_comm]

theorem flat_slice8 (xs : List Nat) (f : Nat → List Byte) (hf : ∀ j, (f j).length = 8)
    (j : Nat) (hj : j < xs.length) : slice (xs.flatMap f) (8 * j) 8 = f xs[j] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero => simp only [Nat.mul_zero, slice, List.drop_zero, List.flatMap_cons, List.getElem_cons_zero]
              exact List.take_left' (hf a)
    | succ j =>
      have h : 8 * (j + 1) = 8 + 8 * j := by omega
      simp only [List.flatMap_cons, h, slice]
      rw [← List.drop_drop]
      rw [List.drop_left' (hf a)]
      exact ih j (by simp at hj; omega)

theorem verifyData_length : Images.verifyData.length = 13456 := by
  rw [Images.verifyData, flat_length8 _ _ (by intro j; simp)]
  rw [List.length_range]

theorem verifyData_word (j : Nat) (hj : j < 1682) :
    w64 (slice Images.verifyData (8 * j) 8) = BitVec.ofNat 64 (Images.verifyWord j) := by
  rw [Images.verifyData, flat_slice8 _ _ (by intro j; simp) j (by simpa using hj)]
  simp only [List.getElem_range]
  change BitVec.ofNat 64 (leNat ((List.range 8).map fun k => byte (Images.verifyWord j / 256 ^ k))) = _
  rw [leNat_map_range]
  apply BitVec.eq_of_toNat_eq
  simp only [show 256 ^ 8 = 2 ^ 64 from rfl, BitVec.toNat_ofNat, Nat.mod_mod]

end SigGolfCandidate.Verify
