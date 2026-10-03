import Mathlib

namespace SigGolfCandidate.T3.Rev
def revBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => (v % 2) * 2 ^ n + revBits n (v / 2)
theorem revBits_lt : ∀ (n v : Nat), revBits n v < 2 ^ n
  | 0, _ => by simp [revBits]
  | n + 1, v => by
    have ih := revBits_lt n (v / 2)
    have h2 : v % 2 = 0 ∨ v % 2 = 1 := Nat.mod_two_eq_zero_or_one v
    simp only [revBits, Nat.pow_succ]
    rcases h2 with h | h <;> rw [h] <;> omega
theorem revBits_mod : ∀ (n v : Nat), revBits n (v % 2 ^ n) = revBits n v
  | 0, _ => rfl
  | n + 1, v => by
    simp only [revBits]
    have h1 : v % 2 ^ (n + 1) % 2 = v % 2 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    have h2 : v % 2 ^ (n + 1) / 2 = v / 2 % 2 ^ n := by
      rw [Nat.pow_succ, Nat.mod_mul_left_div_self]
    rw [h1, h2, revBits_mod n (v / 2)]
theorem revBits_succ' : ∀ (n v : Nat), revBits (n + 1) v = 2 * revBits n v + v / 2 ^ n % 2
  | 0, v => by simp [revBits]
  | n + 1, v => by
    have ih := revBits_succ' n (v / 2)
    show (v % 2) * 2 ^ (n + 1) + revBits (n + 1) (v / 2) =
      2 * ((v % 2) * 2 ^ n + revBits n (v / 2)) + v / 2 ^ (n + 1) % 2
    rw [ih, Nat.div_div_eq_div_mul, show 2 * 2 ^ n = 2 ^ (n + 1) by rw [Nat.pow_succ]; ring, Nat.pow_succ]
    ring
theorem revBits_revBits : ∀ (n v : Nat), v < 2 ^ n → revBits n (revBits n v) = v
  | 0, v, h => by simp at h; subst h; rfl
  | n + 1, v, h => by
    have hr := revBits_lt n (v / 2)
    have hv2 : v / 2 < 2 ^ n := by rw [Nat.pow_succ] at h; omega
    have ih := revBits_revBits n (v / 2) hv2
    have h2 : v % 2 = 0 ∨ v % 2 = 1 := Nat.mod_two_eq_zero_or_one v
    rw [revBits_succ']
    have hw : revBits (n + 1) v = (v % 2) * 2 ^ n + revBits n (v / 2) := rfl
    have hdiv : revBits (n + 1) v / 2 ^ n % 2 = v % 2 := by
      rw [hw]; rcases h2 with h2 | h2 <;> rw [h2]
      · simp only [Nat.zero_mul, Nat.zero_add, Nat.div_eq_of_lt hr]
      · rw [Nat.one_mul, Nat.add_comm, Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hr]
    have hmod : revBits n (revBits (n + 1) v) = v / 2 := by
      rw [← revBits_mod n (revBits (n + 1) v), hw]
      rcases h2 with h2 | h2 <;> rw [h2]
      · simp only [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hr, ih]
      · rw [Nat.one_mul, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hr, ih]
    rw [hdiv, hmod]
    omega
theorem revBits_inj {n a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : revBits n a = revBits n b) : a = b := by
  rw [← revBits_revBits n a ha, ← revBits_revBits n b hb, h]
theorem revBits_succ_div (n v : Nat) (hv : v < 2 ^ (n + 1)) :
    revBits (n + 1) (v / 2) = 2 * revBits (n + 1) v % 2 ^ (n + 1) := by
  have h1 : revBits (n + 1) (v / 2) = 2 * revBits n (v / 2) + v / 2 / 2 ^ n % 2 := revBits_succ' n (v / 2)
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
  have h2 : v / 2 / 2 ^ n = 0 := by
    rw [Nat.div_div_eq_div_mul]; apply Nat.div_eq_of_lt; omega
  have h3 : revBits (n + 1) v = (v % 2) * 2 ^ n + revBits n (v / 2) := rfl
  have hr := revBits_lt n (v / 2)
  rw [h1, h2, h3, hp]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> rw [h]
  · simp only [Nat.zero_mod, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [Nat.zero_mod, Nat.add_zero, Nat.one_mul]
    rw [show 2 * (2 ^ n + revBits n (v / 2)) = 2 * revBits n (v / 2) + 2 * 2 ^ n by ring,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
theorem revBits_top (n v : Nat) : revBits (n + 1) v / 2 ^ n = v % 2 := by
  have h : revBits (n + 1) v = (v % 2) * 2 ^ n + revBits n (v / 2) := rfl
  have hr := revBits_lt n (v / 2)
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> rw [h2]
  · simp only [Nat.zero_mul, Nat.zero_add, Nat.div_eq_of_lt hr]
  · rw [Nat.one_mul, Nat.add_comm, Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hr]
theorem xor1_eq (v : Nat) : v ^^^ 1 = if v % 2 = 0 then v + 1 else v - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero]
    split_ifs with h
    · have : (v + 1) % 2 = 1 := by omega
      simp [h, this]
    · have : (v - 1) % 2 = 0 := by omega
      have h' : v % 2 = 1 := by omega
      simp [h', this]
  | succ j =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, show (1 : Nat) / 2 = 0 from rfl,
      Nat.zero_testBit, Bool.xor_false]
    congr 1
    split_ifs <;> omega
theorem xor1_div2 (v : Nat) : (v ^^^ 1) / 2 = v / 2 := by
  rw [xor1_eq]; split_ifs <;> omega
theorem xor1_mod2 (v : Nat) : (v ^^^ 1) % 2 = 1 - v % 2 := by
  rw [xor1_eq]; split_ifs <;> omega
theorem revBits_xor1 (n v : Nat) : revBits (n + 1) (v ^^^ 1) = (revBits (n + 1) v + 2 ^ n) % 2 ^ (n + 1) := by
  have h : ∀ w, revBits (n + 1) w = (w % 2) * 2 ^ n + revBits n (w / 2) := fun w => rfl
  rw [h, h, xor1_div2, xor1_mod2]
  have hr := revBits_lt n (v / 2)
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; ring
  rw [hp]
  rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> rw [h2]
  · simp only [Nat.sub_zero, Nat.one_mul, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]; ring
  · simp only [Nat.sub_self, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    rw [show 2 ^ n + revBits n (v / 2) + 2 ^ n = revBits n (v / 2) + 2 * 2 ^ n by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
end SigGolfCandidate.T3.Rev
