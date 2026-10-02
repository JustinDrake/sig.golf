import SigGolfCandidate.Legacy.Oracle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The PORS node-header field relabelling `efield` (32-bit bit reversal, an involution on
`[0, 2^32)`).

Honest PORS heap indices `H < 2^15` have `efield H = rev16 H * 2^16`: the parent's field is
`2 * efield H mod 2^32` and the direction bit `H mod 2` is bit 31 of `efield H`, so the verifier
derives both from one `slliw`. `revWord H` is `efield H` sign-extended from bit 31 (the register
form the verifier keeps). -/

namespace SigGolfCandidate.Ref.LeafScale

def left3 (v : Nat) : Nat := 8 * (v % 536870912) + v / 536870912 % 8
def right3 (v : Nat) : Nat := v / 8 + 536870912 * (v % 8)

theorem left3_lt (v : Nat) : left3 v < 4294967296 := by
  unfold left3
  have := Nat.mod_lt v (show 0 < 536870912 by decide)
  have := Nat.mod_lt (v / 536870912) (show 0 < 8 by decide)
  omega

theorem right3_left3 (v : Nat) (hv : v < 4294967296) : right3 (left3 v) = v := by
  have hq : v / 536870912 < 8 := by omega
  unfold left3 right3
  rw [Nat.mod_eq_of_lt hq]
  have := Nat.mod_lt v (show 0 < 536870912 by decide)
  have := Nat.mod_lt (v / 536870912) (show 0 < 8 by decide)
  omega

theorem left3_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : left3 a = left3 b) : a = b := by
  have := congrArg right3 h
  rwa [right3_left3 a ha, right3_left3 b hb] at this

theorem left3_small (v : Nat) (hv : v < 536870912) : left3 v = 8 * v := by
  unfold left3
  rw [Nat.mod_eq_of_lt hv, Nat.div_eq_of_lt hv]
  simp

/-! ### The header relabelling shape (tags 9 and 10)

`swRel f` swaps the 32-bit fields 1 and 2 (`p` and `tau mod 2^32`) and maps field 3 (the header)
by `f`: the PORS tweak `tau` then sits in word 0 (one store per buffer, made with the tag) and the
low half of word 1 is the zero field `p`. -/

/-- Little-endian packing of four 32-bit fields and a tail. -/
def pack4 (a b c d R : Nat) : Nat :=
  a + 4294967296 * (b + 4294967296 * (c + 4294967296 * (d + 4294967296 * R)))

theorem pack4_unpack (a b c d R : Nat) (ha : a < 4294967296) (hb : b < 4294967296)
    (hc : c < 4294967296) (hd : d < 4294967296) :
    pack4 a b c d R % 4294967296 = a ∧ pack4 a b c d R / 4294967296 % 4294967296 = b ∧
    pack4 a b c d R / 4294967296 / 4294967296 % 4294967296 = c ∧
    pack4 a b c d R / 4294967296 / 4294967296 / 4294967296 % 4294967296 = d ∧
    pack4 a b c d R / 4294967296 / 4294967296 / 4294967296 / 4294967296 = R := by
  have s : ∀ x y : Nat, x < 4294967296 → (x + 4294967296 * y) % 4294967296 = x ∧
      (x + 4294967296 * y) / 4294967296 = y := fun x y h => ⟨by omega, by omega⟩
  obtain ⟨e1, f1⟩ := s a (b + 4294967296 * (c + 4294967296 * (d + 4294967296 * R))) ha
  obtain ⟨e2, f2⟩ := s b (c + 4294967296 * (d + 4294967296 * R)) hb
  obtain ⟨e3, f3⟩ := s c (d + 4294967296 * R) hc
  obtain ⟨e4, f4⟩ := s d R hd
  unfold pack4
  rw [f1, f2, f3, f4]
  exact ⟨e1, e2, e3, e4, rfl⟩

theorem pack4_digits (w : Nat) :
    pack4 (w % 4294967296) (w / 4294967296 % 4294967296) (w / 4294967296 / 4294967296 % 4294967296)
      (w / 4294967296 / 4294967296 / 4294967296 % 4294967296)
      (w / 4294967296 / 4294967296 / 4294967296 / 4294967296) = w := by
  unfold pack4
  omega

theorem mod32_lt (x : Nat) : x % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)

def swRel (f : Nat → Nat) (w : Nat) : Nat :=
  pack4 (w % 4294967296) (w / 4294967296 / 4294967296 % 4294967296) (w / 4294967296 % 4294967296)
    (f (w / 4294967296 / 4294967296 / 4294967296 % 4294967296))
    (w / 4294967296 / 4294967296 / 4294967296 / 4294967296)

theorem swRel_unpack (f : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296) (w : Nat) :
    swRel f w % 4294967296 = w % 4294967296 ∧
    swRel f w / 4294967296 % 4294967296 = w / 4294967296 / 4294967296 % 4294967296 ∧
    swRel f w / 4294967296 / 4294967296 % 4294967296 = w / 4294967296 % 4294967296 ∧
    swRel f w / 4294967296 / 4294967296 / 4294967296 % 4294967296 =
      f (w / 4294967296 / 4294967296 / 4294967296 % 4294967296) ∧
    swRel f w / 4294967296 / 4294967296 / 4294967296 / 4294967296 =
      w / 4294967296 / 4294967296 / 4294967296 / 4294967296 :=
  pack4_unpack _ _ _ _ _ (mod32_lt _) (mod32_lt _) (mod32_lt _) (hf _ (mod32_lt _))

/-- `swRel g ∘ swRel f = id` when `g` inverts `f` on 32-bit values. -/
theorem swRel_swRel (f g : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296)
    (hgf : ∀ v, v < 4294967296 → g (f v) = v) (w : Nat) : swRel g (swRel f w) = w := by
  obtain ⟨u1, u2, u3, u4, u5⟩ := swRel_unpack f hf w
  show pack4 (swRel f w % 4294967296) (swRel f w / 4294967296 / 4294967296 % 4294967296)
    (swRel f w / 4294967296 % 4294967296)
    (g (swRel f w / 4294967296 / 4294967296 / 4294967296 % 4294967296))
    (swRel f w / 4294967296 / 4294967296 / 4294967296 / 4294967296) = w
  rw [u1, u2, u3, u4, u5, hgf _ (mod32_lt _)]
  exact pack4_digits w

set_option exponentiation.threshold 1024 in
theorem swRel_lt (f : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296) (w : Nat)
    (h : w < 2 ^ 512) : swRel f w < 2 ^ 512 := by
  have hR : w / 4294967296 / 4294967296 / 4294967296 / 4294967296 < 2 ^ 384 := by
    norm_num only [Nat.reducePow] at h ⊢
    omega
  have h4 := hf (w / 4294967296 / 4294967296 / 4294967296 % 4294967296) (mod32_lt _)
  unfold swRel pack4
  generalize f (w / 4294967296 / 4294967296 / 4294967296 % 4294967296) = e at h4 ⊢
  norm_num only [Nat.reducePow] at hR ⊢
  have := mod32_lt w
  have := mod32_lt (w / 4294967296 / 4294967296)
  have := mod32_lt (w / 4294967296)
  omega

theorem swRel_class (f : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296) (w : Nat) :
    swRel f w % 65536 = w % 65536 := by
  have u1 := (swRel_unpack f hf w).1
  generalize swRel f w = x at u1 ⊢
  omega

/-- The swapped words: for a block `a + 2^64 (b + 2^64 R)` (words `a`, `b`), the relabelled words. -/
theorem swRel_eq (f : Nat → Nat) (a b R : Nat) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    swRel f (a + 18446744073709551616 * (b + 18446744073709551616 * R)) =
      (a % 4294967296 + 4294967296 * (b % 4294967296)) + 18446744073709551616 *
        (a / 4294967296 + 4294967296 * f (b / 4294967296) + 18446744073709551616 * R) := by
  have e : a + 18446744073709551616 * (b + 18446744073709551616 * R) =
      pack4 (a % 4294967296) (a / 4294967296) (b % 4294967296) (b / 4294967296) R := by
    unfold pack4; omega
  obtain ⟨u1, u2, u3, u4, u5⟩ := pack4_unpack (a % 4294967296) (a / 4294967296) (b % 4294967296)
    (b / 4294967296) R (mod32_lt _) (by omega) (mod32_lt _) (by omega)
  unfold swRel
  rw [e, u1, u2, u3, u4, u5]
  unfold pack4
  omega

theorem left3_lt' : ∀ v, v < 4294967296 → left3 v < 4294967296 := fun v _ => left3_lt v

/-- The tag-9 relabelling: fields 1, 2 swap; the leaf field is scaled (`left3`). -/
def rel (w : Nat) : Nat := swRel left3 w

def invRel (w : Nat) : Nat := swRel right3 w

theorem invRel_rel (w : Nat) : invRel (rel w) = w :=
  swRel_swRel left3 right3 left3_lt' right3_left3 w

theorem rel_injective : Function.Injective rel := by
  intro a b h
  have := congrArg invRel h
  rwa [invRel_rel, invRel_rel] at this

theorem rel_class (w : Nat) : rel w % 65536 = w % 65536 := swRel_class left3 left3_lt' w

end SigGolfCandidate.Ref.LeafScale

namespace SigGolfCandidate.Ref.LeafScale
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 1024

theorem rel_lt (w : Nat) (hw : w < 2^512) : rel w < 2^512 := swRel_lt left3 left3_lt' w hw

def queryRel : Query → Query
  | ⟨0,w⟩ => if w.toNat % 65536 = 2305 then ⟨0,BitVec.ofNat 512 (rel w.toNat)⟩ else ⟨0,w⟩
  | ⟨n+1,w⟩ => ⟨n+1,w⟩

def queryInv : Query → Query
  | ⟨0,w⟩ => if w.toNat % 65536 = 2305 then ⟨0,BitVec.ofNat 512 (invRel w.toNat)⟩ else ⟨0,w⟩
  | ⟨n+1,w⟩ => ⟨n+1,w⟩

theorem queryInv_queryRel : Function.LeftInverse queryInv queryRel := by
  rintro ⟨n,w⟩
  cases n with
  | zero =>
    by_cases h : w.toNat % 65536 = 2305
    · have hb := rel_lt _ w.isLt
      have hc : (BitVec.ofNat 512 (rel w.toNat)).toNat % 65536 = 2305 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, rel_class]
        exact h
      simp only [queryRel, if_pos h, queryInv, if_pos hc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hb, invRel_rel, Nat.mod_eq_of_lt w.isLt]
    · simp only [queryRel, if_neg h, queryInv]
  | succ n => rfl

theorem queryRel_injective : Function.Injective queryRel := queryInv_queryRel.injective

theorem queryRel_blocks (q : Query) : (queryRel q).blocks = q.blocks := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => simp only [queryRel]; split <;> rfl
  | succ n => rfl

theorem queryRel_fixed (q : Query) (h : q.2.toNat % 65536 ≠ 2305) : queryRel q = q := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => exact if_neg h
  | succ n => rfl

end SigGolfCandidate.Ref.LeafScale

namespace SigGolfCandidate.Ref.Rev

/-- Bit reversal of the low `n` bits: bit `i` of `v` goes to bit `n - 1 - i`. -/
def revBits : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, v => (v % 2) * 2 ^ n + revBits n (v / 2)

/-- The relabelled 32-bit header field. -/
def efield (v : Nat) : Nat := revBits 32 v

/-- A 32-bit value sign-extended to 64 bits (as a `Nat` below `2^64`). -/
def sext32 (v : Nat) : Nat := if v < 2 ^ 31 then v else 2 ^ 64 - 2 ^ 32 + v

/-- The verifier's register form of heap index `H`: `efield H` sign-extended. -/
def revWord (H : Nat) : BitVec 64 := BitVec.ofNat 64 (sext32 (efield H))

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

/-- The top bit moves to the bottom: `revBits (n+1) v = revBits n (v mod 2^n) * 2 + v / 2^n % 2`. -/
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

theorem efield_lt (v : Nat) : efield v < 2 ^ 32 := revBits_lt 32 v

theorem efield_efield (v : Nat) (h : v < 2 ^ 32) : efield (efield v) = v :=
  revBits_revBits 32 v h

/-! ## The verifier's fold algebra -/

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

/-- The parent's field: one left shift (mod `2^32`) of the child's. -/
theorem efield_div2 (v : Nat) (hv : v < 2 ^ 32) : efield (v / 2) = 2 * efield v % 2 ^ 32 :=
  revBits_succ_div 31 v hv

/-- The direction bit is the top bit of the field. -/
theorem efield_top (v : Nat) : efield v / 2 ^ 31 = v % 2 := by
  have h : efield v = (v % 2) * 2 ^ 31 + revBits 31 (v / 2) := rfl
  have hr := revBits_lt 31 (v / 2)
  rw [h]
  rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> rw [h2] <;> omega

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

/-- The sibling: flipping bit 0 flips the top bit of the field. -/
theorem efield_xor1 (v : Nat) : efield (v ^^^ 1) = (efield v + 2 ^ 31) % 2 ^ 32 := by
  have h : ∀ w, efield w = (w % 2) * 2 ^ 31 + revBits 31 (w / 2) := fun w => rfl
  rw [h, h, xor1_div2, xor1_mod2]
  have hr := revBits_lt 31 (v / 2)
  rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> rw [h2] <;> omega

theorem efield_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : efield a = efield b) : a = b := by
  rw [← efield_efield a ha, ← efield_efield b hb, h]


theorem efield_mod (v : Nat) : efield (v % 2 ^ 32) = efield v := revBits_mod 32 v

theorem sext32_lt (v : Nat) (h : v < 2 ^ 32) : sext32 v < 2 ^ 64 := by
  unfold sext32; split_ifs <;> omega

theorem revWord_toNat (H : Nat) : (revWord H).toNat = sext32 (efield H) := by
  have := sext32_lt _ (efield_lt H)
  simp only [revWord, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt this


/-! ## The register form `revWord` -/

theorem sext32_trunc (v : Nat) (h : v < 2 ^ 32) : sext32 v % 2 ^ 32 = v := by
  unfold sext32; split_ifs <;> omega

theorem revWord_trunc (H : Nat) : (revWord H).toNat % 2 ^ 32 = efield H := by
  rw [revWord_toNat]; exact sext32_trunc _ (efield_lt H)

theorem signExtend_sext32 (x : BitVec 32) : (x.signExtend 64).toNat = sext32 x.toNat := by
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth]
  have := x.isLt
  unfold sext32
  by_cases h : x.toNat < 2 ^ 31
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]
    simp only [show (32 : Nat) - 1 = 31 from rfl, show ¬ (2 ^ 31 ≤ x.toNat) by omega, decide_false]
    rfl
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
    simp only [show (32 : Nat) - 1 = 31 from rfl, show 2 ^ 31 ≤ x.toNat by omega, decide_true, if_true]
    omega

/-- `slliw r, r, 1`: the parent's register form. -/
theorem slliw_revWord (E : Nat) (hE : E < 2 ^ 32) :
    (((revWord E).setWidth 32) <<< 1).signExtend 64 = revWord (E / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [signExtend_sext32, revWord_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, revWord_trunc,
    efield_div2 E hE, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

/-- `addw r, r, x28` (`x28 = sext32 (2^31)`): the sibling's register form. -/
theorem addw_revWord (E : Nat) :
    ((revWord E).setWidth 32 + (BitVec.ofNat 64 (2 ^ 64 - 2 ^ 31)).setWidth 32).signExtend 64 =
      revWord (E ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [signExtend_sext32, revWord_toNat, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    revWord_trunc, efield_xor1, BitVec.toNat_ofNat]
  norm_num

/-- The sign of the register form is the direction bit. -/
theorem revWord_msb (E : Nat) : (revWord E).msb = decide (E % 2 = 1) := by
  rw [BitVec.msb_eq_decide, revWord_toNat]
  have ht := efield_top E
  have hl := efield_lt E
  unfold sext32
  split_ifs with h
  · simp only [show (64 : Nat) - 1 = 63 from rfl]
    rw [decide_eq_decide]; omega
  · simp only [show (64 : Nat) - 1 = 63 from rfl]
    rw [decide_eq_decide]; omega

theorem sext32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : sext32 a = sext32 b) : a = b := by
  rw [← sext32_trunc a ha, ← sext32_trunc b hb, h]

theorem revWord_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : revWord a = revWord b) : a = b := by
  have := congrArg BitVec.toNat h
  rw [revWord_toNat, revWord_toNat] at this
  exact efield_inj ha hb (sext32_inj (efield_lt a) (efield_lt b) this)

theorem revWord_one : revWord 1 = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 31) := by decide

/-- The root test `bne r, x28`. -/
theorem revWord_eq_one (E : Nat) (hE : E < 2 ^ 32) :
    revWord E = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 31) ↔ E = 1 := by
  rw [← revWord_one]
  exact ⟨fun h => revWord_inj hE (by decide) h, fun h => h ▸ rfl⟩

/-- The empty-stack guard `2^32` is never a register form. -/
theorem revWord_ne_guard (E : Nat) : revWord E ≠ 0x100000000#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [revWord_toNat] at this
  have hl := efield_lt E
  unfold sext32 at this
  split_ifs at this <;> simp at this <;> omega

end SigGolfCandidate.Ref.Rev

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

/-! ## The PORS node-header relabelling

A one-block query whose first two bytes are `1, 10` (a PORS node input, word-0 low half `2561`)
has its 32-bit header field (bits `96 .. 128`, the heap index `H`) relabelled by `Rev.efield`
(32-bit bit reversal, an involution) and its fields 1, 2 swapped (`LeafScale.swRel`). The class is disjoint from both chain-header classes
(`wordPerm` maps every word outside `2561` to a word outside `2561`), so the whole map stays an
involution. -/

def nodeRel (w : Nat) : Nat := LeafScale.swRel Rev.efield w

theorem efield_lt' : ∀ v, v < 4294967296 → Rev.efield v < 4294967296 := fun v _ => Rev.efield_lt v

theorem nodeRel_involutive : Function.Involutive nodeRel :=
  LeafScale.swRel_swRel Rev.efield Rev.efield efield_lt' (fun v h => Rev.efield_efield v h)

theorem nodeRel_lt (w : Nat) (h : w < 2 ^ 512) : nodeRel w < 2 ^ 512 :=
  LeafScale.swRel_lt _ efield_lt' w h

theorem nodeRel_class (w : Nat) : nodeRel w % 65536 = w % 65536 := LeafScale.swRel_class _ efield_lt' w

theorem wordPerm_class (w : Nat) (h : w % 65536 ≠ 2561) : wordPerm w % 65536 ≠ 2561 := by
  unfold wordPerm
  split_ifs with ho hn
  · simp only [oldValid] at ho
    unfold oldToNew
    omega
  · simp only [newValid] at hn
    dsimp only [newToOld]
    omega
  · exact h

theorem payloadPerm_class (w : Nat) (h : w % 65536 ≠ 2561) : payloadPerm w % 65536 ≠ 2561 := by
  have h' : w % 18446744073709551616 % 65536 ≠ 2561 := by omega
  have := wordPerm_class _ h'
  unfold payloadPerm
  omega

/-- The relabelling of a one-block payload. -/
def fullPerm (w : Nat) : Nat := if w % 65536 = 2561 then nodeRel w else payloadPerm w

theorem fullPerm_involutive : Function.Involutive fullPerm := by
  intro w
  by_cases h : w % 65536 = 2561
  · have h' : nodeRel w % 65536 = 2561 := by rw [nodeRel_class]; exact h
    simp only [fullPerm, if_pos h, if_pos h', nodeRel_involutive w]
  · have h' := payloadPerm_class w h
    simp only [fullPerm, if_neg h, if_neg h', payloadPerm_involutive w]

theorem fullPerm_lt (w : Nat) (h : w < 2 ^ 512) : fullPerm w < 2 ^ 512 := by
  unfold fullPerm
  split_ifs
  · exact nodeRel_lt w h
  · exact payloadPerm_lt w h

theorem fullPerm_of_ne (w : Nat) (h : w % 65536 ≠ 2561) : fullPerm w = payloadPerm w := by
  simp only [fullPerm, if_neg h]

theorem fullPerm_of_eq (w : Nat) (h : w % 65536 = 2561) : fullPerm w = nodeRel w := by
  simp only [fullPerm, if_pos h]

def baseQueryPerm : Query → Query
  | ⟨0, w⟩ => ⟨0, BitVec.ofNat 512 (fullPerm w.toNat)⟩
  | ⟨n + 1, w⟩ => ⟨n + 1, w⟩

theorem baseQueryPerm_involutive : Function.Involutive baseQueryPerm := by
  rintro ⟨n, w⟩
  cases n with
  | zero =>
    simp only [baseQueryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (fullPerm_lt _ w.isLt), fullPerm_involutive,
      Nat.mod_eq_of_lt w.isLt]
  | succ n => rfl

theorem baseQueryPerm_injective : Function.Injective baseQueryPerm :=
  baseQueryPerm_involutive.injective

theorem baseQueryPerm_blocks (q : Query) : (baseQueryPerm q).blocks = q.blocks := by
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

theorem baseQueryPerm_fixed (q : Query) (h0 : q.2.toNat % 64 ≠ 0)
    (h1 : q.2.toNat % 65536 ≠ 257) (h2 : q.2.toNat % 65536 ≠ 2561) : baseQueryPerm q = q := by
  rcases q with ⟨n, w⟩
  cases n with
  | zero =>
    have h0' : w.toNat % 18446744073709551616 % 64 ≠ 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 64 ∣ 18446744073709551616)]
      exact h0
    have h1' : w.toNat % 18446744073709551616 % 65536 ≠ 257 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 65536 ∣ 18446744073709551616)]
      exact h1
    simp only [baseQueryPerm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, fullPerm_of_ne _ h2, payloadPerm, wordPerm_fixed _ h0' h1']
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

namespace SigGolfCandidate.Ref.LeafClass
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 8192

def header (h : Nat) : Nat := if h=513 then 1025 else if h=1025 then 513 else h

theorem header_lt {h : Nat} (hh : h<65536) : header h<65536 := by
  unfold header;split_ifs <;> omega

theorem header_involutive : Function.Involutive header := by
  intro h
  unfold header
  split_ifs <;> omega

def word (w : Nat) : Nat := header (w%65536)+65536*(w/65536)

theorem word_parts (w : Nat) : word w%65536= header (w%65536) ∧ word w/65536=w/65536 := by
  have hh := header_lt (Nat.mod_lt w (by decide))
  unfold word
  omega

theorem word_involutive : Function.Involutive word := by
  intro w
  obtain ⟨hc,hq⟩ := word_parts w
  change header (word w%65536)+65536*(word w/65536)=w
  rw [hc,hq,header_involutive]
  omega

theorem word_lt_mul {w cap : Nat} (hw : w<65536*cap) : word w<65536*cap := by
  have hh := header_lt (Nat.mod_lt w (by decide))
  unfold word
  omega

theorem word_lt (w : Nat) (hw : w<2^5632) : word w<2^5632 := by
  have hp : (2:Nat)^5632=65536*2^5616 := by
    rw [show (5632:Nat)=16+5616 by decide,Nat.pow_add]
  rw [hp] at hw ⊢
  exact word_lt_mul hw

/-- Transpose only the tag2/tag4 classes of exact11-block queries. Every other
length and every malformed header outside these two classes is fixed. -/
def query (q : Query) : Query :=
  if q.1=10 then ⟨q.1,BitVec.ofNat (8*(64*(q.1+1))) (word q.2.toNat)⟩ else q

theorem query_involutive : Function.Involutive query := by
  rintro ⟨n,w⟩
  by_cases hn:n=10
  · subst n
    change (⟨10,BitVec.ofNat 5632 (word (BitVec.ofNat 5632 (word w.toNat)).toNat)⟩ : Query)=⟨10,w⟩
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (word_lt _ w.isLt),word_involutive,Nat.mod_eq_of_lt w.isLt]
  · simp only [query,if_neg hn]

theorem query_blocks (q : Query) : (query q).blocks=q.blocks := by
  rcases q with ⟨n,w⟩
  simp only [query];split <;> rfl

theorem query_fixed_length (q : Query) (h:q.1≠10) : query q=q := by
  rcases q with ⟨n,w⟩
  exact if_neg h

theorem word_fixed (w : Nat) (h2:w%65536≠513) (h4:w%65536≠1025) : word w=w := by
  unfold word header
  rw [if_neg h2,if_neg h4]
  omega

theorem query_fixed (q : Query) (h2:q.2.toNat%65536≠513) (h4:q.2.toNat%65536≠1025) : query q=q := by
  rcases q with ⟨n,w⟩
  unfold query
  split
  · rw [word_fixed _ h2 h4]
    congr 1
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt w.isLt
  · rfl
end SigGolfCandidate.Ref.LeafClass

namespace SigGolfCandidate.Ref.TopHeap
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 8192
set_option maxHeartbeats 1000000

def mirror (e : Nat) : Nat :=
  if e<2 then e else
  if e<4 then 5-e else
  if e<8 then 11-e else
  if e<16 then 23-e else
  if e<32 then 47-e else
  if e<64 then 95-e else
  if e<128 then 191-e else
  if e<256 then 383-e else
  if e<512 then 767-e else
  if e<1024 then 1535-e else
  if e<2048 then 3071-e else
  e

theorem mirror_involutive : Function.Involutive mirror := by
  intro e
  by_cases h0:e<2
  · have hm:mirror e=e := by simp only [mirror,if_pos h0]
    rw [hm,hm]
  by_cases h1:e<4
  · have hm:mirror e=5-e := by simp only [mirror,if_neg h0,if_pos h1]
    have hmlo:2≤5-e := by omega
    have hmhi:5-e<4 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(5-e<2) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h2:e<8
  · have hm:mirror e=11-e := by simp only [mirror,if_neg h0,if_neg h1,if_pos h2]
    have hmlo:4≤11-e := by omega
    have hmhi:11-e<8 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(11-e<2) by omega)]
    rw [if_neg (show ¬(11-e<4) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h3:e<16
  · have hm:mirror e=23-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_pos h3]
    have hmlo:8≤23-e := by omega
    have hmhi:23-e<16 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(23-e<2) by omega)]
    rw [if_neg (show ¬(23-e<4) by omega)]
    rw [if_neg (show ¬(23-e<8) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h4:e<32
  · have hm:mirror e=47-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4]
    have hmlo:16≤47-e := by omega
    have hmhi:47-e<32 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(47-e<2) by omega)]
    rw [if_neg (show ¬(47-e<4) by omega)]
    rw [if_neg (show ¬(47-e<8) by omega)]
    rw [if_neg (show ¬(47-e<16) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h5:e<64
  · have hm:mirror e=95-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5]
    have hmlo:32≤95-e := by omega
    have hmhi:95-e<64 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(95-e<2) by omega)]
    rw [if_neg (show ¬(95-e<4) by omega)]
    rw [if_neg (show ¬(95-e<8) by omega)]
    rw [if_neg (show ¬(95-e<16) by omega)]
    rw [if_neg (show ¬(95-e<32) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h6:e<128
  · have hm:mirror e=191-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6]
    have hmlo:64≤191-e := by omega
    have hmhi:191-e<128 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(191-e<2) by omega)]
    rw [if_neg (show ¬(191-e<4) by omega)]
    rw [if_neg (show ¬(191-e<8) by omega)]
    rw [if_neg (show ¬(191-e<16) by omega)]
    rw [if_neg (show ¬(191-e<32) by omega)]
    rw [if_neg (show ¬(191-e<64) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h7:e<256
  · have hm:mirror e=383-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7]
    have hmlo:128≤383-e := by omega
    have hmhi:383-e<256 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(383-e<2) by omega)]
    rw [if_neg (show ¬(383-e<4) by omega)]
    rw [if_neg (show ¬(383-e<8) by omega)]
    rw [if_neg (show ¬(383-e<16) by omega)]
    rw [if_neg (show ¬(383-e<32) by omega)]
    rw [if_neg (show ¬(383-e<64) by omega)]
    rw [if_neg (show ¬(383-e<128) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h8:e<512
  · have hm:mirror e=767-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8]
    have hmlo:256≤767-e := by omega
    have hmhi:767-e<512 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(767-e<2) by omega)]
    rw [if_neg (show ¬(767-e<4) by omega)]
    rw [if_neg (show ¬(767-e<8) by omega)]
    rw [if_neg (show ¬(767-e<16) by omega)]
    rw [if_neg (show ¬(767-e<32) by omega)]
    rw [if_neg (show ¬(767-e<64) by omega)]
    rw [if_neg (show ¬(767-e<128) by omega)]
    rw [if_neg (show ¬(767-e<256) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h9:e<1024
  · have hm:mirror e=1535-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9]
    have hmlo:512≤1535-e := by omega
    have hmhi:1535-e<1024 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(1535-e<2) by omega)]
    rw [if_neg (show ¬(1535-e<4) by omega)]
    rw [if_neg (show ¬(1535-e<8) by omega)]
    rw [if_neg (show ¬(1535-e<16) by omega)]
    rw [if_neg (show ¬(1535-e<32) by omega)]
    rw [if_neg (show ¬(1535-e<64) by omega)]
    rw [if_neg (show ¬(1535-e<128) by omega)]
    rw [if_neg (show ¬(1535-e<256) by omega)]
    rw [if_neg (show ¬(1535-e<512) by omega)]
    rw [if_pos hmhi]
    omega
  by_cases h10:e<2048
  · have hm:mirror e=3071-e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10]
    have hmlo:1024≤3071-e := by omega
    have hmhi:3071-e<2048 := by omega
    rw [hm]
    unfold mirror
    rw [if_neg (show ¬(3071-e<2) by omega)]
    rw [if_neg (show ¬(3071-e<4) by omega)]
    rw [if_neg (show ¬(3071-e<8) by omega)]
    rw [if_neg (show ¬(3071-e<16) by omega)]
    rw [if_neg (show ¬(3071-e<32) by omega)]
    rw [if_neg (show ¬(3071-e<64) by omega)]
    rw [if_neg (show ¬(3071-e<128) by omega)]
    rw [if_neg (show ¬(3071-e<256) by omega)]
    rw [if_neg (show ¬(3071-e<512) by omega)]
    rw [if_neg (show ¬(3071-e<1024) by omega)]
    rw [if_pos hmhi]
    omega
  have hm:mirror e=e := by simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10]
  rw [hm,hm]

theorem mirror_lt : ∀e:Nat,e<4294967296 → mirror e<4294967296 := by
  intro e he
  by_cases h0:e<2
  · simp only [mirror,if_pos h0];omega
  by_cases h1:e<4
  · simp only [mirror,if_neg h0,if_pos h1];omega
  by_cases h2:e<8
  · simp only [mirror,if_neg h0,if_neg h1,if_pos h2];omega
  by_cases h3:e<16
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_pos h3];omega
  by_cases h4:e<32
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4];omega
  by_cases h5:e<64
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5];omega
  by_cases h6:e<128
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6];omega
  by_cases h7:e<256
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7];omega
  by_cases h8:e<512
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8];omega
  by_cases h9:e<1024
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9];omega
  by_cases h10:e<2048
  · simp only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10];omega
  simpa only [mirror,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10] using he

def word (w : Nat) : Nat := LeafScale.pack4 (w%4294967296) (w/4294967296%4294967296)
  (w/4294967296/4294967296%4294967296) (mirror (w/4294967296/4294967296/4294967296%4294967296))
  (w/4294967296/4294967296/4294967296/4294967296)

theorem word_parts (w : Nat) :
    word w%4294967296=w%4294967296 ∧
    word w/4294967296%4294967296=w/4294967296%4294967296 ∧
    word w/4294967296/4294967296%4294967296=w/4294967296/4294967296%4294967296 ∧
    word w/4294967296/4294967296/4294967296%4294967296=mirror (w/4294967296/4294967296/4294967296%4294967296) ∧
    word w/4294967296/4294967296/4294967296/4294967296=w/4294967296/4294967296/4294967296/4294967296 :=
  LeafScale.pack4_unpack _ _ _ _ _ (LeafScale.mod32_lt _) (LeafScale.mod32_lt _) (LeafScale.mod32_lt _) (mirror_lt _ (LeafScale.mod32_lt _))

theorem word_involutive : Function.Involutive word := by
  intro w
  obtain ⟨a,b,c,d,e⟩ := word_parts w
  change LeafScale.pack4 (word w%4294967296) (word w/4294967296%4294967296)
    (word w/4294967296/4294967296%4294967296) (mirror (word w/4294967296/4294967296/4294967296%4294967296))
    (word w/4294967296/4294967296/4294967296/4294967296)=w
  rw [a,b,c,d,e,mirror_involutive]
  exact LeafScale.pack4_digits w

theorem word_header (w : Nat) : word w%18446744073709551616=w%18446744073709551616 := by
  obtain ⟨a,b,c,d,e⟩ := word_parts w
  omega

theorem word_lt (w : Nat) (hw:w<2^512) : word w<2^512 := by
  have h := (word_parts w).2.2.2.2
  simp only [Nat.div_div_eq_div_mul] at h
  norm_num only [Nat.reduceMul,Nat.reducePow] at h hw ⊢
  omega

def query : Query → Query
  | ⟨0,w⟩ => if w.toNat%18446744073709551616=769 then ⟨0,BitVec.ofNat 512 (word w.toNat)⟩ else ⟨0,w⟩
  | ⟨n+1,w⟩ => ⟨n+1,w⟩

theorem query_involutive : Function.Involutive query := by
  rintro ⟨n,w⟩
  cases n with
  | zero =>
      by_cases h:w.toNat%18446744073709551616=769
      · have hw := word_lt _ w.isLt
        have hc : (BitVec.ofNat 512 (word w.toNat)).toNat%18446744073709551616=769 := by
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hw,word_header];exact h
        simp only [query,if_pos h,if_pos hc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt hw,word_involutive,Nat.mod_eq_of_lt w.isLt]
      · simp only [query,if_neg h]
  | succ n => rfl

theorem query_blocks (q : Query) : (query q).blocks=q.blocks := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => simp only [query];split <;> rfl
  | succ n => rfl

theorem query_fixed (q : Query) (h:q.2.toNat%18446744073709551616≠769) : query q=q := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => exact if_neg h
  | succ n => rfl

theorem query_fixed_class (q : Query) (h0:q.2.toNat%65536≠769) : query q=q := by
  apply query_fixed
  omega

end SigGolfCandidate.Ref.TopHeap

namespace SigGolfCandidate.Ref.EncodingRotate
set_option Elab.async false
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
open SigGolfCandidate.Legacy

def B : Nat := 2^128
def C : Nat := 2^256
def D : Nat := 2^384
def E : Nat := 2^512
/-- Rotate [L,R,padded counter] to [padded counter,L,R], preserving tweak and high bits. -/
def word (w : Nat) : Nat := w%B+B*(w/D%B)+C*(w/B%B)+D*(w/C%B)+E*(w/E)
theorem word_parts (w : Nat) : word w%B=w%B ∧ word w/B%B=w/D%B ∧
    word w/C%B=w/B%B ∧ word w/D%B=w/C%B ∧ word w/E=w/E := by
  have h0 : w%B<B := Nat.mod_lt _ (by decide)
  have h1 : w/D%B<B := Nat.mod_lt _ (by decide)
  have h2 : w/B%B<B := Nat.mod_lt _ (by decide)
  have h3 : w/C%B<B := Nat.mod_lt _ (by decide)
  have hBB : B*B=C := by norm_num [B,C]
  have hCB : C*B=D := by norm_num [C,B,D]
  have hDB : D*B=E := by norm_num [D,B,E]
  have he : word w = w%B+B*((w/D%B)+B*((w/B%B)+B*((w/C%B)+B*(w/E)))) := by
    dsimp [word,B,C,D,E]; ring
  have q1 : word w/B = (w/D%B)+B*((w/B%B)+B*((w/C%B)+B*(w/E))) := by
    rw [he,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h0]; simp
  have q2 : word w/C = (w/B%B)+B*((w/C%B)+B*(w/E)) := by
    rw [←hBB,←Nat.div_div_eq_div_mul,q1,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h1]; simp [hBB]
  have q3 : word w/D = (w/C%B)+B*(w/E) := by
    rw [←hCB,←Nat.div_div_eq_div_mul,q2,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h2]; simp [hCB]
  have q4 : word w/E = w/E := by
    rw [←hDB,←Nat.div_div_eq_div_mul,q3,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h3]; simp only [hDB,Nat.zero_add]
  refine ⟨?_,?_,?_,?_,q4⟩
  · rw [he,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · rw [q1,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · rw [q2,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · rw [q3,Nat.add_mul_mod_self_left,Nat.mod_mod]

theorem decompose (w : Nat) : w=w%B+B*(w/B%B)+C*(w/C%B)+D*(w/D%B)+E*(w/E) := by
  have h1 : w/B/B=w/C := by simp only [Nat.div_div_eq_div_mul]; norm_num [B,C]
  have h2 : w/C/B=w/D := by simp only [Nat.div_div_eq_div_mul]; norm_num [B,C,D]
  have h3 : w/D/B=w/E := by simp only [Nat.div_div_eq_div_mul]; norm_num [B,D,E]
  norm_num [B,C,D,E] at h1 h2 h3 ⊢
  omega

theorem word_thrice (w : Nat) : word (word (word w))=w := by
  obtain ⟨a0,a1,a2,a3,a4⟩ := word_parts w
  obtain ⟨b0,b1,b2,b3,b4⟩ := word_parts (word w)
  obtain ⟨c0,c1,c2,c3,c4⟩ := word_parts (word (word w))
  rw [decompose (word (word (word w))),c0,c1,c2,c3,c4,b0,b1,b2,b3,b4,a0,a1,a2,a3,a4]
  exact (decompose w).symm

theorem word_lt (w : Nat) (h : w<2^512) : word w<2^512 := by
  have hq := (word_parts w).2.2.2.2
  norm_num [E] at hq
  omega

theorem word_class (w : Nat) : word w%65536=w%65536 := by
  have hq := (word_parts w).1
  norm_num [B] at hq
  omega

def query : Query → Query
  | ⟨0,w⟩ => if w.toNat%65536=1025 then ⟨0,BitVec.ofNat 512 (word w.toNat)⟩ else ⟨0,w⟩
  | ⟨n+1,w⟩ => ⟨n+1,w⟩
theorem query_thrice (q : Query) : query (query (query q))=q := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero =>
    by_cases hc : w.toNat%65536=1025
    · have h1 := word_lt _ w.isLt
      have h2 := word_lt _ h1
      have c1 : (BitVec.ofNat 512 (word w.toNat)).toNat%65536=1025 := by
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,word_class]; exact hc
      have c2 : (BitVec.ofNat 512 (word (word w.toNat))).toNat%65536=1025 := by
        rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,word_class,word_class]; exact hc
      simp only [query,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2,word_class,if_pos hc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt h2,word_thrice,Nat.mod_eq_of_lt w.isLt]
    · simp only [query,if_neg hc]
  | succ n => rfl

def queryInverse (q : Query) : Query := query (query q)
theorem queryInverse_query (q : Query) : queryInverse (query q)=q := query_thrice q
theorem query_queryInverse (q : Query) : query (queryInverse q)=q := query_thrice q
theorem query_injective : Function.Injective query := by
  intro a b h
  have h' := congrArg queryInverse h
  simpa only [queryInverse_query] using h'
theorem query_blocks (q : Query) : (query q).blocks=q.blocks := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => simp only [query]; split <;> rfl
  | succ n => rfl
theorem word_eq (a b c d : Nat) (ha : a<2^128) (hb : b<2^128)
    (hc : c<2^128) (hd : d<2^128) :
    word (a+2^128*b+2^256*c+2^384*d) = a+2^128*d+2^256*b+2^384*c := by
  unfold word
  norm_num only [B,C,D,E,Nat.reducePow] at ha hb hc hd ⊢
  omega

theorem query_fixed (q : Query) (h : q.2.toNat%65536≠1025) : query q=q := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => exact if_neg h
  | succ n => rfl
end SigGolfCandidate.Ref.EncodingRotate

namespace SigGolfCandidate.Ref.LeafCarry
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 8192
set_option maxHeartbeats 1000000

def header (h : Nat) : Nat :=
  if h=1025 then 66305 else if h=66305 then 1025 else
  if h=66561 then 131841 else if h=131841 then 66561 else
  if h=132097 then 197377 else if h=197377 then 132097 else
  if h=197633 then 262913 else if h=262913 then 197633 else h

theorem header_lt {h : Nat} (hh:h<18446744073709551616) : header h<18446744073709551616 := by
  unfold header;split_ifs <;> omega

theorem header_involutive : Function.Involutive header := by
  intro h
  by_cases h0:h=1025
  · subst h;decide
  by_cases h1:h=66305
  · subst h;decide
  by_cases h2:h=66561
  · subst h;decide
  by_cases h3:h=131841
  · subst h;decide
  by_cases h4:h=132097
  · subst h;decide
  by_cases h5:h=197377
  · subst h;decide
  by_cases h6:h=197633
  · subst h;decide
  by_cases h7:h=262913
  · subst h;decide
  simp only [header,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7]

def word (w : Nat) : Nat := header (w%18446744073709551616)+18446744073709551616*(w/18446744073709551616)

theorem word_parts (w : Nat) :
    word w%18446744073709551616=header (w%18446744073709551616) ∧
    word w/18446744073709551616=w/18446744073709551616 := by
  have hh := header_lt (Nat.mod_lt w (by decide))
  unfold word
  omega

theorem word_involutive : Function.Involutive word := by
  intro w
  obtain ⟨hc,hq⟩ := word_parts w
  change header (word w%18446744073709551616)+18446744073709551616*(word w/18446744073709551616)=w
  rw [hc,hq,header_involutive]
  omega

theorem word_lt (w : Nat) (hw:w<2^5632) : word w<2^5632 := by
  have hq := (word_parts w).2
  have hp : (2:Nat)^5632=18446744073709551616*2^5568 := by
    rw [show (5632:Nat)=64+5568 by decide,Nat.pow_add]
  rw [hp] at hw ⊢
  omega

/-- Four complete-header transpositions on704-byte queries only. -/
def query (q : Query) : Query :=
  if q.1=10 then ⟨q.1,BitVec.ofNat (8*(64*(q.1+1))) (word q.2.toNat)⟩ else q

theorem query_involutive : Function.Involutive query := by
  rintro ⟨n,w⟩
  by_cases hn:n=10
  · subst n
    change (⟨10,BitVec.ofNat 5632 (word (BitVec.ofNat 5632 (word w.toNat)).toNat)⟩ : Query)=⟨10,w⟩
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (word_lt _ w.isLt),word_involutive,Nat.mod_eq_of_lt w.isLt]
  · simp only [query,if_neg hn]

theorem query_blocks (q : Query) : (query q).blocks=q.blocks := by
  rcases q with ⟨n,w⟩
  simp only [query];split <;> rfl

theorem query_fixed_length (q : Query) (h:q.1≠10) : query q=q := by
  rcases q with ⟨n,w⟩
  exact if_neg h

theorem word_fixed_classes (w : Nat) (h3:w%65536≠769) (h4:w%65536≠1025) : word w=w := by
  have hm : w%18446744073709551616%65536=w%65536 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣18446744073709551616)]
  unfold word header
  split_ifs <;> omega

theorem query_fixed_classes (q : Query) (h3:q.2.toNat%65536≠769)
    (h4:q.2.toNat%65536≠1025) : query q=q := by
  rcases q with ⟨n,w⟩
  unfold query
  split
  · rw [word_fixed_classes _ h3 h4]
    congr 1
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt w.isLt
  · rfl

def leafHeader (lay : Nat) : Nat :=
  if lay<4 then 769+65536*(lay+1) else 1025+65536*lay

theorem header_leaf (lay : Nat) (hl:lay<5) : header (1025+65536*lay)=leafHeader lay := by
  interval_cases lay <;> decide
end SigGolfCandidate.Ref.LeafCarry

namespace SigGolfCandidate.Ref.DigestZero
open SigGolfCandidate.Legacy

def header (h : Nat) : Nat := if h = 3073 then 0 else if h = 0 then 3073 else h

theorem header_lt {h : Nat} (hh : h < 18446744073709551616) : header h < 18446744073709551616 := by
  unfold header; split_ifs <;> omega

theorem header_involutive : Function.Involutive header := by
  intro h
  by_cases hD : h = 3073
  · subst h; decide
  by_cases hZ : h = 0
  · subst h; decide
  simp only [header, if_neg hD, if_neg hZ]

def word (w : Nat) : Nat := header (w % 18446744073709551616) + 18446744073709551616 * (w / 18446744073709551616)

theorem word_parts (w : Nat) :
    word w % 18446744073709551616 = header (w % 18446744073709551616) ∧
    word w / 18446744073709551616 = w / 18446744073709551616 := by
  have hh := header_lt (Nat.mod_lt w (by decide))
  unfold word
  omega

theorem word_involutive : Function.Involutive word := by
  intro w
  obtain ⟨hc,hq⟩ := word_parts w
  change header (word w % 18446744073709551616) + 18446744073709551616 * (word w / 18446744073709551616) = w
  rw [hc,hq,header_involutive]
  omega

theorem word_lt (w : Nat) (hw : w < 2^512) : word w < 2^512 := by
  have hq := (word_parts w).2
  norm_num only [Nat.reducePow] at hw ⊢
  omega

/-- Swap complete low words 3073 and zero only in one-block queries. -/
def query (q : Query) : Query :=
  if q.1 = 0 then ⟨q.1, BitVec.ofNat (8*(64*(q.1+1))) (word q.2.toNat)⟩ else q

theorem query_involutive : Function.Involutive query := by
  rintro ⟨n,w⟩
  by_cases hn : n = 0
  · subst n
    change (⟨0, BitVec.ofNat 512 (word (BitVec.ofNat 512 (word w.toNat)).toNat)⟩ : Query) = ⟨0,w⟩
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (word_lt _ w.isLt), word_involutive, Nat.mod_eq_of_lt w.isLt]
  · simp only [query,if_neg hn]

theorem query_blocks (q : Query) : (query q).blocks = q.blocks := by
  rcases q with ⟨n,w⟩
  simp only [query]; split <;> rfl

theorem query_fixed_length (q : Query) (h : q.1 ≠ 0) : query q = q := by
  rcases q with ⟨n,w⟩
  exact if_neg h

theorem word_fixed (w : Nat) (hD : w % 18446744073709551616 ≠ 3073)
    (hZ : w % 18446744073709551616 ≠ 0) : word w = w := by
  simp only [word,header,if_neg hD,if_neg hZ]
  omega

theorem query_fixed (q : Query) (hD : q.2.toNat % 18446744073709551616 ≠ 3073)
    (hZ : q.2.toNat % 18446744073709551616 ≠ 0) : query q = q := by
  rcases q with ⟨n,w⟩
  unfold query
  split
  · rw [word_fixed _ hD hZ]
    congr 1
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt w.isLt
  · rfl

theorem query_fixed_class (q : Query) (hD : q.2.toNat % 65536 ≠ 3073)
    (hZ : q.2.toNat % 65536 ≠ 0) : query q = q := by
  have hm : q.2.toNat % 18446744073709551616 % 65536 = q.2.toNat % 65536 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 18446744073709551616)]
  apply query_fixed <;> omega

theorem support_cases (q : Query) (h : query q ≠ q) :
    q.1 = 0 ∧ (q.2.toNat % 18446744073709551616 = 3073 ∨ q.2.toNat % 18446744073709551616 = 0) := by
  constructor
  · by_contra hn; exact h (query_fixed_length q hn)
  · by_contra hh
    push_neg at hh
    exact h (query_fixed q hh.1 hh.2)

theorem support_classes (q : Query) (h : query q ≠ q) :
    q.2.toNat % 65536 = 3073 ∨ q.2.toNat % 65536 = 0 := by
  have hm : q.2.toNat % 18446744073709551616 % 65536 = q.2.toNat % 65536 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 18446744073709551616)]
  rcases (support_cases q h).2 with h | h <;> omega

theorem commute_of_fixes_support (f : Query → Query) (hf : Function.Injective f)
    (hs : ∀ q, query q ≠ q → f q = q) (q : Query) : query (f q) = f (query q) := by
  by_cases h : query q = q
  · rw [h]
    by_contra h'
    have he : f (f q) = f q := hs (f q) h'
    have he' : f q = q := hf he
    exact h' (by rw [he',h])
  · have h' : query (query q) ≠ query q := by rw [query_involutive]; exact Ne.symm h
    rw [hs q h, hs (query q) h']

theorem commute_leafClass (q : Query) : query (LeafClass.query q) = LeafClass.query (query q) :=
  commute_of_fixes_support _ LeafClass.query_involutive.injective (fun q h =>
    LeafClass.query_fixed_length q (by have := (support_cases q h).1; omega)) q

theorem commute_leafCarry (q : Query) : query (LeafCarry.query q) = LeafCarry.query (query q) :=
  commute_of_fixes_support _ LeafCarry.query_involutive.injective (fun q h =>
    LeafCarry.query_fixed_length q (by have := (support_cases q h).1; omega)) q

theorem commute_topHeap (q : Query) : query (TopHeap.query q) = TopHeap.query (query q) :=
  commute_of_fixes_support _ TopHeap.query_involutive.injective (fun q h =>
    TopHeap.query_fixed_class q (by have := support_classes q h; omega)) q

theorem commute_encodingRotate (q : Query) : query (EncodingRotate.query q) = EncodingRotate.query (query q) :=
  commute_of_fixes_support _ EncodingRotate.query_injective (fun q h =>
    EncodingRotate.query_fixed q (by have := support_classes q h; omega)) q

theorem commute_leafScale (q : Query) : query (LeafScale.queryRel q) = LeafScale.queryRel (query q) :=
  commute_of_fixes_support _ LeafScale.queryRel_injective (fun q h =>
    LeafScale.queryRel_fixed q (by have := support_classes q h; omega)) q

theorem base_fixed_support (q : Query) (h : query q ≠ q) : AddressFormat.baseQueryPerm q = q := by
  obtain ⟨hn,hw⟩ := support_cases q h
  have hc := support_classes q h
  rcases q with ⟨n,w⟩
  change n = 0 at hn
  subst n
  change w.toNat % 65536 = 3073 ∨ w.toNat % 65536 = 0 at hc
  have hh : AddressFormat.wordPerm (w.toNat % 18446744073709551616) = w.toNat % 18446744073709551616 := by
    rcases hw with hw | hw <;> rw [hw] <;> decide
  have hf : AddressFormat.fullPerm w.toNat = w.toNat := by
    rw [AddressFormat.fullPerm_of_ne _ (by omega)]
    unfold AddressFormat.payloadPerm
    rw [hh]
    omega
  change (⟨0,BitVec.ofNat 512 (AddressFormat.fullPerm w.toNat)⟩ : Query) = ⟨0,w⟩
  rw [hf]
  congr 1
  exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt w.isLt)

theorem commute_base (q : Query) : query (AddressFormat.baseQueryPerm q) = AddressFormat.baseQueryPerm (query q) :=
  commute_of_fixes_support _ AddressFormat.baseQueryPerm_injective base_fixed_support q

end SigGolfCandidate.Ref.DigestZero

namespace SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Legacy

/-- Native-query permutation preserving the accepted root-pair construction. -/
def queryPerm (q : Query) : Query := DigestZero.query (EncodingRotate.query (LeafCarry.query (TopHeap.query (LeafClass.query (LeafScale.queryRel (baseQueryPerm q))))))
def queryInverse (q : Query) : Query := baseQueryPerm (LeafScale.queryInv (LeafClass.query (TopHeap.query (LeafCarry.query (EncodingRotate.queryInverse (DigestZero.query q))))))

theorem queryPerm_eq_unwrapped (q : Query) (h : DigestZero.query q = q) :
    queryPerm q = EncodingRotate.query (LeafCarry.query (TopHeap.query (LeafClass.query (LeafScale.queryRel (baseQueryPerm q))))) := by
  rw [queryPerm, DigestZero.commute_encodingRotate, DigestZero.commute_leafCarry,
    DigestZero.commute_topHeap, DigestZero.commute_leafClass, DigestZero.commute_leafScale,
    DigestZero.commute_base, h]

theorem queryInverse_queryPerm (q : Query) : queryInverse (queryPerm q) = q := by
  rw [queryInverse, queryPerm, DigestZero.query_involutive, EncodingRotate.queryInverse_query, LeafCarry.query_involutive, TopHeap.query_involutive, LeafClass.query_involutive,
    LeafScale.queryInv_queryRel, baseQueryPerm_involutive]

theorem queryPerm_injective : Function.Injective queryPerm :=
  DigestZero.query_involutive.injective.comp (EncodingRotate.query_injective.comp (LeafCarry.query_involutive.injective.comp (TopHeap.query_involutive.injective.comp (LeafClass.query_involutive.injective.comp
    (LeafScale.queryRel_injective.comp baseQueryPerm_injective)))))

theorem queryPerm_blocks (q : Query) : (queryPerm q).blocks = q.blocks := by
  rw [queryPerm, DigestZero.query_blocks, EncodingRotate.query_blocks, LeafCarry.query_blocks, TopHeap.query_blocks, LeafClass.query_blocks, LeafScale.queryRel_blocks, baseQueryPerm_blocks]

theorem queryPerm_fixed (q : Query) (h0 : q.2.toNat % 64 ≠ 0)
    (h1 : q.2.toNat % 65536 ≠ 257) (h2 : q.2.toNat % 65536 ≠ 2561)
    (h9 : q.2.toNat % 65536 ≠ 2305) (h4 : q.2.toNat % 65536 ≠ 1025)
    (hL : q.2.toNat % 65536 ≠ 513) (h3:q.2.toNat%65536≠769)
    (hD : q.2.toNat % 65536 ≠ 3073) : queryPerm q = q := by
  rw [queryPerm, baseQueryPerm_fixed q h0 h1 h2, LeafScale.queryRel_fixed q h9,
    LeafClass.query_fixed q hL h4, TopHeap.query_fixed_class q h3, LeafCarry.query_fixed_classes q h3 h4, EncodingRotate.query_fixed q h4]
  exact DigestZero.query_fixed_class q hD (by omega)

end SigGolfCandidate.Ref.AddressFormat
