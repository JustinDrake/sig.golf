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

def rel (w : Nat) : Nat :=
  w % 79228162514264337593543950336 +
  79228162514264337593543950336 * left3 (w / 79228162514264337593543950336 % 4294967296) +
  340282366920938463463374607431768211456 * (w / 340282366920938463463374607431768211456)

def invRel (w : Nat) : Nat :=
  w % 79228162514264337593543950336 +
  79228162514264337593543950336 * right3 (w / 79228162514264337593543950336 % 4294967296) +
  340282366920938463463374607431768211456 * (w / 340282366920938463463374607431768211456)

theorem rel_parts (w : Nat) :
    rel w % 79228162514264337593543950336 = w % 79228162514264337593543950336 ∧
    rel w / 79228162514264337593543950336 % 4294967296 =
      left3 (w / 79228162514264337593543950336 % 4294967296) ∧
    rel w / 340282366920938463463374607431768211456 = w / 340282366920938463463374607431768211456 := by
  have := left3_lt (w / 79228162514264337593543950336 % 4294967296)
  unfold rel
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem invRel_rel (w : Nat) : invRel (rel w) = w := by
  obtain ⟨h1,h2,h3⟩ := rel_parts w
  unfold invRel
  rw [h1,h2,h3,right3_left3 _ (Nat.mod_lt _ (by decide))]
  omega

theorem rel_injective : Function.Injective rel := by
  intro a b h
  have := congrArg invRel h
  rwa [invRel_rel, invRel_rel] at this

theorem rel_class (w : Nat) : rel w % 65536 = w % 65536 := by
  have := (rel_parts w).1
  omega

end SigGolfCandidate.Ref.LeafScale

namespace SigGolfCandidate.Ref.LeafScale
open SigGolfCandidate.Legacy
set_option exponentiation.threshold 1024

theorem rel_lt (w : Nat) (hw : w < 2^512) : rel w < 2^512 := by
  have := left3_lt (w / 79228162514264337593543950336 % 4294967296)
  norm_num only [Nat.reducePow] at hw ⊢
  unfold rel
  omega

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

theorem queryRel_class (q : Query) : (queryRel q).2.toNat%65536=q.2.toNat%65536 := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero =>
    by_cases h : w.toNat%65536=2305
    · rw [show queryRel ⟨0,w⟩ = ⟨0,BitVec.ofNat 512 (rel w.toNat)⟩ from if_pos h]
      change (BitVec.ofNat 512 (rel w.toNat)).toNat%65536=w.toNat%65536
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (rel_lt _ w.isLt),rel_class]
    · rw [show queryRel ⟨0,w⟩ = ⟨0,w⟩ from if_neg h]
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
(32-bit bit reversal, an involution). The class is disjoint from both chain-header classes
(`wordPerm` maps every word outside `2561` to a word outside `2561`), so the whole map stays an
involution. -/

def nodeRel (w : Nat) : Nat :=
  w % 79228162514264337593543950336 +
    79228162514264337593543950336 * Rev.efield (w / 79228162514264337593543950336 % 4294967296) +
    340282366920938463463374607431768211456 * (w / 340282366920938463463374607431768211456)

theorem nodeRel_parts (w : Nat) :
    nodeRel w % 79228162514264337593543950336 = w % 79228162514264337593543950336 ∧
    nodeRel w / 79228162514264337593543950336 % 4294967296 =
      Rev.efield (w / 79228162514264337593543950336 % 4294967296) ∧
    nodeRel w / 340282366920938463463374607431768211456 = w / 340282366920938463463374607431768211456 := by
  have he := Rev.efield_lt (w / 79228162514264337593543950336 % 4294967296)
  norm_num only [Nat.reducePow] at he
  unfold nodeRel
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem nodeRel_involutive : Function.Involutive nodeRel := by
  intro w
  obtain ⟨h1, h2, h3⟩ := nodeRel_parts w
  have hb : w / 79228162514264337593543950336 % 4294967296 < 2 ^ 32 := by
    norm_num only [Nat.reducePow]; omega
  generalize nodeRel w = n at h1 h2 h3 ⊢
  unfold nodeRel
  rw [h1, h2, h3, Rev.efield_efield _ hb]
  omega

theorem nodeRel_lt (w : Nat) (h : w < 2 ^ 512) : nodeRel w < 2 ^ 512 := by
  have he := Rev.efield_lt (w / 79228162514264337593543950336 % 4294967296)
  norm_num only [Nat.reducePow] at he h ⊢
  unfold nodeRel
  omega

theorem nodeRel_class (w : Nat) : nodeRel w % 65536 = w % 65536 := by
  have := (nodeRel_parts w).1
  omega

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

namespace SigGolfCandidate.Ref.EncodingSwap
open SigGolfCandidate.Legacy
set_option Elab.async false
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Exchange the two128-bit halves at byte offsets32 and48, retaining the
entire header, public-parameter region, and any higher bits. -/
def word (w : Nat) : Nat :=
  w % 115792089237316195423570985008687907853269984665640564039457584007913129639936 +
  115792089237316195423570985008687907853269984665640564039457584007913129639936 *
    (w / 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 % 340282366920938463463374607431768211456) +
  39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 *
    (w / 115792089237316195423570985008687907853269984665640564039457584007913129639936 % 340282366920938463463374607431768211456) +
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 *
    (w / 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096)

theorem word_parts (w : Nat) :
    word w % 2^256=w%2^256 ∧
    word w / 2^256 % 2^128=w/2^384%2^128 ∧
    word w / 2^384 % 2^128=w/2^256%2^128 ∧
    word w / 2^512=w/2^512 := by
  let B : Nat := 340282366920938463463374607431768211456
  let C : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  let D : Nat := 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816
  let E : Nat := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
  have h0 : w%C<C := Nat.mod_lt _ (by decide)
  have h1 : w/D%B<B := Nat.mod_lt _ (by decide)
  have h2 : w/C%B<B := Nat.mod_lt _ (by decide)
  have he : word w = w%C + C*((w/D%B)+B*((w/C%B)+B*(w/E))) := by
    dsimp [word,B,C,D,E]; ring
  have q1 : word w / C = (w/D%B)+B*((w/C%B)+B*(w/E)) := by
    rw [he,Nat.add_mul_div_left _ _ (show 0<C by decide),Nat.div_eq_of_lt h0]
    simp
  have q2 : word w / D = (w/C%B)+B*(w/E) := by
    have hCB : C*B=D := by norm_num [C,B,D]
    rw [←hCB,←Nat.div_div_eq_div_mul,q1,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h1]
    simp
  have q3 : word w / E = w/E := by
    have hDB : D*B=E := by norm_num [D,B,E]
    rw [←hDB,←Nat.div_div_eq_div_mul,q2,Nat.add_mul_div_left _ _ (show 0<B by decide),Nat.div_eq_of_lt h2]
    simp only [hDB,Nat.zero_add]
  change word w%C=w%C ∧ word w/C%B=w/D%B ∧ word w/D%B=w/C%B ∧ word w/E=w/E
  refine ⟨?_,?_,?_,q3⟩
  · rw [he,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · rw [q1,Nat.add_mul_mod_self_left,Nat.mod_mod]
  · rw [q2,Nat.add_mul_mod_self_left,Nat.mod_mod]

theorem word_involutive : Function.Involutive word := by
  intro w
  obtain ⟨h0,h1,h2,h3⟩ := word_parts w
  norm_num only [Nat.reducePow] at h0 h1 h2 h3
  generalize word w=n at h0 h1 h2 h3 ⊢
  unfold word
  rw [h0,h1,h2,h3]
  have hd1 : w / 2^256 / 2^128 = w / 2^384 := by simp only [Nat.div_div_eq_div_mul]; norm_num
  have hd2 : w / 2^384 / 2^128 = w / 2^512 := by simp only [Nat.div_div_eq_div_mul]; norm_num
  norm_num only [Nat.reducePow] at hd1 hd2
  omega

theorem word_lt (w : Nat) (h : w<2^512) : word w<2^512 := by
  have hh := (word_parts w).2.2.2
  omega

theorem word_class (w : Nat) : word w%65536=w%65536 := by
  have hh := (word_parts w).1
  norm_num only [Nat.reducePow] at hh
  omega

theorem word_eq (a b c : Nat) (ha : a<2^256) (hb : b<2^128) (hc : c<2^128) :
    word (a+2^256*b+2^384*c) = a+2^256*c+2^384*b := by
  unfold word
  norm_num only [Nat.reducePow] at ha hb hc ⊢
  omega

/-- Every Query has at least64 bytes. Only exact one-block tag4 inputs are
swapped; arbitrary longer queries and all other malformed headers are fixed. -/
def query : Query → Query
  | ⟨0,w⟩ => if w.toNat%65536=1025 then ⟨0,BitVec.ofNat 512 (word w.toNat)⟩ else ⟨0,w⟩
  | ⟨n+1,w⟩ => ⟨n+1,w⟩

theorem query_involutive : Function.Involutive query := by
  rintro ⟨n,w⟩
  cases n with
  | zero =>
      by_cases h : w.toNat%65536=1025
      · have hw := word_lt _ w.isLt
        have hc : (BitVec.ofNat 512 (word w.toNat)).toNat%65536=1025 := by
          rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hw,word_class]
          exact h
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

theorem query_fixed (q : Query) (h : q.2.toNat%65536≠1025) : query q=q := by
  rcases q with ⟨n,w⟩
  cases n with
  | zero => exact if_neg h
  | succ n => rfl
end SigGolfCandidate.Ref.EncodingSwap

namespace SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Legacy

/-- Compose the previous chain/node relabelling with a bijection on tag-9 leaf fields. -/
def queryPerm (q : Query) : Query := EncodingSwap.query (LeafScale.queryRel (baseQueryPerm q))

/-- The inverse is needed by the budget layer when decoding formatted query bytes. -/
def queryInverse (q : Query) : Query := baseQueryPerm (LeafScale.queryInv (EncodingSwap.query q))

theorem queryInverse_queryPerm (q : Query) : queryInverse (queryPerm q) = q := by
  rw [queryInverse, queryPerm, EncodingSwap.query_involutive, LeafScale.queryInv_queryRel, baseQueryPerm_involutive]

theorem queryPerm_injective : Function.Injective queryPerm :=
  EncodingSwap.query_involutive.injective.comp (LeafScale.queryRel_injective.comp baseQueryPerm_injective)

theorem queryPerm_blocks (q : Query) : (queryPerm q).blocks = q.blocks := by
  rw [queryPerm, EncodingSwap.query_blocks, LeafScale.queryRel_blocks, baseQueryPerm_blocks]

theorem queryPerm_fixed (q : Query) (h0 : q.2.toNat % 64 ≠ 0)
    (h1 : q.2.toNat % 65536 ≠ 257) (h2 : q.2.toNat % 65536 ≠ 2561)
    (h9 : q.2.toNat % 65536 ≠ 2305) (h4 : q.2.toNat % 65536 ≠ 1025) : queryPerm q = q := by
  rw [queryPerm, baseQueryPerm_fixed q h0 h1 h2, LeafScale.queryRel_fixed q h9, EncodingSwap.query_fixed q h4]

end SigGolfCandidate.Ref.AddressFormat
