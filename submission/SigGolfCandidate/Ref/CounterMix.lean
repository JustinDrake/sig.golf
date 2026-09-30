import SigGolfCandidate.Ref.Basic

/-! # The bounded 96-bit counter codec

Four counters use a 15-bit remainder and a base 17 quotient; the final counter
uses an 18-bit remainder and a base 3 quotient. The remainders occupy 78 bits and
the quotient rank occupies 18 bits. Values outside the declared ranges are
encoded by the reserved all-one 96-bit value in the total serializer.
-/

namespace SigGolfCandidate.Ref.CounterMix

/-- Number of representable tuples: `(17·2^15)^4·(3·2^18)`. -/
def capacity : Nat := 75728020035025082475475894272

def reserved : Nat := 79228162514264337593543950335

def join (base lo hi : Nat) : Nat := lo + base * hi

theorem join_mod {base lo : Nat} (hi : Nat) (h : lo < base) :
    join base lo hi % base = lo := by
  unfold join
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem join_div {base lo : Nat} (hi : Nat) (h : lo < base) :
    join base lo hi / base = hi := by
  unfold join
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

def low (a b c d e : Nat) : Nat :=
  join 32768 (a % 32768) (join 32768 (b % 32768) (join 32768 (c % 32768)
    (join 32768 (d % 32768) (e % 262144))))

def rank (a b c d e : Nat) : Nat :=
  join 17 (a / 32768) (join 17 (b / 32768) (join 17 (c / 32768)
    (join 17 (d / 32768) (e / 262144))))

def raw (a b c d e : Nat) : Nat :=
  low a b c d e + 302231454903657293676544 * rank a b c d e

def decode (v : Nat) : Nat → Nat
  | 0 => join 32768 (v % 32768) (v / 302231454903657293676544 % 17)
  | 1 => join 32768 (v / 32768 % 32768) (v / 302231454903657293676544 / 17 % 17)
  | 2 => join 32768 (v / 32768 / 32768 % 32768) (v / 302231454903657293676544 / 17 / 17 % 17)
  | 3 => join 32768 (v / 32768 / 32768 / 32768 % 32768) (v / 302231454903657293676544 / 17 / 17 / 17 % 17)
  | 4 => join 262144 (v / 32768 / 32768 / 32768 / 32768 % 262144)
      (v / 302231454903657293676544 / 17 / 17 / 17 / 17 % 3)
  | _ => 0

theorem capacity_lt : capacity < 2 ^ 96 := by decide
theorem reserved_eq : reserved = 2 ^ 96 - 1 := by decide
theorem capacity_le_reserved : capacity ≤ reserved := by decide

theorem low_lt (a b c d e : Nat) : low a b c d e < 302231454903657293676544 := by
  unfold low join
  omega

theorem rank_lt (a b c d e : Nat) (ha : a < 557056) (hb : b < 557056)
    (hc : c < 557056) (hd : d < 557056) (he : e < 786432) :
    rank a b c d e < 250563 := by
  unfold rank join
  omega

theorem raw_lt (a b c d e : Nat) (ha : a < 557056) (hb : b < 557056)
    (hc : c < 557056) (hd : d < 557056) (he : e < 786432) :
    raw a b c d e < capacity := by
  have hl := low_lt a b c d e
  have hr := rank_lt a b c d e ha hb hc hd he
  unfold raw capacity
  omega

/-- The decoder recovers all five bounded counters exactly. -/
theorem decode_raw (a b c d e : Nat) (ha : a < 557056) (hb : b < 557056)
    (hc : c < 557056) (hd : d < 557056) (he : e < 786432) :
    decode (raw a b c d e) 0 = a ∧ decode (raw a b c d e) 1 = b ∧
    decode (raw a b c d e) 2 = c ∧ decode (raw a b c d e) 3 = d ∧
    decode (raw a b c d e) 4 = e := by
  have hl := low_lt a b c d e
  have hr : raw a b c d e / 302231454903657293676544 = rank a b c d e := by
    rw [raw, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hl, Nat.zero_add]
  have hraw : raw a b c d e =
      join 32768 (a % 32768) (join 32768 (b % 32768) (join 32768 (c % 32768)
        (join 32768 (d % 32768) (join 262144 (e % 262144) (rank a b c d e))))) := by
    unfold raw low join
    ring
  have hqa : a / 32768 < 17 := by omega
  have hqb : b / 32768 < 17 := by omega
  have hqc : c / 32768 < 17 := by omega
  have hqd : d / 32768 < 17 := by omega
  have hqe : e / 262144 < 3 := by omega
  have hma : a % 32768 < 32768 := Nat.mod_lt _ (by decide)
  have hmb : b % 32768 < 32768 := Nat.mod_lt _ (by decide)
  have hmc : c % 32768 < 32768 := Nat.mod_lt _ (by decide)
  have hmd : d % 32768 < 32768 := Nat.mod_lt _ (by decide)
  have hme : e % 262144 < 262144 := Nat.mod_lt _ (by decide)
  simp only [decode, hr]
  rw [hraw]
  simp only [rank, join_mod, join_div, hqa, hqb, hqc, hqd, hma, hmb, hmc, hmd, hme,
    Nat.mod_eq_of_lt hqe]
  change _ + _ * _ = a ∧ _ + _ * _ = b ∧ _ + _ * _ = c ∧ _ + _ * _ = d ∧ _ + _ * _ = e
  exact ⟨Nat.mod_add_div a 32768, Nat.mod_add_div b 32768, Nat.mod_add_div c 32768,
    Nat.mod_add_div d 32768, Nat.mod_add_div e 262144⟩

theorem decode_lt (v i : Nat) (hi : i < 5) :
    decode v i < (if i = 4 then 786432 else 557056) := by
  interval_cases i <;> norm_num only [decode, join] <;> simp only [if_true, if_false] <;> omega

/-- Adjacent radix pieces recombine to the corresponding remainder. -/
theorem join_mods (v base width : Nat) :
    join base (v % base) (v / base % width) = v % (base * width) := by
  exact Nat.mod_mul.symm

/-- The raw encoder and decoder are inverse on every canonical tail value. -/
theorem raw_decode (v : Nat) :
    raw (decode v 0) (decode v 1) (decode v 2) (decode v 3) (decode v 4) = v % capacity := by
  have hlow : low (decode v 0) (decode v 1) (decode v 2) (decode v 3) (decode v 4)
      = v % 302231454903657293676544 := by
    simp only [low, decode, join_mod, Nat.mod_lt _ (by decide : 0 < 32768),
      Nat.mod_lt _ (by decide : 0 < 262144)]
    rw [join_mods, join_mods, join_mods, join_mods]
  have hrank : rank (decode v 0) (decode v 1) (decode v 2) (decode v 3) (decode v 4)
      = v / 302231454903657293676544 % 250563 := by
    simp only [rank, decode, join_div, Nat.mod_lt _ (by decide : 0 < 32768),
      Nat.mod_lt _ (by decide : 0 < 262144)]
    rw [join_mods, join_mods, join_mods, join_mods]
  rw [raw, hlow, hrank]
  exact Nat.mod_mul.symm

end SigGolfCandidate.Ref.CounterMix
