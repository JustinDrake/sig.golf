import SigGolfCandidate.T3.Rev
import SigGolfCandidate.Rv

/-!
# t3-rl2 (lane fts): the FTS registers hold bit-reversed heap indices

Copy of the verify lane's `RevArith` helpers under the namespace `Verify.FtsRev` (both files can coexist).

The verify FTS code keeps `x23 = rv E = revBits 64 E` (the ghost `E` is the heap index). Its operations:
* `slli x23, x23, 1` is the parent `E / 2` (`rv_sll1`, from `Rev.revBits_succ_div`);
* the sign of `x23` is the side `E % 2` (`rv_slt`, from `Rev.revBits_top`);
* `xor x3, x23, x30` with `x30 = 2^63` is the sibling `E ^^^ 1` (`rv_xor`, from `Rev.revBits_xor1`);
* equality of registers is equality of heap indices (`rv_inj`); the root `E = 1` is `x23 = 2^63` (`rv_one`).
-/

namespace SigGolfCandidate.T3M.Verify.FtsRev
open RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3.Rev

/-- The register image of the heap index `E`. -/
def rv (E : Nat) : BitVec 64 := BitVec.ofNat 64 (revBits 64 E)

theorem rv_toNat (E : Nat) : (rv E).toNat = revBits 64 E := by
  unfold rv; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (revBits_lt 64 E)]

/-- Split reversal into the high image of the low bits and the remaining low image. -/
theorem revBits_split (n k v : Nat) :
    revBits (n+k) v = revBits k v * 2^n + revBits n (v / 2^k) := by
  induction k generalizing v with
  | zero => simp [revBits]
  | succ k ih =>
    rw [show n+(k+1)=(n+k)+1 by omega, revBits, ih, revBits]
    rw [Nat.div_div_eq_div_mul, show 2*2^k=2^(k+1) by rw [Nat.pow_succ]; omega]
    rw [Nat.pow_add]
    ring

theorem revBits_prefix (n k v : Nat) : revBits (n+k) v / 2^n = revBits k v := by
  rw [revBits_split, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos n),
    Nat.div_eq_of_lt (revBits_lt n _), Nat.zero_add]

theorem rv_srl_prefix (E k : Nat) (hk : 0<k ∧ k≤64) :
    BinOp.eval .srl (rv E) (BitVec.ofNat 64 (64-k)) = BitVec.ofNat 64 (revBits k E) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.toNat_ushiftRight, rv_toNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 64-k<2^64), Nat.mod_eq_of_lt (by omega : 64-k<64)]
  rw [Nat.shiftRight_eq_div_pow]
  have hp := revBits_prefix (64-k) k E
  simp only [Nat.sub_add_cancel hk.2] at hp
  rw [hp]
  exact (Nat.mod_eq_of_lt (lt_of_lt_of_le (revBits_lt k E)
    (Nat.pow_le_pow_right (by decide) hk.2))).symm

theorem rv_sll1 (E : Nat) (hE : E < 2 ^ 64) : BinOp.eval .sll (rv E) (BitVec.ofNat 64 1) = rv (E / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.eval, BitVec.toNat_shiftLeft, rv_toNat, Nat.shiftLeft_eq]
  rw [revBits_succ_div 63 E hE]
  norm_num
  ring_nf

theorem revBits_top64 (E : Nat) : revBits 64 E / 2 ^ 63 = E % 2 := revBits_top 63 E

/-- The sign of `rv E` is the side bit `E % 2`. -/
theorem rv_slt (E : Nat) : BitVec.slt (rv E) 0 = decide (E % 2 = 1) := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide, rv_toNat]
  have h := revBits_top64 E
  have hl := revBits_lt 64 E
  rcases Nat.mod_two_eq_zero_or_one E with he | he <;> rw [he] at h <;> simp only [he]
  · have : revBits 64 E < 2 ^ 63 := by
      by_contra hc; have : 1 ≤ revBits 64 E / 2 ^ 63 := (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
      omega
    simp; omega
  · have : 2 ^ 63 ≤ revBits 64 E := by
      by_contra hc; have : revBits 64 E / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
      omega
    simp; omega

theorem xor_two_pow (x k : Nat) : x ^^^ 2 ^ k = 2 ^ k * (x / 2 ^ k ^^^ 1) + x % 2 ^ k := by
  have h1 : (x ^^^ 2 ^ k) / 2 ^ k = x / 2 ^ k ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (by positivity)]
  have h2 : (x ^^^ 2 ^ k) % 2 ^ k = x % 2 ^ k := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  rw [← h1, ← h2, Nat.div_add_mod]

theorem xor_2048 (g : Nat) (hg : g < 2048) : g ^^^ 2048 = 2048 + g := by
  have := xor_two_pow g 11
  rw [Nat.div_eq_of_lt (by norm_num; omega), Nat.mod_eq_of_lt (by norm_num; omega)] at this
  rw [show (2048 : Nat) = 2 ^ 11 by norm_num, this]; rfl

theorem xor_top (x : Nat) (hx : x < 2 ^ 64) : x ^^^ 2 ^ 63 = (x + 2 ^ 63) % 2 ^ 64 := by
  rw [xor_two_pow]
  by_cases h : x < 2 ^ 63
  · rw [Nat.div_eq_of_lt h, show (0 : Nat) ^^^ 1 = 1 from rfl, Nat.mod_eq_of_lt h]; omega
  · have h1 : x / 2 ^ 63 = 1 := by omega
    rw [h1, show (1 : Nat) ^^^ 1 = 0 from rfl]; omega

/-- The sibling: `xor` with `2^63` flips the side bit. -/
theorem rv_xor (E : Nat) : rv E ^^^ BitVec.ofNat 64 (2 ^ 63) = rv (E ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, rv_toNat, rv_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num),
    xor_top _ (revBits_lt 64 E), revBits_xor1 63 E]

theorem rv_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rv a = rv b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [rv_toNat, rv_toNat] at this
    exact revBits_inj ha hb this
  · rintro rfl; rfl

theorem revBits_zero : ∀ n, revBits n 0 = 0
  | 0 => rfl
  | n + 1 => by simp only [revBits, Nat.zero_mod, Nat.zero_mul, Nat.zero_div, revBits_zero n]

theorem revBits_one (n : Nat) : revBits (n + 1) 1 = 2 ^ n := by
  simp only [revBits, show (1 : Nat) % 2 = 1 from rfl, show (1 : Nat) / 2 = 0 from rfl, revBits_zero, one_mul,
    add_zero]

theorem rv_one : rv 1 = BitVec.ofNat 64 (2 ^ 63) := by unfold rv; rw [revBits_one 63]

/-- The root test: `rv E = 2^63` iff `E = 1`. -/
theorem rv_eq_top (E : Nat) (hE : E < 2 ^ 64) : rv E = BitVec.ofNat 64 (2 ^ 63) ↔ E = 1 := by
  rw [← rv_one]; exact rv_inj hE (by norm_num)

theorem revBits_allOnes : ∀ n, revBits n (2 ^ n - 1) = 2 ^ n - 1
  | 0 => rfl
  | n + 1 => by
    have h1 : (2 ^ (n + 1) - 1) % 2 = 1 := by
      have : 0 < 2 ^ n := by positivity
      rw [Nat.pow_succ]; omega
    have h2 : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
      have : 0 < 2 ^ n := by positivity
      rw [Nat.pow_succ]; omega
    simp only [revBits, h1, h2, revBits_allOnes n, one_mul]
    have : 0 < 2 ^ n := by positivity
    rw [Nat.pow_succ]; omega

/-- The stack sentinel `-1` is no heap index below `2^64 - 1`. -/
theorem rv_ne_neg1 (E : Nat) (hE : E < 4096) : rv E ≠ -1#64 := by
  intro h
  have hm : (-1#64 : BitVec 64) = rv (2 ^ 64 - 1) := by
    apply BitVec.eq_of_toNat_eq; rw [rv_toNat, revBits_allOnes 64]; rfl
  rw [hm, rv_inj (by omega) (by norm_num)] at h
  omega

/-- The sentinel's low bit distinguishes it from every reversed small heap index. -/
theorem rv_ne_sentinel (E : Nat) (hE : E < 4096) : rv E ≠ 1#64 := by
  intro h
  have hm : (1#64 : BitVec 64) = rv (2 ^ 63) := by decide +kernel
  rw [hm, rv_inj (by omega) (by norm_num)] at h
  omega

end SigGolfCandidate.T3M.Verify.FtsRev
