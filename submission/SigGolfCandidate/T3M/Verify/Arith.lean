import SigGolfCandidate.T3M.Verify.Spec

/-!
# Bit-level facts about the verify image's stores (T3M)

* `replaceWord32_1_toNat`, `merge_w4_toNat` (`sw v, a + 4`: the high half), `merge_w0_toNat` (in `Mem`);
* `merge_sw2_toNat` / `merge_sw2` : two `sw` into both halves of a doubleword (the T3 header word 1
  `tree | index << 32` of the FTS blocks, written `sw s6, 24(a0); sw E, 28(a0)`), = `ofNat (hdr1 a b)`;
* `hdr0_small`, `hdr1_small` : Core's header words for small fields.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

theorem replaceWord32_1_toNat (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (replaceWord32 w 1 ((BitVec.ofNat 64 p).truncate 32)).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * p := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (1 * 32)) : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := by
    decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have e1 : (2 ^ 32 - 1) % 2 ^ 64 = 2 ^ 32 - 1 := by norm_num
  have e2 : p % 2 ^ 64 % 2 ^ 32 = p := by omega
  have e3 : p % 2 ^ 64 * 2 ^ (1 * 32) % 2 ^ 64 = 2 ^ 32 * p := by
    rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; rw [Nat.mod_eq_of_lt (by norm_num; omega)]; ring
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, e3]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

theorem merge_w4_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 4 v).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * (v.toNat % 2 ^ 32) := by
  have := replaceWord32_1_toNat w (v.toNat % 2 ^ 32) (Nat.mod_lt _ (by decide))
  simp only [StoreKind.merge, show (4 : Nat) / 4 = 1 from rfl]
  have e : (BitVec.ofNat 64 (v.toNat % 2 ^ 32)).truncate 32 = v.truncate 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [← e, this]

/-- Both halves of a doubleword written by two `sw`. -/
theorem merge_sw2_toNat (old a b : BitVec 64) :
    (StoreKind.merge .w (StoreKind.merge .w old 0 a) 4 b).toNat = a.toNat % 2 ^ 32 + 2 ^ 32 * (b.toNat % 2 ^ 32) := by
  rw [merge_w4_toNat, merge_w0_toNat]
  omega

theorem merge_sw2 (old : BitVec 64) (a b : Nat) :
    StoreKind.merge .w (StoreKind.merge .w old 0 (BitVec.ofNat 64 a)) 4 (BitVec.ofNat 64 b) =
      BitVec.ofNat 64 (hdr1 a b) := by
  apply BitVec.eq_of_toNat_eq
  have hl := hdr1_lt a b
  rw [merge_sw2_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod_of_dvd _ (by norm_num)
  have h2 : b % 2 ^ 64 % 2 ^ 32 = b % 2 ^ 32 := Nat.mod_mod_of_dvd _ (by norm_num)
  rw [h1, h2, hdr1]; ring

/-- Header word 0 for small fields. -/
theorem hdr0_small (tag lay tree position : Nat) (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 32)
    (hp : position < 2 ^ 32) :
    hdr0 tag lay tree position = 1 + 256 * tag + 65536 * lay + 2 ^ 32 * position :=
  hdr0_eq tag lay tree position ht hl htr hp

theorem hdr1_small (tree index : Nat) (htr : tree < 2 ^ 32) (hi : index < 2 ^ 32) :
    hdr1 tree index = tree + 2 ^ 32 * index := hdr1_eq tree index htr hi

end SigGolfCandidate.T3M.Verify
