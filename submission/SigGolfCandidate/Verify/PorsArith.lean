import SigGolfCandidate.Verify.PorsRuns
import SigGolfCandidate.Verify.Swar
import Mathlib.Tactic.Ring

/-! # Digest-word arithmetic for the PORS phase: idx, the leaf indices, tweak words, counters -/

set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem prefixN_le (a : Nat) : prefixN a ≤ 2 := by
  unfold prefixN; split_ifs <;> omega

theorem prefixN_lt (a : Nat) (ha : 0 < a) : prefixN a < a := by
  unfold prefixN; split_ifs <;> omega

theorem prefix_tag_slot (a i E bits : Nat) (hi : i ≤ prefixN a)
    (h : E % 2^(3-i) = bits / 2^i) : E % 2 = bits / 2^i % 2 := by
  have hn := prefixN_le a
  have hib : i ≤ 2 := by omega
  interval_cases i <;> norm_num at * <;> omega

theorem prefix_tag_next (a i E bits : Nat) (hi : i < prefixN a)
    (h : E % 2^(3-i) = bits / 2^i) :
    E / 2 % 2^(3-(i+1)) = bits / 2^(i+1) := by
  have hn := prefixN_le a
  have hib : i ≤ 2 := by omega
  interval_cases i <;> norm_num at * <;> omega

theorem prefix_tag_next_slot (a i E bits : Nat) (hi : i < prefixN a)
    (h : E % 2^(3-i) = bits / 2^i) : E / 2 % 2 = bits / 2^(i+1) % 2 := by
  exact prefix_tag_slot a (i+1) (E/2) bits (by omega) (prefix_tag_next a i E bits hi h)

theorem foldBudget_step : ∀ V : Fin 3, ∀ a : Fin 15, ∀ i : Fin 15, i.val < a.val →
    foldBudget V.val a.val i.val = posCycles V.val a.val i.val + 8 + foldBudget V.val a.val (i.val+1) := by
  decide +kernel

theorem posCycles_le : ∀ V : Fin 3, ∀ a : Fin 15, ∀ i : Fin 15, i.val < a.val → posCycles V.val a.val i.val ≤ 10 := by
  decide +kernel

theorem foldBudget_start : ∀ V : Fin 3, ∀ a : Fin 15, 0 < a.val →
    foldBudget V.val a.val 0 = 16*a.val-1-(if 3 ≤ a.val then 1 else 0)-segmentSave V.val a.val := by
  decide +kernel

theorem foldBudget_old_bound : ∀ V : Fin 3, ∀ a : Fin 15, foldBudget V.val a.val 0 ≤ 16*a.val-1 := by
  decide +kernel

theorem tailSel_lt : ∀ V : Fin 3, ∀ t : Fin 2, ∀ a : Fin 15, ∀ bits : Fin 8,
    0 < a.val → tailSel V.val t.val a.val bits.val < tailCopies V.val := by decide +kernel

theorem selected_pos_steps : ∀ V : Fin 3, ∀ t : Fin 2, ∀ a : Fin 15, ∀ i : Fin 15,
    ∀ bits : Fin 8, ∀ t' : Fin 2, i.val<a.val →
    (prefixPosSpec V.val t.val a.val i.val bits.val t'.val).steps = posCycles V.val a.val i.val := by decide +kernel

theorem selected_pos_next : ∀ V : Fin 3, ∀ t : Fin 2, ∀ a : Fin 15, ∀ i : Fin 15,
    ∀ bits : Fin 8, ∀ t' : Fin 2, i.val+1<a.val →
    (i.val < prefixN a.val → t'.val = bits.val / 2^(i.val+1) % 2) →
    (prefixPosSpec V.val t.val a.val i.val bits.val t'.val).pc+1 =
      posCodePc V.val t'.val a.val (i.val+1) bits.val := by decide +kernel

theorem selected_pos_last : ∀ V : Fin 3, ∀ t : Fin 2, ∀ a : Fin 15, ∀ i : Fin 15,
    ∀ bits : Fin 8, ∀ t' : Fin 2, i.val+1=a.val →
    (prefixPosSpec V.val t.val a.val i.val bits.val t'.val).pc+1 =
      tailPc V.val (tailSel V.val t.val a.val bits.val) := by decide +kernel

/-! ## Sub-word stores and counters (copies of `LayArith` facts, so that the PORS part does not
depend on the layer modules) -/

theorem preplaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring

theorem pmerge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [preplaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem pleNat_slice8 (l : List Byte) (off : Nat) (h : off + 4 ≤ l.length) :
    leNat (slice l off 8) = leNat (slice l off 4) + 2 ^ 32 * leNat (slice l (off + 4) 4) := by
  have : slice l off 8 = slice l off 4 ++ slice l (off + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop, Nat.add_comm off 4]
  rw [this, leNat_append]
  have : (slice l off 4).length = 4 := by simp [slice]; omega
  rw [this]; norm_num


theorem pwitCounter_lt (wl : List Byte) (lay : Nat) : witCounter wl lay < 2 ^ 32 := by
  unfold witCounter
  have := leNat_lt (slice wl (ctrOff lay) 4)
  have l4 : (slice wl (ctrOff lay) 4).length ≤ 4 := by simp [slice]
  exact lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))

theorem ext_toNat (a : BitVec 256) (i : Nat) :
    (a.extractLsb' (64 * i) 64).toNat = a.toNat / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem idxE_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    idxE.eval s = BitVec.ofNat 64 (A % 2 ^ 34) := by
  apply BitVec.eq_of_toNat_eq
  have e : idxE.eval s = ((wLdE 0).eval s <<< ((BitVec.ofNat 64 30).toNat % 64)) >>>
      ((BitVec.ofNat 64 30).toNat % 64) := rfl
  rw [e, h0]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

theorem lo32E_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    lo32E.eval s = BitVec.ofNat 64 (2 ^ 32 * (A % 2 ^ 34 % 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  have e : lo32E.eval s = idxE.eval s <<< ((BitVec.ofNat 64 32).toNat % 64) := rfl
  rw [e, idxE_eval A s h0]
  have hX : A % 2 ^ 34 < 2 ^ 34 := Nat.mod_lt _ (by decide)
  generalize A % 2 ^ 34 = X at *
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  norm_num
  omega

theorem hiE_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    hiE.eval s = BitVec.ofNat 64 (2 ^ 24 * (A % 2 ^ 34 / 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  have e : hiE.eval s = ((idxE.eval s >>> ((BitVec.ofNat 64 32).toNat % 64)) <<<
      ((BitVec.ofNat 64 24).toNat % 64)) := rfl
  rw [e, idxE_eval A s h0]
  have hX : A % 2 ^ 34 < 2 ^ 34 := Nat.mod_lt _ (by decide)
  generalize A % 2 ^ 34 = X at *
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

/-- A 14-bit field inside one digest word. -/
theorem field_one (A w b : Nat) (hb : b + 14 ≤ 64) :
    A / 2 ^ (64 * w) % 2 ^ 64 / 2 ^ b % 2 ^ 14 = A / 2 ^ (64 * w + b) % 2 ^ 14 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 14
  · simp only [hj, decide_true, Bool.true_and, show j + b < 64 by omega]
    congr 1; omega
  · simp [hj]

/-- A 14-bit field across two digest words (`srl`, `sll`, `or`). -/
theorem field_two (A w b : Nat) (hb1 : 50 < b) (hb2 : b < 64) :
    (A / 2 ^ (64 * w) % 2 ^ 64 / 2 ^ b ||| A / 2 ^ (64 * (w + 1)) % 2 ^ 64 * 2 ^ (64 - b) % 2 ^ 64) %
      2 ^ 14 = A / 2 ^ (64 * w + b) % 2 ^ 14 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < 14
  · simp only [hj, decide_true, Bool.true_and]
    by_cases h1 : j + b < 64
    · have h2 : ¬ (64 - b ≤ j) := by omega
      simp only [h1, h2, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.or_false]
      congr 1; omega
    · have h2 : 64 - b ≤ j := by omega
      simp only [h1, h2, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or,
        show j < 64 by omega, show j - (64 - b) < 64 by omega]
      congr 1; omega
  · simp [hj]

theorem land16383 (n : Nat) : n &&& 16383 = n % 2 ^ 14 := Nat.and_two_pow_sub_one_eq_mod n 14

 theorem scaled_field_one (A w b : Nat) (hb0 : 3 ≤ b) (hb : b + 14 ≤ 64) :
    (A / 2 ^ (64*w) % 2^64 / 2^(b-3)) &&& (16383*2^3) =
      8 * (A / 2^(64*w+b) % 2^14) := by
  rw [Nat.mul_comm 8, show (8:Nat)=2^3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]
  have hm : (16383 : Nat) = 2^14-1 := rfl
  rw [hm, Nat.testBit_two_pow_sub_one]
  by_cases h3 : 3 ≤ j
  · by_cases h14 : j-3 < 14
    · have h64 : j+(b-3)<64 := by omega
      simp only [h3,h14,h64,decide_true,Bool.true_and,Bool.and_true]
      congr 1; omega
    · simp [h3,h14]
  · simp [h3]
 theorem scaled_field_two (A w b : Nat) (hb1 : 50 < b) (hb2 : b < 64) :
    ((A / 2^(64*w) % 2^64 / 2^(b-3)) |||
       (A / 2^(64*(w+1)) % 2^64 * 2^(64-b+3) % 2^64)) &&& (16383*2^3) =
      8 * (A / 2^(64*w+b) % 2^14) := by
  rw [Nat.mul_comm 8, show (8:Nat)=2^3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]
  have hm : (16383 : Nat) = 2^14-1 := rfl
  rw [hm, Nat.testBit_two_pow_sub_one]
  by_cases h3 : 3 ≤ j
  · by_cases h14 : j-3 < 14
    · by_cases h64 : j+(b-3)<64
      · have hfalse : ¬64-b+3≤j := by omega
        simp only [h3,h14,h64,hfalse,decide_true,decide_false,Bool.true_and,Bool.and_true,Bool.false_and,Bool.or_false,Bool.and_false]
        congr 1; omega
      · have htrue : 64-b+3≤j := by omega
        have hj : j<64 := by omega
        have hj' : j-(64-b+3)<64 := by omega
        simp only [h3,h14,h64,htrue,hj,hj',decide_true,decide_false,Bool.true_and,Bool.and_true,Bool.false_and,Bool.false_or]
        congr 1; omega
    · simp [h3,h14]
  · simp [h3]
/-- The byte offset `8*v_r` computed by the setup. -/
theorem pindE_eval (A : Nat) (s : MachineState)
    (hw : ∀ i, i < 4 → (wLdE i).eval s = BitVec.ofNat 64 (A / 2 ^ (64 * i) % 2 ^ 64)) (r : Nat)
    (hr : r < 15) : (pindE r).eval s = BitVec.ofNat 64 (8 * (A / 2 ^ (34 + 14 * r) % 2 ^ 14)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt (A / 2 ^ (34 + 14 * r)) (show 2 ^ 14 > 0 by decide); omega)]
  unfold pindE
  dsimp only
  have hp : 34 + 14 * r = 64 * ((34 + 14 * r) / 64) + (34 + 14 * r) % 64 := by omega
  have hwl : (34 + 14 * r) / 64 < 4 := by omega
  have hb3 : 3 ≤ (34 + 14 * r) % 64 := by interval_cases r <;> decide
  by_cases h : (34 + 14 * r) % 64 + 14 ≤ 64
  · rw [if_pos h]
    show (((wLdE ((34 + 14 * r) / 64)).eval s >>> ((BitVec.ofNat 64 ((34 + 14 * r) % 64 - 3)).toNat % 64)) &&&
      BitVec.ofNat 64 131064).toNat = _
    rw [hw _ hwl]
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 - 3 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 - 3 < 64 by omega), Nat.mod_mod,
      show 131064 % 2 ^ 64 = 16383*2^3 from rfl, scaled_field_one _ _ _ hb3 h, ← hp]
  · rw [if_neg h]
    have hwl1 : (34 + 14 * r) / 64 + 1 < 4 := by
      interval_cases r <;> simp_all
    show ((((wLdE ((34 + 14 * r) / 64)).eval s >>> ((BitVec.ofNat 64 ((34 + 14 * r) % 64 - 3)).toNat % 64)) |||
      ((wLdE ((34 + 14 * r) / 64 + 1)).eval s <<< ((BitVec.ofNat 64 (64 - (34 + 14 * r) % 64 + 3)).toNat % 64))) &&&
      BitVec.ofNat 64 131064).toNat = _
    rw [hw _ hwl, hw _ hwl1]
    simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 - 3 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 - 3 < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - (34 + 14 * r) % 64 + 3 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - (34 + 14 * r) % 64 + 3 < 64 by omega),
      show 131064 % 2 ^ 64 = 16383*2^3 from rfl]
    simp only [Nat.mod_mod]
    rw [scaled_field_two _ _ _ (by omega) (by omega), ← hp]

theorem sll63_cmp (X : E) (U : Nat) (hU : U < 2 ^ 64) (s : MachineState) (hX : X.eval s = BitVec.ofNat 64 U) :
    CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 1) ∧
    CmpOp.ge.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 0) := by
  have h1 : CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 1) := by
    simp only [CmpOp.eval, E.eval, BinOp.eval, cw, hX]
    rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt hU]
    norm_num
    omega
  refine ⟨h1, ?_⟩
  have : CmpOp.ge.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) =
      !CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) := rfl
  rw [this, h1]
  by_cases h : U % 2 = 1 <;> simp [h] <;> omega

/-! ## The counter check -/

theorem or_disj (lo hi : Nat) (hlo : lo < 2 ^ 32) :
    (lo + 2 ^ 32 * hi) ||| (2 ^ 32 * lo) = lo + 2 ^ 32 * (hi ||| lo) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have a1 : (lo + 2 ^ 32 * hi).testBit j = if j < 32 then lo.testBit j else hi.testBit (j - 32) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo]
  have a2 : (2 ^ 32 * lo).testBit j = if j < 32 then false else lo.testBit (j - 32) := by
    have := Nat.testBit_two_pow_mul_add lo (show 0 < 2 ^ 32 by decide) j
    rw [Nat.add_zero] at this; rw [this]; simp
  have a3 : (lo + 2 ^ 32 * (hi ||| lo)).testBit j =
      if j < 32 then lo.testBit j else (hi ||| lo).testBit (j - 32) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo]
  rw [Nat.testBit_or, a1, a2, a3]
  split <;> simp [Nat.testBit_or]

theorem ctr_shift_iff (x : Nat) (hx : x < 2 ^ 64) :
    (x ||| (x * 2 ^ 32 % 2 ^ 64)) / 2 ^ 54 = 0 ↔ x % 2 ^ 32 < 2 ^ 22 ∧ x / 2 ^ 32 < 2 ^ 22 := by
  have hd := Nat.div_add_mod x (2 ^ 32)
  have hlo : x % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hhi : x / 2 ^ 32 < 2 ^ 32 := by omega
  have e1 : x * 2 ^ 32 % 2 ^ 64 = 2 ^ 32 * (x % 2 ^ 32) := by omega
  have e3 : x ||| 2 ^ 32 * (x % 2 ^ 32) = x % 2 ^ 32 + 2 ^ 32 * (x / 2 ^ 32 ||| x % 2 ^ 32) := by
    rw [← or_disj _ _ hlo]; congr 1; omega
  rw [e1, e3]
  generalize x % 2 ^ 32 = lo at *
  generalize x / 2 ^ 32 = hi at *
  have hor : hi ||| lo < 2 ^ 32 := Nat.or_lt_two_pow hhi hlo
  constructor
  · intro h
    have : hi ||| lo < 2 ^ 22 := by omega
    exact ⟨lt_of_le_of_lt Nat.right_le_or this, lt_of_le_of_lt Nat.left_le_or this⟩
  · rintro ⟨h1, h2⟩
    have := Nat.or_lt_two_pow h2 h1
    omega

/-- `&&&` of two numbers split at bit `w`. -/
theorem and_split (w lo hi mlo mhi : Nat) (hlo : lo < 2 ^ w) (hm : mlo < 2 ^ w) :
    (lo + 2 ^ w * hi) &&& (mlo + 2 ^ w * mhi) = (lo &&& mlo) + 2 ^ w * (hi &&& mhi) := by
  have hand : lo &&& mlo < 2 ^ w := Nat.and_lt_two_pow lo hm
  apply Nat.eq_of_testBit_eq
  intro j
  have a1 : (lo + 2 ^ w * hi).testBit j = if j < w then lo.testBit j else hi.testBit (j - w) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo]
  have a2 : (mlo + 2 ^ w * mhi).testBit j = if j < w then mlo.testBit j else mhi.testBit (j - w) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hm]
  have a3 : ((lo &&& mlo) + 2 ^ w * (hi &&& mhi)).testBit j =
      if j < w then (lo &&& mlo).testBit j else (hi &&& mhi).testBit (j - w) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hand]
  rw [Nat.testBit_and, a1, a2, a3]
  by_cases h : j < w <;> simp [h, Nat.testBit_and]

/-- A 32-bit half masked with bits `22 .. 31` is zero iff the half is below `2^22`. -/
theorem and_hiMask (y : Nat) (hy : y < 2 ^ 32) : y &&& 0xFFC00000 = 0 ↔ y < 2 ^ 22 := by
  have hr : y % 2 ^ 22 < 2 ^ 22 := Nat.mod_lt _ (by norm_num)
  have e : y &&& 0xFFC00000 = 2 ^ 22 * (y / 2 ^ 22 % 2 ^ 10) := by
    have h := and_split 22 (y % 2 ^ 22) (y / 2 ^ 22) 0 1023 hr (by norm_num)
    rw [Nat.mod_add_div, show (0 : Nat) + 2 ^ 22 * 1023 = 0xFFC00000 by norm_num, Nat.and_zero,
      Nat.zero_add, show (1023 : Nat) = 2 ^ 10 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod] at h
    exact h
  rw [e]
  omega

/-- The counter check as one mask: `x &&& 0xFFC00000FFC00000 = 0` iff both 32-bit halves of `x`
are below `2^22` (the right side of `ctr_shift_iff`). -/
theorem ctr_mask_iff (x : Nat) (hx : x < 2 ^ 64) :
    x &&& 0xFFC00000FFC00000 = 0 ↔ x % 2 ^ 32 < 2 ^ 22 ∧ x / 2 ^ 32 < 2 ^ 22 := by
  have hlo : x % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhi : x / 2 ^ 32 < 2 ^ 32 := by omega
  have h := and_split 32 (x % 2 ^ 32) (x / 2 ^ 32) 0xFFC00000 0xFFC00000 hlo (by norm_num)
  rw [Nat.mod_add_div,
    show (0xFFC00000 : Nat) + 2 ^ 32 * 0xFFC00000 = 0xFFC00000FFC00000 by norm_num] at h
  rw [h]
  have e1 := and_hiMask _ hlo
  have e2 := and_hiMask _ hhi
  constructor
  · intro h0
    exact ⟨e1.mp (by omega), e2.mp (by omega)⟩
  · rintro ⟨h1, h2⟩
    have z1 := e1.mpr h1
    have z2 := e2.mpr h2
    omega

/-- Word 0 of the relabelled node buffers. -/
theorem nbW0E_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    nbW0E.eval s = BitVec.ofNat 64 (twLo 10 0 (A % 2 ^ 34) (A % 2 ^ 34)) := by
  have e : nbW0E.eval s = hiE.eval s + BitVec.ofNat 64 0xA01 + lo32E.eval s := rfl
  rw [e, hiE_eval A s h0, lo32E_eval A s h0, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  have hX : A % 2 ^ 34 < 2 ^ 34 := Nat.mod_lt _ (by decide)
  generalize A % 2 ^ 34 = X at *
  congr 1
  unfold twLo
  omega

/-- Word 0 of the relabelled leaf buffer. -/
theorem cbW0E_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    cbW0E.eval s = BitVec.ofNat 64 (twLo 9 0 (A % 2 ^ 34) (A % 2 ^ 34)) := by
  have e : cbW0E.eval s = nbW0E.eval s + BitVec.ofNat 64 18446744073709551360 := rfl
  rw [e, nbW0E_eval A s h0]
  have h10 : twLo 10 0 (A % 2 ^ 34) (A % 2 ^ 34) = twLo 9 0 (A % 2 ^ 34) (A % 2 ^ 34) + 256 := by
    unfold twLo; omega
  rw [h10]
  generalize twLo 9 0 (A % 2 ^ 34) (A % 2 ^ 34) = y
  rw [BitVec.ofNat_add_ofNat, show y + 256 + 18446744073709551360 = y + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]

end SigGolfCandidate.Verify
