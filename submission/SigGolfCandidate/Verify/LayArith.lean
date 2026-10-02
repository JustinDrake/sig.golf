import SigGolfCandidate.Verify.Arith
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Verify.LayerRuns
import SigGolfCandidate.Verify.Common

/-! # Bit-level facts for the layer blocks (sub-word stores, counter, route, encoding check) -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
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

theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem leNat_slice8 (l : List Byte) (off : Nat) (h : off + 4 ≤ l.length) :
    leNat (slice l off 8) = leNat (slice l off 4) + 2 ^ 32 * leNat (slice l (off + 4) 4) := by
  have : slice l off 8 = slice l off 4 ++ slice l (off + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop, Nat.add_comm off 4]
  rw [this, leNat_append]
  have : (slice l off 4).length = 4 := by simp [slice]; omega
  rw [this]; norm_num


theorem ctrA_facts (lay : Nat) (hlay : lay < 5) :
    ctrA lay = 0x800 + (ctrA lay - 0x800) ∧ ctrA lay - 0x800 + 8 ≤ 16384 ∧
      ctrOff lay = ctrA lay - 0x800 + 4 * (lay % 2) ∧ (ctrA lay - 0x800) % 8 = 0 := by
  unfold ctrA ctrOff; rw [wChains_eq, wC4_eq]
  split_ifs <;> omega

/-- The counter of layer `lay` from the doubleword that holds it. -/
theorem ctrE_eval (lay : Nat) (hlay : lay < 5) (wl : List Byte) (hwl : wl.length = 16384)
    (s : MachineState) (hw : s.getMem (BitVec.ofNat 64 (ctrA lay)) = w64 (slice wl (ctrA lay - 0x800) 8)) :
    ((ctrE lay).eval s).toNat = witCounter wl lay := by
  obtain ⟨e1, e2, e3, -⟩ := ctrA_facts lay hlay
  generalize ctrA lay - 0x800 = O at e1 e2 e3 hw
  simp only [ctrE, ldE, Rv.E.eval, UnOp.eval, LoadKind.fromWord, cw]
  rw [hw]
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega), witCounter, e3]
  have hA := leNat_lt (slice wl O 4)
  have hB := leNat_lt (slice wl (O + 4) 4)
  have l4 : ∀ o, (slice wl o 4).length ≤ 4 := fun o => by simp [slice]
  have hA' : leNat (slice wl O 4) < 2 ^ 32 :=
    lt_of_lt_of_le hA (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  have hB' : leNat (slice wl (O + 4) 4) < 2 ^ 32 :=
    lt_of_lt_of_le hB (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  rcases Nat.mod_two_eq_zero_or_one lay with h | h
  · rw [h, show 4 * 0 / 4 * 32 = 0 from rfl, show O + 4 * 0 = O from rfl]
    generalize leNat (slice wl O 4) = A at *
    generalize leNat (slice wl (O + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega
  · rw [h, show 4 * 1 / 4 * 32 = 32 from rfl, show O + 4 * 1 = O + 4 from rfl]
    generalize leNat (slice wl O 4) = A at *
    generalize leNat (slice wl (O + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega

theorem witCounter_lt (wl : List Byte) (lay : Nat) : witCounter wl lay < 2 ^ 32 := by
  unfold witCounter
  have := leNat_lt (slice wl (ctrOff lay) 4)
  have l4 : (slice wl (ctrOff lay) 4).length ≤ 4 := by simp [slice]
  exact lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))

theorem lt_or_eval (a b : Word) :
    CmpOp.lt.eval (a ||| b) (0 : Word) = decide (2 ^ 63 ≤ a.toNat ∨ 2 ^ 63 ≤ b.toNat) := by
  simp only [CmpOp.eval]
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or, BitVec.msb_eq_decide,
    BitVec.msb_eq_decide]
  simp

/-! ## Route -/

def layS (lay : Nat) : Nat := [23, 17, 11, 5, 0].getD lay 0

theorem heightL_eq (lay : Nat) (h : lay < 5) : heightL lay = height lay := by
  interval_cases lay <;> rfl

theorem route_eq (idx lay : Nat) (hlay : lay < 5) :
    route idx lay = (idx / 2 ^ layS lay % 2 ^ heightL lay, idx / 2 ^ (layS lay + heightL lay)) := by
  unfold route
  interval_cases lay <;> rfl

theorem layS_succ (lay : Nat) (h : lay < 4) : layS lay = layS (lay + 1) + heightL (lay + 1) := by
  interval_cases lay <;> rfl

theorem heightL_le (lay : Nat) (h : lay < 5) : 4 ≤ heightL lay ∧ heightL lay ≤ 11 := by
  interval_cases lay <;> decide

theorem and_mask_eval (s : MachineState) (r : Reg) (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64)
    (h : s.getReg r = BitVec.ofNat 64 x) :
    (E.bin .and (.reg r) (cw (2 ^ k - 1))).eval s = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have : x % 2 ^ k < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) this
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]

theorem srl_reg_eval (s : MachineState) (r : Reg) (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 64)
    (h : s.getReg r = BitVec.ofNat 64 x) :
    (E.bin .srl (.reg r) (cw k)).eval s = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : x / 2 ^ k ≤ x := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (show x / 2 ^ k < 2 ^ 64 by omega)]

/-- The value the route reads: `idx` (layer 4, in `x22`) or `tau_{lay+1}` (in `x30`). -/
def routeIn (idx lay : Nat) : Nat := if lay = 4 then idx else idx / 2 ^ layS lay

def routeReg (lay : Nat) : Reg := if lay = 4 then .x22 else .x30

theorem routeIn_lt (idx lay : Nat) (hidx : idx < 2 ^ 34) : routeIn idx lay < 2 ^ 34 := by
  unfold routeIn; split
  · exact hidx
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) hidx

theorem routeIn_eq (idx lay : Nat) (hlay : lay < 5) : routeIn idx lay = idx / 2 ^ layS lay := by
  unfold routeIn; split
  · subst_vars; simp [layS]
  · rfl

/-- The last layer consumes all remaining route bits. -/
theorem routeIn_zero_lt (idx : Nat) (hidx : idx < 2 ^ 34) : idx / 2 ^ layS 0 < 2048 := by
  change idx / 8388608 < 2048
  omega

theorem uEr_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (uEr lay).eval s = BitVec.ofNat 64 (idx / 2 ^ layS lay % 2 ^ heightL lay) := by
  have hr := routeIn_lt idx lay hidx
  have hh := heightL_le lay hlay
  by_cases h0 : lay = 0
  · subst lay
    have hr0 := routeIn_zero_lt idx hidx
    change s.getReg .x30 = BitVec.ofNat 64 (idx / 2 ^ layS 0 % 2048)
    change s.getReg .x30 = BitVec.ofNat 64 (idx / 2 ^ layS 0) at h
    rw [Nat.mod_eq_of_lt hr0]
    exact h
  simp only [uEr, if_neg h0]
  show (E.bin .and (.reg (routeReg lay)) (cw (2 ^ heightL lay - 1))).eval s = _
  rw [and_mask_eval s _ _ _ (by omega) (by omega) h, routeIn_eq idx lay hlay]

theorem tauEr_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (tauEr lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + heightL lay)) := by
  have hr := routeIn_lt idx lay hidx
  have hh := heightL_le lay hlay
  by_cases h0 : lay = 0
  · subst lay
    have hz : idx / 2 ^ (layS 0 + heightL 0) = 0 := by
      change idx / 2 ^ 34 = 0
      exact Nat.div_eq_of_lt hidx
    simp [tauEr, Rv.E.eval, cw, hz]
  simp only [tauEr, if_neg h0]
  show (E.bin .srl (.reg (routeReg lay)) (cw (heightL lay))).eval s = _
  rw [srl_reg_eval s _ _ _ (by omega) (by omega) h, routeIn_eq idx lay hlay, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

theorem tau_lt (lay idx : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) :
    idx / 2 ^ (layS lay + heightL lay) < 2 ^ 30 := by
  have h4 : 4 ≤ layS lay + heightL lay := by interval_cases lay <;> decide
  apply Nat.div_lt_of_lt_mul
  calc idx < 2 ^ 34 := hidx
    _ = 2 ^ 4 * 2 ^ 30 := by norm_num
    _ ≤ 2 ^ (layS lay + heightL lay) * 2 ^ 30 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h4)

theorem e_lt32 (lay idx : Nat) (hlay : lay < 5) : idx / 2 ^ layS lay % 2 ^ heightL lay < 2048 := by
  have := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ heightL lay from Nat.two_pow_pos _)
  have : 2 ^ heightL lay ≤ 2048 := by interval_cases lay <;> decide
  omega

theorem xor_top_sentinel : ∀ e, e < 2048 →
    (BitVec.ofNat 64 e ^^^ 4095#64) = BitVec.ofNat 64 (4095 - e) := by decide +kernel


theorem uHE_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (uHE lay).eval s = BitVec.ofNat 64 (heapU lay (idx / 2 ^ layS lay % 2 ^ heightL lay)) := by
  have he := uEr_eval idx lay hlay hidx s h
  have hm := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ heightL lay from Nat.two_pow_pos _)
  have hh := heightL_le lay hlay
  have hp : 2 ^ heightL lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hh.2
  unfold uHE
  split
  · rename_i h0; subst h0
    show (uEr 0).eval s ^^^ BitVec.ofNat 64 4095 = _
    rw [he]
    exact xor_top_sentinel _ (by simpa [heightL] using hm)
  · rename_i h0
    show (uEr lay).eval s + BitVec.ofNat 64 (2 ^ heightL lay + uOff lay) = _
    rw [he, heapU, if_neg h0]
    have hu : uOff lay ≤ 456 := by unfold uOff; split_ifs <;> omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem carryEr_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (carryEr lay).eval s = BitVec.ofNat 64
      (if lay = 0 then idx / 2 ^ layS lay % 2 ^ heightL lay
       else idx / 2 ^ (layS lay + heightL lay)) := by
  unfold carryEr
  split_ifs
  · exact uEr_eval idx lay hlay hidx s h
  · exact tauEr_eval idx lay hlay hidx s h

theorem x31Er_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (x31Er lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + heightL lay) +
      2 ^ 32 * (idx / 2 ^ layS lay % 2 ^ heightL lay)) := by
  have ht := tau_lt lay idx hlay hidx
  have he := e_lt32 lay idx hlay
  have h1 : (x31Er lay).eval s = (tauEr lay).eval s + ((uEr lay).eval s <<< ((BitVec.ofNat 64 32).toNat % 64)) := by
    by_cases h0 : lay = 0
    · subst lay
      change (s.getReg .x30 <<< 32) = (0#64 + (s.getReg .x30 <<< 32))
      exact (BitVec.zero_add _).symm
    · simp only [x31Er, if_neg h0]; rfl
  rw [h1, tauEr_eval idx lay hlay hidx s h, uEr_eval idx lay hlay hidx s h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize idx / 2 ^ (layS lay + heightL lay) = t at *
  generalize idx / 2 ^ layS lay % 2 ^ heightL lay = e at *
  norm_num
  omega

/-! ## The encoding check -/

def dA (out hi : Nat) (s : MachineState) : Nat := ((d0E out hi).eval s).toNat
def dB (out hi : Nat) (s : MachineState) : Nat := ((d1E out hi).eval s).toNat

section
variable (out hi : Nat) (s : MachineState)

theorem swA3ref_toNat : ((swA3ref out hi).eval s).toNat = sw1 (dA out hi s) (dB out hi s) := by
  simp only [swA3ref, d0E, d1E, m1E, M1w, ldE, cw, Rv.E.eval, BinOp.eval, BitVec.toNat_add,
    BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, sw1, dA, dB]
  try norm_num

/-- Splitting a word by a mask and its complement: the parts have disjoint bits, so they add up to the word. -/
theorem swar7_split (x m : BitVec 64) : (x &&& m) + (x &&& ~~~m) = x := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases x[i] <;> cases m[i] <;> rfl
  · ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]; cases x[i] <;> cases m[i] <;> rfl

/-- `M1` has period 6 with three set bits: bit `i` is set exactly when bit `i + 3` is clear. -/
theorem swar7_period : ∀ i : Fin 61,
    (0x71c71c71c71c71c7#64).getLsbD i.val = !(0x71c71c71c71c71c7#64).getLsbD (i.val + 3) := by
  decide

/-- `(x >>> 3) & M1` is the odd-digit part `x & ~M1` shifted down by three. -/
theorem swar7_shift (x : BitVec 64) :
    (x >>> 3) &&& 0x71c71c71c71c71c7#64 = (x &&& ~~~0x71c71c71c71c71c7#64) >>> 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not]
  by_cases h : i < 61
  · have hp := swar7_period ⟨i, h⟩
    simp only at hp
    rw [hp, show 3 + i = i + 3 by omega]
    simp [show i + 3 < 64 by omega]
  · have hx : x.getLsbD (3 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
    simp [hx]

/-- The odd-digit part `x & ~M1` is a multiple of 8 (bits 0..2 belong to `M1`). -/
theorem swar7_low (x : BitVec 64) : (x &&& ~~~0x71c71c71c71c71c7#64).toNat % 8 = 0 := by
  have h7 : (x &&& ~~~0x71c71c71c71c71c7#64) &&& 7#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero]
    by_cases h : i < 3
    · have : (0x71c71c71c71c71c7#64).getLsbD i = true := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide
      simp [this]
    · have : (7#64).getLsbD i = false := by
        rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
        exact Nat.testBit_lt_two_pow (by
          calc 7 < 2 ^ 3 := by decide
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  have := congrArg BitVec.toNat h7
  rw [BitVec.toNat_and] at this
  have e : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

/-- The 7-step lane word equals the reference one for words below `2^63`: the odd-digit parts
`A - (A & M1)`, `B - (B & M1)` are multiples of 8 and their sum does not wrap. -/
theorem swar7_eq (a b : BitVec 64) (ha : a < 0x8000000000000000#64) (hb : b < 0x8000000000000000#64) :
    ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64)) +
      (((a + b) - ((a &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64))) >>> 3) =
    ((a >>> 3) &&& 0x71c71c71c71c71c7#64) + (a &&& 0x71c71c71c71c71c7#64) +
      ((b >>> 3) &&& 0x71c71c71c71c71c7#64) + (b &&& 0x71c71c71c71c71c7#64) := by
  rw [swar7_shift a, swar7_shift b]
  set M : BitVec 64 := 0x71c71c71c71c71c7#64 with hM
  have sa := congrArg BitVec.toNat (swar7_split a M)
  have sb := congrArg BitVec.toNat (swar7_split b M)
  have la := swar7_low a
  have lb := swar7_low b
  rw [← hM] at la lb
  have ha' : a.toNat < 2 ^ 63 := by rw [BitVec.lt_def] at ha; simpa using ha
  have hb' : b.toNat < 2 ^ 63 := by rw [BitVec.lt_def] at hb; simpa using hb
  have lea : (a &&& M).toNat ≤ a.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  have leb : (b &&& M).toNat ≤ b.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  have loa : (a &&& ~~~M).toNat ≤ a.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  have lob : (b &&& ~~~M).toNat ≤ b.toNat := by rw [BitVec.toNat_and]; exact Nat.and_le_left
  rw [BitVec.toNat_add] at sa sb
  have h1 : (a + b) - ((a &&& M) + (b &&& M)) = (a &&& ~~~M) + (b &&& ~~~M) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (a &&& M).toNat + (b &&& M).toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    omega
  have h2 : ((a &&& ~~~M) + (b &&& ~~~M)) >>> 3 = ((a &&& ~~~M) >>> 3) + ((b &&& ~~~M) >>> 3) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (show (a &&& ~~~M).toNat + (b &&& ~~~M).toNat < 2 ^ 64 by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  ac_rfl

theorem swA3_eval (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    (swA3 out hi).eval s = (swA3ref out hi).eval s := by
  have ha : (d0E out hi).eval s < 0x8000000000000000#64 := BitVec.lt_def.mpr (by simpa [dA] using h0)
  have hb : (d1E out hi).eval s < 0x8000000000000000#64 := BitVec.lt_def.mpr (by simpa [dB] using h1)
  have e3 : (BitVec.ofNat 64 3).toNat % 64 = 3 := by decide
  simp only [swA3, swA3ref, swT1, m1E, M1w, cw, Rv.E.eval, BinOp.eval, e3]
  exact swar7_eq _ _ ha hb

theorem swA3_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swA3 out hi).eval s).toNat = sw1 (dA out hi s) (dB out hi s) := by
  rw [swA3_eval out hi s h0 h1, swA3ref_toNat]

theorem swA4_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swA4 out hi).eval s).toNat = (sw1 (dA out hi s) (dB out hi s) + sw1 (dA out hi s) (dB out hi s) / 64) % 18446744073709551616 := by
  rw [show (swA4 out hi).eval s = (swA3 out hi).eval s + ((swA3 out hi).eval s >>> ((BitVec.ofNat 64 6).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA3_toNat out hi s h0 h1, Nat.shiftRight_eq_div_pow]
  norm_num

theorem swA5_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swA5 out hi).eval s).toNat = m3 ((sw1 (dA out hi s) (dB out hi s) + sw1 (dA out hi s) (dB out hi s) / 64) % 18446744073709551616) := by
  rw [show (swA5 out hi).eval s = (swA4 out hi).eval s &&& 0xf03f03f03f03f03f#64 from rfl, BitVec.toNat_and,
    swA4_toNat out hi s h0 h1]
  rfl

theorem swA6_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swA6 out hi).eval s).toNat = m4 (m3 ((sw1 (dA out hi s) (dB out hi s) + sw1 (dA out hi s) (dB out hi s) / 64) % 18446744073709551616)) := by
  rw [show (swA6 out hi).eval s = (swA5 out hi).eval s + ((swA5 out hi).eval s >>> ((BitVec.ofNat 64 12).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA5_toNat out hi s h0 h1, Nat.shiftRight_eq_div_pow]
  simp only [m4]; norm_num

theorem swA7_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swA7 out hi).eval s).toNat = m5 (m4 (m3 ((sw1 (dA out hi s) (dB out hi s) + sw1 (dA out hi s) (dB out hi s) / 64) % 18446744073709551616))) := by
  rw [show (swA7 out hi).eval s = (swA6 out hi).eval s + ((swA6 out hi).eval s >>> ((BitVec.ofNat 64 24).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA6_toNat out hi s h0 h1, Nat.shiftRight_eq_div_pow]
  simp only [m5]; norm_num

def swarOf (a b : Nat) : Nat := m6 (m3 ((sw1 a b + sw1 a b / 64) % 18446744073709551616)) % 4096

theorem swSBase_toNat (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    ((swSBase out hi).eval s).toNat = swarOf (dA out hi s) (dB out hi s) := by
  change (rv64_remu ((swA5 out hi).eval s) 4095#64).toNat = _
  rw [rv64_remu, if_neg (by decide), BitVec.toNat_umod]
  change ((swA5 out hi).eval s).toNat % 4095 = _
  rw [swA5_toNat out hi s h0 h1, ← swar_mersenne]
  rfl

theorem swS_toNat (lay : Nat) (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) : ((swS out hi lay).eval s).toNat =
    (swarOf (dA out hi s) (dB out hi s) + (if lay = 0 then 0 else 0)) % 2 ^ 64 := by
  rw [swS, swSBase_toNat out hi s h0 h1]
  have hsmall : swarOf (dA out hi s) (dB out hi s) < 4096 := Nat.mod_lt _ (by decide)
  simp only [ite_self, Nat.add_zero]
  omega

theorem swar_adjust_eq (v T d : Nat) (hv : v < 4096) (hT : 185 ≤ T ∧ T ≤ 186) (hd : d ≤ 1) :
    (v + d) % 2 ^ 64 = T + d ↔ v = T := by omega

theorem swS_eq (lay : Nat) (h0 : dA out hi s < 2 ^ 63) (h1 : dB out hi s < 2 ^ 63) :
    (swS out hi lay).eval s = KTof lay ↔
      (digitsOfWord (dA out hi s) ++ digitsOfWord (dB out hi s)).sum = targetFor lay := by
  have hs := swar_nat (dA out hi s) (dB out hi s) h0 h1
  have hl : swarOf (dA out hi s) (dB out hi s) < 4096 := Nat.mod_lt _ (by decide)
  let delta : Nat := if lay = 0 then 0 else 0
  have hd : delta ≤ 1 := by dsimp [delta]; split_ifs <;> decide
  have ht : 185 ≤ targetFor lay ∧ targetFor lay ≤ 186 := by
    unfold targetFor SigGolfCandidate.Ref.targetFor targetSum
    split_ifs <;> omega
  have adj := swar_adjust_eq (swarOf (dA out hi s) (dB out hi s)) (targetFor lay) delta hl ht hd
  rw [← hs]
  change _ ↔ swarOf (dA out hi s) (dB out hi s) = targetFor lay
  constructor
  · intro h
    have hh := congrArg BitVec.toNat h
    rw [swS_toNat out hi s lay h0 h1] at hh
    change (swarOf (dA out hi s) (dB out hi s) + delta) % 2 ^ 64 = (targetFor lay + delta) % 2 ^ 64 at hh
    rw [Nat.mod_eq_of_lt (show targetFor lay + delta < 2 ^ 64 by omega)] at hh
    exact adj.mp hh
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [swS_toNat out hi s lay h0 h1]
    change (swarOf (dA out hi s) (dB out hi s) + delta) % 2 ^ 64 = (targetFor lay + delta) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (show targetFor lay + delta < 2 ^ 64 by omega)]
    exact adj.mpr h

end

end SigGolfCandidate.Verify
