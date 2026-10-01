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

theorem carryEr_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (carryEr lay).eval s = BitVec.ofNat 64
      (if lay = 0 then idx / 2 ^ layS lay % 2 ^ heightL lay
       else idx / 2 ^ (layS lay + heightL lay)) := by
  unfold carryEr
  split_ifs
  · exact uEr_eval idx lay hlay hidx s h
  · exact tauEr_eval idx lay hlay hidx s h

theorem uHE_eval (idx lay : Nat) (hlay : lay < 5) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (uHE lay).eval s = BitVec.ofNat 64 (idx / 2 ^ layS lay % 2 ^ heightL lay + 2 ^ heightL lay) := by
  have he := uEr_eval idx lay hlay hidx s h
  have hm := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ heightL lay from Nat.two_pow_pos _)
  have hh := heightL_le lay hlay
  have hp : 2 ^ heightL lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) hh.2
  unfold uHE
  split
  · rename_i h0; subst h0
    show (uEr 0).eval s + BitVec.ofNat 64 2048 = _
    rw [he, BitVec.ofNat_add_ofNat]; rfl
  · show (uEr lay).eval s ||| BitVec.ofNat 64 (2 ^ heightL lay) = _
    rw [he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show idx / 2 ^ layS lay % 2 ^ heightL lay < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 ^ heightL lay < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show idx / 2 ^ layS lay % 2 ^ heightL lay + 2 ^ heightL lay < 2 ^ 64 by omega),
      Nat.or_comm]
    have := Nat.two_pow_add_eq_or_of_lt hm 1
    rw [Nat.mul_one] at this
    omega

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

def dA (hi : Bool) (s : MachineState) : Nat := ((d0E hi).eval s).toNat
def dB (hi : Bool) (s : MachineState) : Nat := ((d1E hi).eval s).toNat

section
variable (hi : Bool) (s : MachineState)

theorem swA3_toNat : ((swA3 hi).eval s).toNat = sw1 (dA hi s) (dB hi s) := by
  simp only [swA3, d0E, d1E, m1E, M1w, ldE, cw, Rv.E.eval, BinOp.eval, BitVec.toNat_add,
    BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, sw1, dA, dB]
  try norm_num

theorem swA4_toNat : ((swA4 hi).eval s).toNat = (sw1 (dA hi s) (dB hi s) + sw1 (dA hi s) (dB hi s) / 64) % 18446744073709551616 := by
  rw [show (swA4 hi).eval s = (swA3 hi).eval s + ((swA3 hi).eval s >>> ((BitVec.ofNat 64 6).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA3_toNat, Nat.shiftRight_eq_div_pow]
  norm_num

theorem swA5_toNat : ((swA5 hi).eval s).toNat = m3 ((sw1 (dA hi s) (dB hi s) + sw1 (dA hi s) (dB hi s) / 64) % 18446744073709551616) := by
  rw [show (swA5 hi).eval s = (swA4 hi).eval s &&& 0xf03f03f03f03f03f#64 from rfl, BitVec.toNat_and,
    swA4_toNat]
  rfl

theorem swA6_toNat : ((swA6 hi).eval s).toNat = m4 (m3 ((sw1 (dA hi s) (dB hi s) + sw1 (dA hi s) (dB hi s) / 64) % 18446744073709551616)) := by
  rw [show (swA6 hi).eval s = (swA5 hi).eval s + ((swA5 hi).eval s >>> ((BitVec.ofNat 64 12).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA5_toNat, Nat.shiftRight_eq_div_pow]
  simp only [m4]; norm_num

theorem swA7_toNat : ((swA7 hi).eval s).toNat = m5 (m4 (m3 ((sw1 (dA hi s) (dB hi s) + sw1 (dA hi s) (dB hi s) / 64) % 18446744073709551616))) := by
  rw [show (swA7 hi).eval s = (swA6 hi).eval s + ((swA6 hi).eval s >>> ((BitVec.ofNat 64 24).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA6_toNat, Nat.shiftRight_eq_div_pow]
  simp only [m5]; norm_num

def swarOf (a b : Nat) : Nat := m6 (m3 ((sw1 a b + sw1 a b / 64) % 18446744073709551616)) % 4096

theorem swS_toNat : ((swS hi).eval s).toNat = swarOf (dA hi s) (dB hi s) := by
  change (rv64_remu ((swA5 hi).eval s) 4095#64).toNat = _
  rw [rv64_remu, if_neg (by decide), BitVec.toNat_umod]
  change ((swA5 hi).eval s).toNat % 4095 = _
  rw [swA5_toNat, ← swar_mersenne]
  rfl

theorem swS_eq (T : Nat) (hT : T < 2 ^ 64) (h0 : dA hi s < 2 ^ 63) (h1 : dB hi s < 2 ^ 63) :
    (swS hi).eval s = BitVec.ofNat 64 T ↔ (digitsOfWord (dA hi s) ++ digitsOfWord (dB hi s)).sum = T := by
  have hs := swar_nat (dA hi s) (dB hi s) h0 h1
  rw [← hs]
  change _ ↔ swarOf (dA hi s) (dB hi s) = T
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [swS_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at this
    exact this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [swS_toNat, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT]

end

end SigGolfCandidate.Verify
