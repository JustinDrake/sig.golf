import SigGolfCandidate.T3M.Search.CsBlocks

/-!
# `counter_search`: the digit-writing loop (stream E)

`cs_dig` (kernel offsets 442..460) writes the `n` data digits as bytes to `DIGITS`: digit `j` has
width `digW n4 j` (2 below `n4 = s11`, else 3) at bit offset `digOff n4 j` of the answer value `v`;
the 128-bit window `t2:t1` is shifted right by the width after each digit.
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)

set_option linter.unusedSimpArgs false

/-! ## The digit model -/

/-- Width of digit `j`: 2 below `n4`, else 3. -/
def digW (n4 j : Nat) : Nat := if j < n4 then 2 else 3

/-- Bit offset of digit `j`. -/
def digOff (n4 j : Nat) : Nat := if j ≤ n4 then 2 * j else 2 * n4 + 3 * (j - n4)

/-- Digit `j` of `v`. -/
def digVal (v : Digest) (n4 j : Nat) : Nat := v.toNat / 2 ^ digOff n4 j % 2 ^ digW n4 j

theorem digOff_succ (n4 j : Nat) : digOff n4 (j + 1) = digOff n4 j + digW n4 j := by
  unfold digOff digW; split_ifs <;> omega

theorem lowDigits_eq (v : Digest) : lowDigits v = (List.range 42).map (digVal v 0) := by
  unfold lowDigits digVal digOff digW
  apply List.map_congr_left
  intro j _
  by_cases h : j ≤ 0
  · have : j = 0 := by omega
    subst this; simp
  · simp [h]

/-! ## Word lemmas -/

theorem ofNat_truncate8 (a : Nat) : (BitVec.ofNat 64 a).truncate 8 = BitVec.ofNat 8 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem pair_shift (X w : Nat) (hw : w < 64) :
    (BitVec.ofNat 64 X >>> w ||| BitVec.ofNat 64 (X / 2 ^ 64) <<< (64 - w)) =
      BitVec.ofNat 64 (X / 2 ^ w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    Nat.testBit_div_two_pow, hi, decide_true, Bool.true_and]
  by_cases h : w + i < 64
  · simp only [h, decide_true, Bool.true_and, show i < 64 - w by omega, decide_true, Bool.not_true,
      Bool.false_and, Bool.or_false]
    congr 1; omega
  · simp only [h, decide_false, Bool.false_and, Bool.false_or, show ¬ i < 64 - w by omega, decide_false,
      Bool.not_false, Bool.true_and, show i - (64 - w) < 64 by omega, decide_true]
    congr 1; omega

/-! ## The loop -/

/-- The digit table region (`DIGITS`, 64 bytes). -/
def DigW (A : Nat) : Prop := DIGITS ≤ A ∧ A < DIGITS + 64

/-- The registers the digit loop and the success tail may change. -/
abbrev tailRegs : List Reg := [.x6, .x7, .x20, .x21, .x28, .x29, .x30]

section loop
variable {image : Image} {b : Nat}

/-- Invariant at `cs_dig` after `i` digits. -/
structure DigInv (b : Nat) (s0 : MachineState) (v : Digest) (n n4 i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 442)
  hi : i ≤ n
  x20 : t.getReg .x20 = BitVec.ofNat 64 i
  x21 : t.getReg .x21 = BitVec.ofNat 64 n
  x27 : t.getReg .x27 = BitVec.ofNat 64 n4
  x6 : t.getReg .x6 = BitVec.ofNat 64 (v.toNat / 2 ^ digOff n4 i)
  x7 : t.getReg .x7 = BitVec.ofNat 64 (v.toNat / 2 ^ digOff n4 i / 2 ^ 64)
  digs : ∀ j < i, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (digVal v n4 j)
  regs : RegsExcept s0 t tailRegs
  frame : Frame s0 t DigW

/-- One digit: at most 19 cycles. -/
theorem dig_body (hK : KernAt image b) {s0 : MachineState} {v : Digest} {n n4 i : Nat} (hn : n ≤ 58)
    (hin : i < n) {t : MachineState} (hI : DigInv b s0 v n n4 i t) (hn4 : n4 < 2 ^ 63) :
    ∃ k u, Steps image t k k u ∧ k ≤ 19 ∧ DigInv b s0 v n n4 (i + 1) u := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs442_spec hK t hI.pc i n (by omega) (by omega) hI.x20 hI.x21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, h28, h29, r2, f2⟩ := cs443_spec hK t1 p1 i n4 (by omega) hn4
    (by rw [r1.get (by decide), hI.x20]) (by rw [r1.get (by decide), hI.x27])
  -- the width stage: (mask, width) = (2^w - 1, w)
  obtain ⟨k3, t3, s3, k3le, p3, m28, m29, r3, f3⟩ : ∃ k3 t3, Steps image t2 k3 k3 t3 ∧ k3 ≤ 2 ∧
      t3.pc = pcOf (b + 448) ∧ t3.getReg .x28 = BitVec.ofNat 64 (2 ^ digW n4 i - 1) ∧
      t3.getReg .x29 = BitVec.ofNat 64 (digW n4 i) ∧ RegsExcept t2 t3 [.x28, .x29] ∧
      Frame t2 t3 (fun _ => False) := by
    by_cases h : n4 ≤ i
    · rw [if_pos h] at p2
      exact ⟨0, t2, Steps.refl _, by omega, p2, by rw [h28]; simp [digW, show ¬ i < n4 by omega],
        by rw [h29]; simp [digW, show ¬ i < n4 by omega], RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [if_neg h] at p2
      obtain ⟨t3, s3, p3, a28, a29, r3, f3⟩ := cs446_spec hK t2 p2
      exact ⟨2, t3, s3, le_refl _, p3, by rw [a28]; simp [digW, show i < n4 by omega],
        by rw [a29]; simp [digW, show i < n4 by omega], r3, f3⟩
  have hx20 : t3.getReg .x20 = BitVec.ofNat 64 i := by
    rw [r3.get (by decide), r2.get (by decide), r1.get (by decide), hI.x20]
  obtain ⟨t4, s4, p4, h30, a28, r4, f4⟩ := cs448_spec hK t3 p3 i hx20
  have s5 := cs452_spec hK t4 p4 (DIGITS + i) (by simp only [DIGITS]; omega) a28
  set t5 := (t4.setByte (BitVec.ofNat 64 (DIGITS + i)) ((t4.getReg .x30).truncate 8)).setPC (pcOf (b + 453))
  have hp5 : t5.pc = pcOf (b + 453) := rfl
  obtain ⟨t6, s6, p6, h6', h7', h20', r6, f6⟩ := cs453_spec hK t5 hp5
  have hw : digW n4 i < 64 := by unfold digW; split_ifs <;> omega
  have hw0 : 0 < digW n4 i := by unfold digW; split_ifs <;> omega
  have hv := v.isLt
  set X := v.toNat / 2 ^ digOff n4 i with hX
  have hX128 : X < 2 ^ 128 := lt_of_le_of_lt (Nat.div_le_self _ _) hv
  have hX64 : X / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [← Nat.pow_add] using hX128
  -- registers at t4 (= t5 on registers)
  have r4' : RegsExcept t t4 [.x28, .x29, .x30] := (((r1.trans r2).trans r3).trans r4).mono (by decide)
  have g6 : t4.getReg .x6 = BitVec.ofNat 64 X := by rw [r4'.get (by decide)]; exact hI.x6
  have g7 : t4.getReg .x7 = BitVec.ofNat 64 (X / 2 ^ 64) := by rw [r4'.get (by decide)]; exact hI.x7
  have g29 : t4.getReg .x29 = BitVec.ofNat 64 (digW n4 i) := by rw [r4.get (by decide)]; exact m29
  have g20 : t4.getReg .x20 = BitVec.ofNat 64 i := by rw [r4.get (by decide)]; exact hx20
  have g30 : t4.getReg .x30 = BitVec.ofNat 64 (digVal v n4 i) := by
    rw [h30, r3.get (by decide), r2.get (by decide), r1.get (by decide), hI.x6, m28,
      ofNat_and_mask _ _ (by omega)]
    rfl
  have hfr : Frame t t4 (fun _ => False) := (((f1.trans f2).trans f3).trans f4).mono (by simp)
  have r5 : RegsExcept t4 t5 [] := fun r _ => by simp [t5]
  have f5 : Frame t4 t5 DigW := by
    intro A hA hn
    simp only [t5, getMem_setPC']
    rw [getMem_setByte _ _ _ (by simp only [DIGITS]; omega) hA _ (by simp only [DigW, DIGITS] at hn ⊢; omega)]
  refine ⟨1 + 3 + k3 + 4 + 1 + 8, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, by omega, ?_⟩
  have shw : (BitVec.ofNat 64 (digW n4 i)).toNat % 64 = digW n4 i := by
    rw [BitVec.toNat_ofNat]; omega
  have shw' : (64#64 - BitVec.ofNat 64 (digW n4 i)).toNat % 64 = 64 - digW n4 i := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hoff : v.toNat / 2 ^ digOff n4 (i + 1) = X / 2 ^ digW n4 i := by
    rw [digOff_succ, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  refine ⟨p6, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h20', getReg_setPC', getReg_setByte, g20]; exact ofNat_add_ofNat i 1
  · rw [r6.get (by decide), getReg_setPC', getReg_setByte, r4.get (by decide), r3.get (by decide),
      r2.get (by decide), r1.get (by decide), hI.x21]
  · rw [r6.get (by decide), getReg_setPC', getReg_setByte, r4'.get (by decide), hI.x27]
  · rw [h6', getReg_setPC', getReg_setByte, getReg_setPC', getReg_setByte, getReg_setPC', getReg_setByte,
      g6, g7, g29, shw, shw', pair_shift X _ hw, hoff]
  · rw [h7', getReg_setPC', getReg_setByte, getReg_setPC', getReg_setByte, g7, g29, shw,
      ofNat_shr _ _ hX64, hoff]
    congr 1
    simp only [hX, Nat.div_div_eq_div_mul]
    ring_nf
  · intro j hj
    rw [Frame.getByte f6 (by simp only [DIGITS]; omega) (by simp)]
    simp only [t5, getByte_setPC]
    rw [getByte_setByte _ _ _ (by simp only [DIGITS]; omega) (by simp only [DIGITS]; omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [if_neg (by omega), Frame.getByte hfr (by simp only [DIGITS]; omega) (by simp)]
      exact hI.digs j h
    · rw [if_pos rfl, g30, ofNat_truncate8]
  · exact (((hI.regs.trans r4').trans r5).trans r6).mono (by decide)
  · exact (((hI.frame.trans hfr).trans f5).trans f6).mono
      (fun A _ h => by simp only [or_false, or_self] at h; exact h)
theorem dig_loop (hK : KernAt image b) {s0 : MachineState} {v : Digest} {n n4 : Nat} (hn : n ≤ 58)
    (hn4 : n4 < 2 ^ 63) : ∀ m i t, i + m = n → DigInv b s0 v n n4 i t →
      ∃ k u, Steps image t k k u ∧ k ≤ 19 * m ∧ DigInv b s0 v n n4 n u := by
  intro m
  induction m with
  | zero => intro i t h hI; exact ⟨0, t, Steps.refl _, le_refl _, by simpa [← h] using hI⟩
  | succ m ih =>
    intro i t h hI
    obtain ⟨k1, t1, s1, k1le, h1⟩ := dig_body hK hn (by omega) hI hn4
    obtain ⟨k2, t2, s2, k2le, h2⟩ := ih (i + 1) t1 (by omega) h1
    exact ⟨k1 + k2, t2, s1.trans s2, by rw [Nat.mul_succ]; omega, h2⟩

theorem ext_lo_ofNat (v : Digest) (n4 : Nat) :
    v.extractLsb' 0 64 = BitVec.ofNat 64 (v.toNat / 2 ^ digOff n4 0) := by
  simp [digOff, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem ext_hi_ofNat (v : Digest) (n4 : Nat) :
    v.extractLsb' 64 64 = BitVec.ofNat 64 (v.toNat / 2 ^ digOff n4 0 / 2 ^ 64) := by
  simp [digOff, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]


/-- **The success tail** (`cs_ok` to `ret`): with the answer `v` in `t2:t1`, the digit sum `S` in `s9`,
writes the `n` data digits (top: 58, `n4 = 49`; lower: 42, `n4 = 0`, then the checksum digit
`T - S` at `DIGITS + 42`) and returns; at most `5 + 19 n + 6` cycles. -/
theorem cs_tail (hK : KernAt image b) (t : MachineState) (hpc : t.pc = pcOf (b + 438)) (v : Digest)
    (lay T S ret : Nat) (hl : lay < 4) (hT : T < 2 ^ 63) (hST : lay ≠ 0 → S ≤ T)
    (h1 : t.getReg .x1 = pcOf ret) (h8 : t.getReg .x8 = BitVec.ofNat 64 lay)
    (h17 : t.getReg .x17 = BitVec.ofNat 64 T) (h25 : t.getReg .x25 = BitVec.ofNat 64 S)
    (h26 : t.getReg .x26 = BitVec.ofNat 64 (if lay = 0 then 58 else 43))
    (h27 : t.getReg .x27 = BitVec.ofNat 64 (if lay = 0 then 49 else 0))
    (h6 : t.getReg .x6 = v.extractLsb' 0 64) (h7 : t.getReg .x7 = v.extractLsb' 64 64) :
    ∃ k u, Steps image t k k u ∧ k ≤ (if lay = 0 then 1109 else 810) ∧ u.pc = pcOf ret ∧
      (∀ j < (if lay = 0 then 58 else 42),
        u.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (digVal v (if lay = 0 then 49 else 0) j)) ∧
      (lay ≠ 0 → u.getByte (BitVec.ofNat 64 (DIGITS + 42)) = BitVec.ofNat 8 (T - S)) ∧
      RegsExcept t u tailRegs ∧ Frame t u DigW := by
  set n := if lay = 0 then 58 else 42 with hn
  set n4 := if lay = 0 then 49 else 0 with hn4
  have hn58 : n ≤ 58 := by rw [hn]; split_ifs <;> omega
  have hn42 : 42 ≤ n := by rw [hn]; split_ifs <;> omega
  have hn49 : n4 ≤ 49 := by rw [hn4]; split_ifs <;> omega
  obtain ⟨t1, s1, p1, a21, r1, f1⟩ := cs438_spec hK t hpc lay _ hl h8 h26
  -- s5 = n at offset 441
  obtain ⟨k2, t2, s2, k2le, p2, b21, r2, f2⟩ : ∃ k2 t2, Steps image t1 k2 k2 t2 ∧ k2 ≤ 1 ∧
      t2.pc = pcOf (b + 441) ∧ t2.getReg .x21 = BitVec.ofNat 64 n ∧ RegsExcept t1 t2 [.x21] ∧
      Frame t1 t2 (fun _ => False) := by
    by_cases h : lay = 0
    · rw [if_pos h] at p1
      refine ⟨0, t1, Steps.refl _, by omega, p1, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
      rw [a21, hn, if_pos h, if_pos h]
    · rw [if_neg h] at p1
      obtain ⟨t2, s2, p2, b21, r2, f2⟩ := cs440_spec hK t1 p1 (if lay = 0 then 58 else 43)
        (by split_ifs <;> omega) (by split_ifs <;> omega) (by rw [r1.get (by decide), h26])
      refine ⟨1, t2, s2, le_refl _, p2, ?_, r2, f2⟩
      rw [b21, hn, if_neg h, if_neg h]
  obtain ⟨t3, s3, p3, c20, r3, f3⟩ := cs441_spec hK t2 p2
  have r3' : RegsExcept t t3 [.x20, .x21] := ((r1.trans r2).trans r3).mono (by decide)
  have f3' : Frame t t3 (fun _ => False) := ((f1.trans f2).trans f3).mono (by simp)
  have hI : DigInv b t v n n4 0 t3 := by
    refine ⟨p3, by omega, c20, by rw [r3.get (by decide), b21], by rw [r3'.get (by decide), h27],
      by rw [r3'.get (by decide), h6, ext_lo_ofNat v n4], by rw [r3'.get (by decide), h7, ext_hi_ofNat v n4],
      fun j hj => absurd hj (by omega), r3'.mono (by decide), f3'.mono (by simp)⟩
  obtain ⟨k4, t4, s4, k4le, hI4⟩ := dig_loop hK (n := n) (by omega) (by omega) n 0 t3 (by omega) hI
  obtain ⟨t5, s5, p5, r5, f5⟩ := cs442_spec hK t4 hI4.pc n n (by omega) (by omega) hI4.x20 hI4.x21
  rw [if_pos (le_refl _)] at p5
  obtain ⟨t6, s6, p6, r6, f6⟩ := cs461_spec hK t5 p5 lay hl
    (by rw [r5.get (by decide), hI4.regs.get (by decide), h8])
  have hx1 : ∀ u, RegsExcept t u tailRegs → u.getReg .x1 = pcOf ret := fun u hu => by
    rw [hu.get (by decide), h1]
  have r6' : RegsExcept t t6 tailRegs := ((hI4.regs.trans r5).trans r6).mono (by decide)
  have f6' : Frame t t6 DigW := ((hI4.frame.trans f5).trans f6).mono (by intro A _ h; simp only [or_false] at h; exact h)
  by_cases hl0 : lay = 0
  · rw [if_pos hl0] at p6
    have hnn : n = 58 := by rw [hn, if_pos hl0]
    obtain ⟨t7, s7, p7, r7, f7⟩ := cs467_spec hK t6 p6 ret (hx1 t6 r6')
    refine ⟨2 + k2 + 1 + k4 + 1 + 1 + 1, t7, (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7,
      by rw [if_pos hl0]; omega, p7, ?_, fun h => absurd hl0 h, (r6'.trans r7).mono (by decide),
      (f6'.trans f7).mono (by intro A _ h; simp only [or_false] at h; exact h)⟩
    intro j hj
    rw [Frame.getByte f7 (by simp only [DIGITS]; omega) (by simp), Frame.getByte f6 (by simp only [DIGITS]; omega) (by simp),
      Frame.getByte f5 (by simp only [DIGITS]; omega) (by simp)]
    exact hI4.digs j hj
  · rw [if_neg hl0] at p6
    have hnn : n = 42 := by rw [hn, if_neg hl0]
    obtain ⟨t7, s7, p7, a28, a29, r7, f7⟩ := cs462_spec hK t6 p6 T S n (hST hl0) hT
      (by rw [r6'.get (by decide), h17]) (by rw [r6'.get (by decide), h25])
      (by rw [r6.get (by decide), r5.get (by decide), hI4.x21])
    have s8 := cs466_spec hK t7 p7 (DIGITS + n) (by simp only [DIGITS]; omega) a29
    set t8 := (t7.setByte (BitVec.ofNat 64 (DIGITS + n)) ((t7.getReg .x28).truncate 8)).setPC (pcOf (b + 467))
    obtain ⟨t9, s9, p9, r9, f9⟩ := cs467_spec hK t8 rfl ret
      (by simp only [t8, getReg_setPC', getReg_setByte]; rw [r7.get (by decide)]; exact hx1 t6 r6')
    have f8 : Frame t7 t8 DigW := by
      intro A hA hn'
      simp only [t8, getMem_setPC']
      rw [getMem_setByte _ _ _ (by simp only [DIGITS]; omega) hA _ (by simp only [DigW, DIGITS] at hn' ⊢; omega)]
    refine ⟨2 + k2 + 1 + k4 + 1 + 1 + 4 + 1 + 1, t9,
      (((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9,
      by rw [if_neg hl0]; omega, p9, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [Frame.getByte f9 (by simp only [DIGITS]; omega) (by simp)]
      simp only [t8, getByte_setPC]
      rw [getByte_setByte _ _ _ (by simp only [DIGITS]; omega) (by simp only [DIGITS]; omega),
        if_neg (by rw [hn, if_neg hl0] at *; omega),
        Frame.getByte f7 (by simp only [DIGITS]; omega) (by simp), Frame.getByte f6 (by simp only [DIGITS]; omega) (by simp),
        Frame.getByte f5 (by simp only [DIGITS]; omega) (by simp)]
      exact hI4.digs j (by rw [hn, if_neg hl0] at *; omega)
    · intro _
      rw [Frame.getByte f9 (by simp only [DIGITS]; omega) (by simp)]
      simp only [t8, getByte_setPC]
      rw [getByte_setByte _ _ _ (by simp only [DIGITS]; omega) (by simp only [DIGITS]; omega),
        if_pos (by rw [hn, if_neg hl0]), a28, ofNat_truncate8]
    · have r8 : RegsExcept t7 t8 [] := fun r _ => by simp [t8]
      exact (((r6'.trans r7).trans r8).trans r9).mono (by decide)
    · exact (((f6'.trans f7).trans f8).trans f9).mono
        (by intro A _ h; tauto)

end loop

end SigGolfCandidate.T3M.Search
