import SigGolfCandidate.T3M.Search.CsBlocks
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Search.Params
import SigGolfCandidate.T3M.Search.TopCheck
import SigGolfCandidate.T3M.Search.TopUnpack

section

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
set_option linter.unusedSimpArgs false
def digW (n4 j : Nat) : Nat := if j < n4 then 2 else 3
def digOff (n4 j : Nat) : Nat := if j ≤ n4 then 2 * j else 2 * n4 + 3 * (j - n4)
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
def DigW (A : Nat) : Prop := DIGITS ≤ A ∧ A < DIGITS + 64
abbrev tailRegs : List Reg := [.x6, .x7, .x20, .x21, .x28, .x29, .x30]
section loop
variable {image : Image} {b : Nat}
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
theorem dig_body (hK : KernAt image b) {s0 : MachineState} {v : Digest} {n n4 i : Nat} (hn : n ≤ 58)
    (hin : i < n) {t : MachineState} (hI : DigInv b s0 v n n4 i t) (hn4 : n4 < 2 ^ 63) :
    ∃ k u, Steps image t k k u ∧ k ≤ 19 ∧ DigInv b s0 v n n4 (i + 1) u := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs442_spec hK t hI.pc i n (by omega) (by omega) hI.x20 hI.x21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, h28, h29, r2, f2⟩ := cs443_spec hK t1 p1 i n4 (by omega) hn4
    (by rw [r1.get (by decide), hI.x20]) (by rw [r1.get (by decide), hI.x27])
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
end

section






namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)
set_option linter.unusedSimpArgs false
theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    T3.pad64 (T3.encodingInput lay tree leaf msg c) =
      T3.encodingInput lay tree leaf msg c ++ List.replicate 28 0 := by
  unfold T3.pad64
  simp only [T3.encodingInput, List.length_append, SphincsSecurity.bytesLE_length]
theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.encodingInput lay tree leaf msg c)) =
      [msg.extractLsb' 0 64, msg.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 4 lay.val tree 0),
        BitVec.ofNat 64 (hdr1 tree leaf), BitVec.ofNat 64 c.toNat, 0, 0, 0] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : SphincsSecurity.bytesLE 16 msg ++ SphincsSecurity.bytesLE 16 (T3.header 4 lay.val tree 0 leaf) ++
      SphincsSecurity.bytesLE 4 c ++ List.replicate 28 0 =
      SphincsSecurity.bytesLE 16 msg ++ SphincsSecurity.bytesLE 16 (T3.header 4 lay.val tree 0 leaf) ++
        ((SphincsSecurity.bytesLE 4 c ++ List.replicate 4 0) ++ List.replicate 24 0) := by
    simp only [List.append_assoc]
    rfl
  have hc : T3.readLE (SphincsSecurity.bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [e, wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_append8 _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length, List.length_replicate]),
    hc, show (24 : Nat) = 8 * 3 by rfl, wordsOf_replicate_zero]
  rfl
theorem encodingInput_length (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (T3.pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
  rw [pad64_encodingInput]
  simp only [T3.encodingInput, List.length_append, SphincsSecurity.bytesLE_length, List.length_replicate]
theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl := encodingInput_length lay tree leaf msg c
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]
theorem TBSim.shortHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : Digest
  ret : Nat
def csT (lay : Layer) : Nat := if lay = 0 then 201 else 158
def csOk (lay : Layer) : Nat := if lay = 0 then 1308 else 967
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ DigW A
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target A.lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  m0 : s.getMem (BitVec.ofNat 64 ENC) = A.msg.extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = A.msg.extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  z48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = 0
  z56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = 0
  table : TableOK s
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 113)
  hi : i ≤ 2 ^ 22
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, T3.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target A.lay
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW
theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr
section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat) → MachineState → Prop}
    (hK : KernAt image b) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < 2 ^ 22)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')
theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl
theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide
theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 438)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (S : Nat) (ds : List Nat) (hdec : T3.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target A.lay - S]) (hS : S ≤ T3.target A.lay)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) :
    TBSim image sk u 810 (pure (some (BitVec.ofNat 32 i, ds))) (CsPost image b A s0) := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u hpc v A.lay.val
    (T3.target A.lay) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu.reg (by decide), hpre.x1]) (by rw [hu.reg (by decide), hpre.x8])
    (by rw [hu.reg (by decide), hpre.x17]) h25
    (by rw [hu.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) h6 h7
  rw [if_neg hl0] at kle tdig
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine (TBSim.steps st (TBSim.pure ?_)).mono kle (fun _ _ h => h)
  refine ⟨tpc, by rw [hc]; exact hi, by rw [hc, tr.get (by decide), hu.x19], ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, tf.get (by simp only [ENC]; omega) (by simp only [DigW, DIGITS, ENC]; omega), hu.c32]
  · rw [hds, chainCount_eq, if_neg hlz]
    simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq, if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length]; exact hj), lowDigits_eq, getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]), lowDigits_length]
      simpa using tchk hl0
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, BitVec.toNat_ofNat]
    have := target_lt A.lay
    omega
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)
theorem cs_top_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 362))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hvalid : T3.topRanksValid v = true) (hdec : T3.decode A.lay v = some (topDigits v))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 126#64) :
    TBSim image sk u 302 (pure (some (BitVec.ofNat 32 i, topDigits v))) (CsPost image b A s0) := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hv hvalid (hu.table hpre.table) hpc h6 h7 h30
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.steps st (TBSim.pure ?_)
  refine ⟨?_, by rw [hc]; exact hi, ?_, ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tpc, hu.reg (by decide), hpre.x1, pcOf_and_not1]
  · rw [hc, tr.get (by decide), hu.x19]
  · rw [hc, tf.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega), hu.c32]
  · rw [hlz, topDigits_length]; rfl
  · intro j hj
    rw [hlz] at hj
    change j < 54 at hj
    rw [tdig j hj]
    simp only [topDigits, getD_map_range hj]
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, hlz]; decide
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < 2 ^ 22) :
    ∃ t2, Steps image t 10 10 t2 ∧ t2.pc = pcOf (b + 123) ∧ fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (T3.encodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 CsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ A, A < 2 ^ 64 → ¬ CsW A → t2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  refine ⟨t2, s1.trans s2, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, wordsOf_encodingInput, hc]
  have nw : ∀ A, A = ENC ∨ A = ENC + 8 ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 → ¬ CsW A := by
    intro A hA; simp only [CsW, DigW, ENC, EOUT, DIGITS] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.z48, hpre.z56]
theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    ∀ F i t, i + F = 2 ^ 22 → CsInv b A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (T3.counterSearch A.lay A.tree A.leaf A.msg i F)
        (CsPost image b A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]; rfl
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, hf⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := CsPost image b A s0) (a := none) ⟨p2, h5, h10, hf⟩)
    exact this.mono (by unfold csOk; split_ifs <;> omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 22 := by omega
    obtain ⟨t2, s2, p2, hf, h5, hv, hq, h12, hT⟩ := cs_answer hK hpre hI hi
    have prog : T3.counterSearch A.lay A.tree A.leaf A.msg i (F + 1) =
        (T3.shortHash (T3.encodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match T3.decode A.lay answer with
          | none => T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F
          | some digits => pure (some (BitVec.ofNat 32 i, digits))) := rfl
    have ih' : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t (F * csT A.lay + csOk A.lay)
        (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) (CsPost image b A s0) :=
      fun t ht => ih (i + 1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.shortHash_bind hf h5 hv hq
      (W := F * csT A.lay + csOk A.lay + (csT A.lay - 18)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_encodingInput, Nat.succ_mul]; unfold csT; split_ifs <;> omega
    set v := a.extractLsb' 0 128 with hvdef
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc = pcOf (b + 124) := by rw [pc_writeHash, p2, pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    obtain ⟨t4, s4, p4, h6, h7, h25, r4, f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide), hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    by_cases hlz : A.lay = 0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hdec := decode_top_lookup v
      rw [← hlz] at hdec
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs263_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 125
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', h30', r6, f6⟩ := topCheck_spec hK t5 v hr p5
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7])
          (by rw [hT5.reg (by decide), hpre.x17, hlz]; rfl) (hT5.table hpre.table).sum
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : topLookupSum v = 126
        · rw [if_pos hs] at p6
          have hd' : T3.decode A.lay v = some (topDigits v) := by rw [hdec, if_pos ⟨hr, hs⟩]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_top_success hK hpre hT6 p6 hi hlz v hr
            ((topLookupSum_eq_iff v).mp hs).1 hd'
            (by rw [r6.get (by decide), r5.get (by decide), h6])
            (by rw [r6.get (by decide), r5.get (by decide), h7]) h30' (by simpa only [hs] using h25'))).mono ?_ (fun _ _ h => h)
          unfold csT csOk; rw [if_pos hlz, if_pos hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_pos hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd']
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_pos hlz]; omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      have hdec := decode_low A.lay hlz v
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs130_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 126
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', r6, f6⟩ := cs132_spec hK t5 p5 v (T3.target A.lay) (target_lt _)
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7]) (by rw [r5.get (by decide), h25])
          (by rw [hT5.reg (by decide), hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum ≤ T3.target A.lay ∧ T3.target A.lay - (lowDigits v).sum < 8
        · rw [if_pos hs] at p6
          obtain ⟨t7, s7, p7, r7, f7⟩ := cs262_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : T3.decode A.lay v = some (lowDigits v ++ [T3.target A.lay - (lowDigits v).sum]) := by
            rw [hdec, if_pos ⟨hr, hs⟩]
          rw [hd']
          refine (TBSim.steps (((s4.trans s5).trans s6).trans s7) (cs_success hK hpre hT7 p7 hi hlz v _ _ hd' rfl hs.1
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
            (by rw [r7.get (by decide), h25']))).mono ?_ (fun _ _ h => h)
          unfold csT csOk; rw [if_neg hlz, if_neg hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_neg hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd']
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_neg hlz]; omega
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    TBSim image sk s0 (10 + 2 ^ 22 * csT A.lay + csOk A.lay)
      (T3.counterSearch A.lay A.tree A.leaf A.msg 0 T3.counterLimit) (CsPost image b A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay.val A.tree A.leaf A.lay.isLt
    hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  have hI : CsInv b A s0 0 t := by
    refine ⟨pt, by norm_num, h19, h16, h24, ?_, rt.mono (by decide), ft.mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), hx32]⟩
  have := TBSim.steps st (cs_loop (sk := sk) hK hpre (2 ^ 22) 0 t (by norm_num) hI)
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)
end trial
structure FailedAt (b : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 2)
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure CsPreS (b : Nat) (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat) :
    Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  msg : DigAt s ENC msg
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  z48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = 0
  z56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = 0
  table : TableOK s
def CsPostS (b : Nat) (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay
def csCostS (lay : Layer) : Nat := T3.counterLimit * (if lay = 0 then 205 else 160) + 2000
theorem CsPreS.toCsPre {b : Nat} {s : MachineState} {lay : Layer} {tree leaf : Nat} {msg : Digest} {ret : Nat}
    (h : CsPreS b s lay tree leaf msg ret) : CsPre b ⟨lay, tree, leaf, msg, ret⟩ s :=
  ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.msg.1, h.msg.2,
    ⟨_, h.c32, (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm⟩, h.z40, h.z48, h.z56, h.table⟩
theorem counterSearch_spec {image : Image} {b : Nat} {sk : BitVec 256} (hK : KernAt image b)
    (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat)
    (h : CsPreS b s lay tree leaf msg ret) :
    TBSim image sk s (csCostS lay) (T3.counterSearch lay tree leaf msg 0 T3.counterLimit) (CsPostS b s lay ret) := by
  refine (counterSearch_tbsim (sk := sk) hK h.toCsPre).mono ?_ (fun r t ht => ?_)
  · show 10 + 2 ^ 22 * csT lay + csOk lay ≤ 2 ^ 22 * (if lay = 0 then 205 else 160) + 2000
    unfold csT csOk
    split_ifs <;> omega
  · rcases r with _ | ⟨c, ds⟩
    · exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
    · obtain ⟨tpc, hc, _, h32, hdec, _, hdig, hr, hf, h25⟩ := ht
      refine ⟨tpc, ?_, hdec, hdig, ?_, hr, hf, h25⟩
      · rw [hr.get (by decide), h.x5]
      · rw [h32, BitVec.toNat_ofNat]
        omega
end SigGolfCandidate.T3M.Search
end
