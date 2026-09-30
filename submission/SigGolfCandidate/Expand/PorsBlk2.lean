import SigGolfCandidate.Expand.PorsSeg

/-!
# `expand`, phase 2: the other PORS blocks

`pors_init` (495 .. 528), `pr_leaf` (529 .. 549), `pr_segend` and the merge (595 .. 619),
`pr_leafend` / `pr_next` and the final checks (620 .. 638), `pors_ok` (639 .. 672).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

theorem ofNat_ult_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

/-! ## `pr_segend` and the merge -/

/-- 595 .. 601: `s1 += 16 a + 8`, `s4 += a`, test the merge bit. -/
theorem blk595_run (t : MachineState) (hpc : t.pc = pcOf 595) (b ptr folds : Nat) (hb : b < 256)
    (hptr : ptr < 2 ^ 32) (hf : folds < 2 ^ 32)
    (h6 : t.getReg .x6 = BitVec.ofNat 64 b) (h7 : t.getReg .x7 = BitVec.ofNat 64 (b % 16))
    (h9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr)) (h20 : t.getReg .x20 = BitVec.ofNat 64 folds) :
    ∃ t', Steps eimg t 7 7 t' ∧ t'.pc = (if b / 16 % 2 = 1 then pcOf 602 else pcOf 620) ∧
      t'.getReg .x9 = BitVec.ofNat 64 (0x800 + (ptr + 8 + 16 * (b % 16))) ∧
      t'.getReg .x20 = BitVec.ofNat 64 (folds + b % 16) ∧
      RegsEq t t' [.x9, .x13, .x20] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk595 Expand.codeAt_595 t hpc (by simp only [Expand.blk595.res, rv_simp]),
    ?_, ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk595.res, rv_simp, h6]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_ushiftRight _ _ (by omega),
      ofNat_and_ofNat _ _ (by omega) (by norm_num), and_one, ofNat_beq_zero _ (by omega)]
    by_cases h : b / 16 % 2 = 1
    · rw [if_neg (by simp; omega), if_pos h]
    · rw [if_pos (by simp; omega), if_neg h]
  · simp only [Expand.blk595.res, rv_simp, h7, h9]
    bvsimp []
    exact ofNat_congr (by omega)
  · simp only [Expand.blk595.res, rv_simp, h7, h20, ofNat_add_ofNat]

/-- 602: an empty stack (`s5 = STK`) cannot merge. -/
theorem blk602_run (t : MachineState) (hpc : t.pc = pcOf 602) (k : Nat) (hk : k ≤ 15)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * k)) (h22 : t.getReg .x22 = BitVec.ofNat 64 0x30540) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = (if k = 0 then pcOf 284 else pcOf 603) ∧
      RegsEq t t' [] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk602 Expand.codeAt_602 t hpc (by simp only [Expand.blk602.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk602.res, rv_simp, h21, h22, ofNat_beq_ofNat]
  by_cases h : k = 0
  · rw [if_pos (by simp; omega), if_pos h]
  · rw [if_neg (by simp; omega), if_neg h]

/-- 603 .. 605: pop (`s5 -= 32`), the popped heap index against `E`. -/
theorem blk603_run (t : MachineState) (hpc : t.pc = pcOf 603) (k E Q : Nat) (hk : k < 15) (hE : E < 2 ^ 15)
    (hQ : Q < 2 ^ 15)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * (k + 1))) (h19 : t.getReg .x19 = BitVec.ofNat 64 E)
    (hm : t.getMem (BitVec.ofNat 64 (0x30540 + 32 * k + 16)) = BitVec.ofNat 64 Q) :
    ∃ t', Steps eimg t 3 3 t' ∧ t'.pc = (if Q ≠ E then pcOf 284 else pcOf 606) ∧
      t'.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * k) ∧
      RegsEq t t' [.x13, .x21] ∧ ∀ x, t'.getMem x = t.getMem x := by
  have ha : t.getReg .x21 + 18446744073709551600#64 = BitVec.ofNat 64 (0x30540 + 32 * k + 16) := by
    rw [h21, show (18446744073709551600#64 : Word) = BitVec.ofNat 64 18446744073709551600 from rfl,
      ofNat_add_ofNat]
    exact ofNat_eq_iff _ _ |>.mpr (by omega)
  refine ⟨_, symRun_sound Expand.blk603 Expand.codeAt_603 t hpc (by
      simp only [Expand.blk603.res, rv_simp, ha, accessValid_ofNat]; omega),
    ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk603.res, rv_simp, ha, hm, h19, ofNat_bne_ofNat]
    by_cases h : Q ≠ E
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · simp only [Expand.blk603.res, rv_simp, h21]
    bvsimp []
    exact ofNat_congr (by omega)

/-- 606 .. 619: `E >>= 1`; `PB` = (word 1 = `E`, popped node, current node); `s8 = 1`; `j pr_seg`. -/
theorem blk606_run (idx : Nat) (t : MachineState) (hpc : t.pc = pcOf 606) (k E : Nat) (hk : k < 15)
    (hE : E < 2 ^ 15) (h19 : t.getReg .x19 = BitVec.ofNat 64 E)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * k))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) (h26 : t.getReg .x26 = BitVec.ofNat 64 (idx % 2 ^ 32)) :
    ∃ t', Steps eimg t 14 14 t' ∧ t'.pc = pcOf 550 ∧ t'.getReg .x19 = BitVec.ofNat 64 (E / 2) ∧
      t'.getReg .x24 = BitVec.ofNat 64 1 ∧
      t'.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (E / 2)) ∧
      t'.readWords (BitVec.ofNat 64 0x30060) 2 = t.readWords (BitVec.ofNat 64 (0x30540 + 32 * k)) 2 ∧
      t'.readWords (BitVec.ofNat 64 0x30070) 2 = t.readWords (BitVec.ofNat 64 0x30080) 2 ∧
      RegsEq t t' [.x13, .x14, .x15, .x16, .x17, .x19, .x24] ∧
      Frame t t' (fun x => x = 0x30048 ∨ (0x30060 ≤ x ∧ x < 0x30080)) := by
  refine ⟨_, symRun_sound Expand.blk606 Expand.codeAt_606 t hpc (by pobl [Expand.blk606.res, h21, h25]),
    by simp only [Expand.blk606.res, rv_simp], ?_, by simp only [Expand.blk606.res, rv_simp], ?_, ?_, ?_,
    by pregs, ?_⟩
  · simp only [Expand.blk606.res, rv_simp, h19]
    rw [show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_ushiftRight _ _ (by omega), pow_one]
  · pnum [Expand.blk606.res, h19, h25, h26]
    bvsimp []
    exact ofNat_congr (by omega)
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    pnum [Expand.blk606.res, h21, h25]
    try simp (disch := bvomega) only [if_neg]
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    pnum [Expand.blk606.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk606.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-! ## `pr_leafend`, `pr_next`, the final checks -/

/-- 620 .. 621: the last leaf is not pushed. -/
theorem blk620_run (t : MachineState) (hpc : t.pc = pcOf 620) (s : Nat) (hs : s < 15)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 s) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if s = 14 then pcOf 629 else pcOf 622) ∧
      RegsEq t t' [.x17] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk620 Expand.codeAt_620 t hpc (by simp only [Expand.blk620.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk620.res, rv_simp, h8, show (14#64 : Word) = BitVec.ofNat 64 14 from rfl, ofNat_beq_ofNat]
  by_cases h : s = 14
  · rw [if_pos (by simp; omega), if_pos h]
  · rw [if_neg (by simp; omega), if_neg h]

/-- 622 .. 628: push `(OUT, E xor 1)` at `s5`, `s5 += 32`. -/
theorem blk622_run (t : MachineState) (hpc : t.pc = pcOf 622) (k E : Nat) (hk : k < 15) (hE : E < 2 ^ 15)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 E) (h21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * k))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 7 7 t' ∧ t'.pc = pcOf 629 ∧
      t'.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * (k + 1)) ∧
      t'.readWords (BitVec.ofNat 64 (0x30540 + 32 * k)) 2 = t.readWords (BitVec.ofNat 64 0x30080) 2 ∧
      t'.getMem (BitVec.ofNat 64 (0x30540 + 32 * k + 16)) = BitVec.ofNat 64 (E ^^^ 1) ∧
      RegsEq t t' [.x13, .x14, .x15, .x21] ∧
      Frame t t' (fun x => 0x30540 + 32 * k ≤ x ∧ x < 0x30540 + 32 * k + 24) := by
  refine ⟨_, symRun_sound Expand.blk622 Expand.codeAt_622 t hpc (by pobl [Expand.blk622.res, h21, h25]),
    by simp only [Expand.blk622.res, rv_simp], ?_, ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk622.res, rv_simp, h21]; bvsimp []; exact ofNat_congr (by omega)
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    pnum [Expand.blk622.res, h21, h25]
    try simp (disch := bvomega) only [if_neg, if_pos]
  · pnum [Expand.blk622.res, h21, h25, h19]
    try simp (disch := bvomega) only [if_neg, if_pos]
    rw [ofNat_xor_ofNat _ _ (by omega) (by norm_num)]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk622.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h21, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 629 .. 632: `prev = x`, next leaf. -/
theorem blk629_run (t : MachineState) (hpc : t.pc = pcOf 629) (s x : Nat) (hs : s < 15)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 s) (h23 : t.getReg .x23 = BitVec.ofNat 64 x) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = (if s + 1 = 15 then pcOf 633 else pcOf 529) ∧
      t'.getReg .x8 = BitVec.ofNat 64 (s + 1) ∧ t'.getReg .x18 = BitVec.ofNat 64 x ∧
      RegsEq t t' [.x8, .x17, .x18] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk629 Expand.codeAt_629 t hpc (by simp only [Expand.blk629.res, rv_simp]),
    ?_, ?_, by simp only [Expand.blk629.res, rv_simp, h23], by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk629.res, rv_simp, h8, ofNat_add_ofNat, show (15#64 : Word) = BitVec.ofNat 64 15 from rfl,
      ofNat_bne_ofNat]
    by_cases h : s + 1 = 15
    · rw [if_neg (by simp; omega), if_pos h]
    · rw [if_pos (by simp; omega), if_neg h]
  · simp only [Expand.blk629.res, rv_simp, h8, ofNat_add_ofNat]

/-- 633 .. 634: reject more than 118 folds. -/
theorem blk633_run (t : MachineState) (hpc : t.pc = pcOf 633) (f : Nat) (hf : f < 2 ^ 32)
    (h20 : t.getReg .x20 = BitVec.ofNat 64 f) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if 118 < f then pcOf 284 else pcOf 635) ∧
      RegsEq t t' [.x17] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk633 Expand.codeAt_633 t hpc (by simp only [Expand.blk633.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk633.res, rv_simp, h20, show (118#64 : Word) = BitVec.ofNat 64 118 from rfl]
  rw [ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
  by_cases h : 118 < f
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

/-- 635 .. 636: reject `E ≠ 1`. -/
theorem blk635_run (t : MachineState) (hpc : t.pc = pcOf 635) (E : Nat) (hE : E < 2 ^ 15)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 E) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if E ≠ 1 then pcOf 284 else pcOf 637) ∧
      RegsEq t t' [.x17] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk635 Expand.codeAt_635 t hpc (by simp only [Expand.blk635.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk635.res, rv_simp, h19, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_bne_ofNat]
  by_cases h : E ≠ 1
  · rw [if_pos (by simp; omega), if_pos h]
  · rw [if_neg (by simp; omega), if_neg h]

/-- 637: reject a non-empty stack. -/
theorem blk637_run (t : MachineState) (hpc : t.pc = pcOf 637) (k : Nat) (hk : k ≤ 15)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (0x30540 + 32 * k)) (h22 : t.getReg .x22 = BitVec.ofNat 64 0x30540) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = (if k ≠ 0 then pcOf 284 else pcOf 638) ∧
      RegsEq t t' [] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk637 Expand.codeAt_637 t hpc (by simp only [Expand.blk637.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk637.res, rv_simp, h21, h22, ofNat_bne_ofNat]
  by_cases h : k ≠ 0
  · rw [if_pos (by simp; omega), if_pos h]
  · rw [if_neg (by simp; omega), if_neg h]

/-- 638: `j pors_ok`. -/
theorem blk638_run (t : MachineState) (hpc : t.pc = pcOf 638) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = pcOf 639 ∧ RegsEq t t' [] ∧ ∀ y, t'.getMem y = t.getMem y :=
  ⟨_, symRun_sound Expand.blk638 Expand.codeAt_638 t hpc (by simp only [Expand.blk638.res, rv_simp]),
    by simp only [Expand.blk638.res, rv_simp], by pregs, getMem_nil rfl t⟩

/-! ## `pr_leaf` -/

/-- 529 .. 532: `x = KEYS[s] >> 8`; the first leaf skips the order test. -/
theorem blk529_run (t : MachineState) (hpc : t.pc = pcOf 529) (s : Nat) (hs : s < 15) (Ks : Nat) (hK : Ks < 2 ^ 22)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 s) (hk : t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * s)) = BitVec.ofNat 64 Ks) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = (if s = 0 then pcOf 534 else pcOf 533) ∧
      t'.getReg .x23 = BitVec.ofNat 64 (Ks / 256) ∧ RegsEq t t' [.x13, .x23] ∧ ∀ y, t'.getMem y = t.getMem y := by
  have ha : t.getReg .x8 <<< ((3#64 : Word).toNat % 64) + 1760#64 = BitVec.ofNat 64 (0x6E0 + 8 * s) := by
    rw [h8, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shiftLeft,
      show (1760#64 : Word) = BitVec.ofNat 64 1760 from rfl, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  refine ⟨_, symRun_sound Expand.blk529 Expand.codeAt_529 t hpc (by
      simp only [Expand.blk529.res, rv_simp, ha, accessValid_ofNat]; omega),
    ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk529.res, rv_simp, h8, ofNat_beq_zero s (by omega)]
    by_cases h : s = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk529.res, rv_simp, ha, hk, show (8#64 : Word).toNat % 64 = 8 from rfl]
    rw [ofNat_ushiftRight _ _ (by omega)]; rfl

/-- 533: reject `prev ≥ x`. -/
theorem blk533_run (t : MachineState) (hpc : t.pc = pcOf 533) (p x : Nat) (hp : p < 2 ^ 64) (hx : x < 2 ^ 64)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 p) (h23 : t.getReg .x23 = BitVec.ofNat 64 x) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = (if ¬ p < x then pcOf 284 else pcOf 534) ∧
      RegsEq t t' [] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk533 Expand.codeAt_533 t hpc (by simp only [Expand.blk533.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk533.res, rv_simp, h18, h23, ofNat_ult_ofNat p x hp hx]
  by_cases h : p < x
  · rw [if_neg (by simpa using h), if_neg (by simpa using h)]
  · rw [if_pos (by simpa using h), if_pos h]

/-- 534 .. 535: only the last leaf has the range test. -/
theorem blk534_run (t : MachineState) (hpc : t.pc = pcOf 534) (s : Nat) (hs : s < 15)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 s) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if s = 14 then pcOf 536 else pcOf 538) ∧
      RegsEq t t' [.x17] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk534 Expand.codeAt_534 t hpc (by simp only [Expand.blk534.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk534.res, rv_simp, h8, show (14#64 : Word) = BitVec.ofNat 64 14 from rfl, ofNat_bne_ofNat]
  by_cases h : s = 14
  · rw [if_neg (by simp; omega), if_pos h]
  · rw [if_pos (by simp; omega), if_neg h]

/-- 536 .. 537: reject `x ≥ 2^14` (the last leaf). -/
theorem blk536_run (t : MachineState) (hpc : t.pc = pcOf 536) (x : Nat) (hx : x < 2 ^ 64)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 x) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if ¬ x < porsT then pcOf 284 else pcOf 538) ∧
      RegsEq t t' [.x13] ∧ ∀ y, t'.getMem y = t.getMem y := by
  refine ⟨_, symRun_sound Expand.blk536 Expand.codeAt_536 t hpc (by simp only [Expand.blk536.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk536.res, rv_simp, h23, show (16384#64 : Word) = BitVec.ofNat 64 16384 from rfl,
    ofNat_ult_ofNat x 16384 hx (by norm_num)]
  unfold porsT porsH
  by_cases h : x < 16384
  · rw [if_neg (by simpa using h), if_neg (by simpa using h)]
  · rw [if_pos (by simpa using h), if_pos (by simpa using h)]

/-- 538 .. 549: `E = x | 2^14`; `LB` word 1 = leaf `x`; the secret `s` into `LB`; `s8 = 0`. -/
theorem blk538_run (w : List Byte) (idx : Nat) (t : MachineState) (hpc : t.pc = pcOf 538) (s x : Nat)
    (hs : s < 15) (hx : x < 2 ^ 14) (hw : WitMem w t)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 s) (h23 : t.getReg .x23 = BitVec.ofNat 64 x)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) (h26 : t.getReg .x26 = BitVec.ofNat 64 (idx % 2 ^ 32))
    (h27 : t.getReg .x27 = BitVec.ofNat 64 0x800) :
    ∃ t', Steps eimg t 12 12 t' ∧ t'.pc = pcOf 550 ∧ t'.getReg .x19 = BitVec.ofNat 64 (porsT ||| x) ∧
      t'.getReg .x24 = BitVec.ofNat 64 0 ∧
      t'.getMem (BitVec.ofNat 64 0x30008) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * x) ∧
      t'.readWords (BitVec.ofNat 64 0x30020) 2 = wordsOf (wbytes w (32 + 16 * s) 16) ∧
      RegsEq t t' [.x13, .x14, .x15, .x19, .x24] ∧
      Frame t t' (fun y => y = 0x30008 ∨ y = 0x30020 ∨ y = 0x30028) := by
  have ha : t.getReg .x8 <<< ((4#64 : Word).toNat % 64) + t.getReg .x27 = BitVec.ofNat 64 (0x800 + 16 * s) := by
    rw [h8, h27, show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shiftLeft, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  have m0 := hw.get (32 + 16 * s) (by omega) (by omega)
  have m8 := hw.get (32 + 16 * s + 8) (by omega) (by omega)
  refine ⟨_, symRun_sound Expand.blk538 Expand.codeAt_538 t hpc (by pobl [Expand.blk538.res, h8, h27, h25, ofNat_shiftLeft]),
    by simp only [Expand.blk538.res, rv_simp], ?_, by simp only [Expand.blk538.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk538.res, rv_simp, h23]
    rw [show (16384#64 : Word) = BitVec.ofNat 64 16384 from rfl, ofNat_or_ofNat _ _ (by omega) (by norm_num)]
    unfold porsT porsH; rw [Nat.or_comm]; rfl
  · pnum [Expand.blk538.res, h23, h25, h26]
    rw [show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  · rw [readWords_ofNat_two, wordsOf_wbytes16]
    pnum [Expand.blk538.res, h25, ha]
    rw [show 0x800 + 16 * s + 32 = 0x800 + (32 + 16 * s) by ring, m0,
      show 0x800 + 16 * s + 40 = 0x800 + (32 + 16 * s + 8) by ring, m8]
  · apply frame_toState; intro y hy hW
    simp only [Expand.blk538.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

end SigGolfCandidate.ExP
