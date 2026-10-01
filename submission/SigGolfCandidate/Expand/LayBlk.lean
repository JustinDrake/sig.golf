import SigGolfCandidate.Expand.P2Base

/-!
# `expand`, phase 2: the blocks of the layer tail (instructions 382 .. 477)

Scratch `X = 0x30000`: the chain block `CB = X + 320` (value-last format, the value at
`CB + 48`), the node block `NB = X + 448`, the node `NO = X + 512`, the leaf block `LF = X + 576`
(tweak, zero word, the 42 chain ends at `LF + 32`), the counters `CT = X + 1920`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- 382 .. 385 (`enc_ok`): the counter into `CT + 8 lay`; layer 0 goes to `halt_ok`. -/
theorem blk382_run (t : MachineState) (hpc : t.pc = pcOf 382) (lay c : Nat) (hl : lay < 5) (hc : c < 2 ^ 22)
    (h6 : t.getReg .x6 = BitVec.ofNat 64 c) (h8 : t.getReg .x8 = BitVec.ofNat 64 lay)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = (if lay = 0 then pcOf 478 else pcOf 386) ∧
      t'.getMem (BitVec.ofNat 64 (0x30780 + 8 * lay)) = BitVec.ofNat 64 c ∧
      RegsEq t t' [.x14] ∧ Frame t t' (fun a => a = 0x30780 + 8 * lay) := by
  have ha : t.getReg .x8 <<< ((3#64 : Word).toNat % 64) + t.getReg .x25 + 1920#64 =
      BitVec.ofNat 64 (0x30780 + 8 * lay) := by
    rw [h8, h25, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shiftLeft, ofNat_add_ofNat,
      show (1920#64 : Word) = BitVec.ofNat 64 1920 from rfl, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  refine ⟨_, symRun_sound Expand.blk382 Expand.codeAt_382 t hpc (by pobl [Expand.blk382.res, h8, h25,
      ofNat_shiftLeft]), ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk382.res, rv_simp, h8, ofNat_beq_zero lay (by omega)]
    by_cases h : lay = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk382.res, rv_simp, ha, h6]; simp
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk382.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ha, ofNat_eq_iff]
    bvomega

theorem ofNat_mul_ofNat' (a b : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

/-- 386 .. 407: the chain base, the `LF` / `NB` / `CB` tweak words, the chain pointers (W1a: the value
slot of block `(lay, 0)`, `W + 2992 + 2688 lay`, via `li a7, 1344; mul; slli 1`: 25 cycles). -/
theorem blk386_run (t : MachineState) (hpc : t.pc = pcOf 386) (lay tau : Nat) (hl : lay < 5) (htau : tau < 2 ^ 30)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 lay) (h30 : t.getReg .x30 = BitVec.ofNat 64 tau)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 22 25 t' ∧ t'.pc = pcOf 408 ∧
      t'.getReg .x18 = BitVec.ofNat 64 0 ∧ t'.getReg .x19 = t.getReg .x1 ∧
      t'.getReg .x20 = BitVec.ofNat 64 (257 + 65536 * lay) ∧ t'.getReg .x21 = BitVec.ofNat 64 (2 ^ 40) ∧
      t'.getReg .x23 = BitVec.ofNat 64 (0x800 + (2992 + 2688 * lay)) ∧
      t'.getReg .x24 = BitVec.ofNat 64 0x30260 ∧
      t'.getMem (BitVec.ofNat 64 0x30240) = BitVec.ofNat 64 (513 + 65536 * lay) ∧
      t'.getMem (BitVec.ofNat 64 0x30248) = t.getReg .x31 ∧
      t'.getMem (BitVec.ofNat 64 0x301C0) = BitVec.ofNat 64 (769 + 65536 * lay) ∧
      t'.getMem (BitVec.ofNat 64 0x30148) = t.getReg .x31 ∧
      RegsEq t t' [.x15, .x16, .x17, .x18, .x19, .x20, .x21, .x23, .x24] ∧
      Frame t t' (fun a => a = 0x30240 ∨ a = 0x30248 ∨ a = 0x301C0 ∨ a = 0x30148) := by
  have ha5 : t.getReg .x30 >>> ((32#64 : Word).toNat % 64) <<< ((24#64 : Word).toNat % 64) +
      t.getReg .x8 <<< ((16#64 : Word).toNat % 64) = BitVec.ofNat 64 (65536 * lay) := by
    rw [h30, h8, show (32#64 : Word).toNat % 64 = 32 from rfl, show (24#64 : Word).toNat % 64 = 24 from rfl,
      show (16#64 : Word).toNat % 64 = 16 from rfl, ofNat_ushiftRight _ _ (by omega),
      Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), ofNat_shiftLeft, ofNat_shiftLeft, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  refine ⟨_, symRun_sound Expand.blk386 Expand.codeAt_386 t hpc (by pobl [Expand.blk386.res, h25]),
    by simp only [Expand.blk386.res, rv_simp], by simp only [Expand.blk386.res, rv_simp],
    by simp only [Expand.blk386.res, rv_simp], ?_, by pnum [Expand.blk386.res], ?_, by pnum [Expand.blk386.res, h25],
    ?_, ?_, ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk386.res, rv_simp, ha5, ofNat_add_ofNat]; exact ofNat_congr (by ring)
  · simp only [Expand.blk386.res, rv_simp, h8, show (1#64 : Word).toNat % 64 = 1 from rfl,
      show (1344#64 : Word) = BitVec.ofNat 64 1344 from rfl, ofNat_mul_ofNat', ofNat_shiftLeft, ofNat_add_ofNat]
    exact ofNat_congr (by ring)
  · pnum [Expand.blk386.res, h25]; simp only [ha5, ofNat_add_ofNat]; exact ofNat_congr (by ring)
  · pnum [Expand.blk386.res, h25]
  · pnum [Expand.blk386.res, h25]; simp only [ha5, ofNat_add_ofNat]; exact ofNat_congr (by ring)
  · pnum [Expand.blk386.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk386.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 408 .. 411: the digit `t3 = s3 & 7`, `s3 >>= 3`; chain 20 switches to `d1`. -/
theorem blk408_run (t : MachineState) (hpc : t.pc = pcOf 408) (i q : Nat) (hi : i < 42) (hq : q < 2 ^ 64)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 i) (h19 : t.getReg .x19 = BitVec.ofNat 64 q) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = (if i = 20 then pcOf 412 else pcOf 413) ∧
      t'.getReg .x28 = BitVec.ofNat 64 (q % 8) ∧ t'.getReg .x19 = BitVec.ofNat 64 (q / 8) ∧
      RegsEq t t' [.x14, .x19, .x28] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk408 Expand.codeAt_408 t hpc (by simp only [Expand.blk408.res, rv_simp]),
    ?_, ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk408.res, rv_simp, h18, show (20#64 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_bne_ofNat]
    by_cases h : i = 20
    · rw [if_neg (by simp; omega), if_pos h]
    · rw [if_pos (by simp; omega), if_neg h]
  · simp only [Expand.blk408.res, rv_simp, h19]
    rw [show (7#64 : Word) = BitVec.ofNat 64 7 from rfl, ofNat_and_ofNat _ _ hq (by norm_num),
      show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · simp only [Expand.blk408.res, rv_simp, h19, show (3#64 : Word).toNat % 64 = 3 from rfl]
    rw [ofNat_ushiftRight _ _ hq]; rfl

/-- 412: `s3 = d1`. -/
theorem blk412_run (t : MachineState) (hpc : t.pc = pcOf 412) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = pcOf 413 ∧ t'.getReg .x19 = t.getReg .x2 ∧
      RegsEq t t' [.x19] ∧ ∀ x, t'.getMem x = t.getMem x :=
  ⟨_, symRun_sound Expand.blk412 Expand.codeAt_412 t hpc (by simp only [Expand.blk412.res, rv_simp]),
    by simp only [Expand.blk412.res, rv_simp], by simp only [Expand.blk412.res, rv_simp], by pregs,
    getMem_nil rfl t⟩

/-- 413 .. 416: the chain value from the witness into `CB + 48`. -/
theorem blk413_run (w : List Byte) (t : MachineState) (hpc : t.pc = pcOf 413) (o : Nat) (ho : o % 8 = 0)
    (ho' : o + 16 ≤ 0x4000) (hw : WitMem w t)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 (0x800 + o)) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = pcOf 417 ∧
      t'.readWords (BitVec.ofNat 64 0x30170) 2 = wordsOf (wbytes w o 16) ∧
      RegsEq t t' [.x14, .x15] ∧ Frame t t' (fun a => a = 0x30170 ∨ a = 0x30178) := by
  have m0 := hw.get o ho (by omega)
  have m8 := hw.get (o + 8) (by omega) (by omega)
  rw [show 0x800 + (o + 8) = 0x800 + o + 8 by omega] at m8
  refine ⟨_, symRun_sound Expand.blk413 Expand.codeAt_413 t hpc (by pobl [Expand.blk413.res, h23, h25]),
    by simp only [Expand.blk413.res, rv_simp], ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two, wordsOf_wbytes16]
    pnum [Expand.blk413.res, h23, h25, m0, m8]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk413.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 417 .. 418: the chain is done at position 7. -/
theorem blk417_run (t : MachineState) (hpc : t.pc = pcOf 417) (p : Nat) (hp : p < 2 ^ 32)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 p) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = (if 7 ≤ p then pcOf 428 else pcOf 419) ∧
      RegsEq t t' [.x14] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk417 Expand.codeAt_417 t hpc (by simp only [Expand.blk417.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk417.res, rv_simp, h28, show (7#64 : Word) = BitVec.ofNat 64 7 from rfl]
  rw [ofNat_slt_ofNat _ _ (by omega) (by norm_num)]
  by_cases h : 7 ≤ p
  · rw [if_pos (by simp; omega), if_pos h]
  · rw [if_neg (by simp; omega), if_neg h]

/-- 419 .. 425: the chain tweak word 0 (position `t3`), HASH(`CB`, 64, `CB + 48`). -/
theorem blk419_run (t : MachineState) (hpc : t.pc = pcOf 419) (p base : Nat) (hp : p < 8) (hb : base < 2 ^ 48)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 p) (h20 : t.getReg .x20 = BitVec.ofNat 64 base)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 6 6 t' ∧ t'.pc = pcOf 425 ∧
      t'.getReg .x10 = BitVec.ofNat 64 0x30140 ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
      t'.getReg .x12 = BitVec.ofNat 64 0x30170 ∧
      t'.getMem (BitVec.ofNat 64 0x30140) = BitVec.ofNat 64 (base + 2 ^ 32 * p) ∧
      RegsEq t t' [.x10, .x11, .x12, .x14] ∧ Frame t t' (fun a => a = 0x30140) ∧
      t'.getReg .x14 = BitVec.ofNat 64 (base + 2 ^ 32 * p) := by
  refine ⟨_, symRun_sound Expand.blk419 Expand.codeAt_419 t hpc (by pobl [Expand.blk419.res, h25]),
    by simp only [Expand.blk419.res, rv_simp], by pnum [Expand.blk419.res, h25],
    by simp only [Expand.blk419.res, rv_simp], by pnum [Expand.blk419.res, h25], ?_, by pregs, ?_, ?_⟩
  · pnum [Expand.blk419.res, h25, h28, h20, show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft]
    omega
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk419.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

  · pnum [Expand.blk419.res, h28, h20, show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft]
    omega

/-- 426 .. 427: next position. -/
theorem blk426_run (t : MachineState) (hpc : t.pc = pcOf 426) (p : Nat) (h28 : t.getReg .x28 = BitVec.ofNat 64 p) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = pcOf 417 ∧ t'.getReg .x28 = BitVec.ofNat 64 (p + 1) ∧
      RegsEq t t' [.x28] ∧ ∀ x, t'.getMem x = t.getMem x :=
  ⟨_, symRun_sound Expand.blk426 Expand.codeAt_426 t hpc (by simp only [Expand.blk426.res, rv_simp]),
    by simp only [Expand.blk426.res, rv_simp], by pnum [Expand.blk426.res, h28], by pregs, getMem_nil rfl t⟩

/-- 428 .. 437 (`ch_done`): the chain end into `LF + 32 + 16 i`, next chain (W1a: the chain
pointer steps by one 64-byte block). -/
theorem blk428_run (t : MachineState) (hpc : t.pc = pcOf 428) (i o base : Nat) (hi : i < 42)
    (ho : o + 64 < 2 ^ 32) (hb : base < 2 ^ 47)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 i) (h20 : t.getReg .x20 = BitVec.ofNat 64 base)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (2 ^ 40)) (h23 : t.getReg .x23 = BitVec.ofNat 64 o)
    (h24 : t.getReg .x24 = BitVec.ofNat 64 (0x30260 + 16 * i))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 10 10 t' ∧ t'.pc = (if i + 1 = 42 then pcOf 438 else pcOf 408) ∧
      t'.readWords (BitVec.ofNat 64 (0x30260 + 16 * i)) 2 = t.readWords (BitVec.ofNat 64 0x30170) 2 ∧
      t'.getReg .x18 = BitVec.ofNat 64 (i + 1) ∧ t'.getReg .x20 = BitVec.ofNat 64 (base + 2 ^ 40) ∧
      t'.getReg .x23 = BitVec.ofNat 64 (o + 64) ∧ t'.getReg .x24 = BitVec.ofNat 64 (0x30260 + 16 * (i + 1)) ∧
      RegsEq t t' [.x14, .x15, .x18, .x20, .x23, .x24] ∧
      Frame t t' (fun a => a = 0x30260 + 16 * i ∨ a = 0x30260 + 16 * i + 8) := by
  refine ⟨_, symRun_sound Expand.blk428 Expand.codeAt_428 t hpc (by pobl [Expand.blk428.res, h24, h25]),
    ?_, ?_, ?_, ?_, ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk428.res, rv_simp, h18, ofNat_add_ofNat, show (42#64 : Word) = BitVec.ofNat 64 42 from rfl,
      ofNat_bne_ofNat]
    by_cases h : i + 1 = 42
    · rw [if_neg (by simp; omega), if_pos h]
    · rw [if_pos (by simp; omega), if_neg h]
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    pnum [Expand.blk428.res, h24, h25]
    try simp (disch := bvomega) only [if_neg, if_pos]
  · pnum [Expand.blk428.res, h18]
  · pnum [Expand.blk428.res, h20, h21]
  · pnum [Expand.blk428.res, h23]
  · pnum [Expand.blk428.res, h24]; omega
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk428.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h24, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 438 .. 441: HASH(`LF`, 704, `NO`), the OTS leaf. -/
theorem blk438_run (t : MachineState) (hpc : t.pc = pcOf 438) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 3 3 t' ∧ fetch eimg t' = some (.base .ECALL) ∧ t'.pc = pcOf 441 ∧
      t'.getReg .x10 = BitVec.ofNat 64 0x30240 ∧ t'.getReg .x11 = BitVec.ofNat 64 704 ∧
      t'.getReg .x12 = BitVec.ofNat 64 0x30200 ∧
      RegsEq t t' [.x10, .x11, .x12] ∧ ∀ x, t'.getMem x = t.getMem x :=
  ⟨_, symRun_sound Expand.blk438 Expand.codeAt_438 t hpc (by simp only [Expand.blk438.res, rv_simp]),
    symRun_ecall Expand.blk438 Expand.codeAt_438 t (by simp only [Expand.blk438.res, rv_simp]) rfl,
    by simp only [Expand.blk438.res, rv_simp], by pnum [Expand.blk438.res, h25],
    by simp only [Expand.blk438.res, rv_simp], by pnum [Expand.blk438.res, h25], by pregs, getMem_nil rfl t⟩

end SigGolfCandidate.ExP
