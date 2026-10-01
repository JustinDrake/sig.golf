import SigGolfCandidate.Expand.PorsCtx

/-!
# `expand`, phase 2: the blocks of a PORS segment (instructions 550 .. 594)

One lemma per symbolic block: its steps (side conditions discharged), final pc, the registers and
memory it writes, and its frame.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign


/-- `pr_seg` (550 .. 553): the header byte `b`, `a = b & 15`, reject `a > 14`. -/
theorem blk550_run (w : List Byte) (t : MachineState) (ptr : Nat) (hpc : t.pc = pcOf 550)
    (h9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr)) (hptr : ptr % 8 = 0) (hptr' : ptr < 0x4000)
    (hw : WitMem w t) :
    ∃ t', Steps eimg t 4 4 t' ∧
      t'.pc = (if 14 < wbyte w ptr % 16 then pcOf 284 else pcOf 554) ∧
      t'.getReg .x6 = BitVec.ofNat 64 (wbyte w ptr) ∧ t'.getReg .x7 = BitVec.ofNat 64 (wbyte w ptr % 16) ∧
      RegsEq t t' [.x6, .x7, .x17] ∧ ∀ a, t'.getMem a = t.getMem a := by
  have hb : wbyte w ptr < 256 := (w.getD ptr 0).isLt
  have hm := hw.get ptr hptr hptr'
  refine ⟨_, symRun_sound Expand.blk550 Expand.codeAt_550 t hpc (by pobl [Expand.blk550.res, h9]),
    ?_, ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk550.res, rv_simp, h9, hm, LoadKind.fromWord, lbu_wword]
    rw [ofNat_and_ofNat _ _ (by omega) (by norm_num), and_15,
      show (14#64 : Word) = BitVec.ofNat 64 14 from rfl, ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
    by_cases h : 14 < wbyte w ptr % 16
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk550.res, rv_simp, h9, hm, LoadKind.fromWord, lbu_wword]
  · simp only [Expand.blk550.res, rv_simp, h9, hm, LoadKind.fromWord, lbu_wword]
    rw [ofNat_and_ofNat _ _ (by omega) (by norm_num), and_15]

/-- 554: `a = 0` skips the direction test. -/
theorem blk554_run (t : MachineState) (hpc : t.pc = pcOf 554) (a : Nat) (ha : a < 16)
    (h7 : t.getReg .x7 = BitVec.ofNat 64 a) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = (if a = 0 then pcOf 559 else pcOf 555) ∧
      RegsEq t t' [] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk554 Expand.codeAt_554 t hpc (by simp only [Expand.blk554.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk554.res, rv_simp, h7, ofNat_beq_zero a (by omega)]
  by_cases h : a = 0
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

theorem and7_path (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3

/-- 555 .. 558: the low-three-bit path `b >> 5` against `E & 7`. -/
theorem blk555_run (t : MachineState) (hpc : t.pc = pcOf 555) (b E : Nat) (hb : b < 256) (hE : E < 2 ^ 15)
    (h6 : t.getReg .x6 = BitVec.ofNat 64 b) (h19 : t.getReg .x19 = BitVec.ofNat 64 E) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = (if b / 32 ≠ E % 8 then pcOf 284 else pcOf 559) ∧
      RegsEq t t' [.x13, .x14] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk555 Expand.codeAt_555 t hpc (by simp only [Expand.blk555.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk555.res, rv_simp, h6, h19]
  rw [show (5#64 : Word).toNat % 64 = 5 from rfl, ofNat_ushiftRight _ _ (by omega),
    ofNat_and_ofNat _ _ (by omega) (by norm_num), and7_path,
    ofNat_and_ofNat _ _ (by omega) (by norm_num), and7_path, ofNat_bne_ofNat,
    Nat.mod_eq_of_lt (by omega : b / 2 ^ 5 % 8 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : E % 8 < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega : b / 2 ^ 5 < 8)]
  by_cases h : b / 32 ≠ E % 8
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

/-- 559 .. 561: `a0 = LB` (leaf) or `PB` (merge). -/
theorem blk559_run (t : MachineState) (hpc : t.pc = pcOf 559) (k : Nat) (hk : k < 2)
    (h24 : t.getReg .x24 = BitVec.ofNat 64 k) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t' c, Steps eimg t (c) c t' ∧ c ≤ 3 ∧ t'.pc = pcOf 562 ∧
      t'.getReg .x10 = BitVec.ofNat 64 (if k = 0 then 0x30000 else 0x30040) ∧
      RegsEq t t' [.x10] ∧ ∀ x, t'.getMem x = t.getMem x := by
  have hs := symRun_sound Expand.blk559 Expand.codeAt_559 t hpc (by simp only [Expand.blk559.res, rv_simp])
  have hpc1 : (Expand.blk559.res.toState t).pc = if k = 0 then pcOf 562 else pcOf 561 := by
    simp only [Expand.blk559.res, rv_simp, h24, ofNat_beq_zero k (by omega)]
    by_cases h : k = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  have r1 : RegsEq t (Expand.blk559.res.toState t) [.x10] := by pregs
  have x10 : (Expand.blk559.res.toState t).getReg .x10 = BitVec.ofNat 64 0x30000 := by
    simp only [Expand.blk559.res, rv_simp, h25]
  by_cases h : k = 0
  · rw [if_pos h] at hpc1
    exact ⟨_, _, hs, by decide, hpc1, by rw [if_pos h, x10], r1, getMem_nil rfl t⟩
  · rw [if_neg h] at hpc1
    have hs2 := symRun_sound Expand.blk561 Expand.codeAt_561 _ hpc1 (by simp only [Expand.blk561.res, rv_simp])
    refine ⟨_, _, hs.trans hs2, by decide, by simp only [Expand.blk561.res, rv_simp], ?_,
      (r1.trans (show RegsEq _ (Expand.blk561.res.toState _) [.x10] by pregs)).mono (by decide),
      fun x => by rw [getMem_nil rfl, getMem_nil rfl]⟩
    rw [if_neg h]
    pnum [Expand.blk561.res, r1.get .x25, h25]

/-- 562 .. 564: the HASH arguments `a1 = 64`, `a2 = OUT`. -/
theorem blk562_run (t : MachineState) (hpc : t.pc = pcOf 562) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 2 2 t' ∧ fetch eimg t' = some (.base .ECALL) ∧ t'.pc = pcOf 564 ∧
      t'.getReg .x11 = BitVec.ofNat 64 64 ∧ t'.getReg .x12 = BitVec.ofNat 64 0x30080 ∧
      RegsEq t t' [.x11, .x12] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk562 Expand.codeAt_562 t hpc (by simp only [Expand.blk562.res, rv_simp]),
    symRun_ecall Expand.blk562 Expand.codeAt_562 t (by simp only [Expand.blk562.res, rv_simp]) rfl,
    by simp only [Expand.blk562.res, rv_simp], by simp only [Expand.blk562.res, rv_simp],
    by pnum [Expand.blk562.res, h25], by pregs, getMem_nil rfl t⟩

/-- 565 .. 566: `t3 = s1 + 8`, `t4 = a`. -/
theorem blk565_run (t : MachineState) (hpc : t.pc = pcOf 565) (ptr a : Nat)
    (h9 : t.getReg .x9 = BitVec.ofNat 64 (0x800 + ptr)) (h7 : t.getReg .x7 = BitVec.ofNat 64 a) :
    ∃ t', Steps eimg t 2 2 t' ∧ t'.pc = pcOf 567 ∧
      t'.getReg .x28 = BitVec.ofNat 64 (0x800 + ptr + 8 + 16 * 0) ∧ t'.getReg .x29 = BitVec.ofNat 64 (a - 0) ∧
      RegsEq t t' [.x28, .x29] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk565 Expand.codeAt_565 t hpc (by simp only [Expand.blk565.res, rv_simp]),
    by simp only [Expand.blk565.res, rv_simp], ?_, ?_, by pregs, getMem_nil rfl t⟩
  · pnum [Expand.blk565.res, h9]
  · simp only [Expand.blk565.res, rv_simp, h7, Nat.sub_zero]

/-- 567: the fold loop test `t4 = 0`. -/
theorem blk567_run (t : MachineState) (hpc : t.pc = pcOf 567) (n : Nat) (hn : n < 2 ^ 64)
    (h29 : t.getReg .x29 = BitVec.ofNat 64 n) :
    ∃ t', Steps eimg t 1 1 t' ∧ t'.pc = (if n = 0 then pcOf 595 else pcOf 568) ∧
      RegsEq t t' [] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk567 Expand.codeAt_567 t hpc (by simp only [Expand.blk567.res, rv_simp]),
    ?_, by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk567.res, rv_simp, h29, ofNat_beq_zero n hn]
  by_cases h : n = 0
  · rw [if_pos (by simpa using h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

/-- 568 .. 577: `PB` word 1 = heap index `E / 2`, load the sibling and the node, test `E & 1`. -/
theorem blk568_run (w : List Byte) (idx : Nat) (t : MachineState) (hpc : t.pc = pcOf 568) (E o : Nat)
    (hE : E < 2 ^ 15) (ho : o % 8 = 0) (ho' : o + 16 ≤ 0x4000) (hw : WitMem w t)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 E) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000)
    (h26 : t.getReg .x26 = BitVec.ofNat 64 (idx % 2 ^ 32))
    (h28 : t.getReg .x28 = BitVec.ofNat 64 (0x800 + o)) :
    ∃ t', Steps eimg t 10 10 t' ∧ t'.pc = (if E % 2 = 0 then pcOf 583 else pcOf 578) ∧
      t'.getReg .x14 = wword w o ∧ t'.getReg .x15 = wword w (o + 8) ∧
      t'.getReg .x16 = t.getMem (BitVec.ofNat 64 0x30080) ∧ t'.getReg .x17 = t.getMem (BitVec.ofNat 64 0x30088) ∧
      t'.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (E / 2)) ∧
      RegsEq t t' [.x13, .x14, .x15, .x16, .x17] ∧ Frame t t' (fun x => x = 0x30048) := by
  have m0 := hw.get o ho (by omega)
  have m8 := hw.get (o + 8) (by omega) (by omega)
  rw [show 0x800 + (o + 8) = 0x800 + o + 8 by omega] at m8
  refine ⟨_, symRun_sound Expand.blk568 Expand.codeAt_568 t hpc (by pobl [Expand.blk568.res, h25, h28]),
    ?_, ?_, ?_, ?_, ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk568.res, rv_simp, h19]
    rw [ofNat_and_ofNat _ _ (by omega) (by norm_num), and_one, ofNat_beq_zero _ (by omega)]
    by_cases h : E % 2 = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk568.res, rv_simp, h28, m0]
  · pnum [Expand.blk568.res, h28, m8]
  · pnum [Expand.blk568.res, h25]
  · pnum [Expand.blk568.res, h25]
  · simp only [Expand.blk568.res, rv_simp, h25, h19, h26, ofNat_add_ofNat]
    bvsimp [ofNat_eq_iff]
    omega
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk568.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 578 .. 582 (`E` odd): the sibling left, the node right. -/
theorem blk578_run (t : MachineState) (hpc : t.pc = pcOf 578) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 5 5 t' ∧ t'.pc = pcOf 587 ∧
      t'.readWords (BitVec.ofNat 64 0x30060) 2 = [t.getReg .x14, t.getReg .x15] ∧
      t'.readWords (BitVec.ofNat 64 0x30070) 2 = [t.getReg .x16, t.getReg .x17] ∧
      RegsEq t t' [] ∧ Frame t t' (fun x => 0x30060 ≤ x ∧ x < 0x30080) := by
  refine ⟨_, symRun_sound Expand.blk578 Expand.codeAt_578 t hpc (by pobl [Expand.blk578.res, h25]),
    by simp only [Expand.blk578.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two]; pnum [Expand.blk578.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk578.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk578.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 583 .. 586 (`E` even): the node left, the sibling right. -/
theorem blk583_run (t : MachineState) (hpc : t.pc = pcOf 583) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = pcOf 587 ∧
      t'.readWords (BitVec.ofNat 64 0x30060) 2 = [t.getReg .x16, t.getReg .x17] ∧
      t'.readWords (BitVec.ofNat 64 0x30070) 2 = [t.getReg .x14, t.getReg .x15] ∧
      RegsEq t t' [] ∧ Frame t t' (fun x => 0x30060 ≤ x ∧ x < 0x30080) := by
  refine ⟨_, symRun_sound Expand.blk583 Expand.codeAt_583 t hpc (by pobl [Expand.blk583.res, h25]),
    by simp only [Expand.blk583.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two]; pnum [Expand.blk583.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk583.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk583.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 587 .. 590: HASH(`PB`, 64, `OUT`). -/
theorem blk587_run (t : MachineState) (hpc : t.pc = pcOf 587) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 3 3 t' ∧ fetch eimg t' = some (.base .ECALL) ∧ t'.pc = pcOf 590 ∧
      t'.getReg .x10 = BitVec.ofNat 64 0x30040 ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
      t'.getReg .x12 = BitVec.ofNat 64 0x30080 ∧
      RegsEq t t' [.x10, .x11, .x12] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk587 Expand.codeAt_587 t hpc (by simp only [Expand.blk587.res, rv_simp]),
    symRun_ecall Expand.blk587 Expand.codeAt_587 t (by simp only [Expand.blk587.res, rv_simp]) rfl,
    by simp only [Expand.blk587.res, rv_simp],
    by pnum [Expand.blk587.res, h25], by simp only [Expand.blk587.res, rv_simp],
    by pnum [Expand.blk587.res, h25], by pregs, getMem_nil rfl t⟩

/-- 591 .. 594: `E >>= 1`, next sibling, one fold less; back to 567. -/
theorem blk591_run (t : MachineState) (hpc : t.pc = pcOf 591) (E p n : Nat) (hE : E < 2 ^ 15) (hp : p + 16 < 2 ^ 64)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 64)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 E) (h28 : t.getReg .x28 = BitVec.ofNat 64 p)
    (h29 : t.getReg .x29 = BitVec.ofNat 64 n) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = pcOf 567 ∧ t'.getReg .x19 = BitVec.ofNat 64 (E / 2) ∧
      t'.getReg .x28 = BitVec.ofNat 64 (p + 16) ∧ t'.getReg .x29 = BitVec.ofNat 64 (n - 1) ∧
      RegsEq t t' [.x19, .x28, .x29] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk591 Expand.codeAt_591 t hpc (by simp only [Expand.blk591.res, rv_simp]),
    by simp only [Expand.blk591.res, rv_simp], ?_, ?_, ?_, by pregs, getMem_nil rfl t⟩
  · simp only [Expand.blk591.res, rv_simp, h19]; rw [ofNat_ushiftRight _ _ (by omega)]; rfl
  · pnum [Expand.blk591.res, h28]
  · simp only [Expand.blk591.res, rv_simp, h29]; bvsimp []

end SigGolfCandidate.ExP
