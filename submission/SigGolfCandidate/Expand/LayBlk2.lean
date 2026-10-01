import SigGolfCandidate.Expand.LayBlk

/-!
# `expand`, phase 2: the fold blocks (442 .. 477), `halt_ok` (478 .. 494), `pors_ok` (639 .. 672)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- 442 (`j fold_pre`), then 673 .. 682 (`fold_pre`): the path pointer `W + 2416 + 96 lay` (the path of
layer `lay ≥ 1` at `pathOff lay`), the heap index `2^h | e` of the leaf, level 0; `j fd_loop`. -/
theorem blk442_run (t : MachineState) (hpc : t.pc = pcOf 442) (h e lay : Nat) (hh : h ≤ 11) (he : e < 2 ^ h)
    (hl : lay < 5) (h8 : t.getReg .x8 = BitVec.ofNat 64 lay)
    (h9 : t.getReg .x9 = BitVec.ofNat 64 h) (h13 : t.getReg .x13 = BitVec.ofNat 64 e) :
    ∃ t', Steps eimg t 11 14 t' ∧ t'.pc = pcOf 446 ∧ t'.getReg .x18 = BitVec.ofNat 64 (2 ^ h + e) ∧
      t'.getReg .x19 = BitVec.ofNat 64 0 ∧ t'.getReg .x23 = BitVec.ofNat 64 (0x800 + (2416 + 96 * lay)) ∧
      RegsEq t t' [.x14, .x15, .x18, .x19, .x23] ∧ ∀ x, t'.getMem x = t.getMem x := by
  have s1 := symRun_sound Expand.blk442 Expand.codeAt_442 t hpc (by simp only [Expand.blk442.res, rv_simp])
  set t1 := Expand.blk442.res.toState t with ht1
  have p1 : t1.pc = pcOf 673 := by simp only [ht1, Expand.blk442.res, rv_simp]
  have r1 : RegsEq t t1 [] := by pregs
  have m1 : ∀ x, t1.getMem x = t.getMem x := getMem_nil rfl t
  have s2 := symRun_sound Expand.blk673 Expand.codeAt_673 t1 p1 (by simp only [Expand.blk673.res, rv_simp])
  have r2 : RegsEq t1 (Expand.blk673.res.toState t1) [.x14, .x15, .x18, .x19, .x23] := by pregs
  refine ⟨_, s1.trans s2, by simp only [Expand.blk673.res, rv_simp], ?_, by simp only [Expand.blk673.res, rv_simp],
    ?_, (r1.trans r2).mono (by simp), fun x => by rw [getMem_nil rfl t1, m1]⟩
  · simp only [Expand.blk673.res, rv_simp, r1.get .x9 (by simp), r1.get .x13 (by simp), h9, h13]
    have hp : (2 : Nat) ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : h < 2 ^ 64), Nat.mod_eq_of_lt (by omega : h < 64), Nat.one_mul,
      ofNat_or_ofNat _ _ hp (by omega)]
    congr 1
    have := Nat.two_pow_add_eq_or_of_lt he 1
    simpa using this.symm
  · simp only [Expand.blk673.res, rv_simp, r1.get .x8 (by simp), h8,
      show (96#64 : Word) = BitVec.ofNat 64 96 from rfl, ofNat_mul_ofNat', ofNat_add_ofNat]
    exact ofNat_congr (by ring)

/-- 446 .. 455 (`fd_loop`): the direction bit, the parent heap index into `NB` word 1, the
sibling and the node. -/
theorem blk446_run (w : List Byte) (t : MachineState) (hpc : t.pc = pcOf 446) (H tau o : Nat)
    (hH : H < 2 ^ 32) (htau : tau < 2 ^ 32) (ho : o % 8 = 0) (ho' : o + 16 ≤ 0x4000) (hw : WitMem w t)
    (h18 : t.getReg .x18 = BitVec.ofNat 64 H) (h23 : t.getReg .x23 = BitVec.ofNat 64 (0x800 + o))
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) (h30 : t.getReg .x30 = BitVec.ofNat 64 tau) :
    ∃ t', Steps eimg t 10 10 t' ∧ t'.pc = (if H % 2 = 0 then pcOf 461 else pcOf 456) ∧
      t'.getReg .x18 = BitVec.ofNat 64 (H / 2) ∧
      t'.getReg .x16 = wword w o ∧ t'.getReg .x17 = wword w (o + 8) ∧
      t'.getReg .x28 = t.getMem (BitVec.ofNat 64 0x30200) ∧ t'.getReg .x29 = t.getMem (BitVec.ofNat 64 0x30208) ∧
      t'.getMem (BitVec.ofNat 64 0x301C8) = BitVec.ofNat 64 (tau + 2 ^ 32 * (H / 2)) ∧
      RegsEq t t' [.x14, .x15, .x16, .x17, .x18, .x28, .x29] ∧ Frame t t' (fun x => x = 0x301C8) := by
  have m0 := hw.get o ho (by omega)
  have m8 := hw.get (o + 8) (by omega) (by omega)
  rw [show 0x800 + (o + 8) = 0x800 + o + 8 by omega] at m8
  refine ⟨_, symRun_sound Expand.blk446 Expand.codeAt_446 t hpc (by pobl [Expand.blk446.res, h23, h25]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk446.res, rv_simp, h18]
    rw [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_and_ofNat _ _ (by omega) (by norm_num),
      and_one, ofNat_beq_zero _ (by omega)]
    by_cases h : H % 2 = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk446.res, rv_simp, h18, show (1#64 : Word).toNat % 64 = 1 from rfl]
    rw [ofNat_ushiftRight _ _ (by omega), pow_one]
  · simp only [Expand.blk446.res, rv_simp, h23, m0]
  · pnum [Expand.blk446.res, h23, m8]
  · pnum [Expand.blk446.res, h25]
  · pnum [Expand.blk446.res, h25]
  · pnum [Expand.blk446.res, h25, h18, h30, show (1#64 : Word).toNat % 64 = 1 from rfl,
      show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft]
    rw [ofNat_ushiftRight _ _ (by omega)]
    simp only [ofNat_shiftLeft, ofNat_add_ofNat, ofNat_eq_iff]
    omega
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk446.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 456 .. 460 (bit 1): the sibling left, the node right. -/
theorem blk456_run (t : MachineState) (hpc : t.pc = pcOf 456) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 5 5 t' ∧ t'.pc = pcOf 465 ∧
      t'.readWords (BitVec.ofNat 64 0x301E0) 2 = [t.getReg .x16, t.getReg .x17] ∧
      t'.readWords (BitVec.ofNat 64 0x301F0) 2 = [t.getReg .x28, t.getReg .x29] ∧
      RegsEq t t' [] ∧ Frame t t' (fun x => 0x301E0 ≤ x ∧ x < 0x30200) := by
  refine ⟨_, symRun_sound Expand.blk456 Expand.codeAt_456 t hpc (by pobl [Expand.blk456.res, h25]),
    by simp only [Expand.blk456.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two]; pnum [Expand.blk456.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk456.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk456.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 461 .. 464 (bit 0): the node left, the sibling right. -/
theorem blk461_run (t : MachineState) (hpc : t.pc = pcOf 461) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 4 4 t' ∧ t'.pc = pcOf 465 ∧
      t'.readWords (BitVec.ofNat 64 0x301E0) 2 = [t.getReg .x28, t.getReg .x29] ∧
      t'.readWords (BitVec.ofNat 64 0x301F0) 2 = [t.getReg .x16, t.getReg .x17] ∧
      RegsEq t t' [] ∧ Frame t t' (fun x => 0x301E0 ≤ x ∧ x < 0x30200) := by
  refine ⟨_, symRun_sound Expand.blk461 Expand.codeAt_461 t hpc (by pobl [Expand.blk461.res, h25]),
    by simp only [Expand.blk461.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two]; pnum [Expand.blk461.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk461.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk461.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 465 .. 468: HASH(`NB`, 64, `NO`). -/
theorem blk465_run (t : MachineState) (hpc : t.pc = pcOf 465) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 3 3 t' ∧ fetch eimg t' = some (.base .ECALL) ∧ t'.pc = pcOf 468 ∧
      t'.getReg .x10 = BitVec.ofNat 64 0x301C0 ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
      t'.getReg .x12 = BitVec.ofNat 64 0x30200 ∧
      RegsEq t t' [.x10, .x11, .x12] ∧ ∀ x, t'.getMem x = t.getMem x :=
  ⟨_, symRun_sound Expand.blk465 Expand.codeAt_465 t hpc (by simp only [Expand.blk465.res, rv_simp]),
    symRun_ecall Expand.blk465 Expand.codeAt_465 t (by simp only [Expand.blk465.res, rv_simp]) rfl,
    by simp only [Expand.blk465.res, rv_simp], by pnum [Expand.blk465.res, h25],
    by simp only [Expand.blk465.res, rv_simp], by pnum [Expand.blk465.res, h25], by pregs, getMem_nil rfl t⟩

/-- 469 .. 471: next sibling, next level. -/
theorem blk469_run (t : MachineState) (hpc : t.pc = pcOf 469) (o lam h : Nat) (ho : o < 2 ^ 32)
    (hl : lam < 2 ^ 32) (hh : h < 2 ^ 32)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 o) (h19 : t.getReg .x19 = BitVec.ofNat 64 lam)
    (h9 : t.getReg .x9 = BitVec.ofNat 64 h) :
    ∃ t', Steps eimg t 3 3 t' ∧ t'.pc = (if lam + 1 = h then pcOf 472 else pcOf 446) ∧
      t'.getReg .x23 = BitVec.ofNat 64 (o + 16) ∧ t'.getReg .x19 = BitVec.ofNat 64 (lam + 1) ∧
      RegsEq t t' [.x19, .x23] ∧ ∀ x, t'.getMem x = t.getMem x := by
  refine ⟨_, symRun_sound Expand.blk469 Expand.codeAt_469 t hpc (by simp only [Expand.blk469.res, rv_simp]),
    ?_, by pnum [Expand.blk469.res, h23], by pnum [Expand.blk469.res, h19], by pregs, getMem_nil rfl t⟩
  simp only [Expand.blk469.res, rv_simp, h19, h9, ofNat_add_ofNat, ofNat_bne_ofNat]
  by_cases hq : lam + 1 = h
  · rw [if_neg (by simp; omega), if_pos hq]
  · rw [if_pos (by simp; omega), if_neg hq]

/-- 472 .. 477: the root is the next layer's message `M` (`0x120`); `LAY -= 1`; `j layer_loop`. -/
theorem blk472_run (t : MachineState) (hpc : t.pc = pcOf 472) (lay : Nat) (hl : 1 ≤ lay) (hl' : lay < 5)
    (h8 : t.getReg .x8 = BitVec.ofNat 64 lay) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 6 6 t' ∧ t'.pc = pcOf 316 ∧ t'.getReg .x8 = BitVec.ofNat 64 (lay - 1) ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = t.readWords (BitVec.ofNat 64 0x30200) 2 ∧
      RegsEq t t' [.x8, .x14, .x15] ∧ Frame t t' (fun x => x = 0x120 ∨ x = 0x128) := by
  refine ⟨_, symRun_sound Expand.blk472 Expand.codeAt_472 t hpc (by pobl [Expand.blk472.res, h25]),
    by simp only [Expand.blk472.res, rv_simp], ?_, ?_, by pregs, ?_⟩
  · simp only [Expand.blk472.res, rv_simp, h8]; bvsimp []
  · rw [readWords_ofNat_two, readWords_ofNat_two]; pnum [Expand.blk472.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk472.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 478 .. 494 (`halt_ok`): the five counters into the witness (W1a: `c0 .. c3` as two dwords at
`W + 2944` (the tweak slot of block `(0, 0)`), `c4` as a dword at `W + 2392`); HALT(0). -/
theorem blk478_run (t : MachineState) (hpc : t.pc = pcOf 478) (c : Nat → Nat) (hc : ∀ l < 5, c l < 2 ^ 22)
    (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000)
    (hct : ∀ l < 5, t.getMem (BitVec.ofNat 64 (0x30780 + 8 * l)) = BitVec.ofNat 64 (c l)) :
    ∃ t', Steps eimg t 16 16 t' ∧ fetch eimg t' = some (.base .ECALL) ∧ t'.getReg .x5 = 1 ∧
      t'.getReg .x10 = 0 ∧
      t'.getMem (BitVec.ofNat 64 0x1380) = BitVec.ofNat 64 (c 0 + 2 ^ 32 * c 1) ∧
      t'.getMem (BitVec.ofNat 64 0x1388) = BitVec.ofNat 64 (c 2 + 2 ^ 32 * c 3) ∧
      t'.getMem (BitVec.ofNat 64 0x1110) = BitVec.ofNat 64 (c 4) ∧
      Frame t t' (fun x => x = 0x1380 ∨ x = 0x1388 ∨ x = 0x1110) := by
  have c0 := hct 0 (by norm_num)
  have c1 := hct 1 (by norm_num)
  have c2 := hct 2 (by norm_num)
  have c3 := hct 3 (by norm_num)
  have c4 := hct 4 (by norm_num)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at c0 c1 c2 c3 c4
  have l0 := hc 0 (by norm_num)
  have l1 := hc 1 (by norm_num)
  have l2 := hc 2 (by norm_num)
  have l3 := hc 3 (by norm_num)
  refine ⟨_, symRun_sound Expand.blk478 Expand.codeAt_478 t hpc (by pobl [Expand.blk478.res, h25]),
    symRun_ecall Expand.blk478 Expand.codeAt_478 t (by pobl [Expand.blk478.res, h25]) rfl,
    by simp only [Expand.blk478.res, rv_simp], by simp only [Expand.blk478.res, rv_simp], ?_, ?_, ?_, ?_⟩
  · pnum [Expand.blk478.res, h25, c0, c1, show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft]
    omega
  · pnum [Expand.blk478.res, h25, c2, c3, show (32#64 : Word).toNat % 64 = 32 from rfl, ofNat_shiftLeft]
    omega
  · pnum [Expand.blk478.res, h25, c4]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk478.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

/-- 639 .. 672 (`pors_ok`): `M = OUT` at `0x120`, the zero P slots and block constants of the layer
phase, `s6 = idx`, `LAY = 4`, `t2 = 2^22`, the SWAR masks; `j layer_loop`. -/
theorem blk639_run (t : MachineState) (hpc : t.pc = pcOf 639) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000) :
    ∃ t', Steps eimg t 34 34 t' ∧ t'.pc = pcOf 316 ∧
      t'.getReg .x7 = BitVec.ofNat 64 (2 ^ 22) ∧ t'.getReg .x8 = BitVec.ofNat 64 4 ∧
      t'.getReg .x22 = t.getReg .x4 ∧ t'.getReg .x26 = swM1 ∧ t'.getReg .x27 = swM2 ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = t.readWords (BitVec.ofNat 64 0x30080) 2 ∧
      t'.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0] ∧
      t'.readWords (BitVec.ofNat 64 0x30150) 4 = [0, 0, 0, 0] ∧
      t'.readWords (BitVec.ofNat 64 0x30250) 2 = [0, 0] ∧
      t'.readWords (BitVec.ofNat 64 0x301D0) 2 = [0, 0] ∧
      RegsEq t t' [.x7, .x8, .x14, .x15, .x22, .x26, .x27] ∧
      Frame t t' (fun x => (0x110 ≤ x ∧ x < 0x130) ∨ (0x30150 ≤ x ∧ x < 0x30170) ∨ x = 0x30250 ∨
        x = 0x30258 ∨ x = 0x301D0 ∨ x = 0x301D8) := by
  refine ⟨_, symRun_sound Expand.blk639 Expand.codeAt_639 t hpc (by pobl [Expand.blk639.res, h25]),
    by simp only [Expand.blk639.res, rv_simp], by pnum [Expand.blk639.res], by pnum [Expand.blk639.res],
    by simp only [Expand.blk639.res, rv_simp], by pnum [Expand.blk639.res], by pnum [Expand.blk639.res], ?_, ?_, ?_,
    ?_, ?_, by pregs, ?_⟩
  · rw [readWords_ofNat_two, readWords_ofNat_two]; pnum [Expand.blk639.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk639.res, h25]
  · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add, readWords_ofNat_two, readWords_ofNat_two]
    pnum [Expand.blk639.res, h25, List.cons_append, List.nil_append]
  · rw [readWords_ofNat_two]; pnum [Expand.blk639.res, h25]
  · rw [readWords_ofNat_two]; pnum [Expand.blk639.res, h25]
  · apply frame_toState; intro x hx hW
    simp only [Expand.blk639.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, h25, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega

end SigGolfCandidate.ExP
