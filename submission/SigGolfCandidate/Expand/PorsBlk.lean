import SigGolfCandidate.Expand.PorsCtx
import SigGolfCandidate.Sign.PorsLevel

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

private theorem guard_ult (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a<b) := by
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb]

private theorem guard_start_run (t : MachineState) (hpc : t.pc=pcOf 555)
    (b : Nat) (hb : b<256) (h6 : t.getReg .x6=BitVec.ofNat 64 b)
    (h7 : t.getReg .x7=BitVec.ofNat 64 (b%16)) :
    ∃ u, Steps eimg t 4 4 u ∧ u.pc=(if b%16<3 then pcOf 2922 else pcOf 2918) ∧
      u.getReg .x13=BitVec.ofNat 64 (b/32) ∧
      RegsEq t u [.x13,.x14] ∧ ∀ x, u.getMem x=t.getMem x := by
  have h1:=symRun_sound Expand.blk555 Expand.codeAt_555 t hpc
    (by simp only [Expand.blk555.res,rv_simp])
  let u:=Expand.blk555.res.toState t
  have p1:u.pc=pcOf 2915 := by simp only [u,Expand.blk555.res,rv_simp]
  have r1:RegsEq t u [] := by pregs
  have m1:∀ x,u.getMem x=t.getMem x := getMem_nil rfl t
  have x6:u.getReg .x6=BitVec.ofNat 64 b := by rw[r1.get .x6,h6]
  have x7:u.getReg .x7=BitVec.ofNat 64 (b%16) := by rw[r1.get .x7,h7]
  have h2:=symRun_sound Expand.blk2915 Expand.codeAt_2915 u p1
    (by simp only [Expand.blk2915.res,rv_simp])
  have r2:RegsEq u (Expand.blk2915.res.toState u) [.x13,.x14] := by pregs
  refine ⟨_,h1.trans h2,?_,?_,(r1.trans r2).mono (by decide),?_⟩
  · simp only [Expand.blk2915.res,rv_simp,x7]
    rw [show (3#64:Word)=BitVec.ofNat 64 3 from rfl,
      guard_ult _ _ (by omega) (by norm_num)]
    by_cases hs:b%16<3 <;> simp [hs]
  · simp only [Expand.blk2915.res,rv_simp,x6]
    rw [show (5#64:Word).toNat%64=5 from rfl,ofNat_ushiftRight _ _ (by omega)]
    rfl
  · intro x;rw[getMem_nil rfl u x,m1]

private theorem guard_short_run (t : MachineState) (hpc:t.pc=pcOf 2922)
    (b E:Nat) (hb:b<256) (hE:E<2^15)
    (h13:t.getReg .x13=BitVec.ofNat 64 (b/32)) (h19:t.getReg .x19=BitVec.ofNat 64 E) :
    ∃ u,Steps eimg t 3 3 u ∧ u.pc=(if b/32%2≠E%2 then pcOf 2926 else pcOf 2925) ∧
      RegsEq t u [.x13,.x14] ∧ ∀ x,u.getMem x=t.getMem x := by
  refine ⟨_,symRun_sound Expand.blk2922 Expand.codeAt_2922 t hpc
    (by simp only [Expand.blk2922.res,rv_simp]),?_,by pregs,getMem_nil rfl t⟩
  simp only [Expand.blk2922.res,rv_simp,h13,h19]
  rw [ofNat_and_ofNat _ _ (by omega) (by norm_num),and_one,
    ofNat_and_ofNat _ _ (by omega) (by norm_num),and_one,ofNat_bne_ofNat,
    Nat.mod_eq_of_lt (by omega:b/32%2<2^64),Nat.mod_eq_of_lt (by omega:E%2<2^64)]
  by_cases hd:b/32%2≠E%2 <;> simp [hd]

private theorem guard_long_run (t : MachineState) (hpc:t.pc=pcOf 2918)
    (b E:Nat) (hb:b<256) (hE:E<2^15)
    (h13:t.getReg .x13=BitVec.ofNat 64 (b/32)) (h19:t.getReg .x19=BitVec.ofNat 64 E) :
    ∃ u,Steps eimg t 3 3 u ∧ u.pc=(if b/32≠E%8 then pcOf 2926 else pcOf 2921) ∧
      RegsEq t u [.x13,.x14] ∧ ∀ x,u.getMem x=t.getMem x := by
  refine ⟨_,symRun_sound Expand.blk2918 Expand.codeAt_2918 t hpc
    (by simp only [Expand.blk2918.res,rv_simp]),?_,by pregs,getMem_nil rfl t⟩
  simp only [Expand.blk2918.res,rv_simp,h13,h19]
  rw [ofNat_and_ofNat _ _ (by omega) (by norm_num),and7_path,
    ofNat_and_ofNat _ _ (by omega) (by norm_num),and7_path,ofNat_bne_ofNat,
    Nat.mod_eq_of_lt (by omega:b/32%8<2^64),Nat.mod_eq_of_lt (by omega:E%8<2^64)]
  rw [Nat.mod_eq_of_lt (by omega:b/32<8)]
  by_cases hd:b/32≠E%8 <;> simp [hd]

private theorem guard_exit_run (t:MachineState) (pc:Nat) (hpc:t.pc=pcOf pc)
    (hp:pc=2921∨pc=2925∨pc=2926) :
    ∃ u,Steps eimg t 1 1 u ∧ u.pc=(if pc=2926 then pcOf 284 else pcOf 559) ∧
      RegsEq t u [] ∧ ∀ x,u.getMem x=t.getMem x := by
  rcases hp with rfl|rfl|rfl
  · exact ⟨_,symRun_sound Expand.blk2921 Expand.codeAt_2921 t hpc
      (by simp only [Expand.blk2921.res,rv_simp]),by simp only [Expand.blk2921.res,rv_simp];rfl,
      by pregs,getMem_nil rfl t⟩
  · exact ⟨_,symRun_sound Expand.blk2925 Expand.codeAt_2925 t hpc
      (by simp only [Expand.blk2925.res,rv_simp]),by simp only [Expand.blk2925.res,rv_simp];rfl,
      by pregs,getMem_nil rfl t⟩
  · exact ⟨_,symRun_sound Expand.blk2926 Expand.codeAt_2926 t hpc
      (by simp only [Expand.blk2926.res,rv_simp]),by simp only [Expand.blk2926.res,rv_simp];rfl,
      by pregs,getMem_nil rfl t⟩

/-- Short positive segments check parity; long ones check all three path bits.
The appended guard uses eight ordinary instructions on either outcome. -/
theorem blk555_run (t : MachineState) (hpc : t.pc = pcOf 555) (b E : Nat) (hb : b < 256) (hE : E < 2^15)
    (h6 : t.getReg .x6=BitVec.ofNat 64 b) (h7 : t.getReg .x7=BitVec.ofNat 64 (b%16))
    (h19 : t.getReg .x19=BitVec.ofNat 64 E) :
    ∃ u,Steps eimg t 8 8 u ∧
      u.pc=(if b/32%2≠E%2 ∨ (3≤b%16 ∧ b/32/2≠E/2%4) then pcOf 284 else pcOf 559) ∧
      RegsEq t u [.x13,.x14] ∧ ∀ x,u.getMem x=t.getMem x := by
  obtain ⟨t1,hs1,p1,x13,r1,m1⟩:=guard_start_run t hpc b hb h6 h7
  have x19:t1.getReg .x19=BitVec.ofNat 64 E := by rw[r1.get .x19,h19]
  let bad:=b/32%2≠E%2 ∨ (3≤b%16 ∧ b/32/2≠E/2%4)
  obtain ⟨t2,ret,hs2,p2,hr,r2,m2⟩ : ∃ t2 ret,Steps eimg t1 3 3 t2 ∧
      t2.pc=(if bad then pcOf 2926 else pcOf ret) ∧ (ret=2921∨ret=2925) ∧
      RegsEq t1 t2 [.x13,.x14] ∧ ∀ x,t2.getMem x=t1.getMem x := by
    by_cases hs:b%16<3
    · rw[if_pos hs] at p1
      obtain ⟨t2,st,pc,rr,mm⟩:=guard_short_run t1 p1 b E hb hE x13 x19
      refine ⟨t2,2925,st,?_,Or.inr rfl,rr,mm⟩
      simpa [bad,show ¬3≤b%16 by omega] using pc
    · rw[if_neg hs] at p1
      obtain ⟨t2,st,pc,rr,mm⟩:=guard_long_run t1 p1 b E hb hE x13 x19
      refine ⟨t2,2921,st,?_,Or.inl rfl,rr,mm⟩
      have he:bad ↔ b/32≠E%8 := by dsimp[bad];omega
      simpa [he] using pc
  have hret:(if bad then 2926 else ret)=2921∨(if bad then 2926 else ret)=2925∨(if bad then 2926 else ret)=2926 := by
    by_cases h:bad
    · simp [h]
    · simp only [if_neg h]; rcases hr with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have p2':t2.pc=pcOf (if bad then 2926 else ret) := by split_ifs at * <;> assumption
  obtain ⟨t3,hs3,p3,r3,m3⟩:=guard_exit_run t2 _ p2' hret
  refine ⟨t3,(hs1.trans hs2).trans hs3,?_,((r1.trans r2).trans r3).mono (by decide),?_⟩
  · have hn:ret≠2926 := by omega
    change t3.pc = if bad then pcOf 284 else pcOf 559
    by_cases hb:bad
    · simpa only [if_pos hb, if_true] using p3
    · simpa only [if_neg hb, if_neg hn] using p3
  · intro x;rw[m3,m2,m1]


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

/-! ## The rev16 trampolines (`804 .. 831`, `832 .. 859`) -/

/-- `x13` after a rev16 trampoline: the network of `Sign.Rev16`, shifted by `48` instead of `16`. -/
def net48 (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .sll (Rev16.bvS 1#64 21845#64 (Rev16.bvS 2#64 13107#64 (Rev16.bvS 4#64 3855#64 (Rev16.bvA x)))) 48#64

/-- The trampoline network puts the relabelled field in the high half: `net48 v = 2^32 * efield v`. -/
theorem net48_eq (v : Nat) (hv : v < 2 ^ 14) :
    net48 (BitVec.ofNat 64 v) = BitVec.ofNat 64 (2 ^ 32 * Rev.efield v) := by
  set y := Rev16.bvS 1#64 21845#64 (Rev16.bvS 2#64 13107#64 (Rev16.bvS 4#64 3855#64
    (Rev16.bvA (BitVec.ofNat 64 v)))) with hy
  have h16 : Rev16.revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (Rev.efield v) := Rev16.revNetBV_eq v hv
  have hE := Rev.efield_lt v
  have e16 : (Rev16.revNetBV (BitVec.ofNat 64 v)).toNat = y.toNat * 2 ^ 16 % 2 ^ 64 := by
    show (BinOp.eval .sll y 16#64).toNat = _
    simp only [BinOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rfl
  have hy16 : y.toNat < 2 ^ 16 := by
    have := Rev16.rvS_lt 1 21845 (Rev16.bvS 2#64 13107#64 (Rev16.bvS 4#64 3855#64
      (Rev16.bvA (BitVec.ofNat 64 v)))).toNat (by omega) (by omega)
    rw [hy, Rev16.bvS_toNat 1 21845 _ (by omega) (by omega) (by omega)]
    exact this
  have hyE : y.toNat * 2 ^ 16 = Rev.efield v := by
    have := congrArg BitVec.toNat h16
    rw [e16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    exact this
  apply BitVec.eq_of_toNat_eq
  show (BinOp.eval .sll y 48#64).toNat = _
  simp only [BinOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  rw [show (48 : Nat) % 2 ^ 64 % 64 = 48 from rfl, show (2 : Nat) ^ 48 = 2 ^ 16 * 2 ^ 32 by norm_num,
    ← Nat.mul_assoc, hyE, Nat.mul_comm]

theorem blk804_x13 (u : MachineState) :
    (Expand.blk804.res.toState u).getReg .x13 = net48 (BinOp.eval .srl (u.getReg .x19) 1#64) := by
  rw [Result.toState_getReg]; rfl

theorem blk832_x13 (u : MachineState) :
    (Expand.blk832.res.toState u).getReg .x13 = net48 (u.getReg .x19) := by
  rw [Result.toState_getReg]; rfl

theorem blk804_regs (u : MachineState) (r : Reg) (h1 : r ≠ .x13) (h2 : r ≠ .x14) (h3 : r ≠ .x15) :
    (Expand.blk804.res.toState u).getReg r = u.getReg r := by
  cases r <;> (try contradiction) <;> simp only [Expand.blk804.res, rv_simp] <;> rfl

theorem blk832_regs (u : MachineState) (r : Reg) (h1 : r ≠ .x13) (h2 : r ≠ .x14) (h3 : r ≠ .x15) :
    (Expand.blk832.res.toState u).getReg r = u.getReg r := by
  cases r <;> (try contradiction) <;> simp only [Expand.blk832.res, rv_simp] <;> rfl

/-- 568 (`j 804`), the network `804 .. 831` on `x19 >> 1`, back to `570 .. 577`: `PB` word 1 =
`idx | efield (E / 2) << 32`, load the sibling and the node, test `E & 1`. -/
theorem blk568_run (w : List Byte) (idx : Nat) (t : MachineState) (hpc : t.pc = pcOf 568) (E o : Nat)
    (hE : E < 2 ^ 15) (ho : o % 8 = 0) (ho' : o + 16 ≤ 0x4000) (hw : WitMem w t)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 E) (h25 : t.getReg .x25 = BitVec.ofNat 64 0x30000)
    (h26 : t.getReg .x26 = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32))
    (h28 : t.getReg .x28 = BitVec.ofNat 64 (0x800 + o)) :
    ∃ t', Steps eimg t 37 37 t' ∧ t'.pc = (if E % 2 = 0 then pcOf 583 else pcOf 578) ∧
      t'.getReg .x14 = wword w o ∧ t'.getReg .x15 = wword w (o + 8) ∧
      t'.getReg .x16 = t.getMem (BitVec.ofNat 64 0x30080) ∧ t'.getReg .x17 = t.getMem (BitVec.ofNat 64 0x30088) ∧
      t'.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32 + 2 ^ 32 * Rev.efield (E / 2)) ∧
      RegsEq t t' [.x13, .x14, .x15, .x16, .x17] ∧ Frame t t' (fun x => x = 0x30048) := by
  have hs1 := symRun_sound Expand.blk568 Expand.codeAt_568 t hpc (by simp only [Expand.blk568.res, rv_simp])
  set t1 := Expand.blk568.res.toState t with ht1
  have pc1 : t1.pc = pcOf 804 := by simp only [ht1, Expand.blk568.res, rv_simp]
  have g1 : ∀ r, t1.getReg r = t.getReg r := fun r => by
    rw [ht1]; cases r <;> simp only [Expand.blk568.res, rv_simp] <;> rfl
  have m1 : ∀ a, t1.getMem a = t.getMem a := fun a => getMem_nil rfl t a
  have hs2 := symRun_sound Expand.blk804 Expand.codeAt_804 t1 pc1 (by simp only [Expand.blk804.res, rv_simp])
  set t2 := Expand.blk804.res.toState t1 with ht2
  have pc2 : t2.pc = pcOf 570 := by simp only [ht2, Expand.blk804.res, rv_simp]
  have m2 : ∀ a, t2.getMem a = t1.getMem a := fun a => getMem_nil rfl t1 a
  have g2 : ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → t2.getReg r = t.getReg r := fun r a b c => by
    rw [ht2, blk804_regs t1 r a b c, g1]
  have x13 : t2.getReg .x13 = BitVec.ofNat 64 (2 ^ 32 * Rev.efield (E / 2)) := by
    rw [ht2, blk804_x13, g1, h19]
    rw [show BinOp.eval .srl (BitVec.ofNat 64 E) 1#64 = BitVec.ofNat 64 (E / 2) by
      rw [show BinOp.eval .srl (BitVec.ofNat 64 E) 1#64 = BitVec.ofNat 64 E >>> 1 from rfl,
        ofNat_ushiftRight _ _ (by omega), pow_one]]
    exact net48_eq _ (by omega)
  have m0 := hw.get o ho (by omega)
  have m8 := hw.get (o + 8) (by omega) (by omega)
  rw [show 0x800 + (o + 8) = 0x800 + o + 8 by omega] at m8
  have hw2 : ∀ a, t2.getMem a = t.getMem a := fun a => by rw [m2, m1]
  have q25 : t2.getReg .x25 = BitVec.ofNat 64 0x30000 := by rw [g2 .x25 (by decide) (by decide) (by decide), h25]
  have q28 : t2.getReg .x28 = BitVec.ofNat 64 (0x800 + o) := by rw [g2 .x28 (by decide) (by decide) (by decide), h28]
  have q26 : t2.getReg .x26 = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32) := by
    rw [g2 .x26 (by decide) (by decide) (by decide), h26]
  have q19 : t2.getReg .x19 = BitVec.ofNat 64 E := by rw [g2 .x19 (by decide) (by decide) (by decide), h19]
  have hs3 := symRun_sound Expand.blk570 Expand.codeAt_570 t2 pc2 (by pobl [Expand.blk570.res, q25, q28])
  refine ⟨_, Steps.of_eq ((hs1.trans hs2).trans hs3) (by simp only [Expand.blk568.res, Expand.blk804.res,
      Expand.blk570.res]) (by simp only [Expand.blk568.res, Expand.blk804.res, Expand.blk570.res]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expand.blk570.res, rv_simp, q19]
    rw [ofNat_and_ofNat _ _ (by omega) (by norm_num), and_one, ofNat_beq_zero _ (by omega)]
    by_cases h : E % 2 = 0
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · simp only [Expand.blk570.res, rv_simp, q28, hw2, m0]
  · pnum [Expand.blk570.res, q28, hw2, m8]
  · pnum [Expand.blk570.res, q25, hw2]
  · pnum [Expand.blk570.res, q25, hw2]
  · have hE2 := Rev.efield_lt (E / 2)
    have e : (BitVec.ofNat 64 (2 ^ 32 * Rev.efield (E / 2)) + BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32)) =
        BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32 + 2 ^ 32 * Rev.efield (E / 2)) := by
      rw [ofNat_add_ofNat]; exact ofNat_congr (by omega)
    pnum [Expand.blk570.res, q25, x13, q26, e]
    omega
  · intro r hr
    have hr' : r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x15 ∧ r ≠ .x16 ∧ r ≠ .x17 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr
    rw [← g2 r hr'.1 hr'.2.1 hr'.2.2.1]
    exact regsEq_toState Expand.blk570.res t2 [.x13, .x14, .x15, .x16, .x17]
      (fun x hx => by cases x <;> first | (simp at hx; done) | rfl) r hr
  · have f3 : Frame t2 (Expand.blk570.res.toState t2) (fun x => x = 0x30048) := by
      apply frame_toState; intro x hx hW
      simp only [Expand.blk570.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true, ne_eq, q25, ofNat_add_ofNat, ofNat_eq_iff]
      bvomega
    intro a ha hW
    rw [f3 a ha hW, hw2]

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
