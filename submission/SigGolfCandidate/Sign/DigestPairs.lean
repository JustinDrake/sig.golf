import SigGolfCandidate.Sign.DigAn
import SigGolfCandidate.Sign.RndTail
import SigGolfCandidate.Sign.Pair

/-! One digest query and its octopus analysis, preserving the unused randomizer half. -/
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure DigMem (S mm : List Byte) (u : MachineState) : Prop where
  rbS : u.readWords (BitVec.ofNat 64 0x640) 4 = wordsOf S
  rbM : u.readWords (BitVec.ofNat 64 0x660) 4 = wordsOf mm
  rbPack : u.readWords (BitVec.ofNat 64 0x780) 8 =
    rndPackWords (u.getMem (BitVec.ofNat 64 0x640)) (u.getMem (BitVec.ofNat 64 0x648))
      (u.getMem (BitVec.ofNat 64 0x650)) (u.getMem (BitVec.ofNat 64 0x658))
      (u.getMem (BitVec.ofNat 64 0x660)) (u.getMem (BitVec.ofNat 64 0x668))
      (u.getMem (BitVec.ofNat 64 0x670)) (u.getMem (BitVec.ofNat 64 0x678))
  db0 : u.readWords (BitVec.ofNat 64 0x0) 2 = [0, 0]
  dbM : u.readWords (BitVec.ofNat 64 0x20) 4 = wordsOf mm

def digW (a : Nat) : Prop := a = 0x7b8 ∨ (0x10 ≤ a ∧ a < 0x20) ∨ (0x140 ≤ a ∧ a < 0x180) ∨ anW a

def digRegs : List Reg := [.x1, .x2, .x3, .x4, .x6, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18]

def DigInv (u : MachineState) (a : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 65 ∧ t.getReg .x6 = BitVec.ofNat 64 a ∧ a < 2 ^ 19 ∧ RegsEq u t digRegs ∧
    Frame u t digW ∧ lo32 (t.getMem (BitVec.ofNat 64 0x7b8)) = lo32 (u.getMem (BitVec.ofNat 64 0x7b8))

def DigPost (u : MachineState) : Option (Val × Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 141 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (rho, N), t => t.pc = pcOf 145 ∧ RegsEq u t digRegs ∧ Frame u t digW ∧
      rho.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x10) 2 = wordsOf rho ∧
      (∃ ans : BitVec 256, N = ans.toNat ∧
        ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k) ∧
      admissible N = true ∧ KeysAt t (sortKeys (keys0 N)) ∧
      t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)

theorem pcOf_eq (i : Nat) (h : 0x1000 + 4 * i < 2 ^ 64) (w : Word) (hw : w.toNat = 0x1000 + 4 * i) :
    w = pcOf i := by
  apply BitVec.eq_of_toNat_eq; rw [hw]; simp; omega

theorem pcOf_add4 (i : Nat) : pcOf i + 4 = pcOf (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

def digTryW (a : Nat) : Prop := (0x10 ≤ a ∧ a < 0x20) ∨ (0x160 ≤ a ∧ a < 0x180) ∨ anW a

def digTryRegs : List Reg := [.x3, .x4, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The selected randomizer is already in x1/x2. A failed attempt preserves x6,
x18 and both halves at 0x140, so the caller can try the other half. -/
theorem digAttempt (sk : SecretKey) (m : Message) (u v : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0)
    (vpc : v.pc = pcOf 72) (vregs : RegsEq u v digRegs) (vframe : Frame u v digW)
    (rho : Val) (hlen : rho.length = 16)
    (hval : valOfWords (v.getReg .x1) (v.getReg .x2) = rho)
    (rest : OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 137 → RegsEq v t' digTryRegs →
      Frame v t' digTryW → Sim image t' Wr rest (DigPost u)) :
    Sim image v (16 + anCyc + Wr)
      ((liftM (HashSpec.query (addrFmt (digestInput rho (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible ans.toNat then pure (some (rho, ans.toNat)) else rest)
      (DigPost u) := by
  have hm : (toList m).length = 32 := length_toList m
  have hs := symRun_sound blk72 codeAt_72 v vpc (by simp only [blk72.res, rv_simp])
  set t3 := blk72.res.toState v with ht3
  have f3 : Frame v t3 (fun x => x = 0x10 ∨ x = 0x18) := by
    apply frame_toState; intro x hx hW
    simp only [blk72.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq v t3 [.x10, .x11, .x12] := by
    intro r hr; simp only [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 : fetch image t3 = some (.base .ECALL) :=
    symRun_ecall blk72 codeAt_72 v (by simp only [blk72.res, rv_simp]) rfl
  have y10 : t3.getReg .x10 = BitVec.ofNat 64 0x0 := by simp only [ht3, blk72.res, rv_simp]
  have y11 : t3.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht3, blk72.res, rv_simp]
  have y12 : t3.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [ht3, blk72.res, rv_simp]
  have y5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, vregs.get .x5 (by decide), hx5]
  have pc3 : t3.pc = pcOf 77 := by simp only [ht3, blk72.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0x10) 2 = wordsOf rho := by
    rw [← hval, wordsOf_valOfWords, readWords_ofNat_two]
    simp only [ht3, blk72.res, rv_simp]
    rfl
  have fu3 : Frame u t3 digW := (vframe.trans f3).mono (by
    intro x hx; simp only [digW, anW, false_or, or_false] at hx ⊢; omega)
  have hq : hashInput t3 = addrFmt (digestInput rho (toList m)) := by
    refine hashInput_eq_digest t3 _ _ hlen hm y11 (by rw [y10]; decide) ?_
    rw [y10, show (8 : Nat) = 2 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW, anW]; omega), hmem.db0, v3,
      fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW, anW]; omega), hmem.dbM]
  have hc : blk72.res.cycles = 5 := rfl
  rw [hc] at hs
  have hb : (addrFmt (digestInput rho (toList m))).blocks = 1 := by
    rw [addrFmt_blocks,fmt_digestInput _ _ hlen hm]; rfl
  refine (Sim.steps hs (Sim.query_bind (W := anCyc + Wr) e3 y5
    (hashArgs_of y10 y11 y12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun ans => ?_))).mono (by rw [hb]; omega) (fun _ _ h => h)
  set t4 := writeHash t3 ans with ht4
  have f4 : Frame t3 t4 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) :=
    frame_writeHash t3 ans 0x160 y12 (by norm_num)
  have pc4 : t4.pc = pcOf 78 := by rw [ht4, writeHash_pc, pc3, pcOf_add4]
  have w4 : ∀ k, k < 4 → t4.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k := by
    intro k hk
    rw [ht4, writeHash_getMem_ofNat t3 ans 0x160 _ y12 (by norm_num) (by omega)]
    interval_cases k <;> rfl
  obtain ⟨k5, c5, t5, hs5, hc5, pc5, keys5, sent5, r5, f5⟩ := analysis_run ans t4 pc4 w4
  have fv5 : Frame v t5 digTryW := ((f3.trans f4).trans f5).mono (by
    intro x hx; simp only [digTryW, anW] at hx ⊢; omega)
  have rv5 : RegsEq v t5 digTryRegs := ((r3.trans (regsEq_writeHash _ _ [])).trans r5).mono (by decide)
  have fu5 : Frame u t5 digW := (vframe.trans fv5).mono (by
    intro x hx; simp only [digW, digTryW, anW] at hx ⊢; omega)
  have ru5 : RegsEq u t5 digRegs := (vregs.trans rv5).mono (by decide)
  rw [← admissibleM_eq]
  by_cases hadm : admissibleM ans.toNat = true
  · rw [if_pos hadm]
    refine (Sim.pure_steps hs5 ?_).mono (by omega) (fun _ _ h => h)
    refine ⟨by rw [pc5, if_pos hadm], ru5, fu5, hlen, ?_, ⟨ans, rfl, fun k hk => ?_⟩,
      by rwa [← admissibleM_eq], keys5, sent5⟩
    · rw [f5.readWords _ _ (by norm_num) (by intro i hi; simp only [anW]; omega),
        f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3]
    · rw [f5.getMem (by omega) (by simp only [anW]; omega), w4 k hk]
  · rw [if_neg hadm]
    exact (Sim.steps hs5 (hrest t5 (by rw [pc5, if_neg hadm]) rv5 fv5)).mono
      (by omega) (fun _ _ h => h)

end SigGolfCandidate.Sign

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- One randomizer query supplies both candidate randomizers. -/
theorem digRandomizer (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0) (a : Nat) (t : MachineState)
    (hinv : DigInv u a t) (rest : Val → Val → OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ (ans : BitVec 256) t', t'.pc = pcOf 70 →
      t'.getReg .x6 = BitVec.ofNat 64 a → RegsEq u t' digRegs → Frame u t' digW →
      lo32 (t'.getMem (BitVec.ofNat 64 0x7b8)) = lo32 (u.getMem (BitVec.ofNat 64 0x7b8)) →
      t'.readWords (BitVec.ofNat 64 0x140) 2 = wordsOf (answerBytes 16 ans) →
      t'.readWords (BitVec.ofNat 64 0x150) 2 = wordsOf (hiVal ans) →
      Sim image t' Wr (rest (answerBytes 16 ans) (hiVal ans)) (DigPost u)) :
    Sim image t (12 + Wr)
      (prf2 (rndInput (toList sk) (toList m) a) >>= fun p => rest p.1 p.2) (DigPost u) := by
  rw [prf2_eq]
  simp only [H, bind_assoc, pure_bind]
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  obtain ⟨tpc, t6, ha, tregs, tframe, tlo⟩ := hinv
  -- block 27
  have hs1 := symRun_sound blk65 codeAt_65 t tpc (by simp only [blk65.res, rv_simp])
  set t1 := blk65.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x7b8) := by
    apply frame_toState; intro x hx hW
    simp only [blk65.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; simp only [ht1, Result.toState_getReg]
    cases r <;> simp_all [blk65.res, rv_simp] <;> rfl
  have e1 : fetch image t1 = some (.base .ECALL) := symRun_ecall blk65 codeAt_65 t (by simp only [blk65.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x780 := by simp only [ht1, blk65.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk65.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk65.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hx5]
  have pc1 : t1.pc = pcOf 69 := by simp only [ht1, blk65.res, rv_simp]
  let s0 := u.getMem (BitVec.ofNat 64 0x640)
  let s1 := u.getMem (BitVec.ofNat 64 0x648)
  let s2 := u.getMem (BitVec.ofNat 64 0x650)
  let s3 := u.getMem (BitVec.ofNat 64 0x658)
  let m0 := u.getMem (BitVec.ofNat 64 0x660)
  let m1 := u.getMem (BitVec.ofNat 64 0x668)
  let m2 := u.getMem (BitVec.ofNat 64 0x670)
  let m3 := u.getMem (BitVec.ofNat 64 0x678)
  have hsw : wordsOf (toList sk) = [s0, s1, s2, s3] := by
    rw [← hmem.rbS, readWords_ofNat_succ, readWords_ofNat_succ,
      readWords_ofNat_succ, readWords_ofNat_succ]
    rfl
  have hmw : wordsOf (toList m) = [m0, m1, m2, m3] := by
    rw [← hmem.rbM, readWords_ofNat_succ, readWords_ofNat_succ,
      readWords_ofNat_succ, readWords_ofNat_succ]
    rfl
  have hsbytes := eq_of_words4 (toList sk) hS s0 s1 s2 s3 hsw
  have hmbytes := eq_of_words4 (toList m) hm m0 m1 m2 m3 hmw
  have hpacked : wordsOf (rndInput (toList sk) (toList m) a) =
      rndPackWordsAt s0 s1 s2 s3 m0 m1 m2 m3 a := by
    rw [hsbytes, hmbytes]
    exact words_rndInput_packed_at s0 s1 s2 s3 m0 m1 m2 m3 a
  have hbaseLast : u.getMem (BitVec.ofNat 64 0x7b8) = rndW7 m3 := by
    have h := getMem_of_readWords u 8 0x780 7 _ hmem.rbPack (by norm_num)
    simpa [rndPackWords] using h
  have hlast : t1.getMem (BitVec.ofNat 64 0x7b8) = rndW7a m3 a :=
    blk65_rndW7a t m3 a t6 (by rw [tlo, hbaseLast])
  have hpre : t1.readWords (BitVec.ofNat 64 0x780) 7 =
      u.readWords (BitVec.ofNat 64 0x780) 7 := by
    rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW, anW]; omega)]
  have htrial : t1.readWords (BitVec.ofNat 64 0x780) 8 =
      rndPackWordsAt s0 s1 s2 s3 m0 m1 m2 m3 a :=
    rndPackWords_trial u t1 s0 s1 s2 s3 m0 m1 m2 m3 a hmem.rbPack hpre hlast
  have hq1 : hashInput t1 = pad64 (rndInput (toList sk) (toList m) a) := by
    obtain ⟨hn, hw⟩ := words_rndInput _ _ hS hm a
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10]
    exact htrial.trans hpacked.symm
  have hc1 : blk65.res.cycles = 4 := rfl
  rw [hc1] at hs1
  have hb1 : (pad64 (rndInput (toList sk) (toList m) a)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_rndInput _ _ hS hm a).1]
  refine (Sim.steps hs1 (Sim.query_bind (W := Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq1.trans (by rw [addrFmt_rndInput]; exact (fmt_rndInput _ _ _).symm)) (fun ans => ?_))).mono
    (by rw [addrFmt_rndInput, fmt_rndInput, hb1]; omega) (fun _ _ h => h)
  let t2 := writeHash t1 ans
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) :=
    frame_writeHash t1 ans 0x140 x12 (by norm_num)
  apply hrest ans t2
  · rw [writeHash_pc, pc1, pcOf_add4]
  · rw [writeHash_getReg, r1.get .x6, t6]
  · exact ((tregs.trans r1).trans (regsEq_writeHash _ _ [])).mono (by decide)
  · exact ((tframe.trans f1).trans f2).mono (by intro x hx; simp only [digW, anW] at hx ⊢; omega)
  · rw [f2.getMem (by norm_num) (by omega), ht1, blk65_lo32]
    exact tlo
  · exact sec_lo t1 ans x12
  · exact sec_hi t1 ans x12

end SigGolfCandidate.Sign

/-! Digest search using both halves of each 256-bit randomizer query. -/
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

private def lowState (t : MachineState) : MachineState :=
  blk2893.res.toState (blk70.res.toState t)
private def branchState (t : MachineState) : MachineState :=
  blk2897.res.toState (blk137.res.toState t)
private def highState (t : MachineState) : MachineState :=
  blk2900.res.toState (branchState t)
private def nextState (t : MachineState) : MachineState :=
  blk138.res.toState (blk2898.res.toState t)

private theorem low_steps (t : MachineState) (hpc : t.pc = pcOf 70) :
    Steps image t 5 5 (lowState t) := by
  have h0 := symRun_sound blk70 codeAt_70 t hpc (by simp only [blk70.res, rv_simp])
  have h1 := symRun_sound blk2893 codeAt_2893 (blk70.res.toState t)
    (by simp only [blk70.res, rv_simp]) (by simp only [blk2893.res, rv_simp])
  exact h0.trans h1

private theorem branch_steps (t : MachineState) (hpc : t.pc = pcOf 137) :
    Steps image t 2 2 (branchState t) := by
  have h0 := symRun_sound blk137 codeAt_137 t hpc (by simp only [blk137.res, rv_simp])
  have h1 := symRun_sound blk2897 codeAt_2897 (blk137.res.toState t)
    (by simp only [blk137.res, rv_simp]) (by simp only [blk2897.res, rv_simp])
  exact h0.trans h1

private theorem high_steps (t : MachineState) (hpc : t.pc = pcOf 137) (h18 : t.getReg .x18 = 0) :
    Steps image t 6 6 (highState t) := by
  have h0 := branch_steps t hpc
  have h1 := symRun_sound blk2900 codeAt_2900 (branchState t)
    (by simp only [branchState, blk2897.res, blk137.res, rv_simp, h18]; decide)
    (by simp only [blk2900.res, rv_simp])
  exact h0.trans h1

private theorem low_regs (t : MachineState) : RegsEq t (lowState t) [.x1, .x2, .x18] := by
  intro r hr
  simp only [lowState, Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl

private theorem high_regs (t : MachineState) : RegsEq t (highState t) [.x1, .x2, .x18] := by
  intro r hr
  simp only [highState, branchState, Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl

private theorem branch_regs (t : MachineState) : RegsEq t (branchState t) [] := by
  intro r _
  simp only [branchState, Result.toState_getReg]
  cases r <;> rfl

private theorem low_mem (t : MachineState) (x : Word) : (lowState t).getMem x = t.getMem x := by
  simp only [lowState, blk2893.res, blk70.res, rv_simp]
private theorem high_mem (t : MachineState) (x : Word) : (highState t).getMem x = t.getMem x := by
  simp only [highState, branchState, blk2900.res, blk2897.res, blk137.res, rv_simp]
private theorem branch_mem (t : MachineState) (x : Word) : (branchState t).getMem x = t.getMem x := by
  simp only [branchState, blk2897.res, blk137.res, rv_simp]

private theorem eq_of_two_words (l : List Byte) (hl : l.length = 16) (w0 w1 : Word)
    (hw : wordsOf l = [w0, w1]) : valOfWords w0 w1 = l := by
  have e : l = l.take 8 ++ l.drop 8 := (List.take_append_drop 8 l).symm
  rw [e, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  obtain ⟨h0, h1⟩ := hw
  rw [valOfWords, ← h0, ← h1, bytesOfWord_leNat _ (by simp; omega),
    bytesOfWord_leNat _ (by simp; omega)]
  exact e.symm

/-- A pair is exhausted only after both digest attempts reject. -/
theorem digTrial (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0) (a : Nat) (t : MachineState)
    (hinv : DigInv u a t) (rest : OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 2898 → t'.getReg .x6 = BitVec.ofNat 64 a → RegsEq u t' digRegs →
      Frame u t' digW → lo32 (t'.getMem (BitVec.ofNat 64 0x7b8)) = lo32 (u.getMem (BitVec.ofNat 64 0x7b8)) →
      Sim image t' Wr rest (DigPost u)) :
    Sim image t (60 + 2 * anCyc + Wr) (prf2 (rndInput (toList sk) (toList m) a) >>= fun p =>
      (liftM (HashSpec.query (addrFmt (digestInput p.1 (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible ans.toNat then pure (some (p.1, ans.toNat)) else
          (liftM (HashSpec.query (addrFmt (digestInput p.2 (toList m)))) : OracleComp HashSpec _) >>= fun ans' =>
            if admissible ans'.toNat then pure (some (p.2, ans'.toNat)) else rest)
      (DigPost u) := by
  refine (digRandomizer sk m u hmem hx5 a t hinv (fun lo hi =>
    (liftM (HashSpec.query (addrFmt (digestInput lo (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
      if admissible ans.toNat then pure (some (lo, ans.toNat)) else
        (liftM (HashSpec.query (addrFmt (digestInput hi (toList m)))) : OracleComp HashSpec _) >>= fun ans' =>
          if admissible ans'.toNat then pure (some (hi, ans'.toNat)) else rest) (45 + 2 * anCyc + Wr) ?_).mono (W' := 60 + 2 * anCyc + Wr)
    (by omega) (fun _ _ h => h)
  intro ans v vpc v6 vregs vframe vlo vl vh
  have lregs : RegsEq u (lowState v) digRegs := (vregs.trans (low_regs v)).mono (by decide)
  have lframe : Frame u (lowState v) digW := by intro x hx hw; rw [low_mem]; exact vframe x hx hw
  have lpc : (lowState v).pc = pcOf 72 := by simp only [lowState, blk2893.res, blk70.res, rv_simp]
  have lv : valOfWords ((lowState v).getReg .x1) ((lowState v).getReg .x2) = answerBytes 16 ans := by
    apply eq_of_two_words (answerBytes 16 ans) (by simp)
    simpa only [lowState, blk2893.res, blk70.res, rv_simp, readWords_ofNat_two] using vl.symm
  refine (Sim.steps (low_steps v vpc) (digAttempt sk m u (lowState v) hmem hx5 lpc lregs lframe
    _ (by simp) lv _ (24 + anCyc + Wr) ?_)).mono (by omega) (fun _ _ h => h)
  intro v1 v1pc r1 f1
  have v1regs : RegsEq u v1 digRegs := (lregs.trans r1).mono (by decide)
  have v1frame : Frame u v1 digW := (lframe.trans f1).mono (by
    intro x hx; simp only [digW, digTryW, anW] at hx ⊢; omega)
  have v118 : v1.getReg .x18 = 0 := by
    rw [r1.get .x18 (by decide)]
    simp only [lowState, blk2893.res, blk70.res, rv_simp]
  have hregs : RegsEq u (highState v1) digRegs := (v1regs.trans (high_regs v1)).mono (by decide)
  have hframe : Frame u (highState v1) digW := by intro x hx hw; rw [high_mem]; exact v1frame x hx hw
  have hpc : (highState v1).pc = pcOf 72 := by
    simp only [highState, blk2900.res, rv_simp]
  have hv : valOfWords ((highState v1).getReg .x1) ((highState v1).getReg .x2) = hiVal ans := by
    have preserved : v1.readWords (BitVec.ofNat 64 0x150) 2 = wordsOf (hiVal ans) := by
      rw [f1.readWords _ _ (by norm_num) (by intro i hi; simp only [digTryW, anW]; omega)]
      simpa only [readWords_ofNat_two, low_mem] using vh
    apply eq_of_two_words (hiVal ans) (by simp)
    simpa only [highState, branchState, blk2900.res, blk2897.res, blk137.res, rv_simp,
      readWords_ofNat_two] using preserved.symm
  refine (Sim.steps (high_steps v1 v1pc v118) (digAttempt sk m u (highState v1) hmem hx5
    hpc hregs hframe _ (by simp) hv rest (2 + Wr) ?_)).mono (by omega) (fun _ _ h => h)
  intro v2 v2pc r2 f2
  have v218 : v2.getReg .x18 = 1 := by
    rw [r2.get .x18 (by decide)]
    simp only [highState, blk2900.res, rv_simp]
  refine Sim.steps (branch_steps v2 v2pc) (hrest (branchState v2) ?_ ?_ ?_ ?_ ?_)
  · simp only [branchState, blk2897.res, blk137.res, rv_simp, v218]; decide
  · rw [(branch_regs v2).get .x6 (by decide), r2.get .x6 (by decide),
      (high_regs v1).get .x6 (by decide), r1.get .x6 (by decide), (low_regs v).get .x6 (by decide), v6]
  · exact ((hregs.trans r2).trans (branch_regs v2)).mono (by decide)
  · intro x hx hw
    rw [branch_mem]
    exact ((hframe.trans f2).mono (by intro x hx; simp only [digW, digTryW, anW] at hx ⊢; omega)) x hx hw
  · rw [branch_mem, f2.getMem (by norm_num) (by simp only [digTryW, anW]; omega), high_mem,
      f1.getMem (by norm_num) (by simp only [digTryW, anW]; omega), low_mem]
    exact vlo

theorem searchDigestPairs_succ (S mm : List Byte) (a f : Nat) :
    searchDigestPairs S mm a (f + 1) = (prf2 (rndInput S mm a) >>= fun p =>
      (liftM (HashSpec.query (addrFmt (digestInput p.1 mm))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible ans.toNat then pure (some (p.1, ans.toNat)) else
          (liftM (HashSpec.query (addrFmt (digestInput p.2 mm))) : OracleComp HashSpec _) >>= fun ans' =>
            if admissible ans'.toNat then pure (some (p.2, ans'.toNat))
            else searchDigestPairs S mm (a + 1) f) := by
  simp only [searchDigestPairs, digest, H, bind_assoc, pure_bind]

/-- Advance to the next pair, or fail when the fixed pair limit is exhausted. -/
theorem digNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 19)) (a : Nat)
    (ha : a < 2 ^ 19) (t : MachineState) (tpc : t.pc = pcOf 2898) (t6 : t.getReg .x6 = BitVec.ofNat 64 a)
    (tregs : RegsEq u t digRegs) (tframe : Frame u t digW)
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0x7b8)) = lo32 (u.getMem (BitVec.ofNat 64 0x7b8))) :
    ∃ t', Steps image t 3 3 t' ∧
      (a + 1 < 2 ^ 19 → DigInv u (a + 1) t') ∧ (a + 1 = 2 ^ 19 → t'.pc = pcOf 139) ∧
      RegsEq t t' [.x6] := by
  have hs0 := symRun_sound blk2898 codeAt_2898 t tpc (by simp only [blk2898.res, rv_simp])
  have hs1 := symRun_sound blk138 codeAt_138 (blk2898.res.toState t)
    (by simp only [blk2898.res, rv_simp]) (by simp only [blk138.res, rv_simp])
  have rr : RegsEq t (nextState t) [.x6] := by
    intro r hr
    simp only [nextState, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have mm : ∀ x, (nextState t).getMem x = t.getMem x := by
    intro x; simp only [nextState, blk138.res, blk2898.res, rv_simp]
  refine ⟨nextState t, hs0.trans hs1, ?_, ?_, rr⟩
  · intro h
    refine ⟨?_, ?_, h, (tregs.trans rr).mono (by decide), ?_, ?_⟩
    · simp only [nextState, blk138.res, blk2898.res, rv_simp, t6,
        tregs.get .x7 (by decide), hx7, ofNat_add_ofNat, ofNat_bne_ofNat]
      rw [if_pos (by simp; omega)]
    · simp only [nextState, blk138.res, blk2898.res, rv_simp, t6, ofNat_add_ofNat]
    · intro x hx hw; rw [mm]; exact tframe x hx hw
    · rw [mm]; exact tlo
  · intro h
    simp only [nextState, blk138.res, blk2898.res, rv_simp, t6,
      tregs.get .x7 (by decide), hx7, ofNat_add_ofNat, ofNat_bne_ofNat]
    rw [if_neg (by simp; omega)]

def digCyc : Nat := 60 + 2 * anCyc + 3

theorem digLoop_sim (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0)
    (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 19)) :
    ∀ fuel a t, a + (fuel + 1) = 2 ^ 19 → DigInv u a t →
      Sim image t ((fuel + 1) * digCyc + 2) (searchDigestPairs (toList sk) (toList m) a (fuel + 1))
        (DigPost u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a t ha hinv
    rw [searchDigestPairs_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ 5 ?_).mono (by unfold digCyc; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, -, hfail, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    have hs43 := symRun_sound blk139 codeAt_139 t'' (hfail (by omega)) (by simp only [blk139.res, rv_simp])
    have hc : blk139.res.cycles = 2 := rfl
    rw [hc] at hs43
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Val × Nat))) (Q := DigPost u) hs43
      ⟨by simp only [blk139.res, rv_simp], by simp only [blk139.res, rv_simp],
       by simp only [blk139.res, rv_simp]⟩)
    simpa [searchDigestPairs] using this
  | succ f ih =>
    intro a t ha hinv
    rw [searchDigestPairs_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ (3 + ((f + 1) * digCyc + 2)) ?_).mono
      (by unfold digCyc; ring_nf; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, hinv', -, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    exact Sim.steps hs (ih (a + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Sign
