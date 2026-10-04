import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.T3M.Expand.Basic

section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
set_option maxRecDepth 8192
abbrev CHAIN : Nat := 0x201A0
abbrev LEAFPK : Nat := 0x20600
macro "ex_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
theorem ex_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := ofNat_slt a b ha hb
theorem ex_beq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [this, h]
section blocks
variable (s : MachineState)
theorem rl997_spec (hpc : s.pc = pcOf 997) (lay tree leaf : Nat) (htree : tree < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = BitVec.ofNat 64 (tree + 2 ^ 32 * leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = BitVec.ofNat 64 (513 + 65536 * lay) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 24 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  refine ⟨_, symRun_sound eblk_997 codeAt_997 s hpc (by simp [eblk_997.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_997.res, E.eval]
  · simp [eblk_997.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_997.res]
    t3n [h9, h18]
    rw [if_neg (by decide), if_neg (by decide), ofNat_or_disjoint' tree (leaf * 4294967296) 32 htree (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_997.res]
    t3n [h9, h18]
    rw [if_neg (by decide), ofNat_or_disjoint' tree (leaf * 4294967296) 32 htree (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_997.res]
    t3n [h8]
    rw [ofNat_or_disjoint 513 (lay * 65536) 16 (by norm_num) (by omega)]
    congr 1; ring
  · ex_regs eblk_997.res
  · intro A hA hn
    simp only [CHAIN, LEAFPK] at hn
    simp only [Result.toState_getMem, eblk_997.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem rl1010_spec (hpc : s.pc = pcOf 1010) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if n ≤ i then pcOf 1063 else pcOf 1011) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1010 codeAt_1010 s hpc (by simp [eblk_1010.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1010.res, E.eval, CmpOp.eval, h19, h26]
    rw [ex_slt i n hi hn]
    by_cases hc : n ≤ i
    · simp [hc, show ¬ i < n by omega]
    · simp [hc, show i < n by omega]
  · ex_regs eblk_1010.res
  · intro A _ _; simp [eblk_1010.res, rv_simp]
theorem rl1011_spec (hpc : s.pc = pcOf 1011) (i P W : Nat) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616)
    (hP8 : P % 8 = 0) (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h16 : s.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 W) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 1027 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getMem (BitVec.ofNat 64 (W + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (W + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ t.getReg .x28 = BitVec.ofNat 64 (i + DIGITS) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) := by
  have ea : ∀ k, BitVec.ofNat 64 i <<< ((4#64 : Word).toNat % 64) + BitVec.ofNat 64 P + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (P + 16 * i + k) := fun k => by
    rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; ring
  have hne : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
    fun x y hx hy h he => h ((ofNat_inj hx hy).mp he)
  have hv : ∀ x : Nat, x % 8 = 0 → x + 8 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 8 = true := fun x h1 h2 => by
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  refine ⟨_, symRun_sound eblk_1011 codeAt_1011 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1011.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h19, h16, h23,
      ea, ofNat_add_ofNat, show (56#64 : Word) = BitVec.ofNat 64 56 from rfl,
      show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, show (131536#64 : Word) = BitVec.ofNat 64 131536 from rfl,
      show (131544#64 : Word) = BitVec.ofNat 64 131544 from rfl]
    refine ⟨hv _ (by omega) (by omega), hv _ (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hv _ (by omega) (by omega), hv _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_1011.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eblk_1011.res, CHAIN]
      t3n [h19, h16, h23]
      (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h23]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (show W < 2 ^ 64 by omega), toNat_ofNat_lt (show W - 64 < 2 ^ 64 by omega)]
    rw [show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_1011.res
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, eblk_1011.res, rv_simp, h23, ofNat_add_ofNat]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem lbu_word1027 : decodeInstruction (0x000e4a03 : BitVec 32) = some (.base (.LBU .x20 .x28 0)) := rfl
theorem rl1027_spec (hpc : s.pc = pcOf 1027) (i d : Nat) (hi : i < 64) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (i + DIGITS))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1028 ∧ t.getReg .x20 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have ea : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (DIGITS + i) := by
    rw [h28, show signExtend12 (0 : BitVec 12) = 0 from rfl, add_zero, Nat.add_comm]
  have hv : accessValid (s.getReg .x28 + signExtend12 0) 1 = true := by
    rw [ea, accessValid_iff, toNat_ofNat_lt (by simp only [DIGITS]; omega)]; simp only [MEMORY_BYTES, DIGITS]; omega
  refine ⟨_, steps_lbu codeAt_1027 hpc lbu_word1027 hv, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = _; rw [hpc, pcOf_add4]
  · have e2 : ∀ (u : MachineState) (v pc : Word), ((u.setReg .x20 v).setPC pc).getReg .x20 = v :=
      fun u v pc => rfl
    rw [e2, ea, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show ((s.setReg .x20 _).setPC _).getReg r = _
    cases r <;> simp_all [MachineState.getReg, MachineState.setReg, MachineState.setPC]
  · intro A _ _; rfl
theorem rl1028_spec (hpc : s.pc = pcOf 1028) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1030 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt hlay] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound eblk_1028 codeAt_1028 s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h8, hz]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]
theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1158 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 codeAt_1030 s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]
theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf 1160 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 3 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1158 codeAt_1158 s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1158.res, E.eval, CmpOp.eval, h19, h27]
    rw [ex_slt i n4 hi hn]
    by_cases hi' : i < n4 <;> simp [hi']
  · simp [eblk_1158.res, rv_simp]
  · ex_regs eblk_1158.res
  · intro A _ _; simp [eblk_1158.res, rv_simp]
theorem rl1160_spec (hpc : s.pc = pcOf 1160) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1160 codeAt_1160 s hpc (by simp [eblk_1160.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1160.res, E.eval]
  · simp [eblk_1160.res, rv_simp]
  · ex_regs eblk_1160.res
  · intro A _ _; simp [eblk_1160.res, rv_simp]
theorem rl1031_spec (hpc : s.pc = pcOf 1031) (st e : Nat) (hs : st < 2 ^ 63) (he : e < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if e ≤ st then pcOf 1049 else pcOf 1032) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1031 codeAt_1031 s hpc (by simp [eblk_1031.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1031.res, E.eval, CmpOp.eval, h20, h21]
    rw [ex_slt st e hs he]
    by_cases hc : e ≤ st
    · simp [hc, show ¬ st < e by omega]
    · simp [hc, show st < e by omega]
  · ex_regs eblk_1031.res
  · intro A _ _; simp [eblk_1031.res, rv_simp]
theorem rl1032_spec (hpc : s.pc = pcOf 1032) (lay i st : Nat) (hlay : lay < 256) (hpos : 256 * i + st < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 1046 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = BitVec.ofNat 64 (257 + 65536 * lay + 2 ^ 32 * (st + 256 * i)) ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧ Frame s t (fun A => A = CHAIN + 16) := by
  refine ⟨_, symRun_sound eblk_1032 codeAt_1032 s hpc (by simp [eblk_1032.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1032.res, E.eval]
  · simp only [Result.toState_getMem, eblk_1032.res]
    t3n [h8, h19, h20]
    rw [ofNat_or_disjoint (lay * 65536) ((i * 256 + st) * 4294967296) 32 (by omega) (by omega),
      ofNat_or_disjoint 257 _ 16 (by omega) (by omega)]
    congr 1
    ring
  · simp [eblk_1032.res, rv_simp]
  · simp [eblk_1032.res, rv_simp]
  · simp [eblk_1032.res, rv_simp]
  · ex_regs eblk_1032.res
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, eblk_1032.res]
    t3n []
    rw [if_neg (by omega)]
theorem fetch_1046 (hpc : s.pc = pcOf 1046) : fetch image s = some (.base .ECALL) :=
  (codeAt_1046.fetch s hpc).trans rfl
theorem rl1047_spec (hpc : s.pc = pcOf 1047) (st : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1047 codeAt_1047 s hpc (by simp [eblk_1047.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1047.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1047.res, rv_simp, h20, ofNat_add_ofNat]
  · ex_regs eblk_1047.res
  · intro A _ _; simp [eblk_1047.res, rv_simp]
theorem rl1049_spec (hpc : s.pc = pcOf 1049) (i : Nat) (hi : i < 2 ^ 59)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 0 then pcOf 1052 else pcOf 1051) ∧
      t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1049 codeAt_1049 s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1049.res, E.eval, CmpOp.eval, h19]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq i 0 (by omega) (by norm_num)]
    by_cases hc : i = 0
    · simp [hc]
    · simp [hc]
  · simp only [Result.toState_getReg, eblk_1049.res, rv_simp, h19]
    t3n []; congr 1; ring
  · ex_regs eblk_1049.res
  · intro A _ _; simp [eblk_1049.res, rv_simp]
theorem rl1051_spec (hpc : s.pc = pcOf 1051) (x : Nat) (h28 : s.getReg .x28 = BitVec.ofNat 64 x) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1052 ∧ t.getReg .x28 = BitVec.ofNat 64 (x + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1051 codeAt_1051 s hpc (by simp [eblk_1051.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1051.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1051.res, rv_simp, h28, ofNat_add_ofNat]
  · ex_regs eblk_1051.res
  · intro A _ _; simp [eblk_1051.res, rv_simp]
theorem rl1052_spec (hpc : s.pc = pcOf 1052) (i x : Nat) (hx8 : x % 8 = 0) (hx : LEAFPK + x + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 x) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + x ∨ A = LEAFPK + x + 8) := by
  refine ⟨_, symRun_sound eblk_1052 codeAt_1052 s hpc (by
      simp only [eblk_1052.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, ofNat_add_ofNat,
        show (132616#64 : Word) = BitVec.ofNat 64 132616 from rfl,
        show (132608#64 : Word) = BitVec.ofNat 64 132608 from rfl, accessValid_iff, MEMORY_BYTES,
        toNat_ofNat_lt (show x + 132616 < 2 ^ 64 by simp only [LEAFPK] at hx; omega),
        toNat_ofNat_lt (show x + 132608 < 2 ^ 64 by simp only [LEAFPK] at hx; omega)]
      simp only [LEAFPK] at hx; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1052.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1052.res, rv_simp, h19, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · ex_regs eblk_1052.res
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, eblk_1052.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]
theorem rl1063_spec (hpc : s.pc = pcOf 1063) (n : Nat) (hn : n < 2 ^ 32)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf 1072 ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1063 codeAt_1063 s hpc (by simp [eblk_1063.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1063.res, E.eval]
  · simp [eblk_1063.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1063.res, rv_simp, h26]
    have e1 : (BitVec.ofNat 64 n + 1#64) <<< ((4#64 : Word).toNat % 64) + 63#64 =
        BitVec.ofNat 64 (16 * (n + 1) + 63) := by
      rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
        show (63#64 : Word) = BitVec.ofNat 64 63 from rfl, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat]
      congr 1; ring
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt (show 16 * (n + 1) + 63 < 2 ^ 64 by omega),
      toNat_ofNat_lt (show (16 * (n + 1) + 63) / 64 * 64 < 2 ^ 64 by omega),
      show (18446744073709551552#64 : Word).toNat = (2 ^ 58 - 1) * 2 ^ 6 from rfl]
    have key : ∀ x : Nat, x < 2 ^ 64 → x &&& ((2 ^ 58 - 1) * 2 ^ 6) = x / 64 * 64 := by
      intro x hx
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_mul_two_pow, show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_mul_two_pow,
        Nat.testBit_two_pow_sub_one]
      by_cases hk : 6 ≤ k
      · simp only [hk, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
        by_cases hk2 : k - 6 < 58
        · simp [hk2, show k - 6 + 6 = k by omega]
        · simp only [hk2, decide_false, Bool.and_false]
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      · simp [hk]
    exact key _ (by omega)
  · simp [eblk_1063.res, rv_simp]
  · ex_regs eblk_1063.res
  · intro A _ _; simp [eblk_1063.res, rv_simp]
theorem fetch_1072 (hpc : s.pc = pcOf 1072) : fetch image s = some (.base .ECALL) :=
  (codeAt_1072.fetch s hpc).trans rfl
theorem rl1073_spec (hpc : s.pc = pcOf 1073) (P n : Nat) (hP : P + 16 * n < 2 ^ 64)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 P) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 (P + 16 * n) ∧ RegsExcept s t [.x20, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1073 codeAt_1073 s hpc (by simp [eblk_1073.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1073.res, E.eval]
  · simp [eblk_1073.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1073.res, rv_simp, h16, h26]
    t3n []; congr 1; ring
  · ex_regs eblk_1073.res
  · intro A _ _; simp [eblk_1073.res, rv_simp]
theorem rl1076_spec (hpc : s.pc = pcOf 1076) (j hh : Nat) (hj : j < 2 ^ 63) (hh' : hh < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if hh ≤ j then pcOf 1143 else pcOf 1077) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1076 codeAt_1076 s hpc (by simp [eblk_1076.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1076.res, E.eval, CmpOp.eval, h20, h15]
    rw [ex_slt j hh hj hh']
    by_cases hc : hh ≤ j
    · simp [hc, show ¬ j < hh by omega]
    · simp [hc, show j < hh by omega]
  · ex_regs eblk_1076.res
  · intro A _ _; simp [eblk_1076.res, rv_simp]
theorem rl1077_spec (hpc : s.pc = pcOf 1077) (leaf j : Nat) (hl : leaf < 2 ^ 64) (hj : j < 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if leaf / 2 ^ j % 2 = 0 then pcOf 1099 else pcOf 1080) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1077 codeAt_1077 s hpc (by simp [eblk_1077.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1077.res, E.eval, CmpOp.eval, BinOp.eval, h18, h20]
    rw [toNat_ofNat_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj, ofNat_shr _ _ hl, ofNat_and1,
      show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ 0 (by omega) (by norm_num)]
    by_cases hc : leaf / 2 ^ j % 2 = 0
    · simp [hc]
    · simp [hc]
  · ex_regs eblk_1077.res
  · intro A _ _; simp [eblk_1077.res, rv_simp]
theorem ex_ne (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
  fun he => h ((ofNat_inj hx hy).mp he)
theorem ex_valid (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps image s 19 19 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 M) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M ∨ A = M + 8 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1080 codeAt_1080 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1080.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [show (131584 : Nat) = NODE from rfl, show (131592 : Nat) = NODE + 8 from rfl]; exact ex_ne _ _ (by omega) (by omega) (by omega))
        | skip
  · simp [Result.toState_pc, eblk_1080.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1080.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1080.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1080.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M + 48 ∨ A = M + 56 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1099 codeAt_1099 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1099.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
  · simp [Result.toState_pc, eblk_1099.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1099.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1099.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1099.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem rl1117_spec (hpc : s.pc = pcOf 1117) (lay tree leaf hh j : Nat) (hlay : lay < 256) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 21 21 t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (769 + 65536 * lay + 2^32 * tree) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  refine ⟨_, symRun_sound eblk_1117 codeAt_1117 s hpc (by simp [eblk_1117.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1117.res, E.eval]
  · simp only [Result.toState_getMem, eblk_1117.res]
    t3n [h8, h9]
    rw [if_neg (by decide), ofNat_or_disjoint 769 (lay * 65536) 16 (by norm_num) (by omega),
      ofNat_or_disjoint' (lay * 65536 + 769) (tree * 4294967296) 32 (by omega) (by omega)]
    congr 1; ring
  · simp only [Result.toState_getMem, eblk_1117.res, NODE]
    t3n [h9, h15, h20, h18]
    have e1 : (BitVec.ofNat 64 hh - BitVec.ofNat 64 j - 1#64).toNat % 64 = hh - j - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_sub, toNat_ofNat_lt (show hh < 2 ^ 64 by omega),
        toNat_ofNat_lt (show j < 2 ^ 64 by omega), show (1#64 : Word).toNat = 1 from rfl]
      omega
    have e2 : (j + 1) % 18446744073709551616 % 64 = j + 1 := by omega
    have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq : leaf / 2 ^ (j + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
    rw [e1, e2, ofNat_shr _ _ (by omega), Nat.one_mul, ofNat_add_ofNat]
  · simp [eblk_1117.res, rv_simp]
  · simp [eblk_1117.res, rv_simp]
  · simp [eblk_1117.res, rv_simp]
  · ex_regs eblk_1117.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1117.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
theorem fetch_1138 (hpc : s.pc = pcOf 1138) : fetch image s = some (.base .ECALL) :=
  (codeAt_1138.fetch s hpc).trans rfl
theorem rl1139_spec (hpc : s.pc = pcOf 1139) (P M j : Nat) (hM : 64 ≤ M) (hM' : M < 2 ^ 64)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x22, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1139 codeAt_1139 s hpc (by simp [eblk_1139.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1139.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h22, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt hM', toNat_ofNat_lt (show M - 64 < 2 ^ 64 by omega),
      show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h20, ofNat_add_ofNat]
  · ex_regs eblk_1139.res
  · intro A _ _; simp [eblk_1139.res, rv_simp]
theorem rl1143_spec (hpc : s.pc = pcOf 1143) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_1143 codeAt_1143 s hpc (by simp [eblk_1143.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1143.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · ex_regs eblk_1143.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_1143.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]
end blocks
end SigGolfCandidate.T3M.Expand
end

section


namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
theorem chainInput_length' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, T3.zero16]
theorem wordsOf_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (pad64 (chainInput lay tree leaf i step v)) =
      [0, 0, BitVec.ofNat 64 (hdr0 1 lay.val tree (step + 256 * i)), BitVec.ofNat 64 (hdr1 tree leaf),
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_length'])]
  unfold chainInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, T3.zero16]), wordsOf_append _ _ (by simp [bytesLE_length, T3.zero16]),
    wordsOf_append _ _ (by simp [T3.zero16]), wordsOf_zero16, wordsOf_header, wordsOf_bytesLE16]
  rfl
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
  w24 : t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = BitVec.ofNat 64 (hdr1 tree leaf)
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
def StepW (A : Nat) : Prop := A = CHAIN + 16 ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x19 := by rw [hr.get hl.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
  z32 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z32
  z40 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z40
  w24 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.w24
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
theorem chain_step (lay : Layer) (tree leaf i st e : Nat) (htree : tree < 2 ^ 32) (hst : st < e) (he : e ≤ 7)
    (hi : 256 * i + 256 ≤ 2 ^ 32) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim image sk t 25 (shortHash (chainInput lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, m16, a10, a11, a12, r2, f2⟩ := rl1032_spec t1 p1 lay.val i st (by omega) (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have fr : ∀ A, A < 2 ^ 64 → A ≠ CHAIN + 16 → t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => f12.get hA hn
  have hq : hashInput t2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
    refine hashInput_toQ t2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
      a10 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) a11 (by norm_num) ?_
    rw [readWords_eight, wordsOf_chainInput', fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega), m16,
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      hc.z0, hc.z8, hc.w24, hc.z32, hc.z40, hv.1,
      show CHAIN + 48 + 8 = CHAIN + 56 from rfl, hv.2, hdr0_eq 1 lay.val tree (st + 256 * i) (by norm_num) (by omega)
        htree (by omega)]
  have hv2 : hashArgumentsValid t2 = true :=
    hashArgs_const t2 CHAIN 64 (CHAIN + 48) a10 a11 a12 (by simp only [CHAIN]) (by norm_num) (by simp only [CHAIN]; omega)
      (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
  refine (TBSim.steps (s1.trans s2) (tb_shortHash_bind' (W := 2) (fetch_1046 t2 p2)
    (by rw [r2.get (by simp), r1.get (by simp)]; exact hc.x5) hv2 hq (fun a => ?_))).mono
    (by rw [blocks_chainInput']) (fun _ _ h => h)
  have p3 : (writeHash t2 a).pc = pcOf 1047 := by rw [pc_writeHash, p2, pcOf_add4]
  obtain ⟨u, s4, p4, u20, r4, f4⟩ := rl1047_spec (writeHash t2 a) p3 st
    (by rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h20)
  refine TBSim.steps s4 (TBSim.pure ⟨p4, u20, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [r4.get (by simp), getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h21
  · have fw := Frame.writeHash t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    have fall : Frame t u StepW := ((f12.trans fw).trans f4).mono (fun A _ h => by
      unfold StepW; rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
    refine hc.frame (l := stepRegs) (by simp [stepRegs]) ?_ fall
    intro r hr
    rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), getReg_writeHash,
      r2.get (not_mem_of_sub (by simp [stepRegs]) hr), r1.get (by simp)]
  · have hd := DigAt.writeHash_lo t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    exact ⟨by rw [f4.get (by simp only [CHAIN]; omega) (by simp)]; exact hd.1,
      by rw [f4.get (by simp only [CHAIN]; omega) (by simp)]; exact hd.2⟩
  · intro r hr
    rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), getReg_writeHash,
      r2.get (not_mem_of_sub (by simp [stepRegs]) hr), r1.get (by simp)]
  · have fw := Frame.writeHash t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    exact ((f12.trans fw).trans f4).mono (fun A _ h => by
      unfold StepW; rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
theorem chain_loop (lay : Layer) (tree leaf i d e : Nat) (htree : tree < 2 ^ 32) (hd : d ≤ e) (he : e ≤ 7)
    (hi : 256 * i + 256 ≤ 2 ^ 32) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim image sk t ((e - d) * 25 + 1) (chain lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := image) (sk := sk) d (e - d)
    (fun value step => shortHash (chainInput lay tree leaf i step value)) v Inv 25
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step lay tree leaf i (d + j) e htree (by omega) he hi w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : chain lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => shortHash (chainInput lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)
def slotOff (c : Nat) : Nat := if c = 0 then 0 else 16 * c + 16
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8 ∨ A = W + 48 ∨ A = W + 56
def endpoint (lay : Layer) (i n4 : Nat) : Nat :=
  if lay = 0 then (if i < n4 then 4 else 3) else 7
def endpointExtra (lay : Layer) (i n4 : Nat) : Nat :=
  if lay = 0 then (if i < n4 then 5 else 3) else 0
theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat) (htree : tree < 2 ^ 32) (hi : i < n) (hn : n ≤ 58)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim image sk t 211 (chain lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW i W)) := by
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps image t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec ta pa i n4 (by omega) (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19) (by rw [rr.get (by simp)]; exact h27)
      by_cases hi' : i < n4
      · rw [if_pos hi'] at pb
        obtain ⟨tc, qc, pc, xc, rc, fc⟩ := rl1160_spec tb pb
        refine ⟨tc, ?_, pc, ?_, ?_, ?_⟩
        · simpa only [endpointExtra, if_pos hl, if_pos hi'] using (qa.trans qb).trans qc
        · simpa only [he, endpoint, if_pos hl, if_pos hi'] using xc
        · exact ((ra.trans rb).trans rc).mono (by simp)
        · exact ((fa.trans fb).trans fc).mono (by simp)
      · rw [if_neg hi'] at pb
        refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
        · simpa only [endpointExtra, if_pos hl, if_neg hi'] using qa.trans qb
        · simpa only [he, endpoint, if_pos hl, if_neg hi'] using xb
        · exact (ra.trans rb).mono (by simp)
        · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8
      z32 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z32
      z40 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z40
      w24 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.w24 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (sk := sk) lay tree leaf i d e htree hd he7 (by omega) v t5 p5 hc5 x20' x21' hv5
  have hprog : chain lay tree leaf i d (e - d) v = (chain lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * 25 + 1 + 14) ≤ 211 := by
    rw [he]; unfold endpointExtra endpoint
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 14) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u1, q1, pu1, y28, ry1, fy1⟩ := rl1049_spec u pu i (by omega) cu.x19
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ : ∃ u2, Steps image u1 (if i = 0 then 0 else 1) (if i = 0 then 0 else 1) u2 ∧
      u2.pc = pcOf 1052 ∧ u2.getReg .x28 = BitVec.ofNat 64 (slotOff i) ∧ RegsExcept u1 u2 [.x28] ∧
      Frame u1 u2 (fun _ => False) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at pu1
      exact ⟨u1, by simpa [h0] using Steps.refl u1, pu1, by rw [y28, slotOff, if_pos h0, h0], RegsExcept.refl _ _,
        Frame.refl _ _⟩
    · rw [if_neg h0] at pu1
      obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1051_spec u1 pu1 (16 * i) y28
      exact ⟨u2, by simpa [h0] using q2, pu2, by rw [z28, slotOff, if_neg h0], ry2, fy2⟩
  have hslot8 : slotOff i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec u2 pu2 i (slotOff i) hslot8 hslot z28
    (by rw [ry2.get (by simp), ry1.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := (fy1.trans fy2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have hslotC : ∀ A, (A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q1.trans (q2.trans q3)) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x8
        x19 := w19
        z0 := ?_, z8 := ?_, z32 := ?_, z40 := ?_, w24 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8 | exact cu.z32 | exact cu.z40 | exact cu.w24
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry1.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]
def ChW (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff c ∨ A = LEAFPK + slotOff c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
theorem not_ChW_of {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 80 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
theorem not_ChW_hdr {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24 ∨
    A = LEAFPK + 880 ∨ A = LEAFPK + 888) (hk : k ≤ 54) : ¬ ChW WC k A := by
  unfold ChW StepW
  rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
    first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW WC ends.length)
end chain
end SigGolfCandidate.T3M.Expand
end
