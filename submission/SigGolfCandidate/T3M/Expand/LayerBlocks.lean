import SigGolfCandidate.T3M.Expand.Blocks

/-!
# `expand`: block specifications of `recover_layer` (stream E, instance E-S)

`recover_layer` (words 997 .. 1151) is Core's `recoverLayer` for the layer in the registers (`s0` lay, `s1` tree,
`s2` leaf, `s10` N, `s11` N4, `a5` H, `a6` the layer's signature piece, `s7` / `s8` the witness chain / Merkle block
of chain 0 / level 0): per chain the value is copied to `CHAIN+48` and the witness, hashed in place from its digit to
`2^w - 2`, its end stored in the leaf-pk block; the leaf pk; then the Merkle path with the siblings written to the
witness on the side given by the leaf bit; the root to `ENC`. One specification per symbolic block (the digit
`lbu` at word 1027 is stepped by hand).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)

set_option maxRecDepth 8192

/-- `CHAIN`: `0^16 | T1 | 0^16 | value` (the value hashed in place at `+48`). -/
abbrev CHAIN : Nat := 0x201A0
/-- `LEAFPK`: `end0 | T2 | end1 ..`. -/
abbrev LEAFPK : Nat := 0x20600

/-- Close `RegsExcept s (r.toState s) l` for a symbolic block (`ex_regs eblk_o.res`). -/
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

/-- Entry: the chain / leaf-pk headers' word 1 (`tree | leaf << 32`), the leaf-pk word 0 (tag 2), `I = 0`. -/
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

/-- `rl_chain`: done after `N` chains. -/
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

/-- The chain value `values[i]` (at `P + 16 i`) to `CHAIN+48` and to the witness chain block `W` (`+48`);
`W -= 64`; the digit address `DIGITS + i`. -/
theorem rl1011_spec (hpc : s.pc = pcOf 1011) (i P W : Nat) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5744)
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

/-- The digit `lbu s4, 0(t3)` at `DIGITS + i` (stepped by hand: an unaligned symbolic byte load). -/
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

/-- The end step `E = 7` (radix 8) or `3` (radix 4, `i < n4`). -/
theorem rl1028_spec (hpc : s.pc = pcOf 1028) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if n4 ≤ i then pcOf 1031 else pcOf 1030) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1028 codeAt_1028 s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h19, h27]
    rw [ex_slt i n4 hi hn]
    by_cases hc : n4 ≤ i
    · simp [hc, show ¬ i < n4 by omega]
    · simp [hc, show i < n4 by omega]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]

theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 3 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 codeAt_1030 s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · simp [eblk_1030.res, rv_simp]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]

/-- `rl_step`: the chain is done at step `E`. -/
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

/-- One chain step: the header word 0 `257 | lay << 16 | (256 i + step) << 32` at `CHAIN + 16`, the HASH arguments
`CHAIN`, 64, `CHAIN + 48`. -/
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

/-- `rl_end`: the leaf-pk slot offset `16 i` (`+16` past the header for `i ≥ 1`). -/
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

/-- The chain end (`CHAIN + 48`) into its leaf-pk slot `LEAFPK + x`; `I += 1`. -/
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

/-- The leaf-pk HASH arguments `LEAFPK`, `16 (N + 1)` rounded up to 64, `NOUT`. -/
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

/-- The path pointer `s6 = SIGB + 16 N`, `j = 0`. -/
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

/-- `rl_mk`: the path is done after `H` levels. -/
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

/-- The leaf bit `j` selects the side. -/
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

/-- Merkle level with leaf bit 1: the sibling (at `P`) to the witness `[M, M+16)` and to `NODE`, the node `NOUT`
to `NODE + 48`. -/
theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5744)
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

/-- Merkle level with leaf bit 0: the sibling to the witness `[M+48, M+64)` and to `NODE + 48`, the node `NOUT`
to `NODE`. -/
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5744)
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

/-- The Merkle node header: `769 | lay << 16` (tag 3), `tree | heap << 32` with `heap = 2^(h-j-1) + leaf >> (j+1)`;
the HASH arguments `NODE`, 64, `NOUT`. -/
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

/-- Next level: `s6 += 16`, `s8 -= 64`, `j += 1`. -/
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

/-- `rl_mk_done`: the root (`NOUT`) to `ENC`, return. -/
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
