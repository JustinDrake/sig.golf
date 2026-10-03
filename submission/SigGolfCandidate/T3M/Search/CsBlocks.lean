import SigGolfCandidate.T3M.Search.Blocks
import SigGolfCandidate.T3M.Search.Decode

/-!
# `counter_search`: block specifications (stream E; kernel at base 354 or 543)

`counter_search` (kernel offsets 103..469; arguments `s0 = lay`, `s1 = tree`, `s2 = leaf`,
`a7 = target`, `s10 = chainCount`, `s11 = 49 | 0`, the message in the first 16 bytes of the
encoding block `ENC`): headers into `ENC + 16`, `ENC + 24`; per trial `I = s3 < 2^22`: `sw I` into
`ENC + 32`, HASH the block into `EOUT`, range check and unrolled digit sum (lower layers: 42
radix-8 digits, `target - S ∈ [0, 8)`; top: 49 radix-4 + 9 radix-8 digits, `S = 126`), on failure
`I += 1`; on success the digits are written as bytes to `DIGITS` (lower layers also the checksum
digit) and the kernel returns with `s3 = I`. `I = 2^22` halts with `HALT(1)` (`fail`).
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## Word facts -/

theorem ext_shr_ofNat (v : BitVec 128) (base k : Nat) (hk : k < 64) :
    v.extractLsb' base 64 >>> k = BitVec.ofNat 64 (v.toNat / 2 ^ (base + k) % 2 ^ (64 - k)) := by
  have := ext_shr_mask v base k (64 - k) (by omega)
  rw [← this]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases h : i < 64 - k
  · simp [h]
  · simp [h, show ¬ k + i < 64 by omega]

theorem ofNat_sub_ult8 (T S : Nat) (hT : T < 2 ^ 63) (hS : S < 2 ^ 63) :
    (BitVec.ofNat 64 T - BitVec.ofNat 64 S).ult 8#64 = decide (S ≤ T ∧ T - S < 8) := by
  simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show T < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega)]
  by_cases h : S ≤ T
  · rw [show 2 ^ 64 - S + T = 2 ^ 64 + (T - S) by omega, Nat.add_mod_left,
      Nat.mod_eq_of_lt (show T - S < 2 ^ 64 by omega)]
    simp [h]
  · rw [Nat.mod_eq_of_lt (show 2 ^ 64 - S + T < 2 ^ 64 by omega)]
    simp only [h, false_and, decide_false]
    simp; omega

theorem merge_w0_small (x i : Nat) (hx : x < 2 ^ 32) (hi : i < 2 ^ 32) :
    replaceWord32 (BitVec.ofNat 64 x) 0 ((BitVec.ofNat 64 i).truncate 32) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [replaceWord32, Nat.zero_div, Nat.zero_mul, BitVec.shiftLeft_zero,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth, hj, decide_true, Bool.true_and]
  by_cases h : j < 32
  · have : (0xFFFFFFFF : Nat).testBit j = true := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp [h]
    simp [this, h]
  · have h1 : (0xFFFFFFFF : Nat).testBit j = false := by
      rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp; omega
    have h2 : x.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    have h3 : i.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, h2, h3, h]

section blocks
variable {image : Image} {b : Nat}

/-- Entry: the header doublewords of the encoding block, `s3 = 0`. -/
theorem cs103_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 103))
    (lay tree leaf : Nat) (hl : lay < 4) (ht : tree < 2 ^ 32) (hf : leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf (b + 113) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 lay tree 0) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 tree leaf) ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = ENC + 16 ∨ A = ENC + 24) := by
  refine ⟨_, symRun_sound (run_103 hK.2) (codeAt_k_103 hK) s hpc
    (by simp [st_103, blk354_103.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_103, blk354_103.res, E.eval]
  · simp only [Result.toState_getMem, st_103, blk354_103.res]
    t3n [h8, ENC]
    rw [hdr0_eq 4 lay tree 0 (by omega) (by omega) ht (by omega),
      ofNat_or_disjoint 1025 (lay * 65536) 16 (by decide) (by omega)]
    congr 1; omega
  · simp only [Result.toState_getMem, st_103, blk354_103.res]
    t3n [h9, h18, ENC]
    rw [hdr1_eq tree leaf ht hf, ofNat_or_disjoint' tree (leaf * 4294967296) 32 ht (by omega)]
    congr 1; omega
  · simp [st_103, blk354_103.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_103, blk354_103.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_103, blk354_103.res]
    t3n []
    simp only [ENC] at hn
    rw [if_neg (by omega), if_neg (by omega)]

/-- `cs_loop`: `I = 2^22` fails. -/
theorem cs113_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 113)) (i : Nat)
    (hi : i ≤ 2 ^ 22) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 22 then pcOf (b + 0) else pcOf (b + 115)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_113 hK.2) (codeAt_k_113 hK) s hpc (by simp [st_113, blk354_113.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_113, rebase, blk354_113.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 22
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 4194304#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_113, blk354_113.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_113, blk354_113.res, rv_simp]

/-- `fail`: `t0 = 1`, `a0 = 1`, at the `HALT`. -/
theorem cs0_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧
      t.getReg .x10 = BitVec.ofNat 64 1 ∧ fetch image t = some (.base .ECALL) := by
  refine ⟨_, symRun_sound (run_0 hK.2) (codeAt_k_0 hK) s hpc (by simp [st_0, blk354_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, blk354_0.res, E.eval]
  · simp [st_0, blk354_0.res, rv_simp]
  · simp [st_0, blk354_0.res, rv_simp]
  · rw [(codeAt_k_2 hK).fetch _ (by simp [pcE_0, blk354_0.res, E.eval])]; rfl

/-- The counter into the encoding block, the HASH arguments. -/
theorem cs115_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 115)) (i x : Nat)
    (hi : i < 2 ^ 32) (hx : x < 2 ^ 32) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h32 : s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf (b + 123) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i ∧
      t.getReg .x10 = BitVec.ofNat 64 ENC ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 EOUT ∧
      RegsExcept s t [.x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = ENC + 32) := by
  refine ⟨_, symRun_sound (run_115 hK.2) (codeAt_k_115 hK) s hpc
    (by simp [st_115, blk354_115.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_115, blk354_115.res, E.eval]
  · simp only [Result.toState_getMem, st_115, blk354_115.res]
    t3n [h19]
    simp only [ENC, Nat.reduceAdd] at h32
    rw [h32, merge_w0_small x i hx hi]
  · simp [st_115, blk354_115.res, rv_simp]
  · simp [st_115, blk354_115.res, rv_simp]
  · simp [st_115, blk354_115.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_115, blk354_115.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_115, blk354_115.res]
    t3n []
    simp only [ENC] at hn
    rw [if_neg (by omega)]

/-- The answer doublewords into `t1`, `t2`, `s9 = 0`; dispatch on the layer. -/
theorem cs124_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 124)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = (if lay = 0 then pcOf (b + 263) else pcOf (b + 130)) ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 EOUT) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 (EOUT + 8)) ∧
      t.getReg .x25 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x6, .x7, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_124 hK.2) (codeAt_k_124 hK) s hpc
    (by simp [st_124, blk354_124.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_124, rebase, blk354_124.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 lay == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · simp [st_124, blk354_124.res, rv_simp]
  · simp [st_124, blk354_124.res, rv_simp]
  · simp [st_124, blk354_124.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_124, blk354_124.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_124, blk354_124.res, rv_simp]

theorem ext64_shr_eq_zero (v : BitVec 128) (k : Nat) (hk : k < 64) :
    (v.extractLsb' 64 64 >>> k = 0#64) ↔ v.toNat < 2 ^ (64 + k) := by
  rw [ext_shr_ofNat v 64 k hk, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]
  have hv := v.isLt
  have h1 : v.toNat / 2 ^ (64 + k) < 2 ^ (64 - k) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show 64 - k + (64 + k) = 128 by omega]; exact hv
  have h2 : v.toNat / 2 ^ (64 + k) < 2 ^ 64 := lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [Nat.mod_eq_of_lt h1, Nat.zero_mod]
  rw [Nat.mod_eq_of_lt (show v.toNat / 2 ^ (64 + k) < 18446744073709551616 from h2),
    Nat.div_eq_zero_iff_lt (by positivity)]

/-- Lower layers: the range check `v < 2^126`. -/
theorem cs130_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 130)) (v : BitVec 128)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if v.toNat < 2 ^ 126 then pcOf (b + 132) else pcOf (b + 468)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_130 hK.2) (codeAt_k_130 hK) s hpc (by simp [st_130, blk354_130.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_130, rebase, blk354_130.res, E.eval, CmpOp.eval, BinOp.eval, h7,
      BitVec.toNat_ofNat, Nat.reduceMod]
    have := ext64_shr_eq_zero v 62 (by decide)
    rw [show (64 + 62 : Nat) = 126 from rfl] at this
    simp only [Nat.reducePow, Nat.reduceMod, bne_iff_ne, ne_eq, this]
    split_ifs <;> first | rfl | omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_130, blk354_130.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_130, blk354_130.res, rv_simp]

/-- Top layer: the range check `v < 2^125`. -/
theorem cs263_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 263)) (v : BitVec 128)
    (h7 : s.getReg .x7 = v.extractLsb' 64 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if v.toNat < 2 ^ 125 then pcOf (b + 265) else pcOf (b + 468)) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_263 hK.2) (codeAt_k_263 hK) s hpc (by simp [st_263, blk354_263.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_263, rebase, blk354_263.res, E.eval, CmpOp.eval, BinOp.eval, h7,
      BitVec.toNat_ofNat, Nat.reduceMod]
    have := ext64_shr_eq_zero v 61 (by decide)
    rw [show (64 + 61 : Nat) = 125 from rfl] at this
    simp only [Nat.reducePow, Nat.reduceMod, bne_iff_ne, ne_eq, this]
    split_ifs <;> first | rfl | omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_263, blk354_263.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_263, blk354_263.res, rv_simp]

/-- Lower layers: the digit sum `S` into `s9`, the check `S ≤ target`, `target - S < 8`. -/
theorem cs132_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 132)) (v : BitVec 128)
    (T : Nat) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 0) (h17 : s.getReg .x17 = BitVec.ofNat 64 T) :
    ∃ t, Steps image s 130 130 t ∧
      t.pc = (if (lowDigits v).sum ≤ T ∧ T - (lowDigits v).sum < 8 then pcOf (b + 262) else pcOf (b + 468)) ∧
      t.getReg .x25 = BitVec.ofNat 64 (lowDigits v).sum ∧
      RegsExcept s t [.x25, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  have hS : (lowDigits v).sum < 2 ^ 63 := by
    have : ∀ x ∈ lowDigits v, x ≤ 7 := by
      intro x hx; simp only [lowDigits, List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; omega
    have := List.sum_le_card_nsmul (lowDigits v) 7 this
    rw [lowDigits_length] at this; simp at this; omega
  have hsum : s.getReg .x25 + (v.extractLsb' 0 64 &&& 7#64) + (v.extractLsb' 0 64 >>> 3 &&& 7#64) = s.getReg .x25 + (v.extractLsb' 0 64 &&& 7#64) + (v.extractLsb' 0 64 >>> 3 &&& 7#64) := rfl
  refine ⟨_, symRun_sound (run_132 hK.2) (codeAt_k_132 hK) s hpc (by simp [st_132, blk354_132.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_132, rebase, blk354_132.res, E.eval, CmpOp.eval, BinOp.eval, h6, h7, h25,
      h17]
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, ext_and7, ext_shr_and7, cross_low,
      ofNat_add_ofNat, Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, ← lowDigits_sum]
    rw [ofNat_sub_ult8 _ _ hT hS]
    by_cases h : (lowDigits v).sum ≤ T ∧ T - (lowDigits v).sum < 8
    · simp [h]
    · simp [h]
  · simp only [Result.toState_getReg, st_132, blk354_132.res]
    simp only [rv_simp, h6, h7, h25]
    simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, ext_and7, ext_shr_and7, cross_low,
      ofNat_add_ofNat, Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff, ← lowDigits_sum]
  · intro r hr; simp at hr; cases r <;> simp_all [st_132, blk354_132.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_132, blk354_132.res, rv_simp]

/-- Lower layers: `jal cs_ok`. -/
theorem cs262_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 262)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 438) ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_262 hK.2) (codeAt_k_262 hK) s hpc (by simp [st_262, blk354_262.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcE_262, blk354_262.res, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [st_262, blk354_262.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_262, blk354_262.res, rv_simp]

/-- `cs_next`: `I += 1`. -/
theorem cs468_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 468)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 113) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_468 hK.2) (codeAt_k_468 hK) s hpc (by simp [st_468, blk354_468.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_468, blk354_468.res, E.eval]
  · simp only [Result.toState_getReg, st_468, blk354_468.res]; t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [st_468, blk354_468.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_468, blk354_468.res, rv_simp]

/-- `cs_ok`: `s5 = s10` (top) or `s10 - 1` (lower; the checksum digit is written separately). -/
theorem cs438_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 438)) (lay n : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf (b + 441) else pcOf (b + 440)) ∧
      t.getReg .x21 = BitVec.ofNat 64 n ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_438 hK.2) (codeAt_k_438 hK) s hpc (by simp [st_438, blk354_438.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_438, rebase, blk354_438.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 lay == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · simp [st_438, blk354_438.res, rv_simp, h26]
  · intro r hr; simp at hr; cases r <;> simp_all [st_438, blk354_438.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_438, blk354_438.res, rv_simp]

theorem cs440_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 440)) (n : Nat)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 63) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 441) ∧ t.getReg .x21 = BitVec.ofNat 64 (n - 1) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_440 hK.2) (codeAt_k_440 hK) s hpc (by simp [st_440, blk354_440.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_440, blk354_440.res, E.eval]
  · simp only [Result.toState_getReg, st_440, blk354_440.res]
    simp only [rv_simp, h26]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_440, blk354_440.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_440, blk354_440.res, rv_simp]

theorem cs441_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 441)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 442) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_441 hK.2) (codeAt_k_441 hK) s hpc (by simp [st_441, blk354_441.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_441, blk354_441.res, E.eval]
  · simp [st_441, blk354_441.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_441, blk354_441.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_441, blk354_441.res, rv_simp]

/-- `cs_dig`: `s4 ≥ s5` ends the digits. -/
theorem cs442_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 442)) (i n : Nat)
    (hi : i < 2 ^ 63) (hn : n < 2 ^ 63) (h20 : s.getReg .x20 = BitVec.ofNat 64 i)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if n ≤ i then pcOf (b + 461) else pcOf (b + 443)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_442 hK.2) (codeAt_k_442 hK) s hpc (by simp [st_442, blk354_442.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_442, rebase, blk354_442.res, E.eval, CmpOp.eval, h20, h21]
    rw [ofNat_slt _ _ hi hn]
    by_cases h : n ≤ i
    · simp [h, show ¬ i < n by omega]
    · simp [h, show i < n by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_442, blk354_442.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_442, blk354_442.res, rv_simp]

theorem cs443_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 443)) (i n4 : Nat)
    (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63) (h20 : s.getReg .x20 = BitVec.ofNat 64 i)
    (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if n4 ≤ i then pcOf (b + 448) else pcOf (b + 446)) ∧
      t.getReg .x28 = BitVec.ofNat 64 7 ∧ t.getReg .x29 = BitVec.ofNat 64 3 ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_443 hK.2) (codeAt_k_443 hK) s hpc (by simp [st_443, blk354_443.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_443, rebase, blk354_443.res, E.eval, CmpOp.eval, h20, h27]
    rw [ofNat_slt _ _ hi hn]
    by_cases h : n4 ≤ i
    · simp [h, show ¬ i < n4 by omega]
    · simp [h, show i < n4 by omega]
  · simp [st_443, blk354_443.res, rv_simp]
  · simp [st_443, blk354_443.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_443, blk354_443.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_443, blk354_443.res, rv_simp]

theorem cs446_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 446)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 448) ∧
      t.getReg .x28 = BitVec.ofNat 64 3 ∧ t.getReg .x29 = BitVec.ofNat 64 2 ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_446 hK.2) (codeAt_k_446 hK) s hpc (by simp [st_446, blk354_446.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_446, blk354_446.res, E.eval]
  · simp [st_446, blk354_446.res, rv_simp]
  · simp [st_446, blk354_446.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_446, blk354_446.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_446, blk354_446.res, rv_simp]

/-- The digit `t5 = t1 & mask`, its byte address `t3 = DIGITS + s4`. -/
theorem cs448_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 448)) (i : Nat)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 452) ∧
      t.getReg .x30 = s.getReg .x6 &&& s.getReg .x28 ∧ t.getReg .x28 = BitVec.ofNat 64 (DIGITS + i) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_448 hK.2) (codeAt_k_448 hK) s hpc (by simp [st_448, blk354_448.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_448, blk354_448.res, E.eval]
  · simp [st_448, blk354_448.res, rv_simp]
  · simp only [Result.toState_getReg, st_448, blk354_448.res]; t3n [h20, DIGITS]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_448, blk354_448.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_448, blk354_448.res, rv_simp]

/-- `sb t5, 0(t3)`. -/
theorem cs452_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 452)) (A : Nat)
    (hA : A < 2 ^ 24) (h28 : s.getReg .x28 = BitVec.ofNat 64 A) :
    Steps image s 1 1 ((s.setByte (BitVec.ofNat 64 A) ((s.getReg .x30).truncate 8)).setPC (pcOf (b + 453))) := by
  have h := steps_sb (codeAt_k_452 hK) hpc (rs1 := .x28) (rs2 := .x30) (off := 0) rfl
    (by rw [h28]; simp [accessValid_iff, MEMORY_BYTES, signExtend12]; omega)
  rw [h28, hpc, pcOf_add4] at h
  simpa [signExtend12] using h

/-- Shift the 128-bit window `t2:t1` right by `t4`, `s4 += 1`, back to `cs_dig`. -/
theorem cs453_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 453)) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = pcOf (b + 442) ∧
      t.getReg .x6 = (s.getReg .x6 >>> ((s.getReg .x29).toNat % 64) |||
        s.getReg .x7 <<< ((64#64 - s.getReg .x29).toNat % 64)) ∧
      t.getReg .x7 = s.getReg .x7 >>> ((s.getReg .x29).toNat % 64) ∧
      t.getReg .x20 = s.getReg .x20 + 1#64 ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_453 hK.2) (codeAt_k_453 hK) s hpc (by simp [st_453, blk354_453.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_453, blk354_453.res, E.eval]
  · simp [st_453, blk354_453.res, rv_simp]
  · simp [st_453, blk354_453.res, rv_simp]
  · simp [st_453, blk354_453.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_453, blk354_453.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_453, blk354_453.res, rv_simp]

/-- `cs_dig_done`: the top layer returns, lower layers write the checksum digit first. -/
theorem cs461_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 461)) (lay : Nat)
    (hl : lay < 4) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lay = 0 then pcOf (b + 467) else pcOf (b + 462)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_461 hK.2) (codeAt_k_461 hK) s hpc (by simp [st_461, blk354_461.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_461, rebase, blk354_461.res, E.eval, CmpOp.eval, h8]
    by_cases h : lay = 0
    · subst h; simp
    · have : (BitVec.ofNat 64 lay == 0#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_461, blk354_461.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_461, blk354_461.res, rv_simp]

/-- The checksum digit `t3 = a7 - s9` and its address `t4 = DIGITS + s5`. -/
theorem cs462_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 462)) (T S n : Nat)
    (hST : S ≤ T) (hT : T < 2 ^ 63) (h17 : s.getReg .x17 = BitVec.ofNat 64 T)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 S) (h21 : s.getReg .x21 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 466) ∧
      t.getReg .x28 = BitVec.ofNat 64 (T - S) ∧ t.getReg .x29 = BitVec.ofNat 64 (DIGITS + n) ∧
      RegsExcept s t [.x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_462 hK.2) (codeAt_k_462 hK) s hpc (by simp [st_462, blk354_462.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_462, blk354_462.res, E.eval]
  · simp only [Result.toState_getReg, st_462, blk354_462.res]
    simp only [rv_simp, h17, h25]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show T < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show S < 2 ^ 64 by omega),
      show 2 ^ 64 - S + T = 2 ^ 64 + (T - S) by omega, Nat.add_mod_left]
  · simp only [Result.toState_getReg, st_462, blk354_462.res]; t3n [h21, DIGITS]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_462, blk354_462.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_462, blk354_462.res, rv_simp]

/-- `sb t3, 0(t4)`. -/
theorem cs466_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 466)) (A : Nat)
    (hA : A < 2 ^ 24) (h29 : s.getReg .x29 = BitVec.ofNat 64 A) :
    Steps image s 1 1 ((s.setByte (BitVec.ofNat 64 A) ((s.getReg .x28).truncate 8)).setPC (pcOf (b + 467))) := by
  have h := steps_sb (codeAt_k_466 hK) hpc (rs1 := .x29) (rs2 := .x28) (off := 0) rfl
    (by rw [h29]; simp [accessValid_iff, MEMORY_BYTES, signExtend12]; omega)
  rw [h29, hpc, pcOf_add4] at h
  simpa [signExtend12] using h

/-- `ret`. -/
theorem cs467_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 467)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf ret ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_467 hK.2) (codeAt_k_467 hK) s hpc (by simp [st_467, blk354_467.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp [pcE_467, blk354_467.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · intro r hr; simp at hr; cases r <;> simp_all [st_467, blk354_467.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_467, blk354_467.res, rv_simp]

end blocks

end SigGolfCandidate.T3M.Search
