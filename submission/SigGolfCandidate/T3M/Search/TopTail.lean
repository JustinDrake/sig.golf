import SigGolfCandidate.T3M.Search.TopAlu

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem topWindow_tail (v : Digest) (hv : v.toNat < 2 ^ 125) :
    topWindow v 17 = BitVec.ofNat 64 (v.toNat / 2 ^ 119) := by
  apply BitVec.eq_of_toNat_eq
  simp only [topWindow, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.reduceMul,
    BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h1 : v.toNat / 2 ^ 63 < 2 ^ 64 := by omega
  have h2 : v.toNat / 2 ^ 119 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.div_div_eq_div_mul]
  rfl

theorem tailWeight_le (v : Digest) : tailWeight v ≤ 9 := by unfold tailWeight; omega

theorem topTail_sum (v : Digest) (hv : v.toNat < 2 ^ 125) (sum : Nat) :
    BitVec.ofNat 64 sum + (topWindow v 17 &&& 3#64) +
      (topWindow v 17 >>> 2 &&& 3#64) + (topWindow v 17 >>> 4) =
      BitVec.ofNat 64 (sum + tailWeight v) := by
  rw [topWindow_tail v hv]
  have h : v.toNat / 2 ^ 119 < 2 ^ 64 := by omega
  rw [ofNat_shr _ _ h, ofNat_shr _ _ h, ofNat_and3, ofNat_and3,
    ofNat_add_ofNat, ofNat_add_ofNat, ofNat_add_ofNat]
  congr 1
  simp only [tailWeight, Nat.div_div_eq_div_mul]
  norm_num
  omega

/-- The last three radix-four digits and the exact sum check cost nine instructions. -/
theorem topTail_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf (b + 353))
    (h28 : s.getReg .x28 = topWindow v 17)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum) (h17 : s.getReg .x17 = 126#64) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf (b + 362) else pcOf (b + 468)) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + tailWeight v) ∧
      RegsExcept s t [.x25,.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_top353 hK.2) (codeAt_top353 hK) s hpc
    (by simp [topState353, tb354_353.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, topEnd353, rebase, tb354_353.res,
      E.eval, CmpOp.eval, BinOp.eval, h28, h25, h17,
      BitVec.toNat_ofNat, Nat.reduceMod, topTail_sum v hv sum]
    have hh : sum + tailWeight v < 2 ^ 64 := by have := tailWeight_le v; omega
    simp only [bne_iff_ne, ne_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add, ofNat_inj hh (by decide : 126 < 2 ^ 64)]
    split_ifs <;> first | rfl | omega
  · simpa only [Result.toState_getReg, topState353, tb354_353.res, rv_simp,
      h28, h25, BitVec.toNat_ofNat, Nat.reduceMod] using topTail_sum v hv sum
  · intro r hr; cases r <;> simp at hr <;> simp [topState353, tb354_353.res, rv_simp] <;> rfl
  · intro A _ _; simp [topState353, tb354_353.res, rv_simp]

end SigGolfCandidate.T3M.Search
