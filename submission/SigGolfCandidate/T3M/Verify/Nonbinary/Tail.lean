import SigGolfCandidate.T3M.Verify.Nonbinary.Fold
import SigGolfCandidate.T3M.Search.TopTail

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def tailCode : List (BitVec 32) := [0x003ef713, 0x00ec8cb3, 0x002ed713, 0x00377713, 0x00ec8cb3, 0x004ed713, 0x00ec8cb3, 0xf82c8713, 0x04071063]
sym_block tailBase := symRun { noAlias := true } tailCode (pcOf 96252) 200

theorem tail_at : CodeAt Verify.image (pcOf 96252) tailCode := by
  have h := codeAt_from 96252 (by decide)
  have hp : tailCode <+: codeFrom 96252 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

/-- Last three radix-four digits and strong total-sum check in the actual verifier. -/
theorem tail_spec (s : MachineState) (v : Digest) (sum : Nat) (hsum : sum ≤ 4335)
    (hv : v.toNat < 2 ^ 125) (hpc : s.pc = pcOf 96252)
    (h29 : s.getReg .x29 = topWindow v 17) (h25 : s.getReg .x25 = BitVec.ofNat 64 sum) :
    ∃ t, Steps Verify.image s 9 9 t ∧
      t.pc = (if sum + tailWeight v = 126 then pcOf 96261 else pcOf 96276) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + tailWeight v) ∧
      RegsExcept s t [.x25,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailBase tail_at s hpc (by simp [tailBase.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, tailBase.res, E.eval, CmpOp.eval, BinOp.eval,
      h29, h25, BitVec.toNat_ofNat, Nat.reduceMod, topTail_sum v hv sum]
    have hh : sum + tailWeight v < 2 ^ 64 := by have := tailWeight_le v; omega
    rw [show 18446744073709551490#64 = -126#64 from rfl, ← BitVec.sub_eq_add_neg]
    simp only [bne_iff_ne, ne_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add,
      ofNat_inj hh (by decide : 126 < 2 ^ 64)]
    split_ifs <;> first | rfl | omega
  · simpa only [Result.toState_getReg, tailBase.res, rv_simp,
      h29, h25, BitVec.toNat_ofNat, Nat.reduceMod] using topTail_sum v hv sum
  · intro r hr; cases r <;> simp at hr <;> simp [tailBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [tailBase.res, rv_simp]

end SigGolfCandidate.T3M.Verify.Nonbinary
