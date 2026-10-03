import SigGolfCandidate.T3M.Verify.Nonbinary.Decode

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def prologueCode : List (BitVec 32) := [0xd99c0993, 0xd4098b13, 0x00020c37, 0xc00c0c13, 0x000ae7b7, 0x00a81713, 0x01877733, 0x00f70733, 0x9a070067]
sym_block prologueBase := symRun { noAlias := true } prologueCode (pcOf 96220) 200

theorem prologue_at : CodeAt Verify.image (pcOf 96220) prologueCode := by
  have h := codeAt_from 96220 (by decide)
  have hp : prologueCode <+: codeFrom 96220 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

def prologueTarget (v : Digest) : Word :=
  (((v.extractLsb' 0 64 <<< (10 : Word)) &&& 130048#64) + pcOf 176744) &&& ~~~1#64

theorem prologue_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96220) (h24 : s.getReg .x24 = 16383#64)
    (h16 : s.getReg .x16 = v.extractLsb' 0 64) (h17 : s.getReg .x17 = v.extractLsb' 63 64) :
    ∃ t, Steps Verify.image s 9 9 t ∧ t.pc = prologueTarget v ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x22 = 15064#64 ∧ t.getReg .x19 = 15768#64 ∧ t.getReg .x24 = 130048#64 ∧
      t.getReg .x15 = 712704#64 ∧
      RegsExcept s t [.x3,.x17,.x22,.x19,.x24,.x15,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound prologueBase prologue_at s hpc (by simp [prologueBase.res, rv_simp, h24]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, prologueBase.res, rv_simp, h16, prologueTarget, pcOf]
    rfl
  · simpa [prologueBase.res, rv_simp, h24] using h16
  · simp [prologueBase.res, rv_simp, h16, h17]
  · simp [prologueBase.res, rv_simp, h24]
  · simp [prologueBase.res, rv_simp, h24]
  · simp [prologueBase.res, rv_simp, h24]
  · simp [prologueBase.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp at hr <;> simp [prologueBase.res, rv_simp, h24] <;> rfl
  · intro A _ _; simp [prologueBase.res, rv_simp, h24]

end SigGolfCandidate.T3M.Verify.Nonbinary
