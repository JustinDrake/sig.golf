import SigGolfCandidate.T3M.Verify.Nonbinary.Reject
namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
def rejectJumpCode : List (BitVec 32) := [0xb45a206f]
sym_block rejectJumpBase := symRun { noAlias := true } rejectJumpCode (pcOf 96276) 20

theorem rejectJump_at : CodeAt Verify.image (pcOf 96276) rejectJumpCode := by
  have h := codeAt_from 96276 (by decide)
  have hp : rejectJumpCode <+: codeFrom 96276 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
def rejectExitCode : List (BitVec 32) := [0x00100293, 0x00100513]
sym_block rejectExitBase := symRun { noAlias := true } rejectExitCode (pcOf 741) 20

theorem rejectExit_at : CodeAt Verify.image (pcOf 741) rejectExitCode := by
  have h := codeAt_from 741 (by decide)
  have hp : rejectExitCode <+: codeFrom 741 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

theorem reject_halt (s : MachineState) (hpc : s.pc = pcOf 96276) :
    ∃ t, Steps Verify.image s 3 3 t ∧ fetch Verify.image t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 1 := by
  have e1 := symRun_sound rejectJumpBase rejectJump_at s hpc (by simp [rejectJumpBase.res, rv_simp])
  have p1 : (rejectJumpBase.res.toState s).pc = pcOf 741 := by simp [rejectJumpBase.res, rv_simp, pcOf]
  have e2 := symRun_sound rejectExitBase rejectExit_at (rejectJumpBase.res.toState s) p1
    (by simp [rejectExitBase.res, rv_simp])
  refine ⟨_, e1.trans e2, ?_, ?_, ?_⟩
  · have h : CodeAt Verify.image (pcOf 743) [0x00000073] := by
      have h := codeAt_from 743 (by decide)
      have hp : [0x00000073] <+: codeFrom 743 := by decide +kernel
      exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩
    exact h.fetch _ (by simp [rejectExitBase.res, rv_simp, pcOf])
  · simp [rejectExitBase.res, rv_simp]
  · simp [rejectExitBase.res, rv_simp]
end SigGolfCandidate.T3M.Verify.Nonbinary
