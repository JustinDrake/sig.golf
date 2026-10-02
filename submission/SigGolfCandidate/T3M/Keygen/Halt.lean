import SigGolfCandidate.T3M.Keygen.Blocks

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

def haltSetup : List (BitVec 32) := [0x00100293,0x00000513]
theorem haltSetup_at : CodeAt image (pcOf 539) haltSetup :=
  CodeAt.of_append (pre := Images.keygenCode.take 539)
    (post := Images.keygenCode.drop 541) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
sym_block haltSetup_blk := symRun {noAlias := true} haltSetup (pcOf 539) 100

theorem haltSetup_spec (s : MachineState) (hpc : s.pc = pcOf 539) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 541 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x5,.x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound haltSetup_blk haltSetup_at s hpc
    (by simp [haltSetup_blk.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [haltSetup_blk.res,E.eval]
  · simp [haltSetup_blk.res,rv_simp]
  · simp [haltSetup_blk.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [haltSetup_blk.res,rv_simp] <;> rfl
  · intro A _ _; simp [haltSetup_blk.res,rv_simp]

theorem halt_at : CodeAt image (pcOf 541) [0x00000073] :=
  CodeAt.of_append (pre := Images.keygenCode.take 541)
    (post := []) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
theorem fetch_541 (s : MachineState) (hpc : s.pc = pcOf 541) :
    fetch image s = some (.base .ECALL) := (halt_at.fetch s hpc).trans rfl

end SigGolfCandidate.T3M.Keygen
