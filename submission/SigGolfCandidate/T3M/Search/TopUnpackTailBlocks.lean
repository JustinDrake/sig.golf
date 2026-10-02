import SigGolfCandidate.T3M.Search.TopUnpackBlocks

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem tail383_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+383)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+384) ∧
      t.getReg .x28=s.getReg .x6 &&& 3#64 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top383 hK.2) (codeAt_top383 hK) s hpc
    (by simp [topState383,tb354_383.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [topState383,topEnd383,tb354_383.res,rv_simp]
  · simp [topState383,tb354_383.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState383,tb354_383.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState383,tb354_383.res,rv_simp]

theorem tail385_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+385)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf (b+387) ∧
      t.getReg .x6=s.getReg .x6 >>> 2 ∧ t.getReg .x28=(s.getReg .x6 >>> 2) &&& 3#64 ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top385 hK.2) (codeAt_top385 hK) s hpc
    (by simp [topState385,tb354_385.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [topState385,topEnd385,tb354_385.res,rv_simp]
  · simp [topState385,tb354_385.res,rv_simp]
  · simp [topState385,tb354_385.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState385,tb354_385.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState385,tb354_385.res,rv_simp]

theorem tail388_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+388)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf (b+390) ∧
      t.getReg .x6=s.getReg .x6 >>> 2 ∧ t.getReg .x28=(s.getReg .x6 >>> 2) &&& 3#64 ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top388 hK.2) (codeAt_top388 hK) s hpc
    (by simp [topState388,tb354_388.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · simp [topState388,topEnd388,tb354_388.res,rv_simp]
  · simp [topState388,tb354_388.res,rv_simp]
  · simp [topState388,tb354_388.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState388,tb354_388.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState388,tb354_388.res,rv_simp]

theorem tail391_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+391)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=s.getReg .x1 &&& ~~~1#64 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top391 hK.2) (codeAt_top391 hK) s hpc
    (by simp [topState391,tb354_391.res,rv_simp]),?_,?_,?_⟩
  · simp [topState391,topEnd391,tb354_391.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState391,tb354_391.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState391,tb354_391.res,rv_simp]

end SigGolfCandidate.T3M.Search.TopUnpack
