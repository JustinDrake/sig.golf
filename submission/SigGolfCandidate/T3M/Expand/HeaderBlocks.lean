import SigGolfCandidate.T3M.Expand.FrontBlocks
import SigGolfCandidate.T3M.Expand.Header
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem header_1162 (s : MachineState) (hpc : s.pc=pcOf 1162) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if cnt<4 then pcOf 1169 else pcOf 1164) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1162 codeAt_1162 s hpc (by simp [eblk_1162.res,rv_simp]),?_,?_,?_⟩
  · interval_cases cnt <;> simp [Result.toState_pc,eblk_1162.res,rv_simp,h23,CmpOp.eval]
  · ex_regs eblk_1162.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1162.res,rv_simp]

theorem header_1164 (s : MachineState) (hpc : s.pc=pcOf 1164) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1174 ∧
      t.getReg .x28=packLarge (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1164 codeAt_1164 s hpc (by simp [eblk_1164.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1164.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1164.res,rv_simp,h23,packLarge,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1164.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1164.res,rv_simp]

theorem header_1169 (s : MachineState) (hpc : s.pc=pcOf 1169) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1174 ∧
      t.getReg .x28=packSmall (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1169 codeAt_1169 s hpc (by simp [eblk_1169.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1169.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1169.res,rv_simp,h23,packSmall,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1169.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1169.res,rv_simp]

theorem header_1174 (s : MachineState) (hpc : s.pc=pcOf 1174) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 195 ∧ t.getReg .x28=s.getReg .x28 ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1174 codeAt_1174 s hpc (by simp [eblk_1174.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1174.res,rv_simp]
  · simp [Result.toState_getReg,eblk_1174.res,rv_simp]
  · ex_regs eblk_1174.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1174.res,rv_simp]

theorem header_1175 (s : MachineState) (hpc : s.pc=pcOf 1175) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if cnt<4 then pcOf 1182 else pcOf 1177) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1175 codeAt_1175 s hpc (by simp [eblk_1175.res,rv_simp]),?_,?_,?_⟩
  · interval_cases cnt <;> simp [Result.toState_pc,eblk_1175.res,rv_simp,h23,CmpOp.eval]
  · ex_regs eblk_1175.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1175.res,rv_simp]

theorem header_1177 (s : MachineState) (hpc : s.pc=pcOf 1177) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1187 ∧
      t.getReg .x28=packLarge (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1177 codeAt_1177 s hpc (by simp [eblk_1177.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1177.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1177.res,rv_simp,h23,packLarge,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1177.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1177.res,rv_simp]

theorem header_1182 (s : MachineState) (hpc : s.pc=pcOf 1182) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1187 ∧
      t.getReg .x28=packSmall (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1182 codeAt_1182 s hpc (by simp [eblk_1182.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1182.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1182.res,rv_simp,h23,packSmall,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1182.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1182.res,rv_simp]

theorem header_1187 (s : MachineState) (hpc : s.pc=pcOf 1187) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 862 ∧ t.getReg .x28=s.getReg .x28 ∧
      RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1187 codeAt_1187 s hpc (by simp [eblk_1187.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1187.res,rv_simp]
  · simp [Result.toState_getReg,eblk_1187.res,rv_simp]
  · ex_regs eblk_1187.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1187.res,rv_simp]

theorem header_1188 (s : MachineState) (hpc : s.pc=pcOf 1188) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=(if cnt<4 then pcOf 1195 else pcOf 1190) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1188 codeAt_1188 s hpc (by simp [eblk_1188.res,rv_simp]),?_,?_,?_⟩
  · interval_cases cnt <;> simp [Result.toState_pc,eblk_1188.res,rv_simp,h23,CmpOp.eval]
  · ex_regs eblk_1188.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1188.res,rv_simp]

theorem header_1190 (s : MachineState) (hpc : s.pc=pcOf 1190) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1200 ∧
      t.getReg .x28=packLarge (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1190 codeAt_1190 s hpc (by simp [eblk_1190.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1190.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1190.res,rv_simp,h23,packLarge,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1190.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1190.res,rv_simp]

theorem header_1195 (s : MachineState) (hpc : s.pc=pcOf 1195) (cnt : Nat) (hc : cnt<16)
    (h23 : s.getReg .x23=BitVec.ofNat 64 cnt) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 1200 ∧
      t.getReg .x28=packSmall (BitVec.ofNat 64 cnt) (s.getReg .x24) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1195 codeAt_1195 s hpc (by simp [eblk_1195.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1195.res,rv_simp]
  · interval_cases cnt <;> simp [Result.toState_getReg,eblk_1195.res,rv_simp,h23,packSmall,sub_eq_add_neg,add_assoc]
  · ex_regs eblk_1195.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1195.res,rv_simp]

theorem header_1200 (s : MachineState) (hpc : s.pc=pcOf 1200) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf 978 ∧ t.getReg .x28=s.getReg .x28 ||| 128 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_1200 codeAt_1200 s hpc (by simp [eblk_1200.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_1200.res,rv_simp]
  · simp [Result.toState_getReg,eblk_1200.res,rv_simp]
  · ex_regs eblk_1200.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_1200.res,rv_simp]
end SigGolfCandidate.T3M.Expand
