import SigGolfCandidate.T3M.Search.TopUnpackMemory

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

def initCode : List (BitVec 32) := [0x00000a13,0x00020ab7,0x420a8a93,0x080f0f13]
def ptrCode : List (BitVec 32) := [0x07f37e13,0x002e1e13,0x01ee0e33]
def initLayout : Rv.Layout := [(0,initCode),(4,ptrCode)]
theorem initLayout_ok : layoutOk 0 initLayout=true := by decide +kernel
theorem initLayout_code : topSeg362=layoutCode initLayout := by decide +kernel

theorem code_init {image : Image} {b : Nat} (hK : KernAt image b) :
    CodeAt image (pcOf (b+362)) initCode := by
  have hc := codeAt_top362 hK
  rw [initLayout_code] at hc
  have h := codeAt_sublayout hc initLayout_ok (i:=0) (o:=0) (seg:=initCode) (by kernel_rfl)
  simpa only [Nat.add_zero] using h

theorem code_ptr {image : Image} {b : Nat} (hK : KernAt image b) :
    CodeAt image (pcOf (b+366)) ptrCode := by
  have hc := codeAt_top362 hK
  rw [initLayout_code] at hc
  have h := codeAt_sublayout hc initLayout_ok (i:=1) (o:=4) (seg:=ptrCode) (by kernel_rfl)
  simpa only [Nat.add_assoc,Nat.reduceAdd] using h

sym_block ui354 := symRun {noAlias:=true} initCode (pcOf (354+362)) 200
sym_block ui543 := symRun {noAlias:=true} initCode (pcOf (543+362)) 200
def initState : SymState := ui354.res.st
theorem run_init {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} initCode (pcOf (b+362)) 200=
      some ⟨initState,.c (pcOf (b+366)),ui354.res.stop,ui354.res.steps,ui354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact ui354.trans (congrArg some (by kernel_rfl))
  · exact ui543.trans (congrArg some (by kernel_rfl))

sym_block up354 := symRun {noAlias:=true} ptrCode (pcOf (354+366)) 200
sym_block up543 := symRun {noAlias:=true} ptrCode (pcOf (543+366)) 200
def ptrState : SymState := up354.res.st
theorem run_ptr {b : Nat} (hb : b=354 ∨ b=543) :
    symRun {noAlias:=true} ptrCode (pcOf (b+366)) 200=
      some ⟨ptrState,.c (pcOf (b+369)),up354.res.stop,up354.res.steps,up354.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact up354.trans (congrArg some (by kernel_rfl))
  · exact up543.trans (congrArg some (by kernel_rfl))

theorem init_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+362)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc=pcOf (b+366) ∧
      t.getReg .x20=0 ∧ t.getReg .x21=BitVec.ofNat 64 DIGITS ∧
      t.getReg .x30=s.getReg .x30+128#64 ∧
      RegsExcept s t [.x20,.x21,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_init hK.2) (code_init hK) s hpc
    (by simp [initState,ui354.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · rfl
  · simp [initState,ui354.res,rv_simp]
  · simp [initState,ui354.res,rv_simp,DIGITS]
  · simp [initState,ui354.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [initState,ui354.res,rv_simp] <;> rfl
  · intro A _ _; simp [initState,ui354.res,rv_simp]

theorem ptr_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+366)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc=pcOf (b+369) ∧
      t.getReg .x28=((s.getReg .x6 &&& 127#64) <<< 2)+s.getReg .x30 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_ptr hK.2) (code_ptr hK) s hpc
    (by simp [ptrState,up354.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [ptrState,up354.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [ptrState,up354.res,rv_simp] <;> rfl
  · intro A _ _; simp [ptrState,up354.res,rv_simp]

theorem shift371_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+371)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+372) ∧
      t.getReg .x29=s.getReg .x29 >>> 8 ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top371 hK.2) (codeAt_top371 hK) s hpc
    (by simp [topState371,tb354_371.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [topState371,tb354_371.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState371,tb354_371.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState371,tb354_371.res,rv_simp]

theorem shift373_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+373)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+374) ∧
      t.getReg .x29=s.getReg .x29 >>> 8 ∧ RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top373 hK.2) (codeAt_top373 hK) s hpc
    (by simp [topState373,tb354_373.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp [topState373,tb354_373.res,rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [topState373,tb354_373.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState373,tb354_373.res,rv_simp]

theorem update_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+375)) (i : Nat) (hi : i<17)
    (h20 : s.getReg .x20=BitVec.ofNat 64 i) :
    ∃ t, Steps image s 8 8 t ∧
      t.pc=(if i+1<17 then pcOf (b+366) else pcOf (b+383)) ∧
      t.getReg .x6=(s.getReg .x6 >>> 7 ||| s.getReg .x7 <<< 57) ∧
      t.getReg .x7=s.getReg .x7 >>> 7 ∧ t.getReg .x21=s.getReg .x21+3#64 ∧
      t.getReg .x20=BitVec.ofNat 64 (i+1) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (run_top375 hK.2) (codeAt_top375 hK) s hpc
    (by simp [topState375,tb354_375.res,rv_simp]),?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,topEnd375,rebase,tb354_375.res,E.eval,CmpOp.eval,BinOp.eval,h20,
      BitVec.toNat_ofNat,Nat.reduceMod,ofNat_add_ofNat]
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (show i+1<18446744073709551616 by omega)]
    by_cases h : i+1<17 <;> simp [h]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp [topState375,tb354_375.res,rv_simp]
  · simp only [Result.toState_getReg,topState375,tb354_375.res,rv_simp,h20,ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [topState375,tb354_375.res,rv_simp] <;> rfl
  · intro A _ _; simp [topState375,tb354_375.res,rv_simp]

end SigGolfCandidate.T3M.Search.TopUnpack
