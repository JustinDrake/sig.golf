import SigGolfCandidate.T3M.Search.TopSegments
import SigGolfCandidate.T3M.Search.TopWindow

section


namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def Writes (A : Nat) : Prop := DIGITS ≤ A ∧ A < DIGITS+64
abbrev Changed : List Reg := [.x6,.x7,.x20,.x21,.x28,.x29,.x30]
theorem read_wu_byte (s : MachineState) (A k : Nat) (hA : A+8 < 2^64)
    (hal : A%4=0) (hk : k<4) :
    (LoadKind.wu.read s (BitVec.ofNat 64 A) >>> (8*k)).truncate 8 =
      s.getByte (BitVec.ofNat 64 (A+k)) := by
  rw [LoadKind.read_sub _ _ _ (by decide),byteOffset_eq,toNat_ofNat_lt (by omega),
    getByte_eq_word _ _ (by omega)]
  have he : alignToDword (BitVec.ofNat 64 A)=BitVec.ofNat 64 ((A+k)/8*8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat,toNat_ofNat_lt (by omega),toNat_ofNat_lt (by omega)]
    omega
  rw [he]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [LoadKind.fromWord,extractWord32,extractByte,BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_ushiftRight]
  have h1 : 8*k+i<32 := by omega
  have h2 : A%8/4*32+(8*k+i)=(A+k)%8*8+i := by omega
  simp only [hi,h1,show 8*k+i<64 by omega,decide_true,Bool.true_and,h2]
theorem table_rank_byte (s : MachineState) (ht : TableOK s) (r k : Nat)
    (hr : r<125) (hk : k<3) :
    s.getByte (BitVec.ofNat 64 (TOP_DATA+128+4*r+k))=BitVec.ofNat 8 (rankDigit r k) := by
  have h := ht (128+4*r+k) (by omega)
  have he : TOP_DATA+(128+4*r+k)=TOP_DATA+128+4*r+k := by omega
  rw [he] at h
  rw [h]
  unfold tableByte
  simp only [show ¬128+4*r+k<128 by omega,if_false,show 128+4*r+k<628 by omega,if_true]
  have h1 : (128+4*r+k-128)%4=k := by omega
  have h2 : (128+4*r+k-128)/4=r := by omega
  rw [h1,h2,if_pos hk]
theorem load_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+369)) (r : Nat) (hr : r<125)
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*r)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf (b+370) ∧
      t.getReg .x29=LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hd : decodeInstruction (0x000e6e83 : BitVec 32)=some (.base (.LWU .x29 .x28 0)) := rfl
  have hf := ((codeAt_top369 hK).fetch s hpc).trans hd
  have hv : accessValid (s.getReg .x28+0) 4=true := by
    rw [h28]; simp only [add_zero,accessValid_iff,MEMORY_BYTES]
    norm_num [TOP_DATA]
    omega
  have hs : ordinaryStep s (.base (.LWU .x29 .x28 0))=
      some ((s.setReg .x29 (LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)))).setPC (s.pc+4)) := by
    rw [classify_sound (show classify (.base (.LWU .x29 .x28 0))=some (.load .wu .x29 .x28 0) from rfl)]
    simp only [Micro.exec,LoadKind.width,show accessValid (s.getReg .x28+0) 4=true from hv,if_true]
    rw [h28,add_zero]
  refine ⟨_,Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl,?_,?_,?_,?_⟩
  · change s.pc+4=pcOf (b+370)
    rw [hpc,pcOf_add4]
  · change (s.setReg .x29 _).getReg .x29=_
    exact MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ Reg.x0)
  · intro q hq; simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; rfl
theorem store_spec {image : Image} (s : MachineState) (pc : Word) (inst : BitVec 32)
    (rs : Reg) (off : BitVec 12) (A : Nat) (value : BitVec 8)
    (hc : CodeAt image pc [inst]) (hpc : s.pc=pc)
    (hd : decodeInstruction inst=some (.base (.SB .x21 rs off)))
    (ha : s.getReg .x21+signExtend12 off=BitVec.ofNat 64 A)
    (hv : (s.getReg rs).truncate 8=value) (hA : DIGITS ≤ A ∧ A<DIGITS+54) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pc+4 ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=A then value else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [] ∧ Frame s t Writes := by
  have hAb : A<2^64 := by unfold DIGITS at hA;omega
  have haccess : accessValid (s.getReg .x21+signExtend12 off) 1=true := by
    rw [ha]
    simp only [accessValid_iff,MEMORY_BYTES,toNat_ofNat_lt hAb,Nat.mod_one,and_true,true_and]
    unfold DIGITS at hA
    omega
  have hs := steps_sb hc hpc hd haccess
  rw [ha,hv] at hs
  refine ⟨_,hs,congrArg (fun p => p+4) hpc,?_,?_,?_⟩
  · intro B hB
    simp only [getByte_setPC,getByte_setByte s A B hAb hB]
  · intro q _; simp only [getReg_setPC',getReg_setByte]
  · intro B hB hn
    simp only [getMem_setPC']
    apply getMem_setByte s A B hAb hB value
    unfold Writes at hn
    unfold DIGITS at hn hA
    omega
theorem pair_shift (X : Nat) :
    (BitVec.ofNat 64 X >>> 7 ||| BitVec.ofNat 64 (X/2^64) <<< 57)=
      BitVec.ofNat 64 (X/2^7) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or,BitVec.getLsbD_ushiftRight,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat,Nat.testBit_div_two_pow,hi,decide_true,Bool.true_and]
  by_cases h : 7+i<64
  · simp only [h,decide_true,Bool.true_and,show i<57 by omega,decide_true,Bool.not_true,
      Bool.false_and,Bool.or_false]
    congr 1
    omega
  · simp only [h,decide_false,Bool.false_and,Bool.false_or,show ¬i<57 by omega,decide_false,
      Bool.not_false,Bool.true_and,show i-57<64 by omega,decide_true]
    congr 1
    omega
end SigGolfCandidate.T3M.Search.TopUnpack
end

section

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def initCode : List (BitVec 32) := [2579,133815,0x420a8a93,0x80f0f13]
def ptrCode : List (BitVec 32) := [0x7f37e13,3022355,32378419]
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
end

section

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem triple_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+369)) (i r : Nat) (hi : i<17) (hr : r<125)
    (h21 : s.getReg .x21=BitVec.ofNat 64 (DIGITS+3*i))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*r)) (ht : TableOK s) :
    ∃ t, Steps image s 6 6 t ∧ t.pc=pcOf (b+375) ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=DIGITS+3*i+2 then BitVec.ofNat 8 (rankDigit r 2)
        else if B=DIGITS+3*i+1 then BitVec.ofNat 8 (rankDigit r 1)
        else if B=DIGITS+3*i then BitVec.ofNat 8 (rankDigit r 0)
        else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x29] ∧ Frame s t Writes := by
  have hb (k : Nat) (hk : k<3) :
      (LoadKind.wu.read s (BitVec.ofNat 64 (TOP_DATA+128+4*r)) >>> (8*k)).truncate 8=
        BitVec.ofNat 8 (rankDigit r k) := by
    rw [read_wu_byte s _ k (by unfold TOP_DATA;omega) (by unfold TOP_DATA;omega) (by omega)]
    exact table_rank_byte s ht r k hr hk
  obtain ⟨t1,s1,p1,h29,r1,f1⟩ := load_spec hK s hpc r hr h28
  have hv0 : (t1.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 0) := by
    rw [h29]
    simpa using hb 0 (by decide)
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := store_spec t1 (pcOf (b+370)) 0x01da8023 .x29 0
    (DIGITS+3*i) (BitVec.ofNat 8 (rankDigit r 0)) (codeAt_top370 hK) p1 rfl
    (by rw [r1.get (by decide),h21]; simp [signExtend12]) hv0 (by omega)
  have p2' : t2.pc=pcOf (b+371) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p2
  obtain ⟨t3,s3,p3,h29a,r3,f3⟩ := shift371_spec hK t2 p2'
  have hv1 : (t3.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 1) := by
    rw [h29a,r2.get (by decide),h29]
    exact hb 1 (by decide)
  obtain ⟨t4,s4,p4,g4,r4,f4⟩ := store_spec t3 (pcOf (b+372)) 0x01da80a3 .x29 1
    (DIGITS+3*i+1) (BitVec.ofNat 8 (rankDigit r 1)) (codeAt_top372 hK) p3 rfl
    (by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 1) hv1 (by omega)
  have p4' : t4.pc=pcOf (b+373) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p4
  obtain ⟨t5,s5,p5,h29b,r5,f5⟩ := shift373_spec hK t4 p4'
  have hv2 : (t5.getReg .x29).truncate 8=BitVec.ofNat 8 (rankDigit r 2) := by
    rw [h29b,r4.get (by decide),h29a,r2.get (by decide),h29,←BitVec.shiftRight_add]
    exact hb 2 (by decide)
  obtain ⟨t6,s6,p6,g6,r6,f6⟩ := store_spec t5 (pcOf (b+374)) 0x01da8123 .x29 2
    (DIGITS+3*i+2) (BitVec.ofNat 8 (rankDigit r 2)) (codeAt_top374 hK) p5 rfl
    (by rw [r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 2) hv2 (by omega)
  refine ⟨t6,(((((s1.trans s2).trans s3).trans s4).trans s5).trans s6),?_,?_,?_,?_⟩
  · simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p6
  · intro B hB
    rw [g6 B hB,f5.getByte hB (by simp),g4 B hB,f3.getByte hB (by simp),g2 B hB,
      f1.getByte hB (by simp)]
  · exact (((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide)
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end

section

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option Elab.async false
set_option linter.unusedSimpArgs false
structure Inv (b : Nat) (s0 : MachineState) (v : Digest) (i : Nat) (t : MachineState) : Prop where
  bound : i ≤ 17
  pc : t.pc=if i<17 then pcOf (b+366) else pcOf (b+383)
  lo : t.getReg .x6=BitVec.ofNat 64 (v.toNat/2^(7*i))
  hi : t.getReg .x7=BitVec.ofNat 64 (v.toNat/2^(7*i)/2^64)
  index : t.getReg .x20=BitVec.ofNat 64 i
  ptr : t.getReg .x21=BitVec.ofNat 64 (DIGITS+3*i)
  table : t.getReg .x30=BitVec.ofNat 64 (TOP_DATA+128)
  digits : ∀ j, j<3*i → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (T3.coreDigit 0 v j)
  regs : RegsExcept s0 t Changed
  frame : Frame s0 t Writes
theorem ptr_address (X : Nat) :
    ((BitVec.ofNat 64 X &&& 127#64) <<< 2)+BitVec.ofNat 64 (TOP_DATA+128)=
      BitVec.ofNat 64 (TOP_DATA+128+4*(X%128)) := by
  rw [ofNat_and127, ofNat_shl, ofNat_add_ofNat]
  congr 1
  omega
theorem source_rank_digit (v : Digest) (i k : Nat) (hi : i<17) (hk : k<3) :
    T3.coreDigit 0 v (3*i+k)=rankDigit (topRank v i) k := by
  have h1 : (3*i+k)/3=i := by omega
  have h2 : (3*i+k)%3=k := by omega
  simp only [T3.coreDigit,if_pos rfl,show 3*i+k<51 by omega,if_true,h1,h2]
  rfl
theorem body {image : Image} {b : Nat} (hK : KernAt image b) {s0 t : MachineState}
    (ht : TableOK s0) (v : Digest) (hvalid : T3.topRanksValid v=true) (i : Nat) (hi : i<17)
    (hI : Inv b s0 v i t) :
    ∃ u, Steps image t 17 17 u ∧ Inv b s0 v (i+1) u := by
  have pc := hI.pc
  rw [if_pos hi] at pc
  obtain ⟨t1,s1,p1,a28,r1,f1⟩ := ptr_spec hK t pc
  have rankbound : topRank v i<125 := by
    have hv := (List.all_eq_true.mp hvalid) i (List.mem_range.mpr hi)
    exact of_decide_eq_true hv
  have hp1 : t1.getReg .x28=BitVec.ofNat 64 (TOP_DATA+128+4*topRank v i) := by
    rw [a28,hI.lo,hI.table,ptr_address]
    rfl
  have table1 : TableOK t1 := ht.frame (W:=Writes) ((hI.frame.trans f1).mono (by simp)) (by
    intro j hj
    unfold Writes DIGITS TOP_DATA
    omega)
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := triple_spec hK t1 p1 i (topRank v i) hi rankbound
    (by rw [r1.get (by decide),hI.ptr]) hp1 table1
  obtain ⟨u,s3,p3,g6,g7,g21,g20,r3,f3⟩ := update_spec hK t2 p2 i hi
    (by rw [r2.get (by decide),r1.get (by decide),hI.index])
  refine ⟨u,(s1.trans s2).trans s3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · exact p3
  · rw [g6,r2.get (by decide),r1.get (by decide),hI.lo,
      r2.get (by decide),r1.get (by decide),hI.hi,pair_shift]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.div_div_eq_div_mul,←pow_add,show 7*i+7=7*(i+1) by omega]
  · have hv := v.isLt
    have hx := Nat.div_le_self v.toNat (2^(7*i))
    have hh : v.toNat/2^(7*i)/2^64<2^64 := by omega
    rw [g7,r2.get (by decide),r1.get (by decide),hI.hi,ofNat_shr _ _ hh]
    apply congrArg (BitVec.ofNat 64)
    simp only [Nat.div_div_eq_div_mul]
    apply congrArg (fun d => v.toNat/d)
    simp only [←pow_add]
    congr 1 <;> omega
  · exact g20
  · rw [g21,r2.get (by decide),r1.get (by decide),hI.ptr,ofNat_add_ofNat]
    congr 1
  · rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),hI.table]
  · intro j hj
    have hb : DIGITS+j<2^64 := by unfold DIGITS;omega
    rw [f3.getByte hb (by simp),g2 _ hb]
    by_cases he2 : j=3*i+2
    · subst j
      rw [if_pos (by omega)]
      rw [source_rank_digit v i 2 hi (by decide)]
    · rw [if_neg (by omega)]
      by_cases he1 : j=3*i+1
      · subst j
        rw [if_pos (by omega),source_rank_digit v i 1 hi (by decide)]
      · rw [if_neg (by omega)]
        by_cases he0 : j=3*i
        · subst j
          rw [if_pos rfl]
          simpa only [Nat.add_zero] using congrArg (BitVec.ofNat 8) (source_rank_digit v i 0 hi (by decide)).symm
        · rw [if_neg (by omega),f1.getByte hb (by simp)]
          exact hI.digits j (by omega)
  · exact (hI.regs.trans ((r1.trans r2).trans r3)).mono (by decide)
  · exact (hI.frame.trans ((f1.trans f2).trans f3)).mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end

section

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
end

section

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem mask_byte (X : Nat) :
    (BitVec.ofNat 64 X &&& 3#64).truncate 8=BitVec.ofNat 8 (X%4) := by
  rw [ofNat_and3]
  apply BitVec.eq_of_toNat_eq
  simp
theorem tail_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (hpc : s.pc=pcOf (b+383)) (X : Nat) (hX : X<64)
    (h6 : s.getReg .x6=BitVec.ofNat 64 X)
    (h21 : s.getReg .x21=BitVec.ofNat 64 (DIGITS+51)) :
    ∃ t, Steps image s 9 9 t ∧ t.pc=s.getReg .x1 &&& ~~~1#64 ∧
      (∀ B, B<2^64 → t.getByte (BitVec.ofNat 64 B)=
        if B=DIGITS+53 then BitVec.ofNat 8 (X/16%4)
        else if B=DIGITS+52 then BitVec.ofNat 8 (X/4%4)
        else if B=DIGITS+51 then BitVec.ofNat 8 (X%4)
        else s.getByte (BitVec.ofNat 64 B)) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t Writes := by
  obtain ⟨t1,s1,p1,h28,r1,f1⟩ := tail383_spec hK s hpc
  obtain ⟨t2,s2,p2,g2,r2,f2⟩ := store_spec t1 (pcOf (b+384)) 0x01ca8023 .x28 0
    (DIGITS+51) (BitVec.ofNat 8 (X%4)) (codeAt_top384 hK) p1 rfl
    (by rw [r1.get (by decide),h21];simp [signExtend12])
    (by rw [h28,h6,mask_byte]) (by omega)
  have p2' : t2.pc=pcOf (b+385) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p2
  obtain ⟨t3,s3,p3,g6a,h28a,r3,f3⟩ := tail385_spec hK t2 p2'
  have l3 : t3.getReg .x6=BitVec.ofNat 64 (X/4) := by
    rw [g6a,r2.get (by decide),r1.get (by decide),h6,ofNat_shr _ _ (by omega)]
    rfl
  have h28a' : t3.getReg .x28=BitVec.ofNat 64 (X/4) &&& 3#64 := by
    rw [h28a,r2.get (by decide),r1.get (by decide),h6,ofNat_shr _ _ (by omega)]
    rfl
  obtain ⟨t4,s4,p4,g4,r4,f4⟩ := store_spec t3 (pcOf (b+387)) 0x01ca80a3 .x28 1
    (DIGITS+52) (BitVec.ofNat 8 (X/4%4)) (codeAt_top387 hK) p3 rfl
    (by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 1) (by rw [h28a',mask_byte]) (by omega)
  have p4' : t4.pc=pcOf (b+388) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p4
  obtain ⟨t5,s5,p5,g6b,h28b,r5,f5⟩ := tail388_spec hK t4 p4'
  have h28b' : t5.getReg .x28=BitVec.ofNat 64 (X/16) &&& 3#64 := by
    rw [h28b,r4.get (by decide),l3,ofNat_shr _ _ (by omega)]
    rw [Nat.div_div_eq_div_mul]
    rfl
  obtain ⟨t6,s6,p6,g6,r6,f6⟩ := store_spec t5 (pcOf (b+390)) 0x01ca8123 .x28 2
    (DIGITS+53) (BitVec.ofNat 8 (X/16%4)) (codeAt_top390 hK) p5 rfl
    (by rw [r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide),h21]
        exact ofNat_add_ofNat _ 2) (by rw [h28b',mask_byte]) (by omega)
  have p6' : t6.pc=pcOf (b+391) := by simpa only [pcOf_add4,Nat.add_assoc,Nat.reduceAdd] using p6
  obtain ⟨t7,s7,p7,r7,f7⟩ := tail391_spec hK t6 p6'
  refine ⟨t7,((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7),?_,?_,?_,?_⟩
  · rw [p7,r6.get (by decide),r5.get (by decide),r4.get (by decide),r3.get (by decide),r2.get (by decide),r1.get (by decide)]
  · intro B hB
    rw [f7.getByte hB (by simp),g6 B hB,f5.getByte hB (by simp),g4 B hB,
      f3.getByte hB (by simp),g2 B hB,f1.getByte hB (by simp)]
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).mono (by decide)
  · exact ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).mono (by simp)
end SigGolfCandidate.T3M.Search.TopUnpack
end

section

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
theorem init_inv {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hpc : s.pc=pcOf (b+362))
    (h6 : s.getReg .x6=BitVec.ofNat 64 v.toNat)
    (h7 : s.getReg .x7=BitVec.ofNat 64 (v.toNat/2^64))
    (h30 : s.getReg .x30=BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 4 4 t ∧ Inv b s v 0 t := by
  obtain ⟨t,hs,hp,h20,h21,h30',hr,hf⟩ := init_spec hK s hpc
  refine ⟨t,hs,⟨by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · simpa using hp
  · simpa using (hr.get (r:=.x6) (by decide)).trans h6
  · simpa using (hr.get (r:=.x7) (by decide)).trans h7
  · exact h20
  · simpa using h21
  · rw [h30',h30,ofNat_add_ofNat]
  · intro j hj; omega
  · exact hr.mono (by decide)
  · exact hf.mono (by simp)
theorem iter {image : Image} {b : Nat} (hK : KernAt image b) {s t : MachineState}
    (ht : TableOK s) (v : Digest) (hvalid : T3.topRanksValid v=true)
    (hI : Inv b s v 0 t) (n : Nat) (hn : n≤17) :
    ∃ u, Steps image t (17*n) (17*n) u ∧ Inv b s v n u := by
  induction n with
  | zero => exact ⟨t,Steps.refl t,hI⟩
  | succ n ih =>
      obtain ⟨u,hs,hu⟩ := ih (by omega)
      obtain ⟨w,hw,hwI⟩ := body hK ht v hvalid n (by omega) hu
      exact ⟨w,(hs.trans hw).of_eq (by omega) (by omega),hwI⟩
end SigGolfCandidate.T3M.Search.TopUnpack
end

section


namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
private theorem tail_digit (v : Digest) (k : Nat) (hk : k<3) :
    T3.coreDigit 0 v (51+k)=v.toNat/2^119/2^(2*k)%4 := by
  simp [T3.coreDigit,show ¬51+k<51 by omega,Nat.div_div_eq_div_mul,pow_add]
theorem topUnpack_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hv : v.toNat<2^125)
    (hvalid : T3.topRanksValid v=true) (ht : TableOK s)
    (hpc : s.pc=pcOf (b+362))
    (h6 : s.getReg .x6=v.extractLsb' 0 64)
    (h7 : s.getReg .x7=v.extractLsb' 64 64)
    (h30 : s.getReg .x30=BitVec.ofNat 64 TOP_DATA) :
    ∃ t, Steps image s 302 302 t ∧ t.pc=s.getReg .x1 &&& ~~~1#64 ∧
      (∀ j, j<54 → t.getByte (BitVec.ofNat 64 (DIGITS+j))=BitVec.ofNat 8 (T3.coreDigit 0 v j)) ∧
      RegsExcept s t TopUnpack.Changed ∧ Frame s t TopUnpack.Writes := by
  have h6' : s.getReg .x6=BitVec.ofNat 64 v.toNat := by
    rw [h6]
    apply BitVec.eq_of_toNat_eq
    simp
  have h7' : s.getReg .x7=BitVec.ofNat 64 (v.toNat/2^64) := by
    rw [h7]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow]
  obtain ⟨a,sa,ha⟩ := TopUnpack.init_inv hK s v hpc h6' h7' h30
  obtain ⟨m,sm,hm⟩ := TopUnpack.iter hK ht v hvalid ha 17 (by decide)
  have hx : v.toNat/2^119<64 := by omega
  obtain ⟨t,st,pt,gt,rt,ft⟩ := TopUnpack.tail_spec hK m (by simpa using hm.pc)
    (v.toNat/2^119) hx (by simpa using hm.lo) (by simpa using hm.ptr)
  refine ⟨t,(sa.trans sm).trans st,?_,?_,?_,?_⟩
  · rw [pt,hm.regs.get (by decide)]
  · intro j hj
    rw [gt _ (by unfold DIGITS;omega)]
    by_cases h53 : j=53
    · subst j
      simp only [if_pos rfl]
      simpa using congrArg (BitVec.ofNat 8) (tail_digit v 2 (by decide)).symm
    · rw [if_neg (by omega)]
      by_cases h52 : j=52
      · subst j
        rw [if_pos rfl]
        simpa using congrArg (BitVec.ofNat 8) (tail_digit v 1 (by decide)).symm
      · rw [if_neg (by omega)]
        by_cases h51 : j=51
        · subst j
          rw [if_pos rfl]
          simpa using congrArg (BitVec.ofNat 8) (tail_digit v 0 (by decide)).symm
        · rw [if_neg (by omega)]
          exact hm.digits j (by omega)
  · exact (hm.regs.trans rt).mono (by decide)
  · exact (hm.frame.trans ft).mono (by simp)
#print axioms topUnpack_spec
end SigGolfCandidate.T3M.Search
end
