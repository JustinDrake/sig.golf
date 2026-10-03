import SigGolfCandidate.T3M.Search.TopSegments
import SigGolfCandidate.T3M.Search.TopWindow

namespace SigGolfCandidate.T3M.Search.TopUnpack
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Writes are confined to the existing64-byte decoded-digit buffer. -/
def Writes (A : Nat) : Prop := DIGITS ≤ A ∧ A < DIGITS+64
abbrev Changed : List Reg := [.x6,.x7,.x20,.x21,.x28,.x29,.x30]

/-- Extracting a byte from an aligned unsigned32-bit load reads that same byte. -/
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

/-- Every accepted rank has three exact radix-five digit bytes in the image table. -/
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

/-- One aligned packed-triple load, preserving all memory. -/
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

/-- Generic byte-store block used at the six output instructions. -/
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

/-- Rolling the low/high64-bit pair preserves the128-bit source window. -/
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
