import SigGolfCandidate.T3M.Expand.HeaderBlocks
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem header_jump_193 (s : MachineState) (hpc : s.pc=pcOf 193) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 1162 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_193 codeAt_193 s hpc (by simp [eblk_193.res,rv_simp]),?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_193.res,rv_simp]
  · ex_regs eblk_193.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_193.res,rv_simp]

theorem header_pack_193 (s : MachineState) (hpc : s.pc=pcOf 193) (cnt par : Nat)
    (hc : cnt<16) (hp : par<16) (h23 : s.getReg .x23=BitVec.ofNat 64 cnt)
    (h24 : s.getReg .x24=BitVec.ofNat 64 par) :
    ∃ t, Steps image s 9 9 t ∧ t.pc=pcOf 195 ∧
      (t.getReg .x28).truncate 8=BitVec.ofNat 8 (emitHeader cnt false par) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t0,k0,p0,r0,f0⟩:=header_jump_193 s hpc
  have h0 : t0.getReg .x23=BitVec.ofNat 64 cnt := by rw [r0.get (by simp),h23]
  obtain ⟨t1,k1,p1,r1,f1⟩:=header_1162 t0 p0 cnt hc h0
  have h1 : t1.getReg .x23=BitVec.ofNat 64 cnt := by rw [r1.get (by simp),h0]
  have hpar : t1.getReg .x24=BitVec.ofNat 64 par := by rw [r1.get (by simp),r0.get (by simp),h24]
  by_cases hsmall : cnt<4
  · rw [if_pos hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1169 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1174 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par false)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ false
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]
  · rw [if_neg hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1164 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1174 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par false)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ false
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]

theorem header_jump_860 (s : MachineState) (hpc : s.pc=pcOf 860) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 1175 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_860 codeAt_860 s hpc (by simp [eblk_860.res,rv_simp]),?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_860.res,rv_simp]
  · ex_regs eblk_860.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_860.res,rv_simp]

theorem header_pack_860 (s : MachineState) (hpc : s.pc=pcOf 860) (cnt par : Nat)
    (hc : cnt<16) (hp : par<16) (h23 : s.getReg .x23=BitVec.ofNat 64 cnt)
    (h24 : s.getReg .x24=BitVec.ofNat 64 par) :
    ∃ t, Steps image s 9 9 t ∧ t.pc=pcOf 862 ∧
      (t.getReg .x28).truncate 8=BitVec.ofNat 8 (emitHeader cnt false par) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t0,k0,p0,r0,f0⟩:=header_jump_860 s hpc
  have h0 : t0.getReg .x23=BitVec.ofNat 64 cnt := by rw [r0.get (by simp),h23]
  obtain ⟨t1,k1,p1,r1,f1⟩:=header_1175 t0 p0 cnt hc h0
  have h1 : t1.getReg .x23=BitVec.ofNat 64 cnt := by rw [r1.get (by simp),h0]
  have hpar : t1.getReg .x24=BitVec.ofNat 64 par := by rw [r1.get (by simp),r0.get (by simp),h24]
  by_cases hsmall : cnt<4
  · rw [if_pos hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1182 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1187 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par false)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ false
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]
  · rw [if_neg hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1177 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1187 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par false)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ false
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]

theorem header_jump_975 (s : MachineState) (hpc : s.pc=pcOf 975) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 1188 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound eblk_975 codeAt_975 s hpc (by simp [eblk_975.res,rv_simp]),?_,?_,?_⟩
  · simp [Result.toState_pc,eblk_975.res,rv_simp]
  · ex_regs eblk_975.res
  · intro A hA hn; simp [Result.toState_getMem,eblk_975.res,rv_simp]

theorem header_pack_975 (s : MachineState) (hpc : s.pc=pcOf 975) (cnt par : Nat)
    (hc : cnt<16) (hp : par<16) (h23 : s.getReg .x23=BitVec.ofNat 64 cnt)
    (h24 : s.getReg .x24=BitVec.ofNat 64 par) :
    ∃ t, Steps image s 10 10 t ∧ t.pc=pcOf 978 ∧
      (t.getReg .x28).truncate 8=BitVec.ofNat 8 (emitHeader cnt true par) ∧
      RegsExcept s t [.x28,.x30] ∧ Frame s t (fun _=>False) := by
  obtain ⟨t0,k0,p0,r0,f0⟩:=header_jump_975 s hpc
  have h0 : t0.getReg .x23=BitVec.ofNat 64 cnt := by rw [r0.get (by simp),h23]
  obtain ⟨t1,k1,p1,r1,f1⟩:=header_1188 t0 p0 cnt hc h0
  have h1 : t1.getReg .x23=BitVec.ofNat 64 cnt := by rw [r1.get (by simp),h0]
  have hpar : t1.getReg .x24=BitVec.ofNat 64 par := by rw [r1.get (by simp),r0.get (by simp),h24]
  by_cases hsmall : cnt<4
  · rw [if_pos hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1195 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1200 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par true)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ true
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]
  · rw [if_neg hsmall] at p1
    obtain ⟨t2,k2,p2,v2,r2,f2⟩:=header_1190 t1 p1 cnt hc h1
    obtain ⟨t3,k3,p3,v3,r3,f3⟩:=header_1200 t2 p2
    refine ⟨t3,by simpa using ((k0.trans k1).trans k2).trans k3,p3,?_,?_,?_⟩
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (emitHeader_lt cnt par true)]
      rw [v3,v2,hpar]
      have hh:=pack_header ⟨cnt,hc⟩ ⟨par,hp⟩ true
      simpa [hsmall] using hh
    · exact (((r0.trans r1).trans r2).trans r3).mono (by intro r hr; simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at *; tauto)
    · intro A hA hn
      rw [f3 A hA (by simp),f2 A hA (by simp),f1 A hA (by simp),f0 A hA (by simp)]
end SigGolfCandidate.T3M.Expand
