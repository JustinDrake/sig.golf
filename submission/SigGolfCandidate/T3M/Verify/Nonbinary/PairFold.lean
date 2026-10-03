import SigGolfCandidate.T3M.Verify.Nonbinary.PairExec
import SigGolfCandidate.T3M.Verify.Code

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

abbrev packedFoldRegs : List Reg := [.x19,.x24,.x25,.x29,.x14,.x17]

private theorem pairLookup_single (r : Nat) (hr : r < 128) : pairLookup r = rankLookup r := by
  simp only [pairLookup, Nat.mod_eq_of_lt hr, Nat.div_eq_of_lt hr,pairWeight,rankLookup]
  have hz : rankWeight 0 = 0 := rfl
  simp only [show 0 < 125 by decide,and_true,hz,Nat.add_zero]

private theorem pf_96164 : CodeAt Verify.image (pcOf 96164) pairInitCode := by
  have h := codeAt_from 96164 (by decide)
  have hp : pairInitCode <+: codeFrom 96164 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96167 : CodeAt Verify.image (pcOf 96167) pairPtr0Code := by
  have h := codeAt_from 96167 (by decide)
  have hp : pairPtr0Code <+: codeFrom 96167 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96169 : CodeAt Verify.image (pcOf 96169) [0x00074c83] := by
  have h := codeAt_from 96169 (by decide)
  have hp : [0x00074c83] <+: codeFrom 96169 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96170 : CodeAt Verify.image (pcOf 96170) pairShift0Code := by
  have h := codeAt_from 96170 (by decide)
  have hp : pairShift0Code <+: codeFrom 96170 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96171 : CodeAt Verify.image (pcOf 96171) pairPtrCode := by
  have h := codeAt_from 96171 (by decide)
  have hp : pairPtrCode <+: codeFrom 96171 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96173 : CodeAt Verify.image (pcOf 96173) [0x00074703] := by
  have h := codeAt_from 96173 (by decide)
  have hp : [0x00074703] <+: codeFrom 96173 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96174 : CodeAt Verify.image (pcOf 96174) pairTailCode := by
  have h := codeAt_from 96174 (by decide)
  have hp : pairTailCode <+: codeFrom 96174 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96176 : CodeAt Verify.image (pcOf 96176) pairPtrCode := by
  have h := codeAt_from 96176 (by decide)
  have hp : pairPtrCode <+: codeFrom 96176 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96178 : CodeAt Verify.image (pcOf 96178) [0x00074703] := by
  have h := codeAt_from 96178 (by decide)
  have hp : [0x00074703] <+: codeFrom 96178 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96179 : CodeAt Verify.image (pcOf 96179) pairTailCode := by
  have h := codeAt_from 96179 (by decide)
  have hp : pairTailCode <+: codeFrom 96179 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96181 : CodeAt Verify.image (pcOf 96181) pairPtrCode := by
  have h := codeAt_from 96181 (by decide)
  have hp : pairPtrCode <+: codeFrom 96181 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96183 : CodeAt Verify.image (pcOf 96183) [0x00074703] := by
  have h := codeAt_from 96183 (by decide)
  have hp : [0x00074703] <+: codeFrom 96183 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96184 : CodeAt Verify.image (pcOf 96184) pairTailCode := by
  have h := codeAt_from 96184 (by decide)
  have hp : pairTailCode <+: codeFrom 96184 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96186 : CodeAt Verify.image (pcOf 96186) singlePtrCode := by
  have h := codeAt_from 96186 (by decide)
  have hp : singlePtrCode <+: codeFrom 96186 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96188 : CodeAt Verify.image (pcOf 96188) [0x00074703] := by
  have h := codeAt_from 96188 (by decide)
  have hp : [0x00074703] <+: codeFrom 96188 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96189 : CodeAt Verify.image (pcOf 96189) singleTailCode := by
  have h := codeAt_from 96189 (by decide)
  have hp : singleTailCode <+: codeFrom 96189 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96191 : CodeAt Verify.image (pcOf 96191) pairCrossCode := by
  have h := codeAt_from 96191 (by decide)
  have hp : pairCrossCode <+: codeFrom 96191 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96193 : CodeAt Verify.image (pcOf 96193) pairPtrHiCode := by
  have h := codeAt_from 96193 (by decide)
  have hp : pairPtrHiCode <+: codeFrom 96193 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96195 : CodeAt Verify.image (pcOf 96195) [0x00074703] := by
  have h := codeAt_from 96195 (by decide)
  have hp : [0x00074703] <+: codeFrom 96195 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96196 : CodeAt Verify.image (pcOf 96196) pairTailHiCode := by
  have h := codeAt_from 96196 (by decide)
  have hp : pairTailHiCode <+: codeFrom 96196 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96198 : CodeAt Verify.image (pcOf 96198) pairPtrCode := by
  have h := codeAt_from 96198 (by decide)
  have hp : pairPtrCode <+: codeFrom 96198 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96200 : CodeAt Verify.image (pcOf 96200) [0x00074703] := by
  have h := codeAt_from 96200 (by decide)
  have hp : [0x00074703] <+: codeFrom 96200 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96201 : CodeAt Verify.image (pcOf 96201) pairTailCode := by
  have h := codeAt_from 96201 (by decide)
  have hp : pairTailCode <+: codeFrom 96201 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96203 : CodeAt Verify.image (pcOf 96203) pairPtrCode := by
  have h := codeAt_from 96203 (by decide)
  have hp : pairPtrCode <+: codeFrom 96203 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96205 : CodeAt Verify.image (pcOf 96205) [0x00074703] := by
  have h := codeAt_from 96205 (by decide)
  have hp : [0x00074703] <+: codeFrom 96205 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96206 : CodeAt Verify.image (pcOf 96206) pairTailCode := by
  have h := codeAt_from 96206 (by decide)
  have hp : pairTailCode <+: codeFrom 96206 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96208 : CodeAt Verify.image (pcOf 96208) pairPtrCode := by
  have h := codeAt_from 96208 (by decide)
  have hp : pairPtrCode <+: codeFrom 96208 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96210 : CodeAt Verify.image (pcOf 96210) [0x00074703] := by
  have h := codeAt_from 96210 (by decide)
  have hp : [0x00074703] <+: codeFrom 96210 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

private theorem pf_96211 : CodeAt Verify.image (pcOf 96211) pairTailCode := by
  have h := codeAt_from 96211 (by decide)
  have hp : pairTailCode <+: codeFrom 96211 := by decide +kernel
  exact ⟨by decide,by decide,by decide +kernel,hp.trans h.2.2.2⟩

theorem pairStep_spec {image : Image} (s : MachineState) (pc : Word) (v : Digest) (q sum : Nat)
    (hc1 : CodeAt image pc pairPtrCode) (hc2 : CodeAt image (pc+4+4) [0x00074703])
    (hc3 : CodeAt image (pc+4+4+4) pairTailCode) (hpc : s.pc = pc)
    (hq : q < 7 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x29 = topWindow v q) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (hm : s.getReg .x24 = 16383#64)
    (ht : PackedTables s) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc+4+4+4+4+4 ∧
      t.getReg .x29 = topWindow v (q+2) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + pairLookup (pairRank v q)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := pairPtr_spec s pc hc1 hpc v q (by omega) hw hb hm
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 hc2 p1 (by rfl) (by decide)
    _ (pairRank_lt v q) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := pairTail_spec s2 _ hc3 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  exact ⟨s3,(e1.trans e2).trans e3,p3,w3.trans (pairWindow_shift v q (by omega)),a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩

theorem pairHiStep_spec {image : Image} (s : MachineState) (pc : Word) (v : Digest) (q sum : Nat)
    (hc1 : CodeAt image pc pairPtrHiCode) (hc2 : CodeAt image (pc+4+4) [0x00074703])
    (hc3 : CodeAt image (pc+4+4+4) pairTailHiCode) (hpc : s.pc = pc)
    (hq : q < 7 ∨ (9 ≤ q ∧ q < 16))
    (hw : s.getReg .x17 = topWindow v q) (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (hm : s.getReg .x24 = 16383#64)
    (ht : PackedTables s) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pc+4+4+4+4+4 ∧
      t.getReg .x29 = topWindow v (q+2) ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + pairLookup (pairRank v q)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := pairPtrHi_spec s pc hc1 hpc v q (by omega) hw hb hm
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 hc2 p1 (by rfl) (by decide)
    _ (pairRank_lt v q) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := pairTailHi_spec s2 _ hc3 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  exact ⟨s3,(e1.trans e2).trans e3,p3,w3.trans (pairWindow_shift v q (by omega)),a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩

theorem singleStep_spec (s : MachineState) (v : Digest) (sum : Nat)
    (hpc : s.pc = pcOf 96186) (hw : s.getReg .x29 = topWindow v 8)
    (hs : s.getReg .x25 = BitVec.ofNat 64 sum)
    (hb : s.getReg .x19 = BitVec.ofNat 64 PAIR_DATA) (ht : PackedTables s) :
    ∃ t, Steps Verify.image s 5 5 t ∧ t.pc = pcOf 96191 ∧
      t.getReg .x29 = v.extractLsb' 0 64 >>> 63 ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup (topRank v 8)) ∧
      RegsExcept s t [.x25,.x29,.x14] ∧ Frame s t (fun _ => False) := by
  obtain ⟨s1,e1,p1,a1,r1,f1⟩ := singlePtr_spec s _ pf_96186 hpc v hw hb
  obtain ⟨s2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec s1 _ 0x00074703 .x14 pf_96188 p1 (by rfl) (by decide)
    _ (by have := topRank_lt v 8; omega) a1 (ht.frame f1).pair
  obtain ⟨s3,e3,p3,w3,a3,r3,f3⟩ := singleTail_spec s2 _ pf_96189 p2 _ sum _
    (by rw [r2.get (by decide),r1.get (by decide),hw])
    (by rw [r2.get (by decide),r1.get (by decide),hs]) a2
  rw [pairLookup_single _ (topRank_lt v 8)] at a3
  refine ⟨s3,(e1.trans e2).trans e3,p3,?_,a3,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  simpa [topWindow,← BitVec.shiftRight_add] using w3

/-- All nine actual checksum reads, including the preserved cross-word dispatch window. -/
theorem pairedFold_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96164) (h16 : s.getReg .x16 = v.extractLsb' 0 64)
    (h17 : s.getReg .x17 = v.extractLsb' 64 64) (ht : PackedTables s) :
    ∃ t, Steps Verify.image s 49 49 t ∧ t.pc = pcOf 96213 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x25 = BitVec.ofNat 64 (compressedSum (topRank v)) ∧
      t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x19 = BitVec.ofNat 64 PAIR_DATA ∧ t.getReg .x24 = 16383#64 ∧
      RegsExcept s t packedFoldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨u0,e0,p0,b0,m0,r0,f0⟩ := pairInit_spec s _ pf_96164 hpc
  obtain ⟨u1,e1,p1,a1,r1,f1⟩ := pairPtr0_spec u0 _ pf_96167 p0 v 0 (by decide)
    (by rw [r0.get (by decide),h16]; simp [topWindow]) b0 m0
  obtain ⟨u2,e2,p2,a2,r2,f2⟩ := pair_lbu_spec u1 _ 0x00074c83 .x25 pf_96169 p1
    (by rfl) (by decide) _ (pairRank_lt v 0) a1 ((ht.frame f0).frame f1).pair
  obtain ⟨t0,e3,p3,w0,r3,f3⟩ := pairShift0_spec u2 _ pf_96170 p2 v
    (by rw [r2.get (by decide),r1.get (by decide),r0.get (by decide),h16])
  have E0 : Steps Verify.image s 7 7 t0 := ((e0.trans e1).trans e2).trans e3
  have R0 : RegsExcept s t0 packedFoldRegs := (((r0.trans r1).trans r2).trans r3).mono (by decide)
  have F0 : Frame s t0 (fun _ => False) := (((f0.trans f1).trans f2).trans f3).mono (by simp)
  have S0 : t0.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0)) := by rw [r3.get (by decide),a2]
  have B0 : t0.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),b0]
  have M0 : t0.getReg .x24 = 16383#64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),m0]
  have H0 : t0.getReg .x17 = v.extractLsb' 64 64 := by rw [r3.get (by decide),r2.get (by decide),r1.get (by decide),r0.get (by decide),h17]
  obtain ⟨t1,e1p,p1p,w1,a1,r1p,f1p⟩ := pairStep_spec t0 (pcOf 96171) v 2 _
    pf_96171 pf_96173 pf_96174 p3 (by decide) w0 S0 B0 M0 (ht.frame F0)
  have E1 : Steps Verify.image s 12 12 t1 := E0.trans e1p
  have R1 : RegsExcept s t1 packedFoldRegs := (R0.trans r1p).mono (by decide)
  have F1 : Frame s t1 (fun _ => False) := (F0.trans f1p).mono (by simp)
  have S1 : t1.getReg .x25 = BitVec.ofNat 64 (pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) := a1
  have B1 : t1.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r1p.get (by decide),B0]
  have M1 : t1.getReg .x24 = 16383#64 := by rw [r1p.get (by decide),M0]
  have H1 : t1.getReg .x17 = v.extractLsb' 64 64 := by rw [r1p.get (by decide),H0]
  obtain ⟨t2,e2p,p2p,w2,a2,r2p,f2p⟩ := pairStep_spec t1 (pcOf 96176) v 4 _
    pf_96176 pf_96178 pf_96179 p1p (by decide) w1 S1 B1 M1 (ht.frame F1)
  have E2 : Steps Verify.image s 17 17 t2 := E1.trans e2p
  have R2 : RegsExcept s t2 packedFoldRegs := (R1.trans r2p).mono (by decide)
  have F2 : Frame s t2 (fun _ => False) := (F1.trans f2p).mono (by simp)
  have S2 : t2.getReg .x25 = BitVec.ofNat 64 ((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) := a2
  have B2 : t2.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r2p.get (by decide),B1]
  have M2 : t2.getReg .x24 = 16383#64 := by rw [r2p.get (by decide),M1]
  have H2 : t2.getReg .x17 = v.extractLsb' 64 64 := by rw [r2p.get (by decide),H1]
  obtain ⟨t3,e3p,p3p,w3,a3,r3p,f3p⟩ := pairStep_spec t2 (pcOf 96181) v 6 _
    pf_96181 pf_96183 pf_96184 p2p (by decide) w2 S2 B2 M2 (ht.frame F2)
  have E3 : Steps Verify.image s 22 22 t3 := E2.trans e3p
  have R3 : RegsExcept s t3 packedFoldRegs := (R2.trans r3p).mono (by decide)
  have F3 : Frame s t3 (fun _ => False) := (F2.trans f3p).mono (by simp)
  have S3 : t3.getReg .x25 = BitVec.ofNat 64 (((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) := a3
  have B3 : t3.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r3p.get (by decide),B2]
  have M3 : t3.getReg .x24 = 16383#64 := by rw [r3p.get (by decide),M2]
  have H3 : t3.getReg .x17 = v.extractLsb' 64 64 := by rw [r3p.get (by decide),H2]
  obtain ⟨us,es,ps,ws,ass,rs,fs⟩ := singleStep_spec t3 v _ p3p w3 S3 B3 (ht.frame F3)
  obtain ⟨t4,ec,pc,wc,rc,fc⟩ := pairCross_spec us _ pf_96191 ps v ws
    (by rw [rs.get (by decide),H3])
  have E4 : Steps Verify.image s 29 29 t4 := (E3.trans es).trans ec
  have R4 : RegsExcept s t4 packedFoldRegs := ((R3.trans rs).trans rc).mono (by decide)
  have F4 : Frame s t4 (fun _ => False) := ((F3.trans fs).trans fc).mono (by simp)
  have S4 : t4.getReg .x25 = BitVec.ofNat 64 ((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) := by rw [rc.get (by decide),ass]
  have B4 : t4.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [rc.get (by decide),rs.get (by decide),B3]
  have M4 : t4.getReg .x24 = 16383#64 := by rw [rc.get (by decide),rs.get (by decide),M3]
  have H4 : t4.getReg .x17 = v.extractLsb' 63 64 := wc
  obtain ⟨t5,e5p,p5p,w5,a5,r5p,f5p⟩ := pairHiStep_spec t4 (pcOf 96193) v 9 _
    pf_96193 pf_96195 pf_96196 pc (by decide) (by simpa [topWindow] using H4) S4 B4 M4 (ht.frame F4)
  have E5 : Steps Verify.image s 34 34 t5 := E4.trans e5p
  have R5 : RegsExcept s t5 packedFoldRegs := (R4.trans r5p).mono (by decide)
  have F5 : Frame s t5 (fun _ => False) := (F4.trans f5p).mono (by simp)
  have S5 : t5.getReg .x25 = BitVec.ofNat 64 (((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) := a5
  have B5 : t5.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r5p.get (by decide),B4]
  have M5 : t5.getReg .x24 = 16383#64 := by rw [r5p.get (by decide),M4]
  have H5 : t5.getReg .x17 = v.extractLsb' 63 64 := by rw [r5p.get (by decide),H4]
  obtain ⟨t6,e6p,p6p,w6,a6,r6p,f6p⟩ := pairStep_spec t5 (pcOf 96198) v 11 _
    pf_96198 pf_96200 pf_96201 p5p (by decide) w5 S5 B5 M5 (ht.frame F5)
  have E6 : Steps Verify.image s 39 39 t6 := E5.trans e6p
  have R6 : RegsExcept s t6 packedFoldRegs := (R5.trans r6p).mono (by decide)
  have F6 : Frame s t6 (fun _ => False) := (F5.trans f6p).mono (by simp)
  have S6 : t6.getReg .x25 = BitVec.ofNat 64 ((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) := a6
  have B6 : t6.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r6p.get (by decide),B5]
  have M6 : t6.getReg .x24 = 16383#64 := by rw [r6p.get (by decide),M5]
  have H6 : t6.getReg .x17 = v.extractLsb' 63 64 := by rw [r6p.get (by decide),H5]
  obtain ⟨t7,e7p,p7p,w7,a7,r7p,f7p⟩ := pairStep_spec t6 (pcOf 96203) v 13 _
    pf_96203 pf_96205 pf_96206 p6p (by decide) w6 S6 B6 M6 (ht.frame F6)
  have E7 : Steps Verify.image s 44 44 t7 := E6.trans e7p
  have R7 : RegsExcept s t7 packedFoldRegs := (R6.trans r7p).mono (by decide)
  have F7 : Frame s t7 (fun _ => False) := (F6.trans f7p).mono (by simp)
  have S7 : t7.getReg .x25 = BitVec.ofNat 64 (((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) := a7
  have B7 : t7.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r7p.get (by decide),B6]
  have M7 : t7.getReg .x24 = 16383#64 := by rw [r7p.get (by decide),M6]
  have H7 : t7.getReg .x17 = v.extractLsb' 63 64 := by rw [r7p.get (by decide),H6]
  obtain ⟨t8,e8p,p8p,w8,a8,r8p,f8p⟩ := pairStep_spec t7 (pcOf 96208) v 15 _
    pf_96208 pf_96210 pf_96211 p7p (by decide) w7 S7 B7 M7 (ht.frame F7)
  have E8 : Steps Verify.image s 49 49 t8 := E7.trans e8p
  have R8 : RegsExcept s t8 packedFoldRegs := (R7.trans r8p).mono (by decide)
  have F8 : Frame s t8 (fun _ => False) := (F7.trans f8p).mono (by simp)
  have S8 : t8.getReg .x25 = BitVec.ofNat 64 ((((((((pairLookup (pairRank v 0) + pairLookup (pairRank v 2)) + pairLookup (pairRank v 4)) + pairLookup (pairRank v 6)) + rankLookup (topRank v 8)) + pairLookup (pairRank v 9)) + pairLookup (pairRank v 11)) + pairLookup (pairRank v 13)) + pairLookup (pairRank v 15)) := a8
  have B8 : t8.getReg .x19 = BitVec.ofNat 64 PAIR_DATA := by rw [r8p.get (by decide),B7]
  have M8 : t8.getReg .x24 = 16383#64 := by rw [r8p.get (by decide),M7]
  have H8 : t8.getReg .x17 = v.extractLsb' 63 64 := by rw [r8p.get (by decide),H7]
  refine ⟨t8,E8,p8p,w8,?_,H8,B8,M8,R8,F8⟩
  simpa only [pairLookup_pairRank,Nat.reduceAdd,compressedSum] using S8

end SigGolfCandidate.T3M.Verify.Nonbinary
