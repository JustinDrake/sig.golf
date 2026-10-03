import SigGolfCandidate.T3M.Search.TopUnpackTailBlocks

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
