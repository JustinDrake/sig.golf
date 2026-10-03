import SigGolfCandidate.T3M.Search.TopUnpackBlocks

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
