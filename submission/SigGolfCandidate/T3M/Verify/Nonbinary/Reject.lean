import SigGolfCandidate.T3M.Verify.Nonbinary.Decode

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

/-- Every rejected source encoding takes the actual verifier to its rejection jump. -/
theorem decode_reject (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hbad : T3.decode 0 v = none) :
    ∃ k t, Steps Verify.image s k k t ∧ k ≤ 60 ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, b1, r1, f1⟩ := head_spec s v hpc hv
  by_cases hr : v.toNat < 2 ^ 125
  · rw [if_pos hr] at p1
    obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
    have hn : pairedLookupSum v ≠ 126 := by
      intro he
      rw [decode_top_paired,if_pos ⟨hr,he⟩] at hbad
      contradiction
    have hb : compressedSum (topRank v) + tailWeight v ≠ 126 := hn
    obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hr p2 w2 a2 ((ht.frame f1).frame f2)
    rw [if_neg hb] at p3 e3
    exact ⟨58,t3,(e1.trans e2).trans e3,by decide,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [if_neg hr] at p1
    exact ⟨4, t1, e1, by decide, p1, r1.mono (by decide), f1⟩

/-- Full E8: the same from the decoder's entry after the loads. -/
theorem decode_reject2 (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96162) (h16 : s.getReg .x16 = v.extractLsb' 0 64) (h17 : s.getReg .x17 = v.extractLsb' 64 64)
    (ht : PackedTables s) (hbad : T3.decode 0 v = none) :
    ∃ k t, Steps Verify.image s k k t ∧ k ≤ 58 ∧ t.pc = pcOf 96230 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, b1, r1, f1⟩ := head2_spec s v hpc h16 h17
  by_cases hr : v.toNat < 2 ^ 125
  · rw [if_pos hr] at p1
    obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
    have hn : pairedLookupSum v ≠ 126 := by
      intro he
      rw [decode_top_paired,if_pos ⟨hr,he⟩] at hbad
      contradiction
    have hb : compressedSum (topRank v) + tailWeight v ≠ 126 := hn
    obtain ⟨t3,e3,p3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hr p2 w2 a2 ((ht.frame f1).frame f2)
    rw [if_neg hb] at p3 e3
    exact ⟨56,t3,(e1.trans e2).trans e3,by decide,p3,
      ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [if_neg hr] at p1
    exact ⟨2, t1, e1, by decide, p1, r1.mono (by decide), f1⟩

end SigGolfCandidate.T3M.Verify.Nonbinary
