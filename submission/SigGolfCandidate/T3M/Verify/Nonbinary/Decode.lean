import SigGolfCandidate.T3M.Verify.Nonbinary.Tail
import SigGolfCandidate.T3M.Search.CsBlocks

namespace SigGolfCandidate.T3M.Verify.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
def headCode : List (BitVec 32) := [0x14003803, 0x14803883, 0x03d8d713, 0x10071663]
sym_block headBase := symRun { noAlias := true } headCode (pcOf 96160) 200

theorem head_at : CodeAt Verify.image (pcOf 96160) headCode := by
  have h := codeAt_from 96160 (by decide)
  have hp : headCode <+: codeFrom 96160 := by decide +kernel
  exact ⟨by decide, by decide, by decide +kernel, hp.trans h.2.2.2⟩

theorem head_spec (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) :
    ∃ t, Steps Verify.image s 4 4 t ∧
      t.pc = (if v.toNat < 2 ^ 125 then pcOf 96164 else pcOf 96230) ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 64 64 ∧
      RegsExcept s t [.x16,.x17,.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headBase head_at s hpc (by simp [headBase.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, headBase.res, E.eval, CmpOp.eval, BinOp.eval,
      show BitVec.ofNat 64 (320 + 8) = 328#64 from rfl, hv.2,
      BitVec.toNat_ofNat, Nat.reduceMod, bne_iff_ne, ne_eq,
      ext64_shr_eq_zero v 61 (by decide), show (64 + 61 : Nat) = 125 from rfl]
    split_ifs <;> first | rfl | omega
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.1
  · simpa only [Result.toState_getReg, headBase.res, rv_simp] using hv.2
  · intro r hr; cases r <;> simp at hr <;> simp [headBase.res, rv_simp] <;> rfl
  · intro A _ _; simp [headBase.res, rv_simp]

theorem compressedSum_le (v : Digest) : compressedSum (topRank v) ≤ 4335 := by
  have h0 := pairWeight_le (topRank v 0) (topRank v 1)
  have h1 := pairWeight_le (topRank v 2) (topRank v 3)
  have h2 := pairWeight_le (topRank v 4) (topRank v 5)
  have h3 := pairWeight_le (topRank v 6) (topRank v 7)
  have h4 := rankLookup_le (topRank v 8)
  have h5 := pairWeight_le (topRank v 9) (topRank v 10)
  have h6 := pairWeight_le (topRank v 11) (topRank v 12)
  have h7 := pairWeight_le (topRank v 13) (topRank v 14)
  have h8 := pairWeight_le (topRank v 15) (topRank v 16)
  unfold compressedSum; omega

/-- The actual verifier validates exactly the original decoder in sixty steps. -/
theorem decode_ok (s : MachineState) (v : Digest)
    (hpc : s.pc = pcOf 96160) (hv : DigAt s 320 v) (ht : PackedTables s)
    (hvalid : T3.decode 0 v = some (topDigits v)) :
    ∃ t, Steps Verify.image s 60 60 t ∧ t.pc = pcOf 96220 ∧
      t.getReg .x16 = v.extractLsb' 0 64 ∧ t.getReg .x17 = v.extractLsb' 63 64 ∧
      t.getReg .x29 = topWindow v 17 ∧ t.getReg .x25 = 126#64 ∧
      RegsExcept s t [.x16,.x17,.x14,.x25,.x29,.x19,.x24] ∧ Frame s t (fun _ => False) := by
  have hh : v.toNat < 2 ^ 125 ∧ pairedLookupSum v = 126 := by
    rw [decode_top_paired] at hvalid
    split_ifs at hvalid with hh
    exact hh
  obtain ⟨t1,e1,p1,a1,b1,r1,f1⟩ := head_spec s v hpc hv
  rw [if_pos hh.1] at p1
  obtain ⟨t2,e2,p2,w2,a2,h172,b192,b242,r2,f2⟩ := pairedFold_spec t1 v p1 a1 b1 (ht.frame f1)
  have hb : compressedSum (topRank v) + tailWeight v = 126 := hh.2
  obtain ⟨t3,e3,p3,a3,r3,f3⟩ := tail_spec t2 v _ (compressedSum_le v) hh.1 p2 w2 a2 ((ht.frame f1).frame f2)
  rw [if_pos hb] at p3
  refine ⟨t3,(e1.trans e2).trans e3,p3,?_,?_,?_,?_,
    ((r1.trans r2).trans r3).mono (by decide),((f1.trans f2).trans f3).mono (by simp)⟩
  · rw [r3.get (by decide),r2.get (by decide),a1]
  · rw [r3.get (by decide),h172]
  · rw [r3.get (by decide),w2]
  · rw [a3,hb]

end SigGolfCandidate.T3M.Verify.Nonbinary
