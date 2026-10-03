import SigGolfCandidate.T3M.Search.TopFold
import SigGolfCandidate.T3M.Search.TopTail

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

theorem rankPartial_le (v : Digest) (n : Nat) : rankPartial v n ≤ 255 * n := by
  induction n with
  | zero => simp [rankPartial]
  | succ n ih =>
    rw [rankPartial]
    have := rankLookup_le (topRank v n)
    omega

/-- Exact packed-rank validation: 97 instructions after the two-instruction high-bit check. -/
theorem topCheck_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hpc : s.pc = pcOf (b + 265))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h17 : s.getReg .x17 = 126#64) (ht : SumTableOK s) :
    ∃ t, Steps image s 97 97 t ∧
      t.pc = (if topLookupSum v = 126 then pcOf (b + 362) else pcOf (b + 468)) ∧
      t.getReg .x25 = BitVec.ofNat 64 (topLookupSum v) ∧
      t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t foldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, w1, a1, x301, r1, f1⟩ := topFold_spec hK s v hpc h6 h7 ht
  obtain ⟨t2, e2, p2, a2, r2, f2⟩ := topTail_spec hK t1 v (rankPartial v 17)
    (rankPartial_le v 17) hv p1 w1 a1 (by rw [r1.get (by decide), h17])
  have he : rankPartial v 17 + tailWeight v = topLookupSum v := by
    rw [rankPartial_seventeen]; rfl
  refine ⟨t2, e1.trans e2, ?_, ?_, ?_, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (by simp)⟩
  · simpa only [he] using p2
  · simpa only [he] using a2
  · rw [r2.get (by decide), x301]

end SigGolfCandidate.T3M.Search
