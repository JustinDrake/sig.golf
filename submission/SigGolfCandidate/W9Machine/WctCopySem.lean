import SigGolfCandidate.W9Machine.WctRelativeMem

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest)
theorem copyFHRel_mem (s : MachineState) (rb : Reg) (B off dst p A : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s).getMem
      (BitVec.ofNat 64 A) =
      if A = B + dst + 8 then s.getMem (BitVec.ofNat 64 (B + off + 56)) else
      if A = B + dst then s.getMem (BitVec.ofNat 64 (B + off + 48)) else
      s.getMem (BitVec.ofNat 64 A) := by
  have hm := memEval_two s (kAt rb (BitVec.ofNat 64 dst) 8)
    (kAt rb (BitVec.ofNat 64 dst) 0) (lAt rb (BitVec.ofNat 64 off) 56)
    (lAt rb (BitVec.ofNat 64 off) 48) (B + dst + 8) (B + dst + 0) A
    (relative_key s rb B dst 8 hbase) (relative_key s rb B dst 0 hbase)
    (by omega) (by omega) hA
  simpa only [Result.toState_getMem, copyFHRel, lAt, E.eval, addC_eval, hbase,
    ofNat_add_ofNat, Nat.add_zero, Nat.add_assoc] using hm
theorem copyFHRel_frame (s : MachineState) (rb : Reg) (B off dst p : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64) :
    Frame s ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (fun A => A = B + dst ∨ A = B + dst + 8) := by
  intro A hA hn
  rw [copyFHRel_mem s rb B off dst p A hbase hhi hA,
    if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
theorem copyFHRel_digest (s : MachineState) (rb : Reg) (B off dst p : Nat) (value : Digest)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + dst + 16 < 2 ^ 64)
    (hv : DigAt s (B + off + 48) value) :
    DigAt ((copyFHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p).toState s)
      (B + dst) value := by
  constructor
  · rw [copyFHRel_mem s rb B off dst p (B + dst) hbase hhi (by omega),
      if_neg (by omega), if_pos rfl]
    exact hv.1
  · rw [copyFHRel_mem s rb B off dst p (B + dst + 8) hbase hhi (by omega), if_pos rfl]
    simpa only [Nat.add_assoc] using hv.2
end W9Machine
