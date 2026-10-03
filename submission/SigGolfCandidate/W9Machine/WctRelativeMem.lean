import SigGolfCandidate.W9Machine.WctRelative
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildMain

section

namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem headRHRel_keeps (rb : Reg) (off dst : Word) (p chain digit : Nat) :
    Keeps (headRHRel rb off dst p chain digit) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRHRel]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem rungRRel_keeps (rb : Reg) (digit : Nat) (dst : Option Word) (p : Nat) :
    Keeps (rungRRel rb digit dst p) [.x12] := by
  intro x hx; cases dst <;> first | rfl | exact RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))
theorem copyFHRel_keeps (rb : Reg) (off dst : Word) (p : Nat) :
    Keeps (copyFHRel rb off dst p) [.x3, .x14] := by
  intro x hx
  simp only [copyFHRel, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRHRel_addresses (rb : Reg) (off dst : Word) (p chain digit : Nat)
    (s : MachineState) :
    ((headRHRel rb off dst p chain digit).toState s).getReg .x10 = s.getReg rb + off ∧
    ((headRHRel rb off dst p chain digit).toState s).getReg .x12 = s.getReg rb + dst := by
  simp [headRHRel, Result.toState_getReg, RegFile.get, RegFile.set, addC_eval, E.eval]
end W9Machine
end

section


namespace W9Machine
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify SigGolfCandidate.Rv RiscvZkvm.Rv64
open SigGolfCandidate.T3 (Digest pad64)
theorem relative_key (s : MachineState) (rb : Reg) (B off n : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) :
    (kAt rb (BitVec.ofNat 64 off) n).eval s = BitVec.ofNat 64 (B + off + n) := by
  simp only [kAt, Addr.eval, E.eval, hbase, ofNat_add_ofNat, Nat.add_assoc]
theorem headRHRel_mem (s : MachineState) (rb : Reg) (B off dst p chain digit A : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + off + 64 < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s).getMem
      (BitVec.ofNat 64 A) =
      if A = B + off + 24 then s.getReg .x4 else
      if A = B + off + 16 then (hLoad chain digit).eval s else s.getMem (BitVec.ofNat 64 A) := by
  exact memEval_two s _ _ _ _ (B + off + 24) (B + off + 16) A
    (relative_key s rb B off 24 hbase) (relative_key s rb B off 16 hbase)
    (by omega) (by omega) hA
theorem headRHRel_frame (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + off + 64 < 2 ^ 64) :
    Frame s ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s)
      (fun A => A = B + off + 16 ∨ A = B + off + 24) := by
  intro A hA hn
  rw [headRHRel_mem s rb B off dst p chain digit A hbase hhi hA,
    if_neg (fun h => hn (Or.inr h)), if_neg (fun h => hn (Or.inl h))]
theorem headRHRel_hashInput (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (pad0 hdr pad1 value : Digest) (hbase : s.getReg rb = BitVec.ofNat 64 B)
    (halign : (B + off) % 8 = 0) (hhi : B + off + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hlo : (hLoad chain digit).eval s = hdr.extractLsb' 0 64)
    (hhigh : s.getReg .x4 = hdr.extractLsb' 64 64)
    (hp0 : DigAt s (B + off) pad0) (hp1 : DigAt s (B + off + 32) pad1)
    (hv : DigAt s (B + off + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput
      ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := headRHRel_frame s rb B off dst p chain digit hbase hhi
  refine ClaudeWCT.W9.Machine.Merkle.hashInput_blk4 _ (B + off) pad0 hdr pad1 value
    ?_ ?_ halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  · simpa only [hbase, ofNat_add_ofNat] using
      (headRHRel_addresses rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit s).1
  · exact ((headRHRel_keeps rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
      p chain digit).reg s (by decide)).trans h11
  · constructor
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16) hbase hhi (by omega),
        if_neg (by omega), if_pos rfl]
      exact hlo
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16 + 8) hbase hhi (by omega),
        if_pos (by omega)]
      exact hhigh
end W9Machine
end
