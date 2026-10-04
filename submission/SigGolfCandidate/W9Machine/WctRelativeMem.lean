import SigGolfCandidate.W9Machine.WctPackedRuns
import SigGolfCandidate.T3M.Verify.ChainSem

section


set_option autoImplicit false
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
open SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest pad64)
theorem hashInput_blk4 (t : MachineState) (A : Nat) (a b c d : Digest)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (hA : A % 8 = 0)
    (hA' : A + 64 < 2 ^ 64) (ha : DigAt t A a) (hb : DigAt t (A + 16) b) (hc : DigAt t (A + 32) c)
    (hd : DigAt t (A + 48) d) : hashInput t = toQ (pad64 (blk4 a b c d)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA hA' h11
  rw [wordsOf_blk4, ha.1, ha.2, hb.1, hc.1, hd.1, show A + 24 = A + 16 + 8 by omega, hb.2,
    show A + 40 = A + 32 + 8 by omega, hc.2, show A + 56 = A + 48 + 8 by omega, hd.2]
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
      if A = B + off + 16 then (packedHeader chain digit).eval s else s.getMem (BitVec.ofNat 64 A) := by
  exact memEval_one s _ _ (B + off + 16) A
    (relative_key s rb B off 16 hbase) (by omega) hA
theorem headRHRel_frame (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (hbase : s.getReg rb = BitVec.ofNat 64 B) (hhi : B + off + 64 < 2 ^ 64) :
    Frame s ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s)
      (fun A => A = B + off + 16) := by
  intro A hA hn
  rw [headRHRel_mem s rb B off dst p chain digit A hbase hhi hA,
    if_neg hn]
theorem headRHRel_hashInput (s : MachineState) (rb : Reg) (B off dst p chain digit : Nat)
    (pad0 hdr pad1 value : Digest) (hbase : s.getReg rb = BitVec.ofNat 64 B)
    (halign : (B + off) % 8 = 0) (hhi : B + off + 64 < 2 ^ 64)
    (h11 : s.getReg .x11 = BitVec.ofNat 64 64)
    (hlo : (packedHeader chain digit).eval s = hdr.extractLsb' 0 64)
    (hhigh : s.getMem (BitVec.ofNat 64 (B + off + 24)) = hdr.extractLsb' 64 64)
    (hp0 : DigAt s (B + off) pad0) (hp1 : DigAt s (B + off + 32) pad1)
    (hv : DigAt s (B + off + 48) value) :
    SigGolfCandidate.Legacy.Riscv.hashInput
      ((headRHRel rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit).toState s) =
      toQ (pad64 (blk4 pad0 hdr pad1 value)) := by
  have hf := headRHRel_frame s rb B off dst p chain digit hbase hhi
  refine W9Machine.hashInput_blk4 _ (B + off) pad0 hdr pad1 value
    ?_ ?_ halign hhi (hp0.frame hf (by omega) (by omega) (by omega)) ?_
    (hp1.frame hf (by omega) (by omega) (by omega))
    (hv.frame hf (by omega) (by omega) (by omega))
  · simpa only [hbase, ofNat_add_ofNat] using
      (headRHRel_addresses rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst) p chain digit s).1
  · exact ((headRHRel_keeps rb (BitVec.ofNat 64 off) (BitVec.ofNat 64 dst)
      p chain digit).reg s (by decide)).trans h11
  · constructor
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16) hbase hhi (by omega),
        if_pos rfl]
      exact hlo
    · rw [headRHRel_mem s rb B off dst p chain digit (B + off + 16 + 8) hbase hhi (by omega),
        if_neg (by omega)]
      simpa only [Nat.add_assoc] using hhigh
end W9Machine
end
