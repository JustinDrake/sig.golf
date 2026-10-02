import SigGolfCandidate.T3M.Search.Blocks
import SigGolfCandidate.T3M.Search.TopTables

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
variable {image : Image} {b : Nat}

/-- Every poisoned-checksum lookup is an in-bounds byte read, without alignment restrictions. -/
theorem top_lookup_access (r : Nat) (hr : r < 128) :
    accessValid (BitVec.ofNat 64 (TOP_DATA + r)) 1 = true := by
  have hlt : TOP_DATA + r < 2 ^ 64 := by unfold TOP_DATA; omega
  simp only [accessValid_iff, MEMORY_BYTES, toNat_ofNat_lt hlt, Nat.mod_one,
    and_true, true_and]
  unfold TOP_DATA
  omega

/-- The exact table byte is the poisoned rank weight, lifted without truncation. -/
theorem SumTableOK.rank (s : MachineState) (ht : SumTableOK s) (r : Nat) (hr : r < 128) :
    (s.getByte (BitVec.ofNat 64 (TOP_DATA + r))).zeroExtend 64 = BitVec.ofNat 64 (rankLookup r) := by
  rw [ht r hr]
  have h := rankLookup_le r
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A sum-table byte read, stepped directly because symbolic subword loads require aligned bases. -/
theorem top_lbu (s : MachineState) (pc : Word) (inst : BitVec 32) (rd : Reg)
    (hc : CodeAt image pc [inst]) (hpc : s.pc = pc)
    (hd : decodeInstruction inst = some (.base (.LBU rd .x29 0)))
    (r : Nat) (hr : r < 128) (h29 : s.getReg .x29 = BitVec.ofNat 64 (TOP_DATA + r))
    (ht : SumTableOK s) :
    Steps image s 1 1 ((s.setReg rd (BitVec.ofNat 64 (rankLookup r))).setPC (s.pc + 4)) := by
  have hz : signExtend12 (0 : BitVec 12) = (0 : Word) := rfl
  have hv : accessValid (s.getReg .x29 + signExtend12 0) 1 = true := by
    rw [h29, hz]
    simpa only [add_zero] using top_lookup_access r hr
  have hs := steps_lbu hc hpc hd hv
  simpa only [h29, hz, add_zero, SumTableOK.rank s ht r hr] using hs

/-- Framed form of the unaligned byte load used by the checksum fold. -/
theorem top_lbu_spec (s : MachineState) (pc : Word) (inst : BitVec 32) (rd : Reg)
    (hc : CodeAt image pc [inst]) (hpc : s.pc = pc)
    (hd : decodeInstruction inst = some (.base (.LBU rd .x29 0))) (hrd : rd ≠ .x0)
    (r : Nat) (hr : r < 128) (h29 : s.getReg .x29 = BitVec.ofNat 64 (TOP_DATA + r))
    (ht : SumTableOK s) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pc + 4 ∧
      t.getReg rd = BitVec.ofNat 64 (rankLookup r) ∧ RegsExcept s t [rd] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, top_lbu s pc inst rd hc hpc hd r hr h29 ht, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun p => p + 4) hpc
  · exact MachineState.getReg_setReg_eq hrd
  · intro q hq
    simp only [List.mem_singleton] at hq
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hq)
  · intro A _ _; simp [MachineState.setReg, MachineState.setPC, MachineState.getMem]

end SigGolfCandidate.T3M.Search
