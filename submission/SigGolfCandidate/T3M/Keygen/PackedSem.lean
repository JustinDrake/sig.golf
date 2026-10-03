import SigGolfCandidate.T3M.Keygen.PackedBlocks

/-! # Packed producer helper semantics

The high-word store is part of the footprint. The theorem preserves the input
registers and does not assume a zero route spill or canonical source metadata.
-/
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv

/-- RV64 routed address after the layer-specific height selector. -/
def routed (s : MachineState) : Word :=
  (s.getReg .x9 <<< ((s.getReg .x7).toNat % 64)) + s.getReg .x18

/-- The low doubleword assembled by the instruction sequence. -/
def packedWord (s : MachineState) : Word :=
  ((routed s <<< 32) >>> 16) ||| (s.getReg .x8 <<< 48) ||| (193#64 <<< 56) |||
    ((s.getReg .x20 &&& 255#64) <<< 8) ||| (s.getReg .x19 ||| 128#64)

structure BodyPost (s t : MachineState) : Prop where
  low : t.getReg .x6 = packedWord s
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routed s >>> 32
  regs : RegsExcept s t [.x6, .x7, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 24)

theorem keygen_body_post (s : MachineState) : BodyPost s (run_keygen_body.res.toState s) := by
  constructor
  · simp [run_keygen_body.res, rv_simp, packedWord, routed]
  · simp [run_keygen_body.res, rv_simp, routed]
  · intro r hr
    cases r <;> simp_all [run_keygen_body.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, run_keygen_body.res]
    t3n []
    rw [if_neg (by omega)]

theorem keygen_body_spec (s : MachineState) (hpc : s.pc = pcOf 593) :
    ∃ t, Steps Images.keygenImage s 19 19 t ∧ t.pc = pcOf 132 ∧ BodyPost s t := by
  exact ⟨_, steps_keygen_body s hpc, by simp [run_keygen_body.res, rv_simp], keygen_body_post s⟩

theorem sign_body_post (s : MachineState) : BodyPost s (run_sign_body.res.toState s) := by
  have h := keygen_body_post s
  exact ⟨h.low, h.high, h.regs, h.frame⟩

theorem sign_body_spec (s : MachineState) (hpc : s.pc = pcOf 1489) :
    ∃ t, Steps Images.signImage s 19 19 t ∧ t.pc = pcOf 1028 ∧ BodyPost s t := by
  exact ⟨_, steps_sign_body s hpc, by simp [run_sign_body.res, rv_simp], sign_body_post s⟩

theorem expand_body_post (s : MachineState) : BodyPost s (run_expand_body.res.toState s) := by
  have h := keygen_body_post s
  exact ⟨h.low, h.high, h.regs, h.frame⟩

theorem expand_body_spec (s : MachineState) (hpc : s.pc = pcOf 1253) :
    ∃ t, Steps Images.expandImage s 19 19 t ∧ t.pc = pcOf 1038 ∧ BodyPost s t := by
  exact ⟨_, steps_expand_body s hpc, by simp [run_expand_body.res, rv_simp], expand_body_post s⟩

end SigGolfCandidate.T3M.Keygen.PackedBlocks
