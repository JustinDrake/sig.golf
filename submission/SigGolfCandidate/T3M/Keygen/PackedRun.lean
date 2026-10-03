import SigGolfCandidate.T3M.Keygen.PackedSem

/-! Exact executions from each producer header entry to its HASH instruction.
The result is expressed in RV64 words, including the nonzero high spill.
Source-header correspondence additionally requires the source coordinate bounds. -/
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv



/-- Mathematical height selected by the producer, applied with RV64 arithmetic. -/
def routedAt (s : MachineState) (height : Nat) : Word :=
  (s.getReg .x9 <<< height) + s.getReg .x18

def packedAt (s : MachineState) (height : Nat) : Word :=
  ((routedAt s height <<< 32) >>> 16) ||| (s.getReg .x8 <<< 48) ||| (193#64 <<< 56) |||
    ((s.getReg .x20 &&& 255#64) <<< 8) ||| (s.getReg .x19 ||| 128#64)

structure HeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  arg0 : t.getReg .x10 = BitVec.ofNat 64 0x201A0
  arg1 : t.getReg .x11 = 64#64
  arg2 : t.getReg .x12 = BitVec.ofNat 64 (0x201A0 + 48)
  regs : RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)

theorem keygen_header_0 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps Images.keygenImage s 30 30 t ∧ t.pc = pcOf 140 ∧ HeaderPost s t 12 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_body.res.toState s1
  have h2 := steps_keygen_body s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_store.res.toState s2
  have h3 := steps_keygen_store s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s3, ((h0.trans h1).trans h2).trans h3, ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [s3, s2, s1, s0, Result.toState_getMem, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.T3M.Keygen.PackedBlocks
