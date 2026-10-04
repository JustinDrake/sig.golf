import SigGolfCandidate.T3M.Keygen.PackedRun
import SigGolfCandidate.T3.PackedChain
import SigGolfCandidate.T3M.Keygen.Blocks

section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sign_header_0 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps Images.signImage s 30 30 t ∧ t.pc = pcOf 1036 ∧ HeaderPost s t 12 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_body.res.toState s1
  have h2 := steps_sign_body s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_store.res.toState s2
  have h3 := steps_sign_store s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_1 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps Images.signImage s 33 33 t ∧ t.pc = pcOf 1036 ∧ HeaderPost s t 7 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_inc.res.toState s2
  have h3 := steps_sign_inc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_2 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps Images.signImage s 34 34 t ∧ t.pc = pcOf 1036 ∧ HeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem sign_header_3 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps Images.signImage s 34 34 t ∧ t.pc = pcOf 1036 ∧ HeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, run_sign_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end

section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem keygen_header_1 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps Images.keygenImage s 33 33 t ∧ t.pc = pcOf 140 ∧ HeaderPost s t 7 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_inc.res.toState s2
  have h3 := steps_keygen_inc s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem keygen_header_2 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps Images.keygenImage s 34 34 t ∧ t.pc = pcOf 140 ∧ HeaderPost s t 6 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_layer23.res.toState s2
  have h3 := steps_keygen_layer23 s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem keygen_header_3 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps Images.keygenImage s 34 34 t ∧ t.pc = pcOf 140 ∧ HeaderPost s t 6 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_layer23.res.toState s2
  have h3 := steps_keygen_layer23 s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end

section


namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option backward.isDefEq.respectTransparency false
theorem routedAt_nat (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) = BitVec.ofNat 64 (tree * 2 ^ height lay + leaf) := by
  rw [routedAt, ht, hf, ofNat_shl, ofNat_add_ofNat]
theorem routedAt_high_zero (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) >>> 32 = 0 := by
  rw [routedAt_nat s lay tree leaf ht hf, ofNat_shr _ _ (by omega),
    Nat.div_eq_of_lt (by omega)]
  rfl
theorem packedAt_nat (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = BitVec.ofNat 64
      (128 + i + step * 2^8 + (tree * 2^height lay + leaf) * 2^16 + lay.val * 2^48 + 193 * 2^56) := by
  have hl := lay.isLt
  have hm : BitVec.ofNat 64 step &&& 255#64 = BitVec.ofNat 64 step := by
    interval_cases step <;> rfl
  have hroute : ((BitVec.ofNat 64 (tree * 2^height lay + leaf) <<< 32) >>> 16) =
      BitVec.ofNat 64 ((tree * 2^height lay + leaf) * 2^16) := by
    rw [ofNat_shl, ofNat_shr _ _ (by omega)]
    congr 1
    omega
  rw [packedAt, routedAt_nat s lay tree leaf h9 h18, hroute, h8, h19, h20, hm,
    ofNat_shl, ofNat_shl, ofNat_shl]
  rw [ofNat_or_disjoint' i 128 7 (by omega) (by decide)]
  rw [ofNat_or_disjoint' _ _ 48 (by omega) (by omega)]
  rw [ofNat_or_disjoint' _ _ 56 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 16 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 8 (by omega) (by omega)]
  congr 1
  omega
private theorem low_ofNat (n : Nat) :
    (BitVec.ofNat 128 n).extractLsb' 0 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega
theorem packedAt_source (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = (chainHeader lay tree leaf i step).extractLsb' 0 64 := by
  exact (packedAt_nat s lay tree leaf i step hr hi hs h8 h9 h18 h19 h20).trans
    ((congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (low_ofNat _)).symm
private theorem high_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 128 n).extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change _ = 0
  omega
theorem source_high_actual (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 64 64 = 0#64 := by
  have hl := lay.isLt
  exact (congrArg (fun x : BitVec 128 => x.extractLsb' 64 64)
    (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (high_ofNat _ (by omega))
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end

section




namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
open PackedBlocks
set_option backward.isDefEq.respectTransparency false
def headerK (lay : Layer) : Nat := if lay.val = 0 then 30 else if lay.val = 1 then 33 else 34
def rungK (lay : Layer) : Nat := headerK lay + 5
def rungC (lay : Layer) : Nat := headerK lay + 12
theorem shared_header {image : Image} {b : Nat} (h : SubAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      HeaderPost s t (height lay) := by
  rcases h.2.2.2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · fin_cases lay
    · exact keygen_header_0 s hpc h8
    · exact keygen_header_1 s hpc h8
    · exact keygen_header_2 s hpc h8
    · exact keygen_header_3 s hpc h8
  · fin_cases lay
    · exact sign_header_0 s hpc h8
    · exact sign_header_1 s hpc h8
    · exact sign_header_2 s hpc h8
    · exact sign_header_3 s hpc h8
theorem shared_header_source {image : Image} {b : Nat} (h : SubAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    ∃ t, Steps image s (headerK lay) (headerK lay) t ∧ t.pc = pcOf (b + 23) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x201A0 ∧ t.getReg .x11 = 64#64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x201A0 + 48) ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = (chainHeader lay tree leaf i step).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = (chainHeader lay tree leaf i step).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24) := by
  obtain ⟨t, st, pc, post⟩ := shared_header h s hpc lay h8
  refine ⟨t, st, pc, post.arg0, post.arg1, post.arg2,
    post.low.trans (packedAt_source s lay tree leaf i step hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (source_high_actual lay tree leaf i step hr hf hi hs).symm
end SigGolfCandidate.T3M.Keygen
end
