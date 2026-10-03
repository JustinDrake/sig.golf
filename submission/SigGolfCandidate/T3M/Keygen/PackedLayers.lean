import SigGolfCandidate.T3M.Keygen.PackedRun

/-! Complete packed-header executions, before HASH. -/
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
