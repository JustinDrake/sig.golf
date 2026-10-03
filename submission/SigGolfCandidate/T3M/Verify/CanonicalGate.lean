import SigGolfCandidate.T3M.Verify.CanonicalSetup

/-! The digest's three-bit gate, before the FTS initialization. -/
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Verify
set_option linter.unusedSimpArgs false

/-- The gate preserves the reverse-table base until FTS setup replaces it. -/
private theorem gateCheck_keep_sp :
    specB [] [] baseK (runAtC {} baseK [362] 359 [.br false])
      ⟨[], [], 362, false, 3, [gateBrF false], none, 3⟩ [] baseK (.x2 :: selKeep) = true := by
  decide +kernel

theorem fts_gate_accept (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelState pk w a 7 s) (hg : T3.digestGate a = true) :
    ∃ u, Steps fixture s 3 3 u ∧ ReadyC pk w a u := by
  have hb : (gateBrF false).holds s := (gateBrF_holds pk w a s hs.toSelIn false).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_runC gateCheck_keep_sp s hs.pc hs.known (by simpa using hb) (by simp)
  have hm : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
  refine ⟨u, hu.steps, ⟨?_, hu.pc rfl⟩⟩
  refine ⟨⟨rfl, hu.known, ?_, ?_, ?_, hs.ok, ?_, ?_, ?_, ?_, ?_⟩,?_⟩
  · intro k hk
    change u.getReg (nReg k) = _
    rw [hu.keep (nReg k) (by rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)]
    exact hs.nregs k hk
  · change u.getReg .x22 = _
    rw [hu.keep .x22 (by decide)]; exact hs.idx
  · intro c k hc hk
    change u.getMem _ = _
    rw [hm]; exact hs.etab c k hc hk
  · intro j hj
    change u.getMem _ = _
    rw [hm]; exact hs.wit j hj
  · change PkOK pk u
    exact ⟨(hm _).trans hs.pk.1, (hm _).trans hs.pk.2⟩
  · intro A hA h1 h2
    change u.getMem _ = _
    rw [hm]; exact hs.zero A hA h1 h2
  · exact hs.data.congr (fun A _ _ => hm _)
  · change u.getReg .x2 = _
    rw [hu.keep .x2 (by decide)]; exact hs.sp

  · exact hu.tables hs.tables (RelOK.nil s)

theorem gate_reject_checked :
    specB [] [] [] (runAtC {} baseK [] 359 [.br true])
      (rejSpec 6 [gateBrF true]) [] [] []=true := by decide +kernel

theorem fts_gate_reject (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelState pk w a 7 s) (hg : T3.digestGate a = false) :
    ∃ u, Steps fixture s 6 6 u ∧ HaltC1 u := by
  have hb : (gateBrF true).holds s := (gateBrF_holds pk w a s hs.toSelIn true).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_runC gate_reject_checked s hs.pc hs.known (by simpa [rejSpec] using hb) (by simp)
  exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec]),
    hu.regs (.x10, SigGolfCandidate.T3M.Verify.cw 1) (by simp [rejSpec])⟩

#print axioms fts_gate_accept
#print axioms fts_gate_reject
end SigGolfCandidate.T3M.CanonicalNative
