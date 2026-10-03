import SigGolfCandidate.T3M.Verify.FtsCheck

/-! The digest's ten-bit gate, before the FTS initialization. -/
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false

def FtsReady (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) : Prop :=
  SelIn pk w a 7 (s.setPC (pcOf 359)) ∧ s.pc = pcOf 362

theorem digest_gate_field (N : BitVec 256) : (N.extractLsb' 192 64 >>> 54).toNat = N.toNat / 2 ^ 246 := by
  have h1 : N.toNat / 2 ^ 192 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by
    calc N.toNat < 2 ^ 256 := N.isLt
      _ = 2 ^ 192 * 2 ^ 64 := by norm_num)
  rw [BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h1, Nat.div_div_eq_div_mul]
  all_goals norm_num

/-- `srli 54; sltiu 135` on digest word 3 is Core's ten-bit gate. -/
theorem digest_gate_ult (N : BitVec 256) :
    BitVec.ult (N.extractLsb' 192 64 >>> 54) (BitVec.ofNat 64 135) = decide (N.toNat / 2 ^ 246 < 135) := by
  simp only [BitVec.ult, digest_gate_field, BitVec.toNat_ofNat]
  all_goals norm_num

theorem gateBrF_holds (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (reject : Bool) :
    (gateBrF reject).holds s ↔ (!T3.digestGate a) = reject := by
  have hn : s.getReg .x28 = a.extractLsb' 192 64 := hs.nregs 3 (by decide)
  change (((if BitVec.ult (s.getReg .x28 >>> 54) (BitVec.ofNat 64 135) then (1 : BitVec 64) else 0)
    == BitVec.ofNat 64 0) = reject) ↔ _
  rw [hn, digest_gate_ult]
  simp only [T3.digestGate]
  generalize a.toNat / 2 ^ 246 = v
  by_cases hv : v < 135
  · have h' : ¬ 135 ≤ v := by omega
    cases reject <;> simp [hv, h']
  · have h' : 135 ≤ v := by omega
    cases reject <;> simp [hv, h']


/-- The gate preserves the reverse-table base until FTS setup replaces it. -/
private theorem gateCheck_keep_sp :
    specB [] [] baseK (runAt baseK [362] 359 [.br false])
      ⟨[], [], 362, false, 3, [gateBrF false], none, 3⟩ [] baseK (.x2 :: selKeep) = true := by
  decide +kernel

theorem fts_gate_accept (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (hg : T3.digestGate a = true) :
    ∃ u, Steps image s 3 3 u ∧ FtsReady pk w a u := by
  have hb : (gateBrF false).holds s := (gateBrF_holds pk w a s hs false).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_run gateCheck_keep_sp s hs.pc hs.known (by simpa using hb) (by simp)
  have hm : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
  refine ⟨u, hu.steps, ⟨?_, hu.pc rfl⟩⟩
  refine ⟨rfl, hu.known, ?_, ?_, ?_, hs.ok, ?_, ?_, ?_, ?_, ?_⟩
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

theorem fts_gate_reject (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (hg : T3.digestGate a = false) :
    ∃ u, Steps image s 6 6 u ∧ Halt1 u := by
  have hb : (gateBrF true).holds s := (gateBrF_holds pk w a s hs true).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_run gateRejectCheckF_ok s hs.pc hs.known (by simpa [rejSpec] using hb) (by simp)
  exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
    hu.regs (.x10, cw 1) (by simp [rejSpec])⟩

end SigGolfCandidate.T3M.Verify
