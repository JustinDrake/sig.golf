import SigGolfCandidate.T3M.Verify.FtsCheck

/-! The digest's six-bit gate, before the FTS initialization. -/
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false

def FtsReady (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState) : Prop :=
  SelIn pk w a 7 (s.setPC (pcOf 359)) ∧ s.pc = pcOf 362

theorem digest_gate_word (N : BitVec 256) :
    N.extractLsb' 192 64 >>> 14 &&& 63#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
    show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 6
  · simp [h, hi, show 14 + i < 64 by omega, BitVec.testBit_toNat,
      show 192 + (14 + i) = i + 206 by omega]
  · simp [h]

theorem gateBrF_holds (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (reject : Bool) :
    (gateBrF reject).holds s ↔ (!T3.digestGate a) = reject := by
  have hn : s.getReg .x28 = a.extractLsb' 192 64 := hs.nregs 3 (by decide)
  have he : BitVec.ofNat 64 (a.toNat / 2 ^ 206 % 64) = 0#64 ↔ a.toNat / 2 ^ 206 % 64 = 0 :=
    ofNat_inj (by have := Nat.mod_lt (a.toNat / 2 ^ 206) (show 0 < 64 by decide); omega) (by decide)
  change ((s.getReg .x28 >>> 14 &&& 63#64 != 0#64) = reject) ↔ _
  rw [hn, digest_gate_word]
  cases reject <;> simp only [T3.digestGate] <;> simp
  · exact he
  · exact not_congr he


theorem fts_gate_accept (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (hg : T3.digestGate a = true) :
    ∃ u, Steps image s 3 3 u ∧ FtsReady pk w a u := by
  have hb : (gateBrF false).holds s := (gateBrF_holds pk w a s hs false).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_run gateCheckF_ok s hs.pc hs.known (by simpa using hb) (by simp)
  have hm : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
  refine ⟨u, hu.steps, ⟨?_, hu.pc rfl⟩⟩
  refine ⟨rfl, hu.known, ?_, ?_, ?_, hs.ok, ?_, ?_, ?_, ?_⟩
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
  · intro k hk
    change u.getMem _ = _
    rw [hm]; exact hs.data k hk

theorem fts_gate_reject (pk : Digest) (w : WBytes) (a : HashOutput) (s : MachineState)
    (hs : SelIn pk w a 7 s) (hg : T3.digestGate a = false) :
    ∃ u, Steps image s 6 6 u ∧ Halt1 u := by
  have hb : (gateBrF true).holds s := (gateBrF_holds pk w a s hs true).2 (by rw [hg]; rfl)
  obtain ⟨u, hu⟩ := spec_run gateRejectCheckF_ok s hs.pc hs.known (by simpa [rejSpec] using hb) (by simp)
  exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
    hu.regs (.x10, cw 1) (by simp [rejSpec])⟩

end SigGolfCandidate.T3M.Verify
