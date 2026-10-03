import SigGolfCandidate.T3M.Verify.Arith

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))
theorem pcOf_add4 (n : Nat) : pcOf n + 4 = pcOf (n + 1) := by
  unfold pcOf
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
  congr 1
theorem known_get {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s) {r : Reg}
    {v : Word} (hm : (r, v) ∈ known) : s.getReg r = v := h _ hm
theorem KnownOK_append {k1 k2 : List (Reg × Word)} {s : MachineState} :
    KnownOK (k1 ++ k2) s ↔ KnownOK k1 s ∧ KnownOK k2 s := by
  simp only [KnownOK, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp); exacts [h1 p hp, h2 p hp]
theorem KnownOK.writeHash {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s)
    (a : BitVec 256) : KnownOK known (writeHash s a) := Known_writeHash h a
theorem KnownOK.mono {k1 k2 : List (Reg × Word)} {s : MachineState} (h : KnownOK k1 s)
    (hsub : ∀ p ∈ k2, p ∈ k1) : KnownOK k2 s := fun p hp => h p (hsub p hp)
@[simp] theorem E_eval_c (s : MachineState) (v : Word) : (E.c v).eval s = v := rfl
@[simp] theorem E_eval_reg (s : MachineState) (r : Reg) : (E.reg r).eval s = s.getReg r := rfl
end SigGolfCandidate.T3M.Verify
