import SigGolfCandidate.T3M.Verify.MerkleRuns
import SigGolfCandidate.T3M.Verify.Judg

/-! # The final comparison using the HALT exit code

The low-word mismatch branches to the unchanged HALT(1) arm. Otherwise a subtraction of the high
words supplies the HALT exit code, which is zero exactly when those words agree. Every accepting
path takes seven instructions followed by HALT; the fuel bound conservatively remains nine.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest)

/-- A digest is determined by its two doublewords. -/
theorem cmpDig_eq_iff (d e : Digest) :
    d = e ↔ (d.extractLsb' 0 64 = e.extractLsb' 0 64 ∧ d.extractLsb' 64 64 = e.extractLsb' 64 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one] at e1 e2
    have hd : d.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact d.isLt
    have he : e.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]; exact e.isLt
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt he] at e2
    rw [← Nat.mod_add_div d.toNat (2 ^ 64), ← Nat.mod_add_div e.toNat (2 ^ 64), e1, e2]

/-- The state at a compare copy. -/
structure CmpIn (pk root : Digest) (t : MachineState) : Prop where
  copy : ∃ c, c < 64 ∧ t.pc = pcOf (cmpPc c)
  known : KnownOK baseK t
  pk : PkOK pk t
  root : DigAt t 384 root

theorem cmpBr1_holds (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 384) = x)
    (hy : t.getMem (BitVec.ofNat 64 160) = y) (d : Bool) : Br.holds t (cmpBr1 d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr1, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

theorem cmpBr2_holds (t : MachineState) (x y : Word) (hx : t.getMem (BitVec.ofNat 64 392) = x)
    (hy : t.getMem (BitVec.ofNat 64 168) = y) (d : Bool) : Br.holds t (cmpBr2 d) ↔ decide (x ≠ y) = d := by
  simp only [Br.holds, cmpBr2, CmpOp.eval, E.eval, kw, hx, hy]
  cases d <;> simp [bne_iff_ne]

set_option maxRecDepth 100000

/-- All 64 actual comparison copies satisfy the two complete path specifications. -/
theorem cmpCheck_all : (List.range 64).all cmpCheck = true := by decide +kernel

theorem cmpCheck_at (c : Nat) (hc : c < 64) : cmpCheck c = true :=
  List.all_eq_true.mp cmpCheck_all c (List.mem_range.mpr hc)

/-- Comparing both words by the final HALT exit code takes at most eight cycles. -/
theorem cmp_good (pk root : Digest) (t : MachineState) (h : CmpIn pk root t) (Q : Prop) (hQ : Q) :
    GoodQ t 9 8 Q 8 (pure (root == pk, 0)) := by
  obtain ⟨c, hc, hpc⟩ := h.copy
  have hck := cmpCheck_at c hc
  simp only [cmpCheck, Bool.and_eq_true] at hck
  obtain ⟨hA, hR1⟩ := hck
  have hr0 : t.getMem (BitVec.ofNat 64 384) = root.extractLsb' 0 64 := h.root.1
  have hr8 : t.getMem (BitVec.ofNat 64 392) = root.extractLsb' 64 64 := h.root.2
  have hp0 : t.getMem (BitVec.ofNat 64 160) = pk.extractLsb' 0 64 := h.pk.1
  have hp8 : t.getMem (BitVec.ofNat 64 168) = pk.extractLsb' 64 64 := h.pk.2
  have b1 := cmpBr1_holds t _ _ hr0 hp0
  by_cases hlo : root.extractLsb' 0 64 = pk.extractLsb' 0 64
  · obtain ⟨u, hu⟩ := spec_run hA t hpc h.known (by
      intro b hb
      simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 false).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpAcc])
    have h10 : u.getReg .x10 = root.extractLsb' 64 64 - pk.extractLsb' 64 64 := by
      simpa only [cmpDelta, E.eval, BinOp.eval, kw, hr8, hp8] using
        hu.regs (.x10, cmpDelta) (by simp [cmpAcc])
    have heq : u.getReg .x10 = 0 ↔ root = pk := by
      rw [h10]
      change root.extractLsb' 64 64 - pk.extractLsb' 64 64 = 0#64 ↔ root = pk
      rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, cmpDig_eq_iff]
      simp only [hlo, true_and]
    have hg := GoodQ.halt (Q := Q) (A := 1) (hu.ecall rfl) h5 (fun _ => ⟨hQ, le_refl 1⟩)
    have hb : decide (u.getReg .x10 = 0) = (root == pk) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, beq_iff_eq, heq]
    rw [hb] at hg
    exact GoodQ.steps' hu.steps hg (by simp [cmpAcc]) (by simp [cmpAcc])
      (fun q => ⟨q, by simp [cmpAcc]⟩)
  · have hne : root ≠ pk := fun e => hlo (by rw [e])
    rw [show (root == pk) = false from beq_eq_false_iff_ne.mpr hne]
    obtain ⟨u, hu⟩ := spec_run hR1 t hpc h.known (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      exact (b1 true).mpr (by simp [hlo])) (by simp)
    have h5 : u.getReg .x5 = 1 := hu.regs (.x5, kw 1) (by simp [cmpRej1])
    have h10 : u.getReg .x10 = 1 := hu.regs (.x10, kw 1) (by simp [cmpRej1])
    exact GoodQ.steps' hu.steps (GoodQ.reject (Q := Q) (A := 0) (hu.ecall rfl) h5 h10)
      (by simp [cmpRej1]) (by simp [cmpRej1]) (fun q => ⟨q, by simp [cmpRej1]⟩)

end SigGolfCandidate.T3M
