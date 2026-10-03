import SigGolfCandidate.T3M.Verify.FtsRuns
import SigGolfCandidate.T3M.Witness.SideCode

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 20000

theorem parBr_holds {m : MachineState} {ev : Nat} (h : m.getReg .x23 = FtsRev.rv ev)
    (hev : ev < 4096) (a bits : Nat) (ha : 0<a) (d : Bool) :
    Br.holds m (parBr a bits d) ↔ d = decide (ev % segSideMod a ≠ bits % segSideMod a) := by
  by_cases h1 : a=1
  · subst a
    have key : BitVec.slt (m.getReg .x23) 0#64 = decide (ev%2=1) := by rw [h]; exact FtsRev.rv_slt ev
    rcases Nat.mod_two_eq_zero_or_one bits with hb | hb <;>
      rcases Nat.mod_two_eq_zero_or_one ev with he | he <;>
      cases d <;> simp [Br.holds, parBr, segSideMod, E.eval, CmpOp.eval, cw, key, hb, he]
  have hk : 0 < min a 3 ∧ min a 3≤64 := by omega
  have bound (v : Nat) : T3.Rev.revBits (min a 3) v < 2^64 :=
    lt_of_lt_of_le (T3.Rev.revBits_lt _ _) (Nat.pow_le_pow_right (by decide) hk.2)
  have key : (parE a).eval m = BitVec.ofNat 64 (T3.Rev.revBits (min a 3) ev) := by
    simp only [parE, E.eval, cw, h]
    exact FtsRev.rv_srl_prefix ev _ hk
  have heq : (BitVec.ofNat 64 (T3.Rev.revBits (min a 3) ev) =
      BitVec.ofNat 64 (T3.Rev.revBits (min a 3) (bits % segSideMod a))) ↔
      ev % segSideMod a = bits % segSideMod a := by
    constructor
    · intro hw
      have hn := congrArg BitVec.toNat hw
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bound _)] at hn
      apply T3.Rev.revBits_inj (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _))
      simpa only [segSideMod, T3.Rev.revBits_mod] using hn
    · intro hn
      have hn' := congrArg (T3.Rev.revBits (min a 3)) hn
      simp only [segSideMod, T3.Rev.revBits_mod] at hn'
      simp only [segSideMod, T3.Rev.revBits_mod, hn']
  simp only [Br.holds, parBr, if_neg h1, key, E.eval, CmpOp.eval, cw]
  by_cases hn : ev%segSideMod a=bits%segSideMod a
  · have hw := heq.mpr hn
    simp [hn, hw, eq_comm]
  · have hw := fun h => hn (heq.mp h)
    have hb := bne_iff_ne.mpr hw
    simp [hn, hb, eq_comm]

/-- The checked low bits remain available while consuming folds. -/
theorem sides_init (E bits a : Nat) (h : bits % segSideMod a = E % segSideMod a) :
    ∀ k, k < min a 3 → E/2^k%2 = bits/2^k%2 := by
  intro k hk
  have hd : 2^(k+1) ∣ segSideMod a := Nat.pow_dvd_pow 2 (by omega)
  have he := congrArg (fun n => n % (2^(k+1))) h
  simp only [Nat.mod_mod_of_dvd _ hd] at he
  have hh := congrArg (fun n => n / 2^k) he
  rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self] at hh
  exact hh.symm

theorem sides_next (E bits a i : Nat)
    (h : ∀ k, i+k < min a 3 → E/2^k%2 = bits/2^(i+k)%2) :
    ∀ k, i+1+k < min a 3 → (E/2)/2^k%2 = bits/2^(i+1+k)%2 := by
  intro k hk
  have hh := h (k+1) (by omega)
  simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

theorem foldPc_pos (tb X a bits t i : Nat) (hX : X<3) (ha : 0<a ∧ a≤11) (hb : bits<8) :
    0 < foldPc tb X a bits t i := by
  by_cases hin : inlineRow X a
  · simp only [foldPc, if_pos hin]
    unfold rowPc slotPc tabBase; split <;> omega
  simp only [foldPc, if_neg hin]
  have hp : ∀ x:Fin 3, ∀ n:Fin 10, ∀ b:Fin 8, 0<threeStart x (n+2) b := by decide +kernel
  by_cases h1 : a=1
  · simp only [h1,if_pos]
    unfold ladPc ladBase;split_ifs <;> omega
  · have he := hp ⟨X,hX⟩ ⟨a-2,by omega⟩ ⟨bits,hb⟩
    have he' : 0 < threeStart X a bits := by simpa only [Nat.sub_add_cancel (by omega : 2≤a)] using he
    simp only [if_neg h1,threeFoldPc];split_ifs <;> omega

theorem inlineTailId_lt (tb a bits : Nat) (htb : tb<2) (ha : a≤3) (hb : bits<8) :
    inlineTailId tb a bits < 141 := by unfold inlineTailId; omega

theorem foldTailId_lt (tb X a bits t : Nat) (htb : tb<2) (ha : 0<a ∧ a≤11) (hb : bits<8) (ht : t<2) :
    foldTailId tb X a bits t < 141 := by
  by_cases hin : inlineRow X a
  · simp only [foldTailId, if_pos hin]
    exact inlineTailId_lt tb a bits htb (by unfold inlineRow at hin; omega) hb
  · simp only [foldTailId, if_neg hin]
    unfold threeTailId; split_ifs <;> omega

theorem tailPc_pos (X k : Nat) (hX : X<3) (hk : k<141) : 0 < tailPc X k := by
  have h : ∀ x:Fin 3, ∀ k:Fin 141, 0<tailPc x k := by decide +kernel
  exact h ⟨X,hX⟩ ⟨k,hk⟩

theorem zeroTailPc (tb b : Nat) (htb : tb<2) (hb : b<256) (ha : segA b=0) :
    tailPc (segX tb b) (inlineTailId tb 0 (segSides b)) = slotPc tb b + 3 := by
  have h : ∀ tb:Fin 2, ∀ b:Fin 256, segA b=0 →
      tailPc (segX tb b) (inlineTailId tb 0 (segSides b)) = slotPc tb b + 3 := by decide +kernel
  exact h ⟨tb,htb⟩ ⟨b,hb⟩ ha


theorem segSides_lt (b : Nat) (hb : b<256) : segSides b<8 := by
  have h : ∀ x:Fin 256, segSides x.val<8 := by decide +kernel
  exact h ⟨b,hb⟩

end SigGolfCandidate.T3M.Verify
