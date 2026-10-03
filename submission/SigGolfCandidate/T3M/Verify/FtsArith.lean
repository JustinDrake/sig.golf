import SigGolfCandidate.T3M.Verify.FtsRuns
import SigGolfCandidate.T3M.Witness.SideCode

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxRecDepth 20000

theorem parBr_holds {m : MachineState} {ev : Nat} (h : m.getReg .x23 = BitVec.ofNat 64 ev)
    (hev : ev < 4096) (a bits : Nat) (d : Bool) :
    Br.holds m (parBr a bits d) ↔ d = decide (ev % segSideMod a ≠ bits % segSideMod a) := by
  have hm : segSideMod a ≤ 16 := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
  have hpos : 0 < segSideMod a := Nat.two_pow_pos _
  have key : (parE a).eval m = BitVec.ofNat 64 (ev % segSideMod a) := by
    apply BitVec.eq_of_toNat_eq
    simp only [parE, E.eval, BinOp.eval, cw, h, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : ev < 2^64), Nat.mod_eq_of_lt (by omega : segSideMod a-1 < 2^64)]
    change ev &&& (2^(min a 4)-1) = ev % segSideMod a % 2^64
    rw [Nat.and_two_pow_sub_one_eq_mod]
    change ev%segSideMod a = ev%segSideMod a%2^64
    exact (Nat.mod_eq_of_lt (by have := Nat.mod_lt ev hpos;omega : ev%segSideMod a<2^64)).symm
  simp only [Br.holds, parBr, E.eval, key, CmpOp.eval, BinOp.eval, cw]
  have heq : (BitVec.ofNat 64 (ev % segSideMod a) = BitVec.ofNat 64 (bits % segSideMod a)) ↔
      ev % segSideMod a = bits % segSideMod a := by
    constructor
    · intro hw
      have hn:=congrArg BitVec.toNat hw
      simpa only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := Nat.mod_lt ev hpos;omega : ev%segSideMod a<2^64),
        Nat.mod_eq_of_lt (by have := Nat.mod_lt bits hpos;omega : bits%segSideMod a<2^64)] using hn
    · intro hn;rw [hn]
  have hxe : (BitVec.ofNat 64 (ev % segSideMod a) ^^^ BitVec.ofNat 64 (bits % segSideMod a) = 0#64) ↔
      ev % segSideMod a = bits % segSideMod a := BitVec.xor_eq_zero_iff.trans heq
  by_cases hn : ev%segSideMod a=bits%segSideMod a
  · have hw:=hxe.mpr hn
    simp [hn,hw,eq_comm]
  · have hw : (BitVec.ofNat 64 (ev%segSideMod a) ^^^ BitVec.ofNat 64 (bits%segSideMod a)) ≠ 0#64 := fun h=>hn (hxe.mp h)
    have hb : ((BitVec.ofNat 64 (ev%segSideMod a) ^^^ BitVec.ofNat 64 (bits%segSideMod a)) != 0#64) = true := bne_iff_ne.mpr hw
    simp [hn,hb,eq_comm]


/-- The checked low bits remain available while consuming folds. -/
theorem sides_init (E bits a : Nat) (h : bits % segSideMod a = E % segSideMod a) :
    ∀ k, k < min a 4 → E/2^k%2 = bits/2^k%2 := by
  intro k hk
  have hd : 2^(k+1) ∣ segSideMod a := Nat.pow_dvd_pow 2 (by omega)
  have he := congrArg (fun n => n % (2^(k+1))) h
  simp only [Nat.mod_mod_of_dvd _ hd] at he
  have hh := congrArg (fun n => n / 2^k) he
  rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self] at hh
  exact hh.symm

theorem sides_next (E bits a i : Nat)
    (h : ∀ k, i+k < min a 4 → E/2^k%2 = bits/2^(i+k)%2) :
    ∀ k, i+1+k < min a 4 → (E/2)/2^k%2 = bits/2^(i+1+k)%2 := by
  intro k hk
  have hh := h (k+1) (by omega)
  simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

theorem foldPc_pos (X a bits t i : Nat) (hX : X<3) (ha : 0<a ∧ a≤10) (hb : bits<16) :
    0 < foldPc X a bits t i := by
  have hp : ∀ x:Fin 3, ∀ n:Fin 9, ∀ b:Fin 16, 0<fourStart x (n+2) b := by decide +kernel
  by_cases h1 : a=1
  · simp only [foldPc,h1,if_pos]
    unfold ladPc ladBase;split_ifs <;> omega
  · have he := hp ⟨X,hX⟩ ⟨a-2,by omega⟩ ⟨bits,hb⟩
    have he' : 0 < fourStart X a bits := by simpa only [Nat.sub_add_cancel (by omega : 2≤a)] using he
    simp only [foldPc,if_neg h1,fourFoldPc];split_ifs <;> omega

theorem foldTailId_lt (a bits t : Nat) (ha : 0<a ∧ a≤10) (hb : bits<16) (ht : t<2) :
    foldTailId a bits t < 121 := by unfold foldTailId fourTailId;split_ifs <;> omega

theorem tailPc_pos (X k : Nat) (hX : X<3) (hk : k<121) : 0 < tailPc X k := by
  have h : ∀ x:Fin 3, ∀ k:Fin 121, 0<tailPc x k := by decide +kernel
  exact h ⟨X,hX⟩ ⟨k,hk⟩


theorem segSides_lt (b : Nat) (hb : b<256) : segSides b<16 := by
  have h : ∀ x:Fin 256, segSides x.val<16 := by decide +kernel
  exact h ⟨b,hb⟩

end SigGolfCandidate.T3M.Verify
