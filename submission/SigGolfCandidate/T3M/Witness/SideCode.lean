import SigGolfCandidate.T3M.Witness.Layout
namespace SigGolfCandidate.T3M.SideCode
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def sideWidth (a : Nat) : Nat := min a 4
def sideHeader (a merge node : Nat) : Nat := 128*merge+segOffset a+node%segSideMod a

theorem finite_fields : ∀ (a : Fin 11) (m : Fin 2) (s : Fin 16),
    sideHeader a.val m.val s.val <256 ∧
    segFoldCount (sideHeader a.val m.val s.val)=a.val ∧
    segMerge (sideHeader a.val m.val s.val)=m.val ∧
    segSides (sideHeader a.val m.val s.val)=s.val%segSideMod a.val := by decide +kernel

theorem segSideMod_dvd_sixteen (a : Nat) : segSideMod a ∣ 16 := by
  have h := Nat.pow_dvd_pow 2 (Nat.min_le_right a 4)
  exact h

theorem header_mod (a m n : Nat) : sideHeader a m n = sideHeader a m (n%16) := by
  unfold sideHeader
  rw [Nat.mod_mod_of_dvd _ (segSideMod_dvd_sixteen a)]

theorem sideHeader_fields (a merge node : Nat) (ha : a < 11) (hm : merge < 2) :
    sideHeader a merge node <256 ∧ segFoldCount (sideHeader a merge node)=a ∧
    segMerge (sideHeader a merge node)=merge ∧ segSides (sideHeader a merge node)=node%segSideMod a := by
  rw [header_mod]
  have h:=finite_fields ⟨a,ha⟩ ⟨merge,hm⟩ ⟨node%16,Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.mod_mod_of_dvd _ (segSideMod_dvd_sixteen a)] using h

theorem heap_low_bits (g lo a : Nat) (h : lo+a ≤ 11) :
    (2048+g)/2^lo % segSideMod a = g/2^lo % segSideMod a := by
  have hlo : lo ≤ 11 := by omega
  have hp : 2048 = 2^(11-lo)*2^lo := by
    rw [← pow_add,Nat.sub_add_cancel hlo]
    norm_num
  rw [hp,Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.two_pow_pos lo)]
  have hwidth : min a 4 ≤ 11-lo := by omega
  have hd : segSideMod a ∣ 2^(11-lo) := Nat.pow_dvd_pow 2 hwidth
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd,Nat.add_zero,Nat.mod_mod]

theorem honest_sideHeader_check (g lo a merge : Nat) (ha : a < 11) (h : lo+a≤11) (hm : merge<2) :
    segSides (sideHeader a merge (g/2^lo)) % segSideMod a = (2048+g)/2^lo % segSideMod a := by
  rw [(sideHeader_fields a merge (g/2^lo) ha hm).2.2.2,Nat.mod_mod,heap_low_bits g lo a h]

theorem check_preserves_original_parity (b E a : Nat) (ha : 0<a)
    (h : segSides b % segSideMod a = E % segSideMod a) : segSides b %2=E%2 := by
  have hd : 2 ∣ segSideMod a := by
    have hw : 1 ≤ min a 4 := by omega
    have hh:=Nat.pow_dvd_pow 2 hw
    simpa only [segSideMod,pow_one] using hh
  have he:=congrArg (fun n=>n%2) h
  simpa only [Nat.mod_mod_of_dvd _ hd] using he
end SigGolfCandidate.T3M.SideCode
